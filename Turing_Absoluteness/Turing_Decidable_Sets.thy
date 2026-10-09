theory Turing_Decidable_Sets
  imports "Set_Coded_Invariance_ZF.Turing_Halting_Sentences"
begin

text \<open>Main result: every Turing-decidable set of natural numbers belongs to
every transitive set model of ZFC (\<open>tm_decidable_in_transitive_model\<close>).
The proof internalises acceptance on unary inputs and applies Separation
inside the model.\<close>

section \<open>Runs with an arbitrary outer environment\<close>

context tm_model
begin

lemma trans_run_steps:
  assumes env: "env \<in> list(A)" and p: "p \<in> nat" and P: "nth(p,env) = P" "P \<in> machine"
    and c0: "c0 \<in> configuration" and n: "n \<in> nat" and rA: "r \<in> A" and r0: "r`0 = c0"
    and rs: "\<And>k. k \<in> n \<Longrightarrow>
      (A, Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, env)))) \<Turnstile> step_fm(p#+4,1,0))"
  shows "r`n = steps(P,c0,n)"
proof -
  have "\<And>k. k \<in> nat \<Longrightarrow> k \<le> n \<longrightarrow> r`k = steps(P,c0,k)"
  proof -
    fix k assume k: "k \<in> nat"
    then show "k \<le> n \<longrightarrow> r`k = steps(P,c0,k)"
    proof (induct k rule: nat_induct)
      case 0 show ?case using r0 by simp
    next
      case (succ k)
      show ?case
      proof
        assume le: "succ(k) \<le> n"
        then have kn: "k \<in> n" using succ.hyps(1) n by (simp add: succ_le_iff ltD)
        have "k \<le> n" using le by (blast intro: leI succ_leE)
        then have rk: "r`k = steps(P,c0,k)" using succ.hyps(2) by blast
        have conf: "r`k \<in> configuration" using rk steps_type[OF P(2) c0 succ.hyps(1)] by simp
        have kA: "k \<in> A" "succ(k) \<in> A" using succ.hyps(1) by simp_all
        have envA: "Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, env)))) \<in> list(A)"
          using rA kA env by simp
        have "r`succ(k) = step(P,r`k)"
          using sats_step_fm[OF _ _ _ envA, of "p#+4" 1 0 P "r`k" "r`succ(k)"] rs[OF kn] P p conf rA kA
          by simp
        then show "r`succ(k) = steps(P,c0,succ(k))" using rk succ.hyps(1) by simp
      qed
    qed
  qed
  from this[OF n] n show ?thesis by (simp add: nat_into_Ord)
qed

lemma trace_trans:
  assumes env: "env \<in> list(A)" and p: "p \<in> nat" and P: "nth(p,env) = P" "P \<in> machine"
    and c0: "c0 \<in> configuration" and n: "n \<in> nat" and k: "k \<in> n"
  shows "(A, Cons((\<lambda>j\<in>succ(n). steps(P,c0,j))`succ(k), Cons((\<lambda>j\<in>succ(n). steps(P,c0,j))`k,
      Cons(succ(k), Cons(k, env)))) \<Turnstile> step_fm(p#+4,1,0))"
proof -
  have knat: "k \<in> nat" using k n by (blast intro: Ord_trans Ord_nat)
  have sk: "succ(k) \<in> succ(n)" using k n by (simp add: Ord_succ_mem_iff nat_into_Ord)
  have k1: "k \<in> succ(n)" using k by (rule succI2)
  have conf: "steps(P,c0,k) \<in> configuration" using steps_type[OF P(2) c0 knat] .
  have conf2: "steps(P,c0,succ(k)) \<in> configuration"
    using steps_type[OF P(2) c0 nat_succI[OF knat]] .
  have kA: "k \<in> A" "succ(k) \<in> A" using knat by simp_all
  have envA: "Cons(steps(P,c0,succ(k)), Cons(steps(P,c0,k), Cons(succ(k), Cons(k, env)))) \<in> list(A)"
    using kA env conf conf2 by simp
  show ?thesis
    using sats_step_fm[OF _ _ _ envA, of "p#+4" 1 0 P "steps(P,c0,k)" "steps(P,c0,succ(k))"]
      P p conf conf2 sk k1 knat
    by simp
qed

end

section \<open>Unary inputs\<close>

definition rep_fm :: "[i,i] \<Rightarrow> i" where
  "rep_fm(n,x) \<equiv>
    Exists(And(Exists(Exists(And(empty_fm(1), And(Nil_fm(0), fun_apply_fm(2,1,0))))),
      And(Forall(Implies(Member(0,n#+2),
          Exists(Exists(Exists(Exists(
            And(succ_fm(4,3), And(const_fm(1,2), And(fun_apply_fm(5,4,1),
            And(fun_apply_fm(5,3,0), Cons_fm(2,1,0))))))))))),
        fun_apply_fm(0,n#+1,x#+1))))"

lemma rep_fm_type [TC]: "\<lbrakk>n \<in> nat; x \<in> nat\<rbrakk> \<Longrightarrow> rep_fm(n,x) \<in> formula"
  unfolding rep_fm_def by simp

definition rep_witness :: "[i,i,i] \<Rightarrow> o" where
  "rep_witness(g,n,x) \<equiv> g`0 = [] \<and> (\<forall>k\<in>n. g`succ(k) = Cons(1,g`k)) \<and> g`n = x"

context tm_model
begin

lemma repeat_in_A [simp]: "k \<in> nat \<Longrightarrow> repeat(1,k) \<in> A"
proof (rule symbols_in_A)
  assume k: "k \<in> nat"
  have "1 \<in> symbol" by (simp add: symbol_def)
  then show "repeat(1,k) \<in> list(symbol)" using k by (rule repeat_type)
qed

lemma sats_rep_fm_witness:
  assumes idx: "jn \<in> nat" "jx \<in> nat" and env: "env \<in> list(A)"
    and n: "nth(jn,env) \<in> nat"
  shows "(A, env \<Turnstile> rep_fm(jn,jx)) \<longleftrightarrow> (\<exists>g\<in>A. rep_witness(g,nth(jn,env),nth(jx,env)))"
proof -
  have k_A: "\<And>k. k \<in> nth(jn,env) \<Longrightarrow> k \<in> A \<and> succ(k) \<in> A"
    using n by (blast intro: Ord_trans Ord_nat nat_in_A nat_succI)
  show ?thesis
    unfolding rep_fm_def rep_witness_def
    using idx env n k_A by (auto simp add: zero_in_M)
qed

lemma rep_witness_iff:
  assumes n: "n \<in> nat" and x: "x \<in> A"
  shows "(\<exists>g\<in>A. rep_witness(g,n,x)) \<longleftrightarrow> x = repeat(1,n)"
proof
  assume "\<exists>g\<in>A. rep_witness(g,n,x)"
  then obtain g where g0: "g`0 = []" and gs: "\<And>k. k \<in> n \<Longrightarrow> g`succ(k) = Cons(1,g`k)"
    and gn: "g`n = x" unfolding rep_witness_def by blast
  have "\<And>k. k \<in> nat \<Longrightarrow> k \<le> n \<longrightarrow> g`k = repeat(1,k)"
  proof -
    fix k assume k: "k \<in> nat"
    then show "k \<le> n \<longrightarrow> g`k = repeat(1,k)"
    proof (induct k rule: nat_induct)
      case 0 show ?case using g0 by simp
    next
      case (succ k)
      show ?case
      proof
        assume le: "succ(k) \<le> n"
        then have kn: "k \<in> n" using succ.hyps(1) n by (simp add: succ_le_iff ltD)
        have "k \<le> n" using le by (blast intro: leI succ_leE)
        then have "g`k = repeat(1,k)" using succ.hyps(2) by blast
        then show "g`succ(k) = repeat(1,succ(k))" using gs[OF kn] by simp
      qed
    qed
  qed
  from this[OF n] gn n show "x = repeat(1,n)" by (simp add: nat_into_Ord)
next
  assume xx: "x = repeat(1,n)"
  let ?g = "\<lambda>k\<in>succ(n). repeat(1,k)"
  have gA: "?g \<in> A"
  proof -
    have "(##A)(?g)"
    proof (rule tm_finite_lambda_closed[OF nat_succI[OF n]])
      fix k assume "k \<in> succ(n)"
      then have "k \<in> nat" using n by (blast intro: Ord_trans Ord_nat)
      then show "(##A)(repeat(1,k))" by simp
    qed
    then show ?thesis by simp
  qed
  have "rep_witness(?g,n,x)"
    unfolding rep_witness_def
  proof (intro conjI ballI)
    show "?g`0 = []" using ltD[OF nat_0_le[OF n]] by simp
    show "?g`n = x" using xx by simp
  next
    fix k assume k: "k \<in> n"
    have "succ(k) \<in> succ(n)" using k n by (simp add: Ord_succ_mem_iff nat_into_Ord)
    moreover have "k \<in> succ(n)" using k by (rule succI2)
    ultimately show "?g`succ(k) = Cons(1,?g`k)" by simp
  qed
  with gA show "\<exists>g\<in>A. rep_witness(g,n,x)" by blast
qed

lemma sats_rep_fm [simp]:
  assumes "jn \<in> nat" "jx \<in> nat" "env \<in> list(A)" "nth(jn,env) \<in> nat"
  shows "(A, env \<Turnstile> rep_fm(jn,jx)) \<longleftrightarrow> nth(jx,env) = repeat(1,nth(jn,env))"
  using sats_rep_fm_witness[OF assms] rep_witness_iff[OF assms(4) nth_in_A[OF assms(3) assms(2)]]
  by simp

end

section \<open>Output of a halting computation\<close>

definition yield_final_fm :: "[i,i,i] \<Rightarrow> i" where
  "yield_final_fm(r,n,b) \<equiv>
    Exists(Exists(Exists(Exists(Exists(
      And(empty_fm(4), And(fun_apply_fm(r#+5,n#+5,3),
      And(pair_fm(4,2,3), And(pair_fm(1,0,2), hd_fm(0,b#+5))))))))))"

definition yields_fm :: "[i,i,i] \<Rightarrow> i" where
  "yields_fm(p,x,b) \<equiv>
    Exists(And(nat_member_fm(0),
      Exists(And(init_fm(0,x#+2), And(trans_fm(p#+2,0,1), yield_final_fm(0,1,b#+2))))))"

definition accept_fm :: i where
  "accept_fm \<equiv> Exists(And(rep_fm(1,0), Exists(And(const_fm(1,0), yields_fm(3,1,0)))))"

lemma yield_final_fm_type [TC]:
  "\<lbrakk>r \<in> nat; n \<in> nat; b \<in> nat\<rbrakk> \<Longrightarrow> yield_final_fm(r,n,b) \<in> formula"
  unfolding yield_final_fm_def by simp

lemma yields_fm_type [TC]:
  "\<lbrakk>p \<in> nat; x \<in> nat; b \<in> nat\<rbrakk> \<Longrightarrow> yields_fm(p,x,b) \<in> formula"
  unfolding yields_fm_def by simp

lemma accept_fm_type [TC]: "accept_fm \<in> formula"
  unfolding accept_fm_def by simp

context tm_model
begin

lemma sats_yield_final_fm [simp]:
  "\<lbrakk>ir \<in> nat; jn \<in> nat; ib \<in> nat; env \<in> list(A)\<rbrakk> \<Longrightarrow>
    (A, env \<Turnstile> yield_final_fm(ir,jn,ib)) \<longleftrightarrow>
      (\<exists>l\<in>A. \<exists>rr\<in>A. nth(ir,env)`nth(jn,env) = \<langle>0,\<langle>l,rr\<rangle>\<rangle> \<and> nth(ib,env) = hd'(rr))"
  unfolding yield_final_fm_def by (auto simp add: zero_in_M)

lemma sats_yields_fm:
  assumes idx: "ip \<in> nat" "ix \<in> nat" "ib \<in> nat" and env: "env \<in> list(A)"
    and P: "nth(ip,env) = P" "P \<in> machine"
    and x: "nth(ix,env) = x" "x \<in> list(symbol)"
    and b: "nth(ib,env) = b" "b \<in> symbol"
  shows "(A, env \<Turnstile> yields_fm(ip,ix,ib)) \<longleftrightarrow> yields(P,x,b)"
proof -
  have init: "initial_config(x) \<in> configuration" using x(2) by (rule initial_config_type)
  have unf: "(A, env \<Turnstile> yields_fm(ip,ix,ib)) \<longleftrightarrow>
    (\<exists>n\<in>A. n \<in> nat \<and> (\<exists>r\<in>A. r`0 = initial_config(x) \<and>
      (\<forall>k\<in>n. (A, Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, Cons(r, Cons(n, env)))))) \<Turnstile>
         step_fm(ip#+2#+4,1,0))) \<and>
      (\<exists>l\<in>A. \<exists>rr\<in>A. r`n = \<langle>0,\<langle>l,rr\<rangle>\<rangle> \<and> b = hd'(rr))))"
    using idx env P x b sats_nat_member_fm[OF model] by (auto simp add: yields_fm_def)
  show ?thesis
  proof
    assume "A, env \<Turnstile> yields_fm(ip,ix,ib)"
    with unf obtain n r l rr where n: "n \<in> nat" "n \<in> A" and rA: "r \<in> A"
      and r0: "r`0 = initial_config(x)"
      and rs: "\<And>k. k \<in> n \<Longrightarrow> (A, Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, Cons(r, Cons(n, env)))))) \<Turnstile>
         step_fm(ip#+2#+4,1,0))"
      and fin: "r`n = \<langle>0,\<langle>l,rr\<rangle>\<rangle>" and out: "b = hd'(rr)"
      by blast
    have env2: "Cons(r, Cons(n, env)) \<in> list(A)" using env rA n by simp
    have Pn: "nth(ip#+2, Cons(r, Cons(n, env))) = P" using P idx by simp
    have rn: "r`n = steps(P,initial_config(x),n)"
      by (rule trans_run_steps[OF env2 _ Pn P(2) init n(1) rA r0 rs]) (simp add: idx)
    have st: "steps(P,initial_config(x),n) \<in> configuration" using steps_type[OF P(2) init n(1)] .
    with rn fin have rr: "rr \<in> list(symbol)" unfolding configuration_def tape_def by auto
    have stq: "steps(P,initial_config(x),n) = \<langle>0,\<langle>l,rr\<rangle>\<rangle>" using rn fin by simp
    have "fst(steps(P,initial_config(x),n)) = final_state" using stq by simp
    moreover have "scan(snd(steps(P,initial_config(x),n))) = b" using stq out rr by simp
    ultimately show "yields(P,x,b)" unfolding yields_def using P x b n by blast
  next
    assume "yields(P,x,b)"
    then obtain n where n: "n \<in> nat" and fin: "fst(steps(P,initial_config(x),n)) = final_state"
      and out: "scan(snd(steps(P,initial_config(x),n))) = b"
      unfolding yields_def by blast
    let ?r = "\<lambda>k\<in>succ(n). steps(P,initial_config(x),k)"
    have rA: "?r \<in> A" using tm_trace_closed[OF P(2) init n] by simp
    have nA: "n \<in> A" using n by simp
    have r0: "?r`0 = initial_config(x)" using ltD[OF nat_0_le[OF n]] by simp
    have env2: "Cons(?r, Cons(n, env)) \<in> list(A)" using env rA nA by simp
    have Pn: "nth(ip#+2, Cons(?r, Cons(n, env))) = P" using P idx by simp
    have rs: "\<And>k. k \<in> n \<Longrightarrow> (A, Cons(?r`succ(k), Cons(?r`k, Cons(succ(k), Cons(k, Cons(?r, Cons(n, env)))))) \<Turnstile>
         step_fm(ip#+2#+4,1,0))"
      by (rule trace_trans[OF env2 _ Pn P(2) init n]) (simp_all add: idx)
    have "steps(P,initial_config(x),n) \<in> configuration" using steps_type[OF P(2) init n] .
    then obtain l rr where st: "steps(P,initial_config(x),n) = \<langle>0,\<langle>l,rr\<rangle>\<rangle>"
      and l: "l \<in> list(symbol)" and rr: "rr \<in> list(symbol)"
      using fin unfolding configuration_def tape_def by auto
    have rn: "?r`n = \<langle>0,\<langle>l,rr\<rangle>\<rangle>" using st by simp
    have bo: "b = hd'(rr)" using out st rr by simp
    have lA: "l \<in> A" "rr \<in> A" using l rr by simp_all
    show "A, env \<Turnstile> yields_fm(ip,ix,ib)"
      using unf nA n rA r0 rs rn bo lA by blast
  qed
qed

lemma sats_accept_fm:
  assumes P: "P \<in> machine" and n: "n \<in> nat"
  shows "(A, [n,P] \<Turnstile> accept_fm) \<longleftrightarrow> accepts_number(P,n)"
proof -
  have x: "numeral_input(n) \<in> list(symbol)" using n by (rule numeral_input_type)
  have xA: "numeral_input(n) \<in> A" using x by simp
  have one: "1 \<in> symbol" by (simp add: symbol_def)
  have h1: "(A, [n,P] \<Turnstile> accept_fm) \<longleftrightarrow>
      (A, [1, numeral_input(n), n, P] \<Turnstile> yields_fm(3,1,0))"
    using P n xA by (auto simp add: accept_fm_def numeral_input_def)
  have h2: "(A, [1, numeral_input(n), n, P] \<Turnstile> yields_fm(3,1,0)) \<longleftrightarrow> yields(P,numeral_input(n),1)"
    by (rule sats_yields_fm) (simp_all add: P n x one)
  from h1 h2 show ?thesis unfolding accepts_number_def by simp
qed

end


section \<open>Decidable sets belong to every transitive model\<close>

context
  notes Un_assoc[symmetric,simp] Un_trasposition_aux1[simp]
begin
arity_theorem for "rep_fm"
arity_theorem for "yield_final_fm"
arity_theorem for "yields_fm"
arity_theorem for "accept_fm"
end

lemma arity_accept_fm_le: "arity(accept_fm) \<le> 2"
  using arity_accept_fm by (simp add: ord_simp_union)

theorem tm_decidable_in_transitive_model:
  assumes model: "transitive_zfc_model(A)" and dec: "tm_decidable(X)"
  shows "X \<in> A"
proof -
  interpret tm_model A by unfold_locales (rule model)
  from dec obtain P where dP: "decides(P,X)" unfolding tm_decidable_def by blast
  then have P: "P \<in> machine" and XN: "X \<subseteq> nat"
    and acc: "\<And>n. n \<in> nat \<Longrightarrow> accepts_number(P,n) \<longleftrightarrow> n \<in> X"
    unfolding decides_def by auto
  have PA: "P \<in> A" using P by simp
  have Xeq: "X = {n \<in> nat. (A, [n] @ [P] \<Turnstile> accept_fm)}"
    using XN acc sats_accept_fm[OF P] by auto
  have sep: "separation(##A, \<lambda>n. (A, [n] @ [P] \<Turnstile> accept_fm))"
    using separation_ax[of accept_fm "[P]"] PA arity_accept_fm_le by simp
  have "(##A)({n \<in> nat. (A, [n] @ [P] \<Turnstile> accept_fm)})"
    using separation_closed[OF sep] M_nat by simp
  then show ?thesis using Xeq by simp
qed

end
