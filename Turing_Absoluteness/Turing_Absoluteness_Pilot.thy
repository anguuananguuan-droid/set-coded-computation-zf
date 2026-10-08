(*  Title:      Turing_Absoluteness_Pilot.thy
    Purpose:    Pilot for an AFP entry "Absoluteness of Turing computation
                for transitive models of ZFC" on top of the session
                Set_Coded_Computation_ZF.
*)

theory Turing_Absoluteness_Pilot
  imports "Turing_Models.Turing_Arithmetic_Truth"
begin

text \<open>This theory constructs an explicit first-order formula \<open>halt_fm\<close> of
set theory with two free variables and proves that, in every transitive set
model of ZFC, it holds of a machine \<open>P\<close> and an input \<open>x\<close> exactly when
\<open>P\<close> halts on \<open>x\<close> (theorem \<open>transitive_model_halt_fm_iff\<close>).

All auxiliary iterations (dropping elements of a list, the run of the
machine) are expressed by a finite witness function \<open>f\<close> with prescribed
values \<open>f`0\<close> and \<open>f`succ(k)\<close>. Upward absoluteness uses that such finite
functions belong to the model; downward absoluteness is an induction on
\<open>k\<close>.\<close>

section \<open>Closed names for natural numbers\<close>

definition nat_name_fm :: "i \<Rightarrow> i" where
  "nat_name_fm(n) \<equiv> nat_rec(n, empty_fm(0), \<lambda>k p. Exists(And(p, succ_fm(0,1))))"

lemma nat_name_fm_0 [simp]: "nat_name_fm(0) = empty_fm(0)"
  unfolding nat_name_fm_def by (rule nat_rec_0)

lemma nat_name_fm_succ [simp]:
  "n \<in> nat \<Longrightarrow> nat_name_fm(succ(n)) = Exists(And(nat_name_fm(n), succ_fm(0,1)))"
  unfolding nat_name_fm_def by (rule nat_rec_succ)

lemma nat_name_fm_type [TC]: "n \<in> nat \<Longrightarrow> nat_name_fm(n) \<in> formula"
  by (induct n rule: nat_induct) simp_all

lemma arity_nat_name_fm: "n \<in> nat \<Longrightarrow> arity(nat_name_fm(n)) = 1"
proof (induct n rule: nat_induct)
  case 0 show ?case by (simp add: arity_empty_fm)
next
  case (succ n)
  have u: "1 \<union> 2 = 2" by (rule subset_Un_iff[THEN iffD1]) (auto simp: succ_def)
  have s: "arity(succ_fm(0,1)) = 2" using u by (simp add: arity_succ_fm)
  show ?case using succ s u by (simp add: arity_Exists arity_And)
qed

lemma sats_nat_name_fm:
  assumes model: "transitive_zfc_model(A)" and n: "n \<in> nat"
  shows "\<And>x env. x \<in> A \<Longrightarrow> env \<in> list(A) \<Longrightarrow>
    (A, Cons(x,env) \<Turnstile> nat_name_fm(n)) \<longleftrightarrow> x = n"
  using n
proof (induct n rule: nat_induct)
  case 0
  from model have trans: "Transset(A)" unfolding transitive_zfc_model_def by simp
  from Transset_sats_empty_fm_eq_0[of 0 "Cons(x,env)" A] 0 trans show ?case by simp
next
  case (succ n)
  interpret A: M_trivial "##A" by (rule transitive_zfc_M_trivial[OF model])
  have nA: "n \<in> A" using A.nat_into_M[OF succ.hyps(1)] by simp
  have h1: "(A, Cons(x,env) \<Turnstile> nat_name_fm(succ(n))) \<longleftrightarrow>
      (\<exists>y\<in>A. (A, Cons(y,Cons(x,env)) \<Turnstile> nat_name_fm(n)) \<and> x = succ(y))"
    using succ.hyps(1) succ.prems by simp
  have h2: "(\<exists>y\<in>A. (A, Cons(y,Cons(x,env)) \<Turnstile> nat_name_fm(n)) \<and> x = succ(y)) \<longleftrightarrow> (\<exists>y\<in>A. y = n \<and> x = succ(y))"
    using succ.hyps(2) succ.prems by auto
  from h1 h2 nA show ?case by auto
qed

definition const_fm :: "[i,i] \<Rightarrow> i" where
  "const_fm(k,i) \<equiv> Exists(And(nat_name_fm(k), Equal(0,succ(i))))"

lemma const_fm_type [TC]: "\<lbrakk>k \<in> nat; i \<in> nat\<rbrakk> \<Longrightarrow> const_fm(k,i) \<in> formula"
  unfolding const_fm_def by simp

lemma sats_const_fm:
  assumes model: "transitive_zfc_model(A)" and k: "k \<in> nat" and i: "i \<in> nat"
    and env: "env \<in> list(A)"
  shows "(A, env \<Turnstile> const_fm(k,i)) \<longleftrightarrow> nth(i,env) = k"
proof -
  interpret A: M_trivial "##A" by (rule transitive_zfc_M_trivial[OF model])
  have kA: "k \<in> A" using A.nat_into_M[OF k] by simp
  have "(A, env \<Turnstile> const_fm(k,i)) \<longleftrightarrow> (\<exists>y\<in>A. y = k \<and> y = nth(i,env))"
    unfolding const_fm_def using env i k sats_nat_name_fm[OF model k] by auto
  then show ?thesis using kA by auto
qed

section \<open>Internalising one machine step\<close>

text \<open>The locale \<open>tm_model\<close> fixes a transitive set model of ZFC.\<close>

locale tm_model =
  fixes A
  assumes model: "transitive_zfc_model(A)"

sublocale tm_model \<subseteq> M_ZF1_trans A
  by (rule transitive_zfc_M_ZF1_trans[OF model])

context tm_model
begin

lemma tm_const [simp]:
  "\<lbrakk>k \<in> nat; i \<in> nat; env \<in> list(A)\<rbrakk> \<Longrightarrow>
    (A, env \<Turnstile> const_fm(k,i)) \<longleftrightarrow> nth(i,env) = k"
  by (rule sats_const_fm[OF model])

lemma list_in_A:
  assumes l: "l \<in> list(B)" and el: "\<And>a. a \<in> B \<Longrightarrow> a \<in> A"
  shows "l \<in> A"
  using l
proof (induct l rule: list.induct)
  case Nil show ?case using Nil_in_M by simp
next
  case (Cons a l) then show ?case using el Cons_in_M_iff by simp
qed

lemma nat_in_A [simp]: "n \<in> nat \<Longrightarrow> n \<in> A"
  using nat_into_M by simp

lemma pair_in_A [simp]: "\<langle>a,b\<rangle> \<in> A \<longleftrightarrow> a \<in> A \<and> b \<in> A"
  using pair_in_M_iff by simp

lemma Nil_in_A [simp]: "[] \<in> A"
  using Nil_in_M by simp

lemma Cons_in_A [simp]: "Cons(a,l) \<in> A \<longleftrightarrow> a \<in> A \<and> l \<in> A"
  using Cons_in_M_iff by simp

lemma symbol_nat: "a \<in> symbol \<Longrightarrow> a \<in> nat"
  unfolding symbol_def by auto

lemma symbols_in_A [simp]: "l \<in> list(symbol) \<Longrightarrow> l \<in> A"
  by (erule list_in_A) (simp add: symbol_nat)

lemma hd'_list [simp]: "l \<in> list(B) \<Longrightarrow> hd'(l) = hd(l)"
  by (simp add: hd'_def list_imp_quasilist)

lemma tl'_list [simp]: "l \<in> list(B) \<Longrightarrow> tl'(l) = tl(l)"
  by (simp add: tl'_def list_imp_quasilist)

lemma hd_symbol_in_A [simp]: "l \<in> list(symbol) \<Longrightarrow> hd(l) \<in> A"
  by (rule nat_in_A, rule symbol_nat, erule hd_symbol_type)

lemma tl_symbols [simp]: "l \<in> list(symbol) \<Longrightarrow> tl(l) \<in> list(symbol)"
  by (rule list.cases[of l]) auto

lemma tl_symbols_in_A [simp]: "l \<in> list(symbol) \<Longrightarrow> tl(l) \<in> A"
  by simp

end

definition upd_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "upd_fm(a,l,r,l2,r2) \<equiv>
    Or(And(const_fm(0,a), And(Equal(l2,l),
         Exists(Exists(And(const_fm(0,1), And(tl_fm(r#+2,0), Cons_fm(1,0,r2#+2))))))),
    Or(And(const_fm(1,a), And(Equal(l2,l),
         Exists(Exists(And(const_fm(1,1), And(tl_fm(r#+2,0), Cons_fm(1,0,r2#+2))))))),
    Or(And(const_fm(2,a),
         Exists(Exists(And(tl_fm(l#+2,0), And(hd_fm(l#+2,1),
           And(Equal(l2#+2,0), Cons_fm(1,r#+2,r2#+2))))))),
    Or(And(const_fm(3,a),
         Exists(Exists(And(hd_fm(r#+2,1), And(tl_fm(r#+2,0),
           And(Cons_fm(1,l#+2,l2#+2), Equal(r2#+2,0))))))),
       And(Neg(Or(const_fm(0,a), Or(const_fm(1,a), Or(const_fm(2,a), const_fm(3,a))))),
         And(Equal(l2,l), Equal(r2,r)))))))"

lemma upd_fm_type [TC]:
  "\<lbrakk>a \<in> nat; l \<in> nat; r \<in> nat; l2 \<in> nat; r2 \<in> nat\<rbrakk> \<Longrightarrow> upd_fm(a,l,r,l2,r2) \<in> formula"
  unfolding upd_fm_def by simp

context tm_model
begin

lemma sats_upd_fm:
  assumes idx: "ia \<in> nat" "il \<in> nat" "ir \<in> nat" "il2 \<in> nat" "ir2 \<in> nat"
    and env: "env \<in> list(A)"
    and a: "nth(ia,env) = a"
    and l: "nth(il,env) = l" "l \<in> list(symbol)"
    and r: "nth(ir,env) = r" "r \<in> list(symbol)"
    and l2: "nth(il2,env) = l2" "l2 \<in> A"
    and r2: "nth(ir2,env) = r2" "r2 \<in> A"
  shows "(A, env \<Turnstile> upd_fm(ia,il,ir,il2,ir2)) \<longleftrightarrow> \<langle>l2,r2\<rangle> = tm_update(a,\<langle>l,r\<rangle>)"
  using idx env a l r l2 r2
  by (simp add: upd_fm_def tm_update_def)

end


section \<open>Iterated tails\<close>

definition drop_fm :: "[i,i,i] \<Rightarrow> i" where
  "drop_fm(n,l,d) \<equiv>
    Exists(And(Exists(And(empty_fm(0), fun_apply_fm(1,0,l#+2))),
      And(Forall(Implies(Member(0,n#+2),
            Exists(Exists(Exists(And(succ_fm(3,2),
              And(fun_apply_fm(4,3,1), And(fun_apply_fm(4,2,0), tl_fm(1,0))))))))),
        fun_apply_fm(0,n#+1,d#+1))))"

lemma drop_fm_type [TC]:
  "\<lbrakk>n \<in> nat; l \<in> nat; d \<in> nat\<rbrakk> \<Longrightarrow> drop_fm(n,l,d) \<in> formula"
  unfolding drop_fm_def by simp

definition drop_witness :: "[i,i,i,i] \<Rightarrow> o" where
  "drop_witness(f,n,l,d) \<equiv> f`0 = l \<and> (\<forall>k\<in>n. f`succ(k) = tl'(f`k)) \<and> f`n = d"

context tm_model
begin

lemma sats_drop_fm_witness:
  assumes idx: "jn \<in> nat" "il \<in> nat" "jd \<in> nat" and env: "env \<in> list(A)"
    and n: "nth(jn,env) = n" "n \<in> nat"
    and l: "nth(il,env) = l" "l \<in> A"
    and d: "nth(jd,env) = d" "d \<in> A"
  shows "(A, env \<Turnstile> drop_fm(jn,il,jd)) \<longleftrightarrow> (\<exists>f\<in>A. drop_witness(f,n,l,d))"
proof -
  have nA: "n \<in> A" using n by simp
  have k_nat: "\<And>k. k \<in> n \<Longrightarrow> k \<in> nat" using n by (blast intro: Ord_trans Ord_nat)
  have k_A: "\<And>k. k \<in> n \<Longrightarrow> k \<in> A" using k_nat by simp
  have sk_A: "\<And>k. k \<in> n \<Longrightarrow> succ(k) \<in> A" using k_nat by simp
  have ap_A: "\<And>f x. f \<in> A \<Longrightarrow> x \<in> A \<Longrightarrow> f`x \<in> A" using apply_closed by simp
  show ?thesis
    unfolding drop_fm_def drop_witness_def
    using idx env n l d nA k_A sk_A ap_A by (auto simp add: zero_in_M)
qed

definition drop_tl :: "[i,i] \<Rightarrow> i" where
  "drop_tl(n,l) \<equiv> (\<lambda>x. tl'(x))^n (l)"

lemma drop_tl_0 [simp]: "drop_tl(0,l) = l"
  unfolding drop_tl_def by simp

lemma drop_tl_succ [simp]: "n \<in> nat \<Longrightarrow> drop_tl(succ(n),l) = tl'(drop_tl(n,l))"
  unfolding drop_tl_def by simp

lemma drop_tl_list:
  assumes l: "l \<in> list(B)" and n: "n \<in> nat"
  shows "drop_tl(n,l) = drop(n,l)"
  using n
proof (induct n rule: nat_induct)
  case 0 then show ?case by (simp add: drop_0)
next
  case (succ n)
  have "drop(n,l) \<in> list(B)" using succ.hyps(1) l by simp
  then show ?case using succ by (simp add: drop_succ)
qed

lemma tl'_in_A [simp]: "x \<in> A \<Longrightarrow> tl'(x) \<in> A"
proof (cases "quasilist(x)")
  case True
  assume xA: "x \<in> A"
  from True show ?thesis
  proof (unfold quasilist_def, elim disjE exE)
    assume "x = []" then show ?thesis using Nil_in_M by (simp add: tl'_def)
  next
    fix a t assume "x = Cons(a,t)"
    with xA show ?thesis using Cons_in_M_iff by (simp add: tl'_def)
  qed
next
  case False then show ?thesis using zero_in_M by (simp add: tl'_def)
qed

lemma drop_tl_in_A [simp]:
  assumes l: "l \<in> A" and n: "n \<in> nat"
  shows "drop_tl(n,l) \<in> A"
  using n by (induct n rule: nat_induct) (simp_all add: l)

lemma drop_witness_iff:
  assumes n: "n \<in> nat" and l: "l \<in> A" and d: "d \<in> A"
  shows "(\<exists>f\<in>A. drop_witness(f,n,l,d)) \<longleftrightarrow> d = drop_tl(n,l)"
proof
  assume "\<exists>f\<in>A. drop_witness(f,n,l,d)"
  then obtain f where f0: "f`0 = l" and fs: "\<And>k. k \<in> n \<Longrightarrow> f`succ(k) = tl'(f`k)"
    and fn: "f`n = d" unfolding drop_witness_def by blast
  have "\<And>k. k \<in> nat \<Longrightarrow> k \<le> n \<longrightarrow> f`k = drop_tl(k,l)"
  proof -
    fix k assume k: "k \<in> nat"
    then show "k \<le> n \<longrightarrow> f`k = drop_tl(k,l)"
    proof (induct k rule: nat_induct)
      case 0 show ?case using f0 by simp
    next
      case (succ k)
      show ?case
      proof
        assume le: "succ(k) \<le> n"
        then have kn: "k \<in> n" using succ.hyps(1) n by (simp add: succ_le_iff ltD)
        have "k \<le> n" using le by (blast intro: leI succ_leE)
        then have "f`k = drop_tl(k,l)" using succ.hyps(2) by blast
        then show "f`succ(k) = drop_tl(succ(k),l)" using fs[OF kn] succ.hyps(1) by simp
      qed
    qed
  qed
  from this[OF n] fn n show "d = drop_tl(n,l)" by (simp add: nat_into_Ord)
next
  assume dd: "d = drop_tl(n,l)"
  let ?f = "\<lambda>k\<in>succ(n). drop_tl(k,l)"
  have fA: "?f \<in> A"
  proof -
    have "(##A)(?f)"
    proof (rule tm_finite_lambda_closed[OF nat_succI[OF n]])
      fix k assume "k \<in> succ(n)"
      then have "k \<in> nat" using n by (blast intro: Ord_trans Ord_nat)
      then show "(##A)(drop_tl(k,l))" using l by simp
    qed
    then show ?thesis by simp
  qed
  have "drop_witness(?f,n,l,d)"
    unfolding drop_witness_def
  proof (intro conjI ballI)
    show "?f`0 = l" using ltD[OF nat_0_le[OF n]] by simp
    show "?f`n = d" using dd by simp
  next
    fix k assume k: "k \<in> n"
    then have knat: "k \<in> nat" using n by (blast intro: Ord_trans Ord_nat)
    have "succ(k) \<in> succ(n)" using k n by (simp add: Ord_succ_mem_iff nat_into_Ord)
    moreover have "k \<in> succ(n)" using k by (rule succI2)
    ultimately show "?f`succ(k) = tl'(?f`k)" using knat by simp
  qed
  with fA show "\<exists>f\<in>A. drop_witness(f,n,l,d)" by blast
qed

lemma sats_drop_fm [simp]:
  assumes idx: "jn \<in> nat" "il \<in> nat" "jd \<in> nat" and env: "env \<in> list(A)"
    and n: "nth(jn,env) \<in> nat" and l: "nth(il,env) \<in> A" and d: "nth(jd,env) \<in> A"
  shows "(A, env \<Turnstile> drop_fm(jn,il,jd)) \<longleftrightarrow>
    nth(jd,env) = drop_tl(nth(jn,env),nth(il,env))"
  using sats_drop_fm_witness[OF idx env refl n refl l refl d]
    drop_witness_iff[OF n l d]
  by simp

end


section \<open>Fetching an instruction\<close>

lemma nth_via_drop:
  assumes P: "P \<in> list(B)" and s: "s \<in> nat"
  shows "(if s < length(P) then nth(s,P) else c) =
    (if drop(s,P) = [] then c else hd(drop(s,P)))"
proof (cases "s < length(P)")
  case True
  then have "s \<in> length(P)" by (rule ltD)
  then obtain z zs where dz: "drop(s,P) = Cons(z,zs)" using drop_length[OF P] by blast
  have "nth(0, drop(s,P)) = nth(s #+ 0, P)" using nth_drop[OF s, of 0 P B] P by simp
  then have "nth(s,P) = z" using dz s by simp
  then show ?thesis using True dz by simp
next
  case False
  then have "length(P) \<le> s" using s P by (simp add: not_lt_iff_le)
  then have "drop(s,P) = []" using drop_all[OF s P] by simp
  then show ?thesis using False by simp
qed

lemma fetch_via_drop:
  assumes P: "P \<in> list(B)" and q: "q \<in> nat" and b: "b \<in> nat"
  shows "fetch(P,q,b) =
    (if q = 0 then \<langle>nop,0\<rangle>
     else if drop(b, drop(pred(q), drop(pred(q),P))) = [] then \<langle>nop,0\<rangle>
     else hd(drop(b, drop(pred(q), drop(pred(q),P)))))"
proof (cases "q = 0")
  case True then show ?thesis by (simp add: fetch_def)
next
  case False
  then obtain p where p: "p \<in> nat" and qp: "q = succ(p)" using q by (blast elim: natE)
  have dd: "drop(b, drop(p, drop(p,P))) = drop(p #+ p #+ b, P)"
  proof -
    have pp: "p #+ p \<in> nat" by simp
    have "drop(p, drop(p,P)) = drop(p #+ p, P)" using drop_drop[OF p] P p by simp
    moreover have "drop(b, drop(p #+ p, P)) = drop(b #+ (p #+ p), P)"
      using drop_drop[OF pp] P b by simp
    ultimately show ?thesis by (simp add: add_commute)
  qed
  have sn: "p #+ p #+ b \<in> nat" by simp
  show ?thesis using False qp p dd nth_via_drop[OF P sn, of "\<langle>nop,0\<rangle>"]
    by (auto simp add: fetch_def split: split_if_asm)
qed


definition nop_instr_fm :: "i \<Rightarrow> i" where
  "nop_instr_fm(i) \<equiv> Exists(Exists(And(const_fm(nop,1), And(const_fm(0,0), pair_fm(1,0,i#+2)))))"

lemma nop_instr_fm_type [TC]: "i \<in> nat \<Longrightarrow> nop_instr_fm(i) \<in> formula"
  unfolding nop_instr_fm_def by simp

definition fetch_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "fetch_fm(p,q,b,ins) \<equiv>
    Or(And(const_fm(0,q), nop_instr_fm(ins)),
       And(Neg(const_fm(0,q)),
         Exists(And(succ_fm(0,q#+1),
           Exists(And(drop_fm(1,p#+2,0),
             Exists(And(drop_fm(2,1,0),
               Exists(And(drop_fm(b#+4,1,0),
                 Or(And(Nil_fm(0), nop_instr_fm(ins#+4)),
                    And(Neg(Nil_fm(0)), hd_fm(0,ins#+4)))))))))))))"

lemma fetch_fm_type [TC]:
  "\<lbrakk>p \<in> nat; q \<in> nat; b \<in> nat; ins \<in> nat\<rbrakk> \<Longrightarrow> fetch_fm(p,q,b,ins) \<in> formula"
  unfolding fetch_fm_def by simp

context tm_model
begin

lemma nth_in_A [simp]: "env \<in> list(A) \<Longrightarrow> i \<in> nat \<Longrightarrow> nth(i,env) \<in> A"
proof (cases "i < length(env)")
  case True
  assume "env \<in> list(A)" then show ?thesis using True by (rule nth_type)
next
  case False
  assume "env \<in> list(A)" "i \<in> nat"
  then have "nth(i,env) = 0" using False by (simp add: nth_eq_0 not_lt_iff_le)
  then show ?thesis using zero_in_M by simp
qed

lemma nop_in_A [simp]: "nop \<in> A"
  by (rule nat_in_A) simp

lemma sats_nop_instr_fm [simp]:
  "\<lbrakk>i \<in> nat; env \<in> list(A)\<rbrakk> \<Longrightarrow>
    (A, env \<Turnstile> nop_instr_fm(i)) \<longleftrightarrow> nth(i,env) = \<langle>nop,0\<rangle>"
  unfolding nop_instr_fm_def by auto

lemma machine_in_A [simp]: "P \<in> machine \<Longrightarrow> P \<in> A"
  using tm_machine_closed by simp

lemma sats_fetch_fm:
  assumes idx: "ip \<in> nat" "iq \<in> nat" "ib \<in> nat" "ii \<in> nat" and env: "env \<in> list(A)"
    and P: "nth(ip,env) = P" "P \<in> machine"
    and q: "nth(iq,env) = q" "q \<in> nat"
    and b: "nth(ib,env) = b" "b \<in> nat"
    and ins: "nth(ii,env) = ins" "ins \<in> A"
  shows "(A, env \<Turnstile> fetch_fm(ip,iq,ib,ii)) \<longleftrightarrow> ins = fetch(P,q,b)"
proof -
  have PL: "P \<in> list(instruction)" using P(2) unfolding machine_def .
  show ?thesis
  proof (cases "q = 0")
    case True
    then show ?thesis using idx env P q b ins PL
      by (simp add: fetch_fm_def fetch_via_drop[OF PL q(2) b(2)])
  next
    case False
    then obtain p where p: "p \<in> nat" and qp: "q = succ(p)" using q(2) by (blast elim: natE)
    have D1: "drop(p,P) \<in> list(instruction)" using p PL by simp
    have D2: "drop(p,drop(p,P)) \<in> list(instruction)" using p D1 by simp
    have D3: "drop(b,drop(p,drop(p,P))) \<in> list(instruction)" using b D2 by simp
    have D1A: "drop(p,P) \<in> A" using drop_tl_in_A[OF machine_in_A[OF P(2)] p] drop_tl_list[OF PL p] by simp
    have D2A: "drop(p,drop(p,P)) \<in> A"
      using drop_tl_in_A[OF D1A p] drop_tl_list[OF D1 p] by simp
    have D3A: "drop(b,drop(p,drop(p,P))) \<in> A"
      using drop_tl_in_A[OF D2A b(2)] drop_tl_list[OF D2 b(2)] by simp
    show ?thesis using idx env P q b ins PL qp p D1 D2 D3 D1A D2A D3A
      by (simp add: fetch_fm_def fetch_via_drop[OF PL nat_succI[OF p] b(2)] drop_tl_list)
  qed
qed


lemma sats_upd_fm_simp [simp]:
  "\<lbrakk>ia \<in> nat; il \<in> nat; ir \<in> nat; il2 \<in> nat; ir2 \<in> nat; env \<in> list(A);
    nth(il,env) \<in> list(symbol); nth(ir,env) \<in> list(symbol)\<rbrakk> \<Longrightarrow>
   (A, env \<Turnstile> upd_fm(ia,il,ir,il2,ir2)) \<longleftrightarrow>
     \<langle>nth(il2,env),nth(ir2,env)\<rangle> = tm_update(nth(ia,env),\<langle>nth(il,env),nth(ir,env)\<rangle>)"
  by (rule sats_upd_fm) simp_all

lemma sats_fetch_fm_simp [simp]:
  "\<lbrakk>ip \<in> nat; iq \<in> nat; ib \<in> nat; ii \<in> nat; env \<in> list(A);
    nth(ip,env) \<in> machine; nth(iq,env) \<in> nat; nth(ib,env) \<in> nat\<rbrakk> \<Longrightarrow>
   (A, env \<Turnstile> fetch_fm(ip,iq,ib,ii)) \<longleftrightarrow>
     nth(ii,env) = fetch(nth(ip,env),nth(iq,env),nth(ib,env))"
  by (rule sats_fetch_fm) simp_all

end

section \<open>One step\<close>

definition step_fm :: "[i,i,i] \<Rightarrow> i" where
  "step_fm(p,c,d) \<equiv>
    Exists(Exists(Exists(Exists(Exists(Exists(Exists(Exists(Exists(Exists(Exists(
      And(pair_fm(10,9,c#+11),
      And(pair_fm(8,7,9),
      And(hd_fm(7,6),
      And(fetch_fm(p#+11,10,6,5),
      And(pair_fm(4,3,5),
      And(upd_fm(4,8,7,2,1),
      And(pair_fm(2,1,0),
          pair_fm(3,0,d#+11)))))))))))))))))))"

lemma step_fm_type [TC]:
  "\<lbrakk>p \<in> nat; c \<in> nat; d \<in> nat\<rbrakk> \<Longrightarrow> step_fm(p,c,d) \<in> formula"
  unfolding step_fm_def by simp

context tm_model
begin

lemma configuration_in_A [simp]: "c \<in> configuration \<Longrightarrow> c \<in> A"
  using tm_configuration_closed by simp

lemma sats_step_fm:
  assumes idx: "ip \<in> nat" "ic \<in> nat" "jd \<in> nat" and env: "env \<in> list(A)"
    and P: "nth(ip,env) = P" "P \<in> machine"
    and c: "nth(ic,env) = c" "c \<in> configuration"
    and d: "nth(jd,env) = d" "d \<in> A"
  shows "(A, env \<Turnstile> step_fm(ip,ic,jd)) \<longleftrightarrow> d = step(P,c)"
proof -
  from c(2) obtain q l r where cq: "c = \<langle>q,\<langle>l,r\<rangle>\<rangle>" and q: "q \<in> nat"
    and l: "l \<in> list(symbol)" and r: "r \<in> list(symbol)"
    unfolding configuration_def tape_def by blast
  have b: "hd(r) \<in> nat" using r by (blast intro: symbol_nat hd_symbol_type)
  have lrA: "\<langle>l,r\<rangle> \<in> A" using pair_in_M_iff l r by simp
  have "fetch(P,q,hd(r)) \<in> instruction" using P(2) by (rule fetch_type)
  then obtain fa fq where fe: "fetch(P,q,hd(r)) = \<langle>fa,fq\<rangle>" and fa: "fa \<in> action"
    and fq: "fq \<in> nat" unfolding instruction_def by blast
  have faA: "fa \<in> A" using fa action_in_nat Ord_nat by (blast dest: OrdmemD intro: nat_in_A)
  have "tm_update(fa,\<langle>l,r\<rangle>) \<in> tape" by (rule tm_update_type) (simp add: l r tape_def)
  then obtain u1 u2 where ue: "tm_update(fa,\<langle>l,r\<rangle>) = \<langle>u1,u2\<rangle>"
    and u1: "u1 \<in> list(symbol)" and u2: "u2 \<in> list(symbol)" unfolding tape_def by blast
  have feA: "\<langle>fa,fq\<rangle> \<in> A" using pair_in_M_iff faA fq by simp
  have ueA: "\<langle>u1,u2\<rangle> \<in> A" using pair_in_M_iff u1 u2 by simp
  show ?thesis
    using idx env P c d cq q l r b lrA fe fa fq faA ue u1 u2 feA ueA
    by (simp add: step_fm_def)
qed

end


section \<open>Halting\<close>

definition init_fm :: "[i,i] \<Rightarrow> i" where
  "init_fm(r,x) \<equiv>
    Exists(Exists(Exists(Exists(Exists(
      And(empty_fm(4), And(const_fm(1,3), And(Nil_fm(2),
      And(pair_fm(2,x#+5,1), And(pair_fm(3,1,0), fun_apply_fm(r#+5,4,0)))))))))))"

definition trans_fm :: "[i,i,i] \<Rightarrow> i" where
  "trans_fm(p,r,n) \<equiv>
    Forall(Implies(Member(0,n#+1),
      Exists(Exists(Exists(
        And(succ_fm(3,2), And(fun_apply_fm(r#+4,3,1),
        And(fun_apply_fm(r#+4,2,0), step_fm(p#+4,1,0)))))))))"

definition final_fm :: "[i,i] \<Rightarrow> i" where
  "final_fm(r,n) \<equiv>
    Exists(Exists(Exists(
      And(empty_fm(2), And(fun_apply_fm(r#+3,n#+3,1), pair_fm(2,0,1))))))"

definition halt_fm :: i where
  "halt_fm \<equiv>
    Exists(And(nat_member_fm(0),
      Exists(And(init_fm(0,3), And(trans_fm(2,0,1), final_fm(0,1))))))"

lemma init_fm_type [TC]: "\<lbrakk>r \<in> nat; x \<in> nat\<rbrakk> \<Longrightarrow> init_fm(r,x) \<in> formula"
  unfolding init_fm_def by simp

lemma trans_fm_type [TC]: "\<lbrakk>p \<in> nat; r \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> trans_fm(p,r,n) \<in> formula"
  unfolding trans_fm_def by simp

lemma final_fm_type [TC]: "\<lbrakk>r \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> final_fm(r,n) \<in> formula"
  unfolding final_fm_def by simp

lemma halt_fm_type [TC]: "halt_fm \<in> formula"
  unfolding halt_fm_def by simp

context tm_model
begin

lemma ap_in_A [simp]: "f \<in> A \<Longrightarrow> a \<in> A \<Longrightarrow> f`a \<in> A"
  using apply_closed by simp

lemma sats_init_fm [simp]:
  "\<lbrakk>ir \<in> nat; ix \<in> nat; env \<in> list(A)\<rbrakk> \<Longrightarrow>
    (A, env \<Turnstile> init_fm(ir,ix)) \<longleftrightarrow> nth(ir,env)`0 = initial_config(nth(ix,env))"
  unfolding init_fm_def by (auto simp add: zero_in_M)

lemma sats_final_fm [simp]:
  "\<lbrakk>ir \<in> nat; jn \<in> nat; env \<in> list(A)\<rbrakk> \<Longrightarrow>
    (A, env \<Turnstile> final_fm(ir,jn)) \<longleftrightarrow> (\<exists>t\<in>A. nth(ir,env)`nth(jn,env) = \<langle>0,t\<rangle>)"
  unfolding final_fm_def by (auto simp add: zero_in_M)

lemma sats_trans_fm [simp]:
  assumes "ip \<in> nat" "ir \<in> nat" "jn \<in> nat" "env \<in> list(A)" "nth(jn,env) \<in> nat"
  shows "(A, env \<Turnstile> trans_fm(ip,ir,jn)) \<longleftrightarrow>
    (\<forall>k\<in>nth(jn,env). (A, Cons(nth(ir,env)`succ(k), Cons(nth(ir,env)`k,
        Cons(succ(k), Cons(k, env)))) \<Turnstile> step_fm(ip#+4,1,0)))"
proof -
  have kA: "\<And>k. k \<in> nth(jn,env) \<Longrightarrow> k \<in> A \<and> succ(k) \<in> A"
    using assms(5) by (blast intro: Ord_trans Ord_nat nat_in_A nat_succI)
  show ?thesis unfolding trans_fm_def using assms kA by auto
qed

lemma halting_witness_iff:
  assumes P: "P \<in> machine" and x: "x \<in> list(symbol)"
  shows "(\<exists>n\<in>A. n \<in> nat \<and> (\<exists>r\<in>A. r`0 = initial_config(x) \<and>
      (\<forall>k\<in>n. (A, Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, [r,n,P,x])))) \<Turnstile>
         step_fm(6,1,0))) \<and>
      (\<exists>t\<in>A. r`n = \<langle>0,t\<rangle>))) \<longleftrightarrow> halts_on(P,x)"
proof
  assume "\<exists>n\<in>A. n \<in> nat \<and> (\<exists>r\<in>A. r`0 = initial_config(x) \<and>
      (\<forall>k\<in>n. (A, Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, [r,n,P,x])))) \<Turnstile>
         step_fm(6,1,0))) \<and>
      (\<exists>t\<in>A. r`n = \<langle>0,t\<rangle>))"
  then obtain n r t where n: "n \<in> nat" "n \<in> A" and rA: "r \<in> A"
    and r0: "r`0 = initial_config(x)"
    and rs: "\<And>k. k \<in> n \<Longrightarrow> (A, Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, [r,n,P,x])))) \<Turnstile>
         step_fm(6,1,0))"
    and tA: "t \<in> A" and rn: "r`n = \<langle>0,t\<rangle>"
    by blast
  have init: "initial_config(x) \<in> configuration" using x by (rule initial_config_type)
  have "\<And>k. k \<in> nat \<Longrightarrow> k \<le> n \<longrightarrow> r`k = steps(P,initial_config(x),k)"
  proof -
    fix k assume k: "k \<in> nat"
    then show "k \<le> n \<longrightarrow> r`k = steps(P,initial_config(x),k)"
    proof (induct k rule: nat_induct)
      case 0 show ?case using r0 by simp
    next
      case (succ k)
      show ?case
      proof
        assume le: "succ(k) \<le> n"
        then have kn: "k \<in> n" using succ.hyps(1) n by (simp add: succ_le_iff ltD)
        have "k \<le> n" using le by (blast intro: leI succ_leE)
        then have rk: "r`k = steps(P,initial_config(x),k)" using succ.hyps(2) by blast
        have conf: "r`k \<in> configuration" using rk steps_type[OF P init succ.hyps(1)] by simp
        have kA: "k \<in> A" "succ(k) \<in> A" using succ.hyps(1) by simp_all
        have xA: "x \<in> A" using x by simp
        have envA: "Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, [r,n,P,x])))) \<in> list(A)"
          using rA kA n xA P by simp
        have "r`succ(k) = step(P,r`k)"
          using sats_step_fm[OF _ _ _ envA, of 6 1 0 P "r`k" "r`succ(k)"] rs[OF kn] P conf rA kA
          by simp
        then show "r`succ(k) = steps(P,initial_config(x),succ(k))" using rk succ.hyps(1) by simp
      qed
    qed
  qed
  from this[OF n(1)] n(1) have "r`n = steps(P,initial_config(x),n)" by (simp add: nat_into_Ord)
  with rn have "fst(steps(P,initial_config(x),n)) = final_state" by simp
  with P x n(1) show "halts_on(P,x)" unfolding halts_on_def by blast
next
  assume h: "halts_on(P,x)"
  then obtain n where n: "n \<in> nat" and fin: "fst(steps(P,initial_config(x),n)) = final_state"
    unfolding halts_on_def by blast
  have init: "initial_config(x) \<in> configuration" using x by (rule initial_config_type)
  let ?r = "\<lambda>k\<in>succ(n). steps(P,initial_config(x),k)"
  have rA: "?r \<in> A" using tm_trace_closed[OF P init n] by simp
  have nA: "n \<in> A" using n by simp
  have xA: "x \<in> A" using x by simp
  have r0: "?r`0 = initial_config(x)" using ltD[OF nat_0_le[OF n]] by simp
  have rs: "\<And>k. k \<in> n \<Longrightarrow> (A, Cons(?r`succ(k), Cons(?r`k, Cons(succ(k), Cons(k, [?r,n,P,x])))) \<Turnstile>
         step_fm(6,1,0))"
  proof -
    fix k assume k: "k \<in> n"
    then have knat: "k \<in> nat" using n by (blast intro: Ord_trans Ord_nat)
    have sk: "succ(k) \<in> succ(n)" using k n by (simp add: Ord_succ_mem_iff nat_into_Ord)
    have k1: "k \<in> succ(n)" using k by (rule succI2)
    have conf: "steps(P,initial_config(x),k) \<in> configuration" using steps_type[OF P init knat] .
    have conf2: "steps(P,initial_config(x),succ(k)) \<in> configuration"
      using steps_type[OF P init nat_succI[OF knat]] .
    have kA: "k \<in> A" "succ(k) \<in> A" using knat by simp_all
    have envA: "Cons(?r`succ(k), Cons(?r`k, Cons(succ(k), Cons(k, [?r,n,P,x])))) \<in> list(A)"
      using rA kA nA xA P conf conf2 sk k1 by simp
    show "(A, Cons(?r`succ(k), Cons(?r`k, Cons(succ(k), Cons(k, [?r,n,P,x])))) \<Turnstile> step_fm(6,1,0))"
      using sats_step_fm[OF _ _ _ envA, of 6 1 0 P "?r`k" "?r`succ(k)"] P conf conf2 sk k1 knat
      by simp
  qed
  have "steps(P,initial_config(x),n) \<in> configuration" using steps_type[OF P init n] .
  then obtain t where st: "steps(P,initial_config(x),n) = \<langle>0,t\<rangle>" and t: "t \<in> tape"
    using fin unfolding configuration_def by auto
  have tA: "t \<in> A" using t pair_in_M_iff unfolding tape_def by auto
  have rn: "?r`n = \<langle>0,t\<rangle>" using st by simp
  show "\<exists>n\<in>A. n \<in> nat \<and> (\<exists>r\<in>A. r`0 = initial_config(x) \<and>
      (\<forall>k\<in>n. (A, Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, [r,n,P,x])))) \<Turnstile>
         step_fm(6,1,0))) \<and>
      (\<exists>t\<in>A. r`n = \<langle>0,t\<rangle>))"
    using nA n rA r0 rs tA rn by blast
qed

theorem sats_halt_fm:
  assumes P: "P \<in> machine" and x: "x \<in> list(symbol)"
  shows "(A, [P,x] \<Turnstile> halt_fm) \<longleftrightarrow> halts_on(P,x)"
proof -
  have xA: "x \<in> A" using x by simp
  have "(A, [P,x] \<Turnstile> halt_fm) \<longleftrightarrow>
    (\<exists>n\<in>A. n \<in> nat \<and> (\<exists>r\<in>A. r`0 = initial_config(x) \<and>
      (\<forall>k\<in>n. (A, Cons(r`succ(k), Cons(r`k, Cons(succ(k), Cons(k, [r,n,P,x])))) \<Turnstile>
         step_fm(6,1,0))) \<and>
      (\<exists>t\<in>A. r`n = \<langle>0,t\<rangle>)))"
    using P xA sats_nat_member_fm[OF model] by (auto simp add: halt_fm_def)
  then show ?thesis using halting_witness_iff[OF P x] by simp
qed

end

theorem transitive_model_halt_fm_iff:
  assumes "transitive_zfc_model(A)" "P \<in> machine" "x \<in> list(symbol)"
  shows "(A, [P,x] \<Turnstile> halt_fm) \<longleftrightarrow> halts_on(P,x)"
  using tm_model.sats_halt_fm[of A P x] assms unfolding tm_model_def by simp

context tm_model
begin

end


section \<open>Arities\<close>

context
  notes Un_assoc[symmetric,simp] Un_trasposition_aux1[simp]
begin
arity_theorem for "Nil_fm"
arity_theorem for "Cons_fm"
arity_theorem for "quasilist_fm"
arity_theorem for "hd_fm"
arity_theorem for "tl_fm"
end

declare arity_nat_name_fm[arity]

context
  notes Un_assoc[symmetric,simp] Un_trasposition_aux1[simp]
begin
arity_theorem for "const_fm"
arity_theorem for "upd_fm"
arity_theorem for "drop_fm"
arity_theorem for "nop_instr_fm"
arity_theorem for "fetch_fm"
arity_theorem for "step_fm"
arity_theorem for "init_fm"
arity_theorem for "trans_fm"
arity_theorem for "final_fm"
arity_theorem for "nat_member_fm"
arity_theorem for "halt_fm"
end

lemma arity_halt_fm_eq: "arity(halt_fm) = 2"
  using arity_halt_fm by (simp add: ord_simp_union)

thm arity_step_fm arity_halt_fm

end
