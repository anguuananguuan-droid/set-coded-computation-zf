theory Turing_Halting_Sentences
  imports
    Turing_Halting_Formula
    Turing_CH
    "Set_Coded_Computation_ZF.Turing_Rejection"
begin

text \<open>Closed sentences are obtained from \<open>halt_fm\<close> by naming the machine
and the input with formulas that define them in every transitive model.
The second part derives model-theoretic consequences, using the
independence of CH from the AFP entry \<open>Independence_CH\<close>.\<close>

section \<open>Closed names for finite lists\<close>

lemma sym_nat: "a \<in> symbol \<Longrightarrow> a \<in> nat"
  unfolding symbol_def by auto

lemma nat_name_sym_type: "a \<in> symbol \<Longrightarrow> nat_name_fm(a) \<in> formula"
  by (rule nat_name_fm_type, erule sym_nat)

lemma arity_nat_name_sym: "a \<in> symbol \<Longrightarrow> arity(nat_name_fm(a)) = 1"
  by (rule arity_nat_name_fm, erule sym_nat)

lemma sats_nat_name_sym:
  "\<lbrakk>transitive_zfc_model(A); a \<in> symbol; y \<in> A; env \<in> list(A)\<rbrakk> \<Longrightarrow>
    (A, Cons(y,env) \<Turnstile> nat_name_fm(a)) \<longleftrightarrow> y = a"
  by (rule sats_nat_name_fm, assumption, erule sym_nat)

definition list_name_fm :: "[i \<Rightarrow> i, i] \<Rightarrow> i" where
  "list_name_fm(N,l) \<equiv>
    list_rec(Nil_fm(0), \<lambda>a t p. Exists(And(N(a), Exists(And(p, Cons_fm(1,0,2))))), l)"

lemma list_name_fm_Nil [simp]: "list_name_fm(N,[]) = Nil_fm(0)"
  unfolding list_name_fm_def by simp

lemma list_name_fm_Cons [simp]:
  "list_name_fm(N,Cons(a,t)) = Exists(And(N(a), Exists(And(list_name_fm(N,t), Cons_fm(1,0,2)))))"
  unfolding list_name_fm_def by simp

lemma list_name_fm_type [TC]:
  assumes l: "l \<in> list(B)" and N: "\<And>a. a \<in> B \<Longrightarrow> N(a) \<in> formula"
  shows "list_name_fm(N,l) \<in> formula"
proof (rule list.induct[OF l])
  show "list_name_fm(N,[]) \<in> formula" by simp
next
  fix a t assume a: "a \<in> B" and t: "list_name_fm(N,t) \<in> formula"
  have "N(a) \<in> formula" using N[OF a] .
  then show "list_name_fm(N,Cons(a,t)) \<in> formula" using t by simp
qed

lemma arity_list_name_fm:
  assumes l: "l \<in> list(B)" and N: "\<And>a. a \<in> B \<Longrightarrow> N(a) \<in> formula"
    and aN: "\<And>a. a \<in> B \<Longrightarrow> arity(N(a)) = 1"
  shows "arity(list_name_fm(N,l)) = 1"
proof (rule list.induct[OF l])
  show "arity(list_name_fm(N,[])) = 1" by (simp add: arity_Nil_fm ord_simp_union)
next
  fix a t assume a: "a \<in> B" and tl: "t \<in> list(B)" and ih: "arity(list_name_fm(N,t)) = 1"
  have t: "list_name_fm(N,t) \<in> formula" using tl N by (rule list_name_fm_type)
  show "arity(list_name_fm(N,Cons(a,t))) = 1" using ih aN[OF a] N[OF a] t
    by (simp add: arity_Exists arity_And arity_Cons_fm ord_simp_union)
qed

lemma sats_list_name_fm:
  assumes model: "transitive_zfc_model(A)" and l: "l \<in> list(B)"
    and BA: "B \<subseteq> A"
    and N: "\<And>a y env. a \<in> B \<Longrightarrow> y \<in> A \<Longrightarrow> env \<in> list(A) \<Longrightarrow>
      (A, Cons(y,env) \<Turnstile> N(a)) \<longleftrightarrow> y = a"
  shows "\<And>y env. y \<in> A \<Longrightarrow> env \<in> list(A) \<Longrightarrow>
    (A, Cons(y,env) \<Turnstile> list_name_fm(N,l)) \<longleftrightarrow> y = l"
  using l
proof (induct l rule: list.induct)
  case Nil
  interpret tm_model A by unfold_locales (rule model)
  show ?case using Nil by simp
next
  case (Cons a t)
  interpret tm_model A by unfold_locales (rule model)
  have aA: "a \<in> A" using Cons.hyps(1) BA by blast
  have tA: "t \<in> A" using list_in_A[OF Cons.hyps(2)] BA by blast
  show ?case using Cons.prems Cons.hyps(3) N[OF Cons.hyps(1)] aA tA by auto
qed

definition instr_name_fm :: "i \<Rightarrow> i" where
  "instr_name_fm(i) \<equiv>
    Exists(And(nat_name_fm(fst(i)), Exists(And(nat_name_fm(snd(i)), pair_fm(1,0,2)))))"

lemma instr_name_fm_type [TC]: "i \<in> instruction \<Longrightarrow> instr_name_fm(i) \<in> formula"
  unfolding instr_name_fm_def instruction_def using action_subset_nat by auto

lemma arity_instr_name_fm: "i \<in> instruction \<Longrightarrow> arity(instr_name_fm(i)) = 1"
  unfolding instr_name_fm_def instruction_def using action_subset_nat
  by (auto simp add: arity_Exists arity_And arity_nat_name_fm arity_pair_fm ord_simp_union)

lemma sats_instr_name_fm:
  assumes model: "transitive_zfc_model(A)" and i: "i \<in> instruction"
    and y: "y \<in> A" and env: "env \<in> list(A)"
  shows "(A, Cons(y,env) \<Turnstile> instr_name_fm(i)) \<longleftrightarrow> y = i"
proof -
  interpret tm_model A by unfold_locales (rule model)
  from i obtain a q where iq: "i = \<langle>a,q\<rangle>" and a: "a \<in> nat" and q: "q \<in> nat"
    unfolding instruction_def using action_subset_nat by blast
  show ?thesis
    using iq a q y env sats_nat_name_fm[OF model a] sats_nat_name_fm[OF model q]
    by (auto simp add: instr_name_fm_def)
qed

section \<open>Closed halting sentences\<close>

definition halt_sentence :: "[i,i] \<Rightarrow> i" where
  "halt_sentence(P,x) \<equiv>
    Exists(And(list_name_fm(nat_name_fm,x),
      Exists(And(list_name_fm(instr_name_fm,P), halt_fm))))"

lemma halt_sentence_type [TC]:
  assumes P: "P \<in> machine" and x: "x \<in> list(symbol)"
  shows "halt_sentence(P,x) \<in> formula"
proof -
  have "list_name_fm(nat_name_fm,x) \<in> formula"
    using x by (rule list_name_fm_type) (rule nat_name_sym_type)
  moreover have "list_name_fm(instr_name_fm,P) \<in> formula"
    using P unfolding machine_def by (rule list_name_fm_type) simp
  ultimately show ?thesis unfolding halt_sentence_def by simp
qed

lemma arity_halt_sentence:
  assumes P: "P \<in> machine" and x: "x \<in> list(symbol)"
  shows "arity(halt_sentence(P,x)) = 0"
proof -
  have "arity(list_name_fm(nat_name_fm,x)) = 1"
    using x by (rule arity_list_name_fm) (erule nat_name_sym_type, erule arity_nat_name_sym)
  moreover have "arity(list_name_fm(instr_name_fm,P)) = 1"
    using P unfolding machine_def by (rule arity_list_name_fm) (auto intro: arity_instr_name_fm)
  moreover have "list_name_fm(nat_name_fm,x) \<in> formula"
    using x by (rule list_name_fm_type) (rule nat_name_sym_type)
  moreover have "list_name_fm(instr_name_fm,P) \<in> formula"
    using P unfolding machine_def by (rule list_name_fm_type) simp
  ultimately show ?thesis unfolding halt_sentence_def
    by (simp add: arity_Exists arity_And arity_halt_fm_eq ord_simp_union)
qed

theorem sats_halt_sentence_iff:
  assumes model: "transitive_zfc_model(A)"
    and P: "P \<in> machine" and x: "x \<in> list(symbol)"
  shows "(A, [] \<Turnstile> halt_sentence(P,x)) \<longleftrightarrow> halts_on(P,x)"
proof -
  interpret tm_model A by unfold_locales (rule model)
  have symA: "symbol \<subseteq> A" using sym_nat by auto
  have insA: "instruction \<subseteq> A"
    unfolding instruction_def using action_subset_nat by auto
  have PL: "P \<in> list(instruction)" using P unfolding machine_def .
  have nx: "\<And>y env. y \<in> A \<Longrightarrow> env \<in> list(A) \<Longrightarrow>
      (A, Cons(y,env) \<Turnstile> list_name_fm(nat_name_fm,x)) \<longleftrightarrow> y = x"
    by (rule sats_list_name_fm[OF model x symA]) (rule sats_nat_name_sym[OF model])
  have nP: "\<And>y env. y \<in> A \<Longrightarrow> env \<in> list(A) \<Longrightarrow>
      (A, Cons(y,env) \<Turnstile> list_name_fm(instr_name_fm,P)) \<longleftrightarrow> y = P"
    by (rule sats_list_name_fm[OF model PL insA]) (rule sats_instr_name_fm[OF model])
  have xA: "x \<in> A" using x by simp
  have PA: "P \<in> A" using P by simp
  have "(A, [] \<Turnstile> halt_sentence(P,x)) \<longleftrightarrow> (A, [P,x] \<Turnstile> halt_fm)"
    unfolding halt_sentence_def using nx nP xA PA by auto
  then show ?thesis using sats_halt_fm[OF P x] by simp
qed


section \<open>Model-theoretic consequences\<close>

corollary transitive_models_agree_on_halting:
  assumes "transitive_zfc_model(A)" "transitive_zfc_model(B)"
    and "P \<in> machine" "x \<in> list(symbol)"
  shows "(A, [] \<Turnstile> halt_sentence(P,x)) \<longleftrightarrow> (B, [] \<Turnstile> halt_sentence(P,x))"
  using sats_halt_sentence_iff assms by blast

text \<open>The following interpretation discharges the abstract halting
interface using the closed sentence constructed above.\<close>

interpretation blank_halting_sentence: halting_sentence "\<lambda>e. halt_sentence(decode_machine(e),[])"
proof
  fix e assume e: "e \<in> nat"
  have P: "decode_machine(e) \<in> machine" using e by (rule decode_machine_type)
  show "halt_sentence(decode_machine(e),[]) \<in> formula" using P by simp
  show "arity(halt_sentence(decode_machine(e),[])) = 0" using P by (simp add: arity_halt_sentence)
next
  fix e M assume e: "e \<in> nat" and M: "transitive_zfc_model(M)"
  have P: "decode_machine(e) \<in> machine" using e by (rule decode_machine_type)
  show "(M, [] \<Turnstile> halt_sentence(decode_machine(e),[])) \<longleftrightarrow> halts_blank(decode_machine(e))"
    using sats_halt_sentence_iff[OF M P] by simp
qed

theorem blank_halting_or_CH_invariant_iff:
  assumes "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC" "e \<in> nat"
  shows "zfc_invariant(Or(halt_sentence(decode_machine(e),[]), \<cdot>CH\<cdot>)) \<longleftrightarrow>
    halts_blank(decode_machine(e))"
  using blank_halting_sentence.halting_or_CH_invariant_iff_halts_blank[OF assms]
  unfolding blank_halting_sentence.halting_or_CH_fm_def .

definition self_halting_or_CH :: "i \<Rightarrow> i" where
  "self_halting_or_CH(e) \<equiv>
    Or(halt_sentence(decode_machine(e),numeral_input(e)), \<cdot>CH\<cdot>)"

theorem invariant_index_set_eq_self_halting:
  assumes countable: "M \<approx> \<omega>" and transitive: "Transset(M)" and zfc: "M \<Turnstile> ZFC"
  shows "{e \<in> nat. zfc_invariant(self_halting_or_CH(e))} = self_halting"
proof -
  have CH_type: "\<cdot>CH\<cdot> \<in> formula" by typecheck
  have CH_closed: "arity(\<cdot>CH\<cdot>) = 0" by (simp add: Not_CH.arity_is_ContHyp_fm)
  have CH_noninv: "\<not> zfc_invariant(\<cdot>CH\<cdot>)"
    by (rule CH_not_invariant[OF countable transitive zfc])
  have "\<And>e. e \<in> nat \<Longrightarrow>
      zfc_invariant(self_halting_or_CH(e)) \<longleftrightarrow> halts_on(decode_machine(e),numeral_input(e))"
  proof -
    fix e assume e: "e \<in> nat"
    have P: "decode_machine(e) \<in> machine" using e by (rule decode_machine_type)
    have x: "numeral_input(e) \<in> list(symbol)" using e by (rule numeral_input_type)
    show "zfc_invariant(self_halting_or_CH(e)) \<longleftrightarrow> halts_on(decode_machine(e),numeral_input(e))"
      unfolding self_halting_or_CH_def
      by (rule uniform_or_invariant_iff[OF halt_sentence_type[OF P x] arity_halt_sentence[OF P x]
            CH_type CH_closed CH_noninv])
        (rule sats_halt_sentence_iff[OF _ P x])
  qed
  then show ?thesis unfolding self_halting_def by blast
qed

corollary invariant_index_set_not_tm_decidable:
  assumes "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows "\<not> tm_decidable({e \<in> nat. zfc_invariant(self_halting_or_CH(e))})"
  using invariant_index_set_eq_self_halting[OF assms] self_halting_not_tm_decidable by simp

end
