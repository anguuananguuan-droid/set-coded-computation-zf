(*  Title:      Turing_Effective_Invariance.thy
    Author:     Tang Ziyi
*)

section \<open>Effective Syntax for Invariance\<close>

theory Turing_Effective_Invariance
  imports
    "Turing_Machine_Name_Primrec"
    "Turing_Invariance_Codes"
    "Turing_Primrec_Reductions"
begin

text \<open>The positive and negative reducing functions construct the
codes of the closed halting sentence and its negation, each disjoined with
CH. The reduction equations require that CH is not invariant. A countable
transitive ZFC set model supplies this premise through
\<open>CH_not_invariant\<close>.
The functions belong to \<open>prim_rec\<close>; the conclusions use
\<open>pr_reduces\<close> and \<open>pr_many_one_reducible\<close>.\<close>

subsection \<open>Closed halting sentence code\<close>

definition pr_halt_sentence_code :: i where
  "pr_halt_sentence_code \<equiv>
    COMP(pr_formula_exists,
      [COMP(pr_formula_and,
        [pr_input_name_code,
         COMP(pr_formula_exists,
           [COMP(pr_formula_and,
             [pr_machine_name_code,CONSTANT(formula_code(halt_fm))])])])])"

lemma pr_halt_sentence_code_in_prim_rec [TC]:
  "pr_halt_sentence_code \<in> prim_rec"
  unfolding pr_halt_sentence_code_def
  by typecheck

theorem pr_halt_sentence_code_apply:
  assumes e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_halt_sentence_code`Cons(e,l) =
    formula_code(halt_sentence(decode_machine(e),numeral_input(e)))"
proof -
  have halt: "halt_fm \<in> formula" by (rule halt_fm_type)
  from e have input: "numeral_input(e) \<in> list(symbol)"
    by (rule numeral_input_type)
  from e have tm_machine: "decode_machine(e) \<in> tm_machine"
    by (rule decode_machine_type)
  from input have input_name:
    "list_name_fm(nat_name_fm,numeral_input(e)) \<in> formula"
    by (rule list_name_fm_type) (rule nat_name_sym_type)
  from tm_machine have machine_name:
    "list_name_fm(instr_name_fm,decode_machine(e)) \<in> formula"
    unfolding tm_machine_def by (rule list_name_fm_type) (rule instr_name_fm_type)
  from machine_name halt have inner:
    "Exists(And(list_name_fm(instr_name_fm,decode_machine(e)),halt_fm))
      \<in> formula" by typecheck
  from input_name inner have outer:
    "And(list_name_fm(nat_name_fm,numeral_input(e)),
      Exists(And(list_name_fm(instr_name_fm,decode_machine(e)),halt_fm)))
      \<in> formula" by typecheck
  from e tail halt input_name machine_name inner outer show ?thesis
    unfolding pr_halt_sentence_code_def halt_sentence_def
    by (simp add: COMP_1 COMP_2 CONSTANT
        pr_input_name_code_apply pr_machine_name_code_apply
        pr_formula_and_apply pr_formula_exists_apply formula_code_type)
qed

subsection \<open>Positive and negative sentence codes\<close>

definition pr_invariance_positive :: i where
  "pr_invariance_positive \<equiv>
    COMP(pr_formula_or,
      [pr_halt_sentence_code,CONSTANT(formula_code(\<cdot>CH\<cdot>))])"

lemma pr_invariance_positive_in_prim_rec [TC]:
  "pr_invariance_positive \<in> prim_rec"
  unfolding pr_invariance_positive_def
  by typecheck

theorem pr_invariance_positive_apply:
  assumes e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_invariance_positive`Cons(e,l) = self_halting_positive_code(e)"
proof -
  from e have tm_machine: "decode_machine(e) \<in> tm_machine"
    by (rule decode_machine_type)
  from e have input: "numeral_input(e) \<in> list(symbol)"
    by (rule numeral_input_type)
  from tm_machine input have sentence:
    "halt_sentence(decode_machine(e),numeral_input(e)) \<in> formula"
    by (rule halt_sentence_type)
  have ch: "\<cdot>CH\<cdot> \<in> formula" by typecheck
  from e tail sentence ch show ?thesis
    unfolding pr_invariance_positive_def self_halting_positive_code_def
      self_halting_or_CH_def
    by (simp add: COMP_2 CONSTANT pr_halt_sentence_code_apply
        pr_formula_or_apply formula_code_type)
qed

definition pr_invariance_negative :: i where
  "pr_invariance_negative \<equiv>
    COMP(pr_formula_or,
      [COMP(pr_formula_neg,[pr_halt_sentence_code]),
       CONSTANT(formula_code(\<cdot>CH\<cdot>))])"

lemma pr_invariance_negative_in_prim_rec [TC]:
  "pr_invariance_negative \<in> prim_rec"
  unfolding pr_invariance_negative_def
  by typecheck

theorem pr_invariance_negative_apply:
  assumes e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_invariance_negative`Cons(e,l) = self_halting_negative_code(e)"
proof -
  from e have tm_machine: "decode_machine(e) \<in> tm_machine"
    by (rule decode_machine_type)
  from e have input: "numeral_input(e) \<in> list(symbol)"
    by (rule numeral_input_type)
  from tm_machine input have sentence:
    "halt_sentence(decode_machine(e),numeral_input(e)) \<in> formula"
    by (rule halt_sentence_type)
  from sentence have neg:
    "Neg(halt_sentence(decode_machine(e),numeral_input(e))) \<in> formula"
    by typecheck
  have ch: "\<cdot>CH\<cdot> \<in> formula" by typecheck
  from e tail sentence neg ch show ?thesis
    unfolding pr_invariance_negative_def self_halting_negative_code_def
      self_nonhalting_or_CH_def
    by (simp add: COMP_2 COMP_1 CONSTANT pr_halt_sentence_code_apply
        pr_formula_neg_apply pr_formula_or_apply formula_code_type)
qed

subsection \<open>Uniform sentence families\<close>

text \<open>Let a family of closed sentences express membership in a set
uniformly over all transitive ZFC set models. If their codes are produced
by a primitive-recursive function, disjoining any fixed non-invariant
sentence gives a primitive-recursive reduction to invariant sentence codes.
This statement does not require a machine interpretation of the source set
or use CH.\<close>

theorem pr_reduces_invariance:
  assumes f: "f \<in> prim_rec"
    and A: "A \<subseteq> nat"
    and fam: "\<And>e. e \<in> nat \<Longrightarrow> \<phi>(e) \<in> formula \<and> arity(\<phi>(e)) = 0"
    and code: "\<And>e. e \<in> nat \<Longrightarrow> f`[e] = formula_code(\<phi>(e))"
    and uniform: "\<And>e M. e \<in> nat \<Longrightarrow> transitive_zfc_model(M) \<Longrightarrow>
        ((M, [] \<Turnstile> \<phi>(e)) \<longleftrightarrow> e \<in> A)"
    and \<sigma>: "\<sigma> \<in> formula" "arity(\<sigma>) = 0" "\<not> zfc_invariant(\<sigma>)"
  shows "pr_reduces(COMP(pr_formula_or,[f,CONSTANT(formula_code(\<sigma>))]),
           A, invariant_formula_codes)"
proof -
  have "COMP(pr_formula_or,[f,CONSTANT(formula_code(\<sigma>))]) \<in> prim_rec"
    using f \<sigma> by (simp add: formula_code_type)
  moreover have "\<forall>e\<in>nat. e \<in> A \<longleftrightarrow>
      COMP(pr_formula_or,[f,CONSTANT(formula_code(\<sigma>))])`[e]
        \<in> invariant_formula_codes"
  proof
    fix e assume e: "e \<in> nat"
    from fam[OF e] have p: "\<phi>(e) \<in> formula" and c: "arity(\<phi>(e)) = 0" by auto
    have val: "COMP(pr_formula_or,[f,CONSTANT(formula_code(\<sigma>))])`[e]
        = formula_code(Or(\<phi>(e),\<sigma>))"
      using e f p \<sigma>(1) code[OF e]
      by (simp add: COMP_2 CONSTANT pr_formula_or_apply formula_code_type)
    have "zfc_invariant(Or(\<phi>(e),\<sigma>)) \<longleftrightarrow> e \<in> A"
      by (rule uniform_or_invariant_iff[OF p c \<sigma>]) (rule uniform[OF e])
    then show "e \<in> A \<longleftrightarrow>
        COMP(pr_formula_or,[f,CONSTANT(formula_code(\<sigma>))])`[e]
          \<in> invariant_formula_codes"
      using val invariant_formula_code_iff[of "Or(\<phi>(e),\<sigma>)"] p \<sigma>(1) by simp
  qed
  ultimately show ?thesis
    using A invariant_formula_codes_subset_nat unfolding pr_reduces_def by blast
qed

subsection \<open>Explicit reducing functions\<close>

theorem positive_primitive_recursive_reduction_of_CH_not_invariant:
  assumes CH_noninv: "\<not> zfc_invariant(\<cdot>CH\<cdot>)"
  shows
    "pr_reduces(pr_invariance_positive,self_halting,invariant_formula_codes)"
proof -
  let ?\<phi> = "\<lambda>e. halt_sentence(decode_machine(e),numeral_input(e))"
  have "pr_reduces(COMP(pr_formula_or,
      [pr_halt_sentence_code,CONSTANT(formula_code(\<cdot>CH\<cdot>))]),
      self_halting, invariant_formula_codes)"
  proof (rule pr_reduces_invariance[where \<phi> = ?\<phi>])
    show "pr_halt_sentence_code \<in> prim_rec" by typecheck
    show "self_halting \<subseteq> nat" by (rule self_halting_subset_nat)
    fix e assume e: "e \<in> nat"
    then show "?\<phi>(e) \<in> formula \<and> arity(?\<phi>(e)) = 0"
      by (simp add: halt_sentence_type arity_halt_sentence
          decode_machine_type numeral_input_type)
    from e show "pr_halt_sentence_code`[e] = formula_code(?\<phi>(e))"
      by (simp add: pr_halt_sentence_code_apply)
    fix M assume "transitive_zfc_model(M)"
    then show "(M, [] \<Turnstile> ?\<phi>(e)) \<longleftrightarrow> e \<in> self_halting"
      using e sats_halt_sentence_iff[OF transitive_zfc_model_imp_zf]
        decode_machine_type numeral_input_type self_halting_iff by simp
  next
    show "\<cdot>CH\<cdot> \<in> formula" by typecheck
    show "arity(\<cdot>CH\<cdot>) = 0" by (simp add: Not_CH.arity_is_ContHyp_fm)
    show "\<not> zfc_invariant(\<cdot>CH\<cdot>)" by (rule CH_noninv)
  qed
  then show ?thesis unfolding pr_invariance_positive_def .
qed

theorem negative_primitive_recursive_reduction_of_CH_not_invariant:
  assumes CH_noninv: "\<not> zfc_invariant(\<cdot>CH\<cdot>)"
  shows "pr_reduces(pr_invariance_negative,nat -
    self_halting,invariant_formula_codes)"
proof -
  let ?\<phi> = "\<lambda>e. Neg(halt_sentence(decode_machine(e),numeral_input(e)))"
  have "pr_reduces(COMP(pr_formula_or,
      [COMP(pr_formula_neg,[pr_halt_sentence_code]),
       CONSTANT(formula_code(\<cdot>CH\<cdot>))]),
      nat - self_halting, invariant_formula_codes)"
  proof (rule pr_reduces_invariance[where \<phi> = ?\<phi>])
    show "COMP(pr_formula_neg,[pr_halt_sentence_code]) \<in> prim_rec" by typecheck
    show "nat - self_halting \<subseteq> nat" by blast
    fix e assume e: "e \<in> nat"
    then show "?\<phi>(e) \<in> formula \<and> arity(?\<phi>(e)) = 0"
      by (simp add: halt_sentence_type arity_halt_sentence
          decode_machine_type numeral_input_type)
    from e show "COMP(pr_formula_neg,[pr_halt_sentence_code])`[e] =
        formula_code(?\<phi>(e))"
      by (simp add: COMP_1 pr_halt_sentence_code_apply pr_formula_neg_apply
          halt_sentence_type decode_machine_type numeral_input_type)
    fix M assume "transitive_zfc_model(M)"
    then show "(M, [] \<Turnstile> ?\<phi>(e)) \<longleftrightarrow> e \<in> nat - self_halting"
      using e sats_halt_sentence_iff[OF transitive_zfc_model_imp_zf]
        decode_machine_type numeral_input_type self_halting_iff by simp
  next
    show "\<cdot>CH\<cdot> \<in> formula" by typecheck
    show "arity(\<cdot>CH\<cdot>) = 0" by (simp add: Not_CH.arity_is_ContHyp_fm)
    show "\<not> zfc_invariant(\<cdot>CH\<cdot>)" by (rule CH_noninv)
  qed
  then show ?thesis unfolding pr_invariance_negative_def .
qed

theorem positive_primitive_recursive_reduction:
  assumes "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows
    "pr_reduces(pr_invariance_positive,self_halting,invariant_formula_codes)"
  by (rule positive_primitive_recursive_reduction_of_CH_not_invariant
      [OF CH_not_invariant[OF assms]])

theorem negative_primitive_recursive_reduction:
  assumes "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows "pr_reduces(pr_invariance_negative,nat -
    self_halting,invariant_formula_codes)"
  by (rule negative_primitive_recursive_reduction_of_CH_not_invariant
      [OF CH_not_invariant[OF assms]])

subsection \<open>Many-one reducibility\<close>

theorem self_halting_pr_many_one_invariance_of_CH_not_invariant:
  assumes "\<not> zfc_invariant(\<cdot>CH\<cdot>)"
  shows "pr_many_one_reducible(self_halting,invariant_formula_codes)"
  unfolding pr_many_one_reducible_def
  using positive_primitive_recursive_reduction_of_CH_not_invariant[OF assms] by
    blast

theorem nonhalting_pr_many_one_invariance_of_CH_not_invariant:
  assumes "\<not> zfc_invariant(\<cdot>CH\<cdot>)"
  shows "pr_many_one_reducible(nat - self_halting,invariant_formula_codes)"
  unfolding pr_many_one_reducible_def
  using negative_primitive_recursive_reduction_of_CH_not_invariant[OF assms] by
    blast

theorem self_halting_pr_many_one_invariance:
  assumes "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows "pr_many_one_reducible(self_halting,invariant_formula_codes)"
  by (rule self_halting_pr_many_one_invariance_of_CH_not_invariant
      [OF CH_not_invariant[OF assms]])

theorem nonhalting_pr_many_one_invariance:
  assumes "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows "pr_many_one_reducible(nat - self_halting,invariant_formula_codes)"
  by (rule nonhalting_pr_many_one_invariance_of_CH_not_invariant
      [OF CH_not_invariant[OF assms]])

end
