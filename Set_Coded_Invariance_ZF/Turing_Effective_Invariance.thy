(*  Title:      Turing_Effective_Invariance.thy
    Author:     Tang Ziyi
*)

section \<open>Effective Syntax for Invariance\<close>

theory Turing_Effective_Invariance
  imports
    Turing_Machine_Name_Primrec
    Turing_Invariance_Codes
    "Set_Coded_Computation_ZF.Turing_Primrec_Reductions"
begin

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
  by (typecheck add: formula_code_type)

theorem pr_halt_sentence_code_apply:
  assumes e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_halt_sentence_code`Cons(e,l) =
    formula_code(halt_sentence(decode_machine(e),numeral_input(e)))"
proof -
  have halt: "halt_fm \<in> formula" by (rule halt_fm_type)
  from e have input: "numeral_input(e) \<in> list(symbol)"
    by (rule numeral_input_type)
  from e have machine: "decode_machine(e) \<in> machine"
    by (rule decode_machine_type)
  from input have input_name:
    "list_name_fm(nat_name_fm,numeral_input(e)) \<in> formula"
    by (rule list_name_fm_type) (rule nat_name_sym_type)
  from machine have machine_name:
    "list_name_fm(instr_name_fm,decode_machine(e)) \<in> formula"
    unfolding machine_def by (rule list_name_fm_type) (rule instr_name_fm_type)
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

definition pr_invariance_positive :: i where
  "pr_invariance_positive \<equiv>
    COMP(pr_formula_or,
      [pr_halt_sentence_code,CONSTANT(formula_code(\<cdot>CH\<cdot>))])"

lemma pr_invariance_positive_in_prim_rec [TC]:
  "pr_invariance_positive \<in> prim_rec"
  unfolding pr_invariance_positive_def
  by (typecheck add: formula_code_type)

theorem pr_invariance_positive_apply:
  assumes e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_invariance_positive`Cons(e,l) = self_halting_positive_code(e)"
proof -
  from e have machine: "decode_machine(e) \<in> machine"
    by (rule decode_machine_type)
  from e have input: "numeral_input(e) \<in> list(symbol)"
    by (rule numeral_input_type)
  from machine input have sentence:
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
  by (typecheck add: formula_code_type)

theorem pr_invariance_negative_apply:
  assumes e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_invariance_negative`Cons(e,l) = self_halting_negative_code(e)"
proof -
  from e have machine: "decode_machine(e) \<in> machine"
    by (rule decode_machine_type)
  from e have input: "numeral_input(e) \<in> list(symbol)"
    by (rule numeral_input_type)
  from machine input have sentence:
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

theorem positive_primitive_recursive_reduction:
  assumes countable: "M \<approx> \<omega>" and transitive: "Transset(M)"
    and zfc: "M \<Turnstile> ZFC"
  shows "pr_reduces(pr_invariance_positive,self_halting,invariant_formula_codes)"
proof -
  have "pr_invariance_positive \<in> prim_rec"
    by (rule pr_invariance_positive_in_prim_rec)
  moreover have "self_halting \<subseteq> nat"
    by (rule self_halting_subset_nat)
  moreover have "invariant_formula_codes \<subseteq> nat"
    by (rule invariant_formula_codes_subset_nat)
  moreover have "\<forall>e\<in>nat.
      e \<in> self_halting \<longleftrightarrow>
      pr_invariance_positive`[e] \<in> invariant_formula_codes"
  proof (intro ballI)
    fix e assume e: "e \<in> nat"
    from positive_code_reduces_self_halting[OF countable transitive zfc e]
      pr_invariance_positive_apply[OF e]
    show "e \<in> self_halting \<longleftrightarrow>
      pr_invariance_positive`[e] \<in> invariant_formula_codes" by simp
  qed
  ultimately show ?thesis unfolding pr_reduces_def by blast
qed

theorem negative_primitive_recursive_reduction:
  assumes countable: "M \<approx> \<omega>" and transitive: "Transset(M)"
    and zfc: "M \<Turnstile> ZFC"
  shows "pr_reduces(pr_invariance_negative,nat - self_halting,invariant_formula_codes)"
proof -
  have "pr_invariance_negative \<in> prim_rec"
    by (rule pr_invariance_negative_in_prim_rec)
  moreover have "nat - self_halting \<subseteq> nat" by blast
  moreover have "invariant_formula_codes \<subseteq> nat"
    by (rule invariant_formula_codes_subset_nat)
  moreover have "\<forall>e\<in>nat.
      e \<in> nat - self_halting \<longleftrightarrow>
      pr_invariance_negative`[e] \<in> invariant_formula_codes"
  proof (intro ballI)
    fix e assume e: "e \<in> nat"
    from e negative_code_reduces_nonhalting[OF countable transitive zfc e]
      pr_invariance_negative_apply[OF e]
    show "e \<in> nat - self_halting \<longleftrightarrow>
      pr_invariance_negative`[e] \<in> invariant_formula_codes" by simp
  qed
  ultimately show ?thesis unfolding pr_reduces_def by blast
qed

theorem self_halting_pr_many_one_invariance:
  assumes "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows "pr_many_one_reducible(self_halting,invariant_formula_codes)"
  unfolding pr_many_one_reducible_def
  using positive_primitive_recursive_reduction[OF assms] by blast

theorem nonhalting_pr_many_one_invariance:
  assumes "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows "pr_many_one_reducible(nat - self_halting,invariant_formula_codes)"
  unfolding pr_many_one_reducible_def
  using negative_primitive_recursive_reduction[OF assms] by blast

end
