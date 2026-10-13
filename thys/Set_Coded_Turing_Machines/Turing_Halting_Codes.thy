(*  Title:      Turing_Halting_Codes.thy
    Author:     Tang Ziyi
*)

section \<open>Effective Halting Sentences\<close>

theory Turing_Halting_Codes
  imports "Turing_Machine_Name_Primrec"
begin

text \<open>The unary primitive-recursive function constructs the code of the
closed sentence saying that the decoded machine halts on its own unary
code. Membership in \<open>prim_rec\<close> certifies the numerical function,
independently of a machine implementation of that function.\<close>

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
    unfolding tm_machine_def
    by (rule list_name_fm_type) (rule instr_name_fm_type)
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

corollary transitive_zf_contains_decoded_machine:
  "\<lbrakk>transitive_zf_model(A); e \<in> nat\<rbrakk> \<Longrightarrow> decode_machine(e) \<in> A"
  by (rule transitive_zf_contains_machine) (auto intro: decode_machine_type)

end
