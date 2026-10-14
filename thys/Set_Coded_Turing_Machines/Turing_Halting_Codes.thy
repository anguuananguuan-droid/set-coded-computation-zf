(*  Title:      Turing_Halting_Codes.thy
    Author:     Tang Ziyi
*)

section \<open>Effective Halting Sentences\<close>

theory Turing_Halting_Codes
  imports "Turing_Machine_Name_Primrec"
begin

text \<open>The machine code and unary input are independent arguments of a
primitive-recursive sentence constructor. The resulting code determines a
closed formula whose satisfaction is equivalent to the specified execution
halting. The self-input constructor is the diagonal instance. Membership
in \<open>prim_rec\<close> certifies numerical construction independently of
a machine implementation of that function.\<close>

subsection \<open>Closed halting sentence code\<close>

definition pr_machine_input_sentence_code :: i where
  "pr_machine_input_sentence_code \<equiv>
    COMP(pr_formula_exists,
      [COMP(pr_formula_and,
        [COMP(pr_input_name_code,[PROJ(1)]),
         COMP(pr_formula_exists,
           [COMP(pr_formula_and,
             [pr_machine_name_code,CONSTANT(formula_code(halt_fm))])])])])"

lemma pr_machine_input_sentence_code_in_prim_rec [TC]:
  "pr_machine_input_sentence_code \<in> prim_rec"
  unfolding pr_machine_input_sentence_code_def
  by typecheck

theorem pr_machine_input_sentence_code_apply:
  assumes e: "e \<in> nat" and n: "n \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_machine_input_sentence_code`Cons(e,Cons(n,l)) =
    formula_code(halt_sentence(decode_machine(e),numeral_input(n)))"
proof -
  have halt: "halt_fm \<in> formula" by (rule halt_fm_type)
  from n have input: "numeral_input(n) \<in> list(symbol)"
    by (rule numeral_input_type)
  from e have tm_machine: "decode_machine(e) \<in> tm_machine"
    by (rule decode_machine_type)
  from input have input_name:
    "list_name_fm(nat_name_fm,numeral_input(n)) \<in> formula"
    by (rule list_name_fm_type) (rule nat_name_sym_type)
  from tm_machine have machine_name:
    "list_name_fm(instr_name_fm,decode_machine(e)) \<in> formula"
    unfolding tm_machine_def
    by (rule list_name_fm_type) (rule instr_name_fm_type)
  from machine_name halt have inner:
    "Exists(And(list_name_fm(instr_name_fm,decode_machine(e)),halt_fm))
      \<in> formula" by typecheck
  from input_name inner have outer:
    "And(list_name_fm(nat_name_fm,numeral_input(n)),
      Exists(And(list_name_fm(instr_name_fm,decode_machine(e)),halt_fm)))
      \<in> formula" by typecheck
  from e n tail halt input_name machine_name inner outer show ?thesis
    unfolding pr_machine_input_sentence_code_def halt_sentence_def
    by (simp add: COMP_1 COMP_2 CONSTANT PROJ_0
        pr_input_name_code_apply pr_machine_name_code_apply
        pr_formula_and_apply pr_formula_exists_apply formula_code_type)
qed

text \<open>The code interface characterises any formula with the constructed
code. Injectivity removes the need for a separate formula decoder. Formula
membership is a premise because the coding function is specified on formulas.\<close>

theorem pr_machine_input_sentence_code_iff:
  assumes e: "e \<in> nat" and n: "n \<in> nat" and p: "p \<in> formula"
  shows "formula_code(p) = pr_machine_input_sentence_code`[e,n] \<longleftrightarrow>
    p = halt_sentence(decode_machine(e),numeral_input(n))"
  using pr_machine_input_sentence_code_apply[OF e n, of "[]"] p
    halt_sentence_type[OF decode_machine_type[OF e] numeral_input_type[OF n]]
    formula_code_injective by auto

theorem sats_machine_input_sentence_code_iff:
  assumes model: "transitive_zf_model(A)"
    and e: "e \<in> nat" and n: "n \<in> nat" and p: "p \<in> formula"
    and code: "formula_code(p) = pr_machine_input_sentence_code`[e,n]"
  shows "(A, [] \<Turnstile> p) \<longleftrightarrow>
    halts_on(decode_machine(e),numeral_input(n))"
  using pr_machine_input_sentence_code_iff[OF e n p] code
    sats_halt_sentence_iff[OF model decode_machine_type[OF e]
      numeral_input_type[OF n]] by simp

subsection \<open>Self-input instance\<close>

definition pr_halt_sentence_code :: i where
  "pr_halt_sentence_code \<equiv>
    COMP(pr_machine_input_sentence_code,[PROJ(0),PROJ(0)])"

lemma pr_halt_sentence_code_in_prim_rec [TC]:
  "pr_halt_sentence_code \<in> prim_rec"
  unfolding pr_halt_sentence_code_def by typecheck

theorem pr_halt_sentence_code_apply:
  assumes e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_halt_sentence_code`Cons(e,l) =
    formula_code(halt_sentence(decode_machine(e),numeral_input(e)))"
  using e tail unfolding pr_halt_sentence_code_def
  by (simp add: COMP_2 PROJ_0 pr_machine_input_sentence_code_apply)

corollary transitive_zf_contains_decoded_machine:
  "\<lbrakk>transitive_zf_model(A); e \<in> nat\<rbrakk> \<Longrightarrow> decode_machine(e) \<in> A"
  by (rule transitive_zf_contains_machine) (auto intro: decode_machine_type)

end
