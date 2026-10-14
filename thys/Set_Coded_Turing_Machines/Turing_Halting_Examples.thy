(*  Title:      Turing_Halting_Examples.thy
    Author:     Tang Ziyi
*)

section \<open>Using the Halting Formula Interface\<close>

theory Turing_Halting_Examples
  imports Turing_Examples Turing_Halting_Codes
begin

text \<open>The operational proof from the machine example supplies an
internal theorem in every transitive ZF set model. The same result applies
to a formula identified only by its numerical code. Both clients use the
public interfaces without unfolding the halting formula, its finite-object
names, or the primitive-recursive constructor.\<close>

subsection \<open>From execution to satisfaction\<close>

theorem scan_append_sentence:
  assumes model: "transitive_zf_model(A)" and n: "n \<in> nat"
  shows "(A, [] \<Turnstile> halt_sentence(scan_append_machine,numeral_input(n)))"
  using sats_halt_sentence_iff[OF model scan_append_machine_type
      numeral_input_type[OF n]] scan_append_halts[OF n] by simp

subsection \<open>From a sentence code to satisfaction\<close>

theorem scan_append_sentence_code:
  assumes model: "transitive_zf_model(A)" and n: "n \<in> nat"
    and p: "p \<in> formula"
    and code: "formula_code(p) =
      pr_machine_input_sentence_code`[encode_machine(scan_append_machine),n]"
  shows "(A, [] \<Turnstile> p)"
  using sats_machine_input_sentence_code_iff[OF model
      encode_machine_natural[OF scan_append_machine_type] n p code]
    decode_encode_machine[OF scan_append_machine_type] scan_append_halts[OF n]
  by simp

end
