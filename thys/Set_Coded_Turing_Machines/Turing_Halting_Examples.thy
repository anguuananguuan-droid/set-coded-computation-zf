(*  Title:      Turing_Halting_Examples.thy
    Author:     Tang Ziyi
*)

section \<open>Using the Halting Formula Interface\<close>

theory Turing_Halting_Examples
  imports Turing_Examples Turing_Halting_Sentences
begin

text \<open>The operational proof from the machine example supplies an
internal theorem in every transitive ZF set model. The client uses the
satisfaction interface without unfolding the halting formula or its
finite-object names.\<close>

theorem scan_append_sentence:
  assumes model: "transitive_zf_model(A)" and n: "n \<in> nat"
  shows "(A, [] \<Turnstile> halt_sentence(scan_append_machine,numeral_input(n)))"
  using sats_halt_sentence_iff[OF model scan_append_machine_type
      numeral_input_type[OF n]] scan_append_halts[OF n] by simp

end
