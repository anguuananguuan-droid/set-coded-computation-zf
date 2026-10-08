(*  Title:      Turing_Halting_Index.thy
    Author:     Tang Ziyi
*)

section \<open>Halting Index Sets in Transitive Models\<close>

theory Turing_Halting_Index
  imports Turing_Arithmetic_Truth "Set_Coded_Computation_ZF.Turing_Rejection"
begin

definition model_self_halting :: "i \<Rightarrow> i" where
  "model_self_halting(A) \<equiv>
    {e\<in>nat. model_halting_witness(A,decode_machine(e),numeral_input(e))}"

theorem transitive_zfc_model_self_halting_eq:
  assumes model: "transitive_zfc_model(A)"
  shows "model_self_halting(A) = self_halting"
  unfolding model_self_halting_def self_halting_def
  using transitive_zfc_halting_witness_iff[OF model] by blast

corollary transitive_models_agree_on_self_halting:
  assumes "transitive_zfc_model(A)" "transitive_zfc_model(B)"
  shows "model_self_halting(A) = model_self_halting(B)"
  using assms transitive_zfc_model_self_halting_eq by simp

corollary model_self_halting_not_tm_decidable:
  assumes "transitive_zfc_model(A)"
  shows "\<not> tm_decidable(model_self_halting(A))"
  using transitive_zfc_model_self_halting_eq[OF assms]
    self_halting_not_tm_decidable by simp

end
