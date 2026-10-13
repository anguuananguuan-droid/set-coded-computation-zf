(*  Title:      Turing_Halting_Index.thy
    Author:     Tang Ziyi
*)

section \<open>Halting Index Sets in Transitive Models\<close>

theory Turing_Halting_Index
  imports "Turing_Arithmetic_Truth" "Turing_Invariance.Turing_Rejection"
begin

text \<open>The external finite-run relation can be restricted to witnesses
belonging to a transitive ZF model without changing halting. The indexed
consequences below retain their ZFC model interface.\<close>

subsection \<open>Finite halting certificates\<close>

context M_trivial
begin

lemma tm_halting_certificate:
  assumes halts: "halts_on(P,x)"
  obtains n r where "n \<in> nat" "M(n)" "M(r)" "finite_run(P,n,r)"
    "r`0 = initial_config(x)" "fst(r`n) = final_state"
proof -
  from halts obtain n where P: "P \<in> tm_machine" and x: "x \<in> list(symbol)"
    and n: "n \<in> nat" and final: "fst(steps(P,initial_config(x),n)) =
      final_state"
    unfolding halts_on_def by auto
  let ?r = "\<lambda>k\<in>succ(n). steps(P,initial_config(x),k)"
  have trace: "M(?r)" by (rule tm_trace_closed[OF P initial_config_type[OF x]
    n])
  have run: "finite_run(P,n,?r) \<and> ?r`0 = initial_config(x)"
    using finite_run_iff_steps[OF n, of P ?r "initial_config(x)"] by simp
  have last: "fst(?r`n) = final_state" using final n by simp
  show thesis by (rule that[OF n nat_into_M[OF n] trace run[THEN conjunct1]
    run[THEN conjunct2] last])
qed


end

subsection \<open>Model witnesses\<close>

definition model_halting_witness :: "[i,i,i] \<Rightarrow> o" where
  "model_halting_witness(A,P,x) \<equiv>
    P \<in> tm_machine \<and> x \<in> list(symbol) \<and> P \<in> A \<and> x \<in> A \<and>
    (\<exists>n\<in>nat \<inter> A. \<exists>r\<in>A.
      finite_run(P,n,r) \<and> r`0 = initial_config(x) \<and> fst(r`n) = final_state)"

theorem transitive_zf_halting_witness_iff:
  assumes model: "transitive_zf_model(A)"
  shows "model_halting_witness(A,P,x) \<longleftrightarrow> halts_on(P,x)"
proof
  assume "model_halting_witness(A,P,x)"
  then show "halts_on(P,x)" unfolding model_halting_witness_def
    halts_on_iff_finite_run by blast
next
  assume halts: "halts_on(P,x)"
  interpret A: M_trivial "##A" by (rule transitive_zf_M_trivial[OF model])
  from halts have P: "P \<in> tm_machine" and x: "x \<in> list(symbol)" unfolding
    halts_on_def by auto
  obtain n r where
    n: "n \<in> nat" "n \<in> A" and r: "r \<in> A" "finite_run(P,n,r)"
    "r`0 = initial_config(x)" "fst(r`n) = final_state"
    by (rule A.tm_halting_certificate[OF halts]) auto
  from P x A.tm_machine_closed[OF P] A.tm_input_closed[OF x] n r
  show "model_halting_witness(A,P,x)" unfolding model_halting_witness_def by
    auto
qed

corollary transitive_models_agree_on_finite_halting_witnesses:
  "\<lbrakk>transitive_zf_model(A); transitive_zf_model(B)\<rbrakk> \<Longrightarrow>
    (model_halting_witness(A,P,x) \<longleftrightarrow> model_halting_witness(B,P,x))"
  using transitive_zf_halting_witness_iff by blast

corollary transitive_zf_blank_code_witness_iff:
  "transitive_zf_model(A) \<Longrightarrow> (model_halting_witness(A,decode_machine(e),[]) \<longleftrightarrow>
      halts_blank(decode_machine(e)))"
  by (rule transitive_zf_halting_witness_iff)

subsection \<open>Self-halting indices\<close>

definition model_self_halting :: "i \<Rightarrow> i" where
  "model_self_halting(A) \<equiv>
    {e\<in>nat. model_halting_witness(A,decode_machine(e),numeral_input(e))}"

theorem transitive_zfc_model_self_halting_eq:
  assumes model: "transitive_zfc_model(A)"
  shows "model_self_halting(A) = self_halting"
  unfolding model_self_halting_def self_halting_def
  using transitive_zf_halting_witness_iff[OF transitive_zfc_model_imp_zf[OF model]] by blast

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
