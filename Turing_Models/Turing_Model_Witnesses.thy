(*  Title:      Turing_Model_Witnesses.thy
    Author:     Tang Ziyi
*)

section \<open>Finite Computation Witnesses in Transitive Models\<close>

theory Turing_Model_Witnesses
  imports "Turing_CH.Turing_CH"
begin

text \<open>Finite machines and their finite execution traces belong to every
transitive ZFC set model. This discharges a closure obligation for the later
internal halting formula. The finite_run predicate below is still the external
set-theoretic definition; no satisfaction theorem is claimed here.\<close>

context M_trivial
begin

lemma tm_list_closed:
  assumes xs: "xs \<in> list(A)" and elements: "\<And>a. a \<in> A \<Longrightarrow> M(a)"
  shows "M(xs)"
  using xs by (induct xs rule: list.induct) (auto intro: elements)

lemma tm_symbol_closed: "a \<in> symbol \<Longrightarrow> M(a)"
  unfolding symbol_def by (auto intro: nat_into_M)

lemma tm_instruction_closed: "ins \<in> instruction \<Longrightarrow> M(ins)"
  unfolding instruction_def action_def by (auto intro: nat_into_M)

lemma tm_machine_closed: "P \<in> machine \<Longrightarrow> M(P)"
  unfolding machine_def by (rule tm_list_closed) (auto intro: tm_instruction_closed)

lemma tm_input_closed: "x \<in> list(symbol) \<Longrightarrow> M(x)"
  by (rule tm_list_closed) (auto intro: tm_symbol_closed)

lemma tm_configuration_closed: "c \<in> configuration \<Longrightarrow> M(c)"
  unfolding configuration_def tape_def by (auto intro: nat_into_M tm_input_closed)

lemma tm_finite_lambda_closed:
  assumes n: "n \<in> nat" and values: "\<And>k. k \<in> n \<Longrightarrow> M(f(k))"
  shows "M(\<lambda>k\<in>n. f(k))"
  using n values
proof (induct n rule: nat_induct)
  case 0 show ?case by simp
next
  case (succ n)
  have fn: "M(f(n))" using succ.prems by auto
  have rest: "M(\<lambda>k\<in>n. f(k))" by (rule succ.hyps(2)) (auto intro: succ.prems)
  have split: "(\<lambda>k\<in>succ(n). f(k)) = cons(\<langle>n,f(n)\<rangle>,\<lambda>k\<in>n. f(k))"
    unfolding lam_def succ_def by auto
  from fn rest nat_into_M[OF succ.hyps(1)] split show ?case by simp
qed

lemma tm_trace_closed:
  assumes P: "P \<in> machine" and c: "c \<in> configuration" and n: "n \<in> nat"
  shows "M(\<lambda>k\<in>succ(n). steps(P,c,k))"
proof (rule tm_finite_lambda_closed[OF nat_succI[OF n]])
  fix k assume k: "k \<in> succ(n)"
  have natural: "k \<in> nat" using k n by (blast intro: Ord_trans Ord_nat)
  show "M(steps(P,c,k))" by (rule tm_configuration_closed[OF steps_type[OF P c natural]])
qed

lemma tm_halting_certificate:
  assumes halts: "halts_on(P,x)"
  obtains n r where "n \<in> nat" "M(n)" "M(r)" "finite_run(P,n,r)"
    "r`0 = initial_config(x)" "fst(r`n) = final_state"
proof -
  from halts obtain n where P: "P \<in> machine" and x: "x \<in> list(symbol)"
    and n: "n \<in> nat" and final: "fst(steps(P,initial_config(x),n)) = final_state"
    unfolding halts_on_def by auto
  let ?r = "\<lambda>k\<in>succ(n). steps(P,initial_config(x),k)"
  have trace: "M(?r)" by (rule tm_trace_closed[OF P initial_config_type[OF x] n])
  have run: "finite_run(P,n,?r) \<and> ?r`0 = initial_config(x)"
    using finite_run_iff_steps[OF n, of P ?r "initial_config(x)"] by simp
  have last: "fst(?r`n) = final_state" using final n by simp
  show thesis by (rule that[OF n nat_into_M[OF n] trace run[THEN conjunct1] run[THEN conjunct2] last])
qed

end

lemma transitive_zfc_M_ZF1_trans:
  assumes model: "transitive_zfc_model(A)"
  shows "M_ZF1_trans(A)"
proof -
  from model have trans: "Transset(A)" and zf: "A \<Turnstile> ZF"
    unfolding transitive_zfc_model_def ZFC_def by auto
  from M_satT_imp_M_ZF2[OF zf] trans show ?thesis
    unfolding M_ZF1_trans_def M_Z_trans_def M_transset_def M_ZF1_def by auto
qed

lemma transitive_zfc_M_trivial:
  "transitive_zfc_model(A) \<Longrightarrow> M_trivial(##A)"
proof -
  assume model: "transitive_zfc_model(A)"
  interpret A: M_ZF1_trans A by (rule transitive_zfc_M_ZF1_trans[OF model])
  show "M_trivial(##A)" by unfold_locales
qed

lemma transitive_zfc_M_trancl:
  "transitive_zfc_model(A) \<Longrightarrow> M_trancl(##A)"
proof -
  assume model: "transitive_zfc_model(A)"
  interpret A: M_ZF1_trans A by (rule transitive_zfc_M_ZF1_trans[OF model])
  show "M_trancl(##A)" by unfold_locales
qed

lemma transitive_zfc_M_ZF2_trans:
  assumes model: "transitive_zfc_model(A)"
  shows "M_ZF2_trans(A)"
proof -
  from model have zf: "A \<Turnstile> ZF"
    unfolding transitive_zfc_model_def ZFC_def by auto
  interpret Z: M_ZF A by (rule M_satT_imp_M_ZF[OF zf])
  interpret T: M_ZF1_trans A by (rule transitive_zfc_M_ZF1_trans[OF model])
  show ?thesis by unfold_locales
qed

theorem transitive_zfc_contains_machine:
  "\<lbrakk>transitive_zfc_model(A); P \<in> machine\<rbrakk> \<Longrightarrow> P \<in> A"
  using M_trivial.tm_machine_closed[OF transitive_zfc_M_trivial] by simp

theorem transitive_zfc_contains_configuration:
  "\<lbrakk>transitive_zfc_model(A); c \<in> configuration\<rbrakk> \<Longrightarrow> c \<in> A"
  using M_trivial.tm_configuration_closed[OF transitive_zfc_M_trivial] by simp

corollary transitive_zfc_contains_decoded_machine:
  "\<lbrakk>transitive_zfc_model(A); e \<in> nat\<rbrakk> \<Longrightarrow> decode_machine(e) \<in> A"
  by (rule transitive_zfc_contains_machine) (auto intro: decode_machine_type)

theorem transitive_zfc_contains_trace:
  "\<lbrakk>transitive_zfc_model(A); P \<in> machine; c \<in> configuration; n \<in> nat\<rbrakk> \<Longrightarrow>
    (\<lambda>k\<in>succ(n). steps(P,c,k)) \<in> A"
  using M_trivial.tm_trace_closed[OF transitive_zfc_M_trivial] by simp

definition model_halting_witness :: "[i,i,i] \<Rightarrow> o" where
  "model_halting_witness(A,P,x) \<equiv>
    P \<in> machine \<and> x \<in> list(symbol) \<and> P \<in> A \<and> x \<in> A \<and>
    (\<exists>n\<in>nat \<inter> A. \<exists>r\<in>A.
      finite_run(P,n,r) \<and> r`0 = initial_config(x) \<and> fst(r`n) = final_state)"

theorem transitive_zfc_halting_witness_iff:
  assumes model: "transitive_zfc_model(A)"
  shows "model_halting_witness(A,P,x) \<longleftrightarrow> halts_on(P,x)"
proof
  assume "model_halting_witness(A,P,x)"
  then show "halts_on(P,x)" unfolding model_halting_witness_def halts_on_iff_finite_run by blast
next
  assume halts: "halts_on(P,x)"
  interpret A: M_trivial "##A" by (rule transitive_zfc_M_trivial[OF model])
  from halts have P: "P \<in> machine" and x: "x \<in> list(symbol)" unfolding halts_on_def by auto
  obtain n r where
    n: "n \<in> nat" "n \<in> A" and r: "r \<in> A" "finite_run(P,n,r)"
    "r`0 = initial_config(x)" "fst(r`n) = final_state"
    by (rule A.tm_halting_certificate[OF halts]) auto
  from P x A.tm_machine_closed[OF P] A.tm_input_closed[OF x] n r
  show "model_halting_witness(A,P,x)" unfolding model_halting_witness_def by auto
qed

corollary transitive_models_agree_on_finite_halting_witnesses:
  "\<lbrakk>transitive_zfc_model(A); transitive_zfc_model(B)\<rbrakk> \<Longrightarrow>
    (model_halting_witness(A,P,x) \<longleftrightarrow> model_halting_witness(B,P,x))"
  using transitive_zfc_halting_witness_iff by blast

corollary transitive_zfc_blank_code_witness_iff:
  "transitive_zfc_model(A) \<Longrightarrow>
    (model_halting_witness(A,decode_machine(e),[]) \<longleftrightarrow>
      halts_blank(decode_machine(e)))"
  by (rule transitive_zfc_halting_witness_iff)

end
