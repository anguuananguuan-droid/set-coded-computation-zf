(*  Title:      Turing_Model_Witnesses.thy
    Author:     Tang Ziyi
*)

section \<open>Finite Witnesses in Transitive Models\<close>

theory Turing_Model_Witnesses
  imports
    "Turing_Machine"
    "Independence_CH.ZF_Trans_Interpretations"
begin

definition transitive_zf_model :: "i \<Rightarrow> o" where
  "transitive_zf_model(M) \<equiv> Transset(M) \<and> M \<Turnstile> ZF"

text \<open>Finite machines, inputs, configurations, and canonical finite
traces belong to each transitive ZF set model. Choice is not required for
finite object closure or finite runs.\<close>

subsection \<open>Finite object closure\<close>

context M_trivial
begin

lemma tm_list_closed:
  assumes xs: "xs \<in> list(A)" and elements: "\<And>a. a \<in> A \<Longrightarrow> M(a)"
  shows "M(xs)"
  using xs by (induct xs rule: list.induct) (auto intro: elements)

lemma tm_symbol_closed: "a \<in> symbol \<Longrightarrow> M(a)"
  unfolding symbol_def by auto

lemma tm_instruction_closed: "ins \<in> instruction \<Longrightarrow> M(ins)"
  unfolding instruction_def action_def by auto

lemma tm_machine_closed: "P \<in> tm_machine \<Longrightarrow> M(P)"
  unfolding tm_machine_def by (rule tm_list_closed) (auto intro:
    tm_instruction_closed)

lemma tm_input_closed: "x \<in> list(symbol) \<Longrightarrow> M(x)"
  by (rule tm_list_closed) (auto intro: tm_symbol_closed)

lemma tm_configuration_closed: "c \<in> configuration \<Longrightarrow> M(c)"
  unfolding configuration_def tm_tape_def by (auto intro: tm_input_closed)

lemma tm_finite_lambda_closed:
  assumes n: "n \<in> nat" and values: "\<And>k. k \<in> n \<Longrightarrow> M(f(k))"
  shows "M(\<lambda>k\<in>n. f(k))"
  using n values
proof (induct n rule: nat_induct)
  case 0 show ?case by simp
next
  case (succ n)
  have fn: "M(f(n))" using succ.prems by auto
  have rest: "M(\<lambda>k\<in>n. f(k))" by (rule succ.hyps(2)) (auto intro:
    succ.prems)
  have split: "(\<lambda>k\<in>succ(n). f(k)) = cons(\<langle>n,f(n)\<rangle>,\<lambda>k\<in>n. f(k))"
    unfolding lam_def succ_def by auto
  from fn rest nat_into_M[OF succ.hyps(1)] split show ?case by simp
qed

lemma tm_trace_closed:
  assumes P: "P \<in> tm_machine" and c: "c \<in> configuration" and n: "n \<in> nat"
  shows "M(\<lambda>k\<in>succ(n). steps(P,c,k))"
proof (rule tm_finite_lambda_closed[OF nat_succI[OF n]])
  fix k assume k: "k \<in> succ(n)"
  have natural: "k \<in> nat" using k n by (blast intro: Ord_trans)
  show "M(steps(P,c,k))" by (rule tm_configuration_closed[OF steps_type[OF P c
    natural]])
qed


end

subsection \<open>Transitive model interpretations\<close>

lemma transitive_zf_M_ZF1_trans:
  assumes model: "transitive_zf_model(A)"
  shows "M_ZF1_trans(A)"
proof -
  from model have trans: "Transset(A)" and zf: "A \<Turnstile> ZF"
    unfolding transitive_zf_model_def by auto
  from M_satT_imp_M_ZF2[OF zf] trans show ?thesis
    unfolding M_ZF1_trans_def M_Z_trans_def M_transset_def M_ZF1_def by auto
qed

lemma transitive_zf_M_trivial:
  "transitive_zf_model(A) \<Longrightarrow> M_trivial(##A)"
proof -
  assume model: "transitive_zf_model(A)"
  interpret A: M_ZF1_trans A by (rule transitive_zf_M_ZF1_trans[OF model])
  show "M_trivial(##A)" by unfold_locales
qed

lemma transitive_zf_M_trancl:
  "transitive_zf_model(A) \<Longrightarrow> M_trancl(##A)"
proof -
  assume model: "transitive_zf_model(A)"
  interpret A: M_ZF1_trans A by (rule transitive_zf_M_ZF1_trans[OF model])
  show "M_trancl(##A)" by unfold_locales
qed

subsection \<open>Machine objects in a set model\<close>

theorem transitive_zf_contains_machine:
  "\<lbrakk>transitive_zf_model(A); P \<in> tm_machine\<rbrakk> \<Longrightarrow> P \<in> A"
  using M_trivial.tm_machine_closed[OF transitive_zf_M_trivial] by simp

theorem transitive_zf_contains_configuration:
  "\<lbrakk>transitive_zf_model(A); c \<in> configuration\<rbrakk> \<Longrightarrow> c \<in> A"
  using M_trivial.tm_configuration_closed[OF transitive_zf_M_trivial] by simp

theorem transitive_zf_contains_trace:
  "\<lbrakk>transitive_zf_model(A); P \<in> tm_machine; c \<in> configuration; n \<in> nat\<rbrakk> \<Longrightarrow>
    (\<lambda>k\<in>succ(n). steps(P,c,k)) \<in> A"
  using M_trivial.tm_trace_closed[OF transitive_zf_M_trivial] by simp

end
