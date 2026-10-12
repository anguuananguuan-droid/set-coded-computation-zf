(*  Title:      Turing_CH.thy
    Author:     Tang Ziyi
*)

section \<open>Sentence Invariance and CH\<close>

theory Turing_CH
  imports
    Turing_Model_Witnesses
    "Independence_CH.Definitions_Main"
begin

text \<open>Invariance concerns closed sentences and all transitive ZFC set
models. The existence of a countable transitive model supplies two such
models that disagree on CH.\<close>

subsection \<open>Model agreement\<close>

definition zfc_invariant :: "i \<Rightarrow> o" where
  "zfc_invariant(\<phi>) \<equiv>
    \<phi> \<in> formula \<and>
    arity(\<phi>) = 0 \<and>
    (\<forall>M N.
      transitive_zfc_model(M) \<longrightarrow>
      transitive_zfc_model(N) \<longrightarrow>
      ((M, [] \<Turnstile> \<phi>) \<longleftrightarrow> (N, [] \<Turnstile>
        \<phi>)))"

theorem CH_not_invariant:
  assumes countable: "M \<approx> \<omega>"
    and transitive: "Transset(M)"
    and zfc: "M \<Turnstile> ZFC"
  shows "\<not> zfc_invariant(\<cdot>CH\<cdot>)"
proof -
  from CH.ctm_ZFC_imp_ctm_CH[OF countable transitive zfc]
  obtain M_CH where
    "Transset(M_CH)"
    and "M_CH \<Turnstile> ZFC \<union> {\<cdot>CH\<cdot>}"
    by blast
  then have M_CH_model:
    "transitive_zfc_model(M_CH)"
    and M_CH_truth:
    "M_CH, [] \<Turnstile> \<cdot>CH\<cdot>"
    unfolding transitive_zfc_model_def by auto

  from Not_CH.ctm_ZFC_imp_ctm_not_CH[OF countable transitive zfc]
  obtain M_not_CH where
    "Transset(M_not_CH)"
    and "M_not_CH \<Turnstile> ZFC \<union>
      {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>}"
    by blast
  then have M_not_CH_model:
    "transitive_zfc_model(M_not_CH)"
    and M_not_CH_falsity:
    "\<not> (M_not_CH, [] \<Turnstile> \<cdot>CH\<cdot>)"
    unfolding transitive_zfc_model_def by auto

  show ?thesis
    unfolding zfc_invariant_def
    using M_CH_model M_CH_truth M_not_CH_model M_not_CH_falsity
    by blast
qed

subsection \<open>Uniform truth and disagreement\<close>

text \<open>A sentence with uniform truth across the models can be combined
with any sentence on which the models disagree. The result is invariant
exactly when the uniform truth value holds.\<close>

lemma uniform_or_invariant_iff:
  assumes stable: "\<phi> \<in> formula" and stable_closed: "arity(\<phi>) = 0"
    and sentence: "\<sigma> \<in> formula" and closed: "arity(\<sigma>) = 0"
    and noninvariant: "\<not> zfc_invariant(\<sigma>)"
    and uniform: "\<And>M. transitive_zfc_model(M) \<Longrightarrow> ((M, []
      \<Turnstile> \<phi>) \<longleftrightarrow> P)"
  shows "zfc_invariant(Or(\<phi>,\<sigma>)) \<longleftrightarrow> P"
proof -
  from noninvariant sentence closed have disagreement:
    "\<not> (\<forall>M N.
      transitive_zfc_model(M) \<longrightarrow>
      transitive_zfc_model(N) \<longrightarrow>
      ((M, [] \<Turnstile> \<sigma>) \<longleftrightarrow> (N, [] \<Turnstile>
        \<sigma>)))"
    unfolding zfc_invariant_def by blast
  show ?thesis unfolding zfc_invariant_def
    using stable stable_closed sentence closed uniform disagreement
    by (auto simp add: arity_Or)
qed

end
