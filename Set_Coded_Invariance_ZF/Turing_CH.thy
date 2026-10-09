(*  Title:      Turing_CH.thy
    Author:     Tang Ziyi
*)

section \<open>Halting and ZFC-Invariance\<close>

theory Turing_CH
  imports
    "Set_Coded_Computation_ZF.Turing_Coding"
    "Independence_CH.Definitions_Main"
begin

definition transitive_zfc_model :: "i \<Rightarrow> o" where
  "transitive_zfc_model(M) \<equiv> Transset(M) \<and> M \<Turnstile> ZFC"

definition zfc_invariant :: "i \<Rightarrow> o" where
  "zfc_invariant(\<phi>) \<equiv>
    \<phi> \<in> formula \<and>
    arity(\<phi>) = 0 \<and>
    (\<forall>M N.
      transitive_zfc_model(M) \<longrightarrow>
      transitive_zfc_model(N) \<longrightarrow>
      ((M, [] \<Turnstile> \<phi>) \<longleftrightarrow> (N, [] \<Turnstile> \<phi>)))"

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
    and "M_not_CH \<Turnstile> ZFC \<union> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>}"
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

text \<open>A sentence with uniform truth across the models can be combined
with any sentence on which the models disagree. The result is invariant
exactly when the uniform truth value holds.\<close>

lemma uniform_or_invariant_iff:
  assumes stable: "\<phi> \<in> formula" and stable_closed: "arity(\<phi>) = 0"
    and sentence: "\<sigma> \<in> formula" and closed: "arity(\<sigma>) = 0"
    and noninvariant: "\<not> zfc_invariant(\<sigma>)"
    and uniform: "\<And>M. transitive_zfc_model(M) \<Longrightarrow> ((M, [] \<Turnstile> \<phi>) \<longleftrightarrow> P)"
  shows "zfc_invariant(Or(\<phi>,\<sigma>)) \<longleftrightarrow> P"
proof -
  from noninvariant sentence closed have disagreement:
    "\<not> (\<forall>M N.
      transitive_zfc_model(M) \<longrightarrow>
      transitive_zfc_model(N) \<longrightarrow>
      ((M, [] \<Turnstile> \<sigma>) \<longleftrightarrow> (N, [] \<Turnstile> \<sigma>)))"
    unfolding zfc_invariant_def by blast
  show ?thesis unfolding zfc_invariant_def
    using stable stable_closed sentence closed uniform disagreement
    by (auto simp add: arity_Or)
qed

locale halting_sentence =
  fixes halt_fm :: "i \<Rightarrow> i"
  assumes halt_fm_type [TC]:
    "e \<in> nat \<Longrightarrow> halt_fm(e) \<in> formula"
    and halt_fm_closed:
    "e \<in> nat \<Longrightarrow> arity(halt_fm(e)) = 0"
    and sats_halt_fm_iff:
    "\<lbrakk>e \<in> nat; transitive_zfc_model(M)\<rbrakk> \<Longrightarrow>
      ((M, [] \<Turnstile> halt_fm(e)) \<longleftrightarrow>
        halts_blank(decode_machine(e)))"
begin

lemma halting_or_invariant_iff_halts_blank:
  assumes code: "e \<in> nat"
    and sentence: "\<sigma> \<in> formula"
    and closed: "arity(\<sigma>) = 0"
    and noninvariant: "\<not> zfc_invariant(\<sigma>)"
  shows "zfc_invariant(Or(halt_fm(e), \<sigma>)) \<longleftrightarrow>
    halts_blank(decode_machine(e))"
  by (rule uniform_or_invariant_iff[OF halt_fm_type[OF code]
      halt_fm_closed[OF code] sentence closed noninvariant])
    (rule sats_halt_fm_iff[OF code])

lemma nonhalting_or_invariant_iff_not_halts_blank:
  assumes code: "e \<in> nat"
    and sentence: "\<sigma> \<in> formula"
    and closed: "arity(\<sigma>) = 0"
    and noninvariant: "\<not> zfc_invariant(\<sigma>)"
  shows "zfc_invariant(Or(Neg(halt_fm(e)),\<sigma>)) \<longleftrightarrow>
    \<not> halts_blank(decode_machine(e))"
proof (rule uniform_or_invariant_iff[OF _ _ sentence closed noninvariant])
  show "Neg(halt_fm(e)) \<in> formula" using code by typecheck
  show "arity(Neg(halt_fm(e))) = 0" using halt_fm_closed[OF code] by simp
  fix M assume model: "transitive_zfc_model(M)"
  show "(M, [] \<Turnstile> Neg(halt_fm(e))) \<longleftrightarrow> \<not> halts_blank(decode_machine(e))"
    using sats_halt_fm_iff[OF code model] by simp
qed

definition halting_or_CH_fm :: "i \<Rightarrow> i" where
  "halting_or_CH_fm(e) \<equiv> Or(halt_fm(e), \<cdot>CH\<cdot>)"

lemma halting_or_CH_fm_type [TC]:
  "e \<in> nat \<Longrightarrow> halting_or_CH_fm(e) \<in> formula"
  unfolding halting_or_CH_fm_def by typecheck

lemma halting_or_CH_fm_closed:
  "e \<in> nat \<Longrightarrow> arity(halting_or_CH_fm(e)) = 0"
  unfolding halting_or_CH_fm_def
  by (simp add: arity_Or halt_fm_closed Not_CH.arity_is_ContHyp_fm)

lemma sats_halting_or_CH_fm_iff [simp]:
  "(M, [] \<Turnstile> halting_or_CH_fm(e)) \<longleftrightarrow>
    ((M, [] \<Turnstile> halt_fm(e)) \<or> (M, [] \<Turnstile> \<cdot>CH\<cdot>))"
  unfolding halting_or_CH_fm_def by simp

theorem halting_or_CH_invariant_iff_halts_blank:
  assumes countable: "M \<approx> \<omega>"
    and transitive: "Transset(M)"
    and zfc: "M \<Turnstile> ZFC"
    and code: "e \<in> nat"
  shows "zfc_invariant(halting_or_CH_fm(e)) \<longleftrightarrow>
    halts_blank(decode_machine(e))"
  unfolding halting_or_CH_fm_def
  by (rule halting_or_invariant_iff_halts_blank[OF code])
    (typecheck, simp add: Not_CH.arity_is_ContHyp_fm,
      rule CH_not_invariant[OF countable transitive zfc])

end

end
