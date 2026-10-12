(*  Title:      Turing_Invariance_Codes.thy
    Author:     Tang Ziyi
*)

section \<open>Invariance of Numbered Sentences\<close>

theory Turing_Invariance_Codes
  imports
    "Turing_Halting_Sentences"
    "Formula_Coding"
    "Sentence_Invariance"
    "Turing_Decidability"
begin

text \<open>The target set contains codes of closed sentences whose truth
agrees across all transitive ZFC set models. Injectivity of formula codes
identifies membership at the code of a given formula with its invariance.
The two sentence families below use CH as the disagreement witness.\<close>

subsection \<open>Target codes\<close>

definition invariant_formula_codes :: i where
  "invariant_formula_codes \<equiv>
    {n \<in> nat. \<exists>p \<in> formula.
      n = formula_code(p) \<and> zfc_invariant(p)}"

lemma invariant_formula_codes_subset_nat:
  "invariant_formula_codes \<subseteq> nat"
  unfolding invariant_formula_codes_def by blast

lemma invariant_formula_code_iff:
  assumes p: "p \<in> formula"
  shows "formula_code(p) \<in> invariant_formula_codes \<longleftrightarrow> zfc_invariant(p)"
proof
  assume "formula_code(p) \<in> invariant_formula_codes"
  then obtain q where q: "q \<in> formula"
    and same: "formula_code(p) = formula_code(q)"
    and inv: "zfc_invariant(q)"
    unfolding invariant_formula_codes_def by blast
  from formula_code_injective[OF p q same] inv show "zfc_invariant(p)" by simp
next
  assume inv: "zfc_invariant(p)"
  from p have code: "formula_code(p) \<in> nat" by (rule formula_code_type)
  from code p inv show "formula_code(p) \<in> invariant_formula_codes"
    unfolding invariant_formula_codes_def by blast
qed

subsection \<open>Halting sentence families\<close>

definition self_halting_or_CH :: "i \<Rightarrow> i" where
  "self_halting_or_CH(e) \<equiv>
    Or(halt_sentence(decode_machine(e),numeral_input(e)), \<cdot>CH\<cdot>)"

definition self_nonhalting_or_CH :: "i \<Rightarrow> i" where
  "self_nonhalting_or_CH(e) \<equiv>
    Or(Neg(halt_sentence(decode_machine(e),numeral_input(e))),
      \<cdot>CH\<cdot>)"

lemma self_halting_or_CH_type [TC]:
  "e \<in> nat \<Longrightarrow> self_halting_or_CH(e) \<in> formula"
  unfolding self_halting_or_CH_def using decode_machine_type numeral_input_type
  by typecheck

lemma self_nonhalting_or_CH_type [TC]:
  "e \<in> nat \<Longrightarrow> self_nonhalting_or_CH(e) \<in> formula"
  unfolding self_nonhalting_or_CH_def using decode_machine_type
    numeral_input_type
  by typecheck

theorem self_halting_or_CH_invariant_iff_of_CH_not_invariant:
  assumes CH_noninv: "\<not> zfc_invariant(\<cdot>CH\<cdot>)" and e: "e \<in> nat"
  shows "zfc_invariant(self_halting_or_CH(e)) \<longleftrightarrow> e \<in> self_halting"
proof -
  have P: "decode_machine(e) \<in> machine" using e by (rule
    decode_machine_type)
  have x: "numeral_input(e) \<in> list(symbol)" using e by (rule
    numeral_input_type)
  have sentence: "halt_sentence(decode_machine(e),numeral_input(e)) \<in> formula"
    by (rule halt_sentence_type[OF P x])
  have closed: "arity(halt_sentence(decode_machine(e),numeral_input(e))) = 0"
    by (rule arity_halt_sentence[OF P x])
  have CH_type: "\<cdot>CH\<cdot> \<in> formula" by typecheck
  have CH_closed: "arity(\<cdot>CH\<cdot>) = 0"
    by (simp add: Not_CH.arity_is_ContHyp_fm)
  have "zfc_invariant(self_halting_or_CH(e)) \<longleftrightarrow>
      halts_on(decode_machine(e),numeral_input(e))"
    unfolding self_halting_or_CH_def
    by (rule uniform_or_invariant_iff[OF sentence closed CH_type CH_closed
      CH_noninv])
      (rule sats_halt_sentence_iff[OF transitive_zfc_model_imp_zf P x])
  with e show ?thesis unfolding self_halting_def by blast
qed

theorem self_nonhalting_or_CH_invariant_iff_of_CH_not_invariant:
  assumes CH_noninv: "\<not> zfc_invariant(\<cdot>CH\<cdot>)" and e: "e \<in> nat"
  shows "zfc_invariant(self_nonhalting_or_CH(e)) \<longleftrightarrow> e \<notin> self_halting"
proof -
  have P: "decode_machine(e) \<in> machine" using e by (rule
    decode_machine_type)
  have x: "numeral_input(e) \<in> list(symbol)" using e by (rule
    numeral_input_type)
  have sentence: "halt_sentence(decode_machine(e),numeral_input(e)) \<in> formula"
    by (rule halt_sentence_type[OF P x])
  have closed: "arity(halt_sentence(decode_machine(e),numeral_input(e))) = 0"
    by (rule arity_halt_sentence[OF P x])
  have CH_type: "\<cdot>CH\<cdot> \<in> formula" by typecheck
  have CH_closed: "arity(\<cdot>CH\<cdot>) = 0"
    by (simp add: Not_CH.arity_is_ContHyp_fm)
  have inv:
    "zfc_invariant(self_nonhalting_or_CH(e)) \<longleftrightarrow>
      \<not> halts_on(decode_machine(e),numeral_input(e))"
    unfolding self_nonhalting_or_CH_def
  proof (rule uniform_or_invariant_iff[OF _ _ CH_type CH_closed CH_noninv])
    from sentence show "Neg(halt_sentence(decode_machine(e),numeral_input(e)))
      \<in> formula"
      by typecheck
    from closed show
      "arity(Neg(halt_sentence(decode_machine(e),numeral_input(e)))) = 0"
      by simp
    fix A assume model: "transitive_zfc_model(A)"
    from sats_halt_sentence_iff[OF transitive_zfc_model_imp_zf[OF model] P x] show
      "(A, [] \<Turnstile> Neg(halt_sentence(decode_machine(e),numeral_input(e)))) \<longleftrightarrow>
        \<not> halts_on(decode_machine(e),numeral_input(e))"
      by simp
  qed
  from e inv show ?thesis unfolding self_halting_def by blast
qed


subsection \<open>Numerical images\<close>

definition self_halting_positive_code :: "i \<Rightarrow> i" where
  "self_halting_positive_code(e) \<equiv> formula_code(self_halting_or_CH(e))"

definition self_halting_negative_code :: "i \<Rightarrow> i" where
  "self_halting_negative_code(e) \<equiv>
    formula_code(self_nonhalting_or_CH(e))"

theorem positive_code_reduces_self_halting_of_CH_not_invariant:
  assumes CH_noninv: "\<not> zfc_invariant(\<cdot>CH\<cdot>)" and e: "e \<in> nat"
  shows "e \<in> self_halting \<longleftrightarrow>
    self_halting_positive_code(e) \<in> invariant_formula_codes"
  using self_halting_or_CH_invariant_iff_of_CH_not_invariant[OF CH_noninv e]
    invariant_formula_code_iff[OF self_halting_or_CH_type[OF e]]
  unfolding self_halting_positive_code_def by blast

theorem negative_code_reduces_nonhalting_of_CH_not_invariant:
  assumes CH_noninv: "\<not> zfc_invariant(\<cdot>CH\<cdot>)" and e: "e \<in> nat"
  shows "e \<notin> self_halting \<longleftrightarrow>
    self_halting_negative_code(e) \<in> invariant_formula_codes"
  using self_nonhalting_or_CH_invariant_iff_of_CH_not_invariant[OF CH_noninv e]
    invariant_formula_code_iff[OF self_nonhalting_or_CH_type[OF e]]
  unfolding self_halting_negative_code_def by blast


end
