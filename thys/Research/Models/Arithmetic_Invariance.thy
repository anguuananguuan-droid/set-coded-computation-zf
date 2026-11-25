(*  Title:      Arithmetic_Invariance.thy
    Author:     Tang Ziyi
*)

section \<open>Arithmetic Truth and Invariance\<close>

theory Arithmetic_Invariance
  imports Arithmetic_Translation "Turing_Invariance.Sentence_Invariance"
begin

subsection \<open>The semantic reduction\<close>

text \<open>Combining a translated arithmetic sentence with a fixed
disagreement sentence gives the sentence-level equivalence used in the
arithmetic-truth reduction. This statement precedes the choice of an
arithmetic coding and does not assert effectiveness on codes.\<close>

theorem arith_or_invariant_iff:
  assumes p: "arith_sentence(p)"
    and q: "q \<in> formula" "arity(q) = 0"
    and disagreement: "\<not> zfc_invariant(q)"
  shows "zfc_invariant(Or(arith_translate(p),q)) \<longleftrightarrow>
    [] \<in> arith_true_envs(p)"
proof (rule uniform_or_invariant_iff
    [OF arith_translate_sentence(1)[OF p] arith_translate_sentence(2)[OF p]
      q disagreement])
  fix A
  assume "transitive_zfc_model(A)"
  then have "transitive_zf_model(A)" by (rule transitive_zfc_model_imp_zf)
  then show "(A, [] \<Turnstile> arith_translate(p)) \<longleftrightarrow>
      [] \<in> arith_true_envs(p)"
    by (rule sats_arith_sentence_iff[OF _ p])
qed

end
