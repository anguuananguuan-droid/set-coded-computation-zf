(*  Title:      Turing_Formula_Coding.thy
    Author:     Tang Ziyi
*)

section \<open>Numerical Coding of Formulas\<close>

theory Turing_Formula_Coding
  imports
    "Set_Coded_Computation_ZF.Turing_Coding"
    "ZF-Constructible.Formula"
begin

text \<open>The four primitive constructors of formulas receive distinct
tags. Pairing supplies a natural-number code at each recursive step.\<close>

subsection \<open>Constructor codes\<close>

consts formula_code :: "i \<Rightarrow> i"

primrec
  "formula_code(Member(x,y)) = pair_code(0,pair_code(x,y))"
  "formula_code(Equal(x,y)) = pair_code(1,pair_code(x,y))"
  "formula_code(Nand(p,q)) =
    pair_code(2,pair_code(formula_code(p),formula_code(q)))"
  "formula_code(Forall(p)) = pair_code(succ(2),formula_code(p))"

lemma formula_code_type [TC]:
  "p \<in> formula \<Longrightarrow> formula_code(p) \<in> nat"
  by (induct set: formula) (auto intro: pair_code_type)

subsection \<open>Injectivity\<close>

lemma pair_code_inject:
  assumes a: "a \<in> nat" and b: "b \<in> nat"
    and c: "c \<in> nat" and d: "d \<in> nat"
    and same: "pair_code(a,b) = pair_code(c,d)"
  shows "a = c \<and> b = d"
proof -
  from same have decoded:
    "pair_decode(pair_code(a,b)) = pair_decode(pair_code(c,d))"
    by (simp only: same)
  from decoded have pairs: "\<langle>a,b\<rangle> = \<langle>c,d\<rangle>"
    by (simp only: pair_decode_code[OF a b] pair_decode_code[OF c d])
  from pairs show ?thesis by auto
qed

lemma pair_code_eq_iff:
  assumes "a \<in> nat" "b \<in> nat" "c \<in> nat" "d \<in> nat"
  shows "pair_code(a,b) = pair_code(c,d) \<longleftrightarrow> a = c \<and> b =
    d"
  using pair_code_inject[OF assms] by auto

lemma formula_code_injective:
  assumes "p \<in> formula" "q \<in> formula"
    "formula_code(p) = formula_code(q)"
  shows "p = q"
  using assms
proof (induct p arbitrary: q rule: formula.induct)
  case (Member x y)
  from Member.prems(1) show ?case
    by cases (use Member in \<open>simp_all add:
        pair_code_eq_iff pair_code_type formula_code_type\<close>)
next
  case (Equal x y)
  from Equal.prems(1) show ?case
    by cases (use Equal in \<open>simp_all add:
        pair_code_eq_iff pair_code_type formula_code_type\<close>)
next
  case (Nand p r)
  from Nand.prems(1) Nand.prems(2) Nand.hyps(1,3) show ?case
    by cases (auto simp add: pair_code_eq_iff pair_code_type
        formula_code_type intro: Nand.hyps(2,4))
next
  case (Forall p)
  from Forall.prems(1) Forall.prems(2) Forall.hyps(1) show ?case
    by cases (auto simp add: pair_code_eq_iff pair_code_type
        formula_code_type intro: Forall.hyps(2))
qed

end
