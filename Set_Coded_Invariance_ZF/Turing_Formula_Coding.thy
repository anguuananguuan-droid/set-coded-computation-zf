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
  shows "pair_code(a,b) = pair_code(c,d) \<longleftrightarrow> a = c \<and> b = d"
  using pair_code_inject[OF assms] by auto

lemma formula_code_member_inj:
  assumes x: "x \<in> nat" and y: "y \<in> nat"
    and q: "q \<in> formula"
    and same: "formula_code(Member(x,y)) = formula_code(q)"
  shows "Member(x,y) = q"
proof -
  from q show ?thesis
  proof (cases rule: formula.cases)
    case (Member a b)
    with x y same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type)
  next
    case (Equal a b)
    with x y same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type)
  next
    case (Nand p r)
    with x y same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  next
    case (Forall p)
    with x y same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  qed
qed

lemma formula_code_equal_inj:
  assumes x: "x \<in> nat" and y: "y \<in> nat"
    and q: "q \<in> formula"
    and same: "formula_code(Equal(x,y)) = formula_code(q)"
  shows "Equal(x,y) = q"
proof -
  from q show ?thesis
  proof (cases rule: formula.cases)
    case (Member a b)
    with x y same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type)
  next
    case (Equal a b)
    with x y same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type)
  next
    case (Nand p r)
    with x y same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  next
    case (Forall p)
    with x y same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  qed
qed

lemma formula_code_nand_inj:
  assumes p: "p \<in> formula" and r: "r \<in> formula"
    and ih_p: "\<And>s. s \<in> formula \<Longrightarrow> formula_code(p) = formula_code(s) \<Longrightarrow> p = s"
    and ih_r: "\<And>s. s \<in> formula \<Longrightarrow> formula_code(r) = formula_code(s) \<Longrightarrow> r = s"
    and q: "q \<in> formula"
    and same: "formula_code(Nand(p,r)) = formula_code(q)"
  shows "Nand(p,r) = q"
proof -
  from q show ?thesis
  proof (cases rule: formula.cases)
    case (Member a b)
    with p r same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  next
    case (Equal a b)
    with p r same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  next
    case (Nand a b)
    from p r Nand same have codes:
      "formula_code(p) = formula_code(a) \<and>
       formula_code(r) = formula_code(b)"
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
    from ih_p codes Nand have "p = a" by blast
    moreover from ih_r codes Nand have "r = b" by blast
    ultimately show ?thesis using Nand by simp
  next
    case (Forall a)
    with p r same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  qed
qed

lemma formula_code_forall_inj:
  assumes p: "p \<in> formula"
    and ih: "\<And>s. s \<in> formula \<Longrightarrow> formula_code(p) = formula_code(s) \<Longrightarrow> p = s"
    and q: "q \<in> formula"
    and same: "formula_code(Forall(p)) = formula_code(q)"
  shows "Forall(p) = q"
proof -
  from q show ?thesis
  proof (cases rule: formula.cases)
    case (Member a b)
    with p same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  next
    case (Equal a b)
    with p same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  next
    case (Nand a b)
    with p same show ?thesis
      by (simp add: pair_code_eq_iff pair_code_type formula_code_type)
  next
    case (Forall a)
    from p Forall same have code: "formula_code(p) = formula_code(a)"
      by (simp add: pair_code_eq_iff formula_code_type)
    from ih code Forall have "p = a" by blast
    then show ?thesis using Forall by simp
  qed
qed

lemma formula_code_injective:
  assumes p: "p \<in> formula" and q: "q \<in> formula"
    and same: "formula_code(p) = formula_code(q)"
  shows "p = q"
  using p q same
proof (induct p arbitrary: q rule: formula.induct)
  case (Member x y)
  then show ?case by (rule formula_code_member_inj)
next
  case (Equal x y)
  then show ?case by (rule formula_code_equal_inj)
next
  case (Nand p r)
  then show ?case by (blast intro: formula_code_nand_inj)
next
  case (Forall p)
  then show ?case by (blast intro: formula_code_forall_inj)
qed

end
