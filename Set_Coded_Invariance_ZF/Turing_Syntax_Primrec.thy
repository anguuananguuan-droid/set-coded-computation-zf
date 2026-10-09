(*  Title:      Turing_Syntax_Primrec.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Formula Constructors\<close>

theory Turing_Syntax_Primrec
  imports Turing_Formula_Coding "Set_Coded_Computation_ZF.Turing_Primrec"
begin

definition pr_formula_binary :: "i \<Rightarrow> i" where
  "pr_formula_binary(k) \<equiv>
    COMP(pr_pair_code,
      [CONSTANT(k),COMP(pr_pair_code,[PROJ(0),PROJ(1)])])"

lemma pr_formula_binary_in_prim_rec [TC]:
  "k \<in> nat \<Longrightarrow> pr_formula_binary(k) \<in> prim_rec"
  unfolding pr_formula_binary_def by typecheck

lemma pr_formula_binary_apply:
  assumes k: "k \<in> nat" and x: "x \<in> nat" and y: "y \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_formula_binary(k)`Cons(x,Cons(y,l)) =
    pair_code(k,pair_code(x,y))"
proof -
  from x y have inner: "pair_code(x,y) \<in> nat" by (rule pair_code_type)
  from k x y tail inner show ?thesis
    unfolding pr_formula_binary_def
    by (simp add: COMP_2 CONSTANT PROJ_0 PROJ_1 pr_pair_code_apply)
qed

definition pr_formula_unary :: "i \<Rightarrow> i" where
  "pr_formula_unary(k) \<equiv>
    COMP(pr_pair_code,[CONSTANT(k),PROJ(0)])"

lemma pr_formula_unary_in_prim_rec [TC]:
  "k \<in> nat \<Longrightarrow> pr_formula_unary(k) \<in> prim_rec"
  unfolding pr_formula_unary_def by typecheck

lemma pr_formula_unary_apply:
  assumes k: "k \<in> nat" and x: "x \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_formula_unary(k)`Cons(x,l) = pair_code(k,x)"
  using k x tail unfolding pr_formula_unary_def
  by (simp add: COMP_2 CONSTANT PROJ_0 pr_pair_code_apply)

definition pr_formula_neg :: i where
  "pr_formula_neg \<equiv>
    COMP(pr_formula_binary(2),[PROJ(0),PROJ(0)])"

lemma pr_formula_neg_in_prim_rec [TC]:
  "pr_formula_neg \<in> prim_rec"
  unfolding pr_formula_neg_def by typecheck

lemma pr_formula_neg_raw_apply:
  assumes c: "c \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_formula_neg`Cons(c,l) = pair_code(2,pair_code(c,c))"
  using c tail unfolding pr_formula_neg_def
  by (simp add: COMP_2 PROJ_0 pr_formula_binary_apply)

lemma pr_formula_neg_apply:
  assumes p: "p \<in> formula" and tail: "l \<in> list(nat)"
  shows "pr_formula_neg`Cons(formula_code(p),l) = formula_code(Neg(p))"
  using p tail unfolding Neg_def
  by (simp add: pr_formula_neg_raw_apply formula_code_type)

definition pr_formula_and :: i where
  "pr_formula_and \<equiv>
    COMP(pr_formula_neg,
      [COMP(pr_formula_binary(2),[PROJ(0),PROJ(1)])])"

lemma pr_formula_and_in_prim_rec [TC]:
  "pr_formula_and \<in> prim_rec"
  unfolding pr_formula_and_def by typecheck

lemma pr_formula_and_apply:
  assumes p: "p \<in> formula" and q: "q \<in> formula"
    and tail: "l \<in> list(nat)"
  shows "pr_formula_and`Cons(formula_code(p),Cons(formula_code(q),l)) =
    formula_code(And(p,q))"
proof -
  from p q have pq: "Nand(p,q) \<in> formula" by typecheck
  from p q tail pq show ?thesis unfolding pr_formula_and_def And_def Neg_def
    by (simp add: COMP_2 COMP_1 PROJ_0 PROJ_1
        pr_formula_binary_apply pr_formula_neg_raw_apply formula_code_type)
qed

definition pr_formula_or :: i where
  "pr_formula_or \<equiv>
    COMP(pr_formula_binary(2),
      [COMP(pr_formula_neg,[PROJ(0)]),
       COMP(pr_formula_neg,[PROJ(1)])])"

lemma pr_formula_or_in_prim_rec [TC]:
  "pr_formula_or \<in> prim_rec"
  unfolding pr_formula_or_def by typecheck

lemma pr_formula_or_apply:
  assumes p: "p \<in> formula" and q: "q \<in> formula"
    and tail: "l \<in> list(nat)"
  shows "pr_formula_or`Cons(formula_code(p),Cons(formula_code(q),l)) =
    formula_code(Or(p,q))"
  using p q tail unfolding pr_formula_or_def Or_def Neg_def
  by (simp add: COMP_2 COMP_1 PROJ_0 PROJ_1
      pr_formula_neg_apply pr_formula_binary_apply formula_code_type Neg_def)

definition pr_formula_exists :: i where
  "pr_formula_exists \<equiv>
    COMP(pr_formula_neg,
      [COMP(pr_formula_unary(succ(2)),
        [COMP(pr_formula_neg,[PROJ(0)])])])"

lemma pr_formula_exists_in_prim_rec [TC]:
  "pr_formula_exists \<in> prim_rec"
  unfolding pr_formula_exists_def by typecheck

lemma pr_formula_exists_apply:
  assumes p: "p \<in> formula" and tail: "l \<in> list(nat)"
  shows "pr_formula_exists`Cons(formula_code(p),l) =
    formula_code(Exists(p))"
proof -
  from p have neg: "Neg(p) \<in> formula" by typecheck
  from neg have forall: "Forall(Neg(p)) \<in> formula" by typecheck
  from p tail neg forall show ?thesis
    unfolding pr_formula_exists_def Exists_def Neg_def
    by (simp add: COMP_1 PROJ_0 pr_formula_neg_apply
        pr_formula_neg_raw_apply pr_formula_unary_apply formula_code_type)
qed

end
