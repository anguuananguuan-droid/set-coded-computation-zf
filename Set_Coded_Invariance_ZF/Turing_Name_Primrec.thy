(*  Title:      Turing_Name_Primrec.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Names for Numerals\<close>

theory Turing_Name_Primrec
  imports Turing_Syntax_Primrec Turing_Halting_Sentences
begin

definition pr_nat_name_step :: i where
  "pr_nat_name_step \<equiv>
    COMP(pr_formula_exists,
      [COMP(pr_formula_and,
        [PROJ(0),CONSTANT(formula_code(succ_fm(0,1)))])])"

lemma pr_nat_name_step_in_prim_rec [TC]:
  "pr_nat_name_step \<in> prim_rec"
  unfolding pr_nat_name_step_def
  by (typecheck add: formula_code_type)

lemma pr_nat_name_step_apply:
  assumes k: "k \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_nat_name_step`Cons(formula_code(nat_name_fm(k)),l) =
    formula_code(nat_name_fm(succ(k)))"
proof -
  from k have name: "nat_name_fm(k) \<in> formula" by (rule nat_name_fm_type)
  have successor: "succ_fm(0,1) \<in> formula" by typecheck
  from name successor have conjunction:
    "And(nat_name_fm(k),succ_fm(0,1)) \<in> formula" by typecheck
  from k tail name successor conjunction show ?thesis
    unfolding pr_nat_name_step_def
    by (simp add: COMP_1 COMP_2 PROJ_0 CONSTANT
        pr_formula_and_apply pr_formula_exists_apply formula_code_type)
qed

definition pr_nat_name_code :: i where
  "pr_nat_name_code \<equiv>
    PREC(CONSTANT(formula_code(empty_fm(0))),pr_nat_name_step)"

lemma pr_nat_name_code_in_prim_rec [TC]:
  "pr_nat_name_code \<in> prim_rec"
  unfolding pr_nat_name_code_def
  by (typecheck add: formula_code_type)

theorem pr_nat_name_code_apply:
  assumes n: "n \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_nat_name_code`Cons(n,l) = formula_code(nat_name_fm(n))"
  using n
proof (induct n rule: nat_induct)
  case 0
  with tail show ?case
    unfolding pr_nat_name_code_def
    by (simp add: PREC_0 CONSTANT)
next
  case (succ n)
  from succ.hyps(1) have name: "nat_name_fm(n) \<in> formula"
    by (rule nat_name_fm_type)
  from name have code: "formula_code(nat_name_fm(n)) \<in> nat"
    by (rule formula_code_type)
  from succ tail code show ?case
    unfolding pr_nat_name_code_def
    by (simp add: PREC_succ pr_nat_name_step_apply)
qed

definition pr_list_name_cons :: i where
  "pr_list_name_cons \<equiv>
    COMP(pr_formula_exists,
      [COMP(pr_formula_and,
        [PROJ(0),
         COMP(pr_formula_exists,
           [COMP(pr_formula_and,
             [PROJ(1),CONSTANT(formula_code(Cons_fm(1,0,2)))])])])])"

lemma pr_list_name_cons_in_prim_rec [TC]:
  "pr_list_name_cons \<in> prim_rec"
  unfolding pr_list_name_cons_def
  by (typecheck add: formula_code_type)

lemma pr_list_name_cons_apply:
  assumes p: "p \<in> formula" and q: "q \<in> formula"
    and tail: "l \<in> list(nat)"
  shows "pr_list_name_cons`Cons(formula_code(p),Cons(formula_code(q),l)) =
    formula_code(Exists(And(p,Exists(And(q,Cons_fm(1,0,2))))))"
proof -
  have cons: "Cons_fm(1,0,2) \<in> formula" by typecheck
  from q cons have inner: "And(q,Cons_fm(1,0,2)) \<in> formula" by typecheck
  from inner have exists: "Exists(And(q,Cons_fm(1,0,2))) \<in> formula" by typecheck
  from p exists have outer: "And(p,Exists(And(q,Cons_fm(1,0,2)))) \<in> formula"
    by typecheck
  from p q tail cons inner exists outer show ?thesis
    unfolding pr_list_name_cons_def
    by (simp add: COMP_1 COMP_2 PROJ_0 PROJ_1 CONSTANT
        pr_formula_and_apply pr_formula_exists_apply formula_code_type)
qed

definition pr_input_name_step :: i where
  "pr_input_name_step \<equiv>
    COMP(pr_list_name_cons,
      [CONSTANT(formula_code(nat_name_fm(one_symbol))),PROJ(0)])"

lemma pr_input_name_step_in_prim_rec [TC]:
  "pr_input_name_step \<in> prim_rec"
  unfolding pr_input_name_step_def
  by (typecheck add: formula_code_type)

lemma pr_input_name_step_apply:
  assumes n: "n \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_input_name_step`Cons(
      formula_code(list_name_fm(nat_name_fm,numeral_input(n))),l) =
    formula_code(list_name_fm(nat_name_fm,numeral_input(succ(n))))"
proof -
  have one: "one_symbol \<in> symbol" by simp
  from one have item: "nat_name_fm(one_symbol) \<in> formula"
    by (rule nat_name_sym_type)
  from n have input: "numeral_input(n) \<in> list(symbol)"
    by (rule numeral_input_type)
  from input have named:
    "list_name_fm(nat_name_fm,numeral_input(n)) \<in> formula"
    by (rule list_name_fm_type) (rule nat_name_sym_type)
  from n tail item named show ?thesis
    unfolding pr_input_name_step_def numeral_input_def
    by (simp add: COMP_2 CONSTANT PROJ_0
        pr_list_name_cons_apply formula_code_type)
qed

definition pr_input_name_code :: i where
  "pr_input_name_code \<equiv>
    PREC(CONSTANT(formula_code(Nil_fm(0))),pr_input_name_step)"

lemma pr_input_name_code_in_prim_rec [TC]:
  "pr_input_name_code \<in> prim_rec"
  unfolding pr_input_name_code_def
  by (typecheck add: formula_code_type)

theorem pr_input_name_code_apply:
  assumes n: "n \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_input_name_code`Cons(n,l) =
    formula_code(list_name_fm(nat_name_fm,numeral_input(n)))"
  using n
proof (induct n rule: nat_induct)
  case 0
  with tail show ?case
    unfolding pr_input_name_code_def numeral_input_def
    by (simp add: PREC_0 CONSTANT)
next
  case (succ n)
  from succ.hyps(1) have input: "numeral_input(n) \<in> list(symbol)"
    by (rule numeral_input_type)
  from input have named:
    "list_name_fm(nat_name_fm,numeral_input(n)) \<in> formula"
    by (rule list_name_fm_type) (rule nat_name_sym_type)
  from named have code:
    "formula_code(list_name_fm(nat_name_fm,numeral_input(n))) \<in> nat"
    by (rule formula_code_type)
  from succ tail code show ?case
    unfolding pr_input_name_code_def
    by (simp add: PREC_succ pr_input_name_step_apply)
qed

end
