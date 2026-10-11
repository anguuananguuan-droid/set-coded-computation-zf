(*  Title:      Turing_Instruction_Normalization.thy
    Author:     Tang Ziyi
*)

section \<open>Instruction Code Normalization\<close>

theory Turing_Instruction_Normalization
  imports Turing_Primrec
begin

text \<open>Invalid action codes denote the no-op instruction entering the
final state. Normalization and its primitive-recursive certificate depend
only on coding operations.\<close>

lemma action_iff_le_nop:
  assumes natural: "a \<in> nat"
  shows "a \<in> action \<longleftrightarrow> a \<le> nop"
  using natural nat_into_Ord[OF natural]
  unfolding action_def
  by (simp add: Ord_mem_iff_lt)

definition pr_valid_action :: i where
  "pr_valid_action \<equiv>
    COMP(pr_le,[PROJ(0),CONSTANT(nop)])"

lemma pr_valid_action_in_prim_rec [TC]:
  "pr_valid_action \<in> prim_rec"
  unfolding pr_valid_action_def by typecheck

lemma pr_valid_action_apply:
  assumes action_code: "a \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_valid_action`Cons(a,l) =
    (if a \<in> action then 1 else 0)"
  unfolding pr_valid_action_def
  using action_code tail action_iff_le_nop[OF action_code]
  by (simp add: COMP_2 CONSTANT PROJ_0 pr_le_apply)

definition pr_valid_instruction_code :: i where
  "pr_valid_instruction_code \<equiv>
    COMP(pr_valid_action,[pr_pair_left])"

lemma pr_valid_instruction_code_in_prim_rec [TC]:
  "pr_valid_instruction_code \<in> prim_rec"
  unfolding pr_valid_instruction_code_def by typecheck

lemma pr_valid_instruction_code_apply:
  assumes instruction_number: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_valid_instruction_code`Cons(n,l) =
    (if pair_left_code(n) \<in> action then 1 else 0)"
proof -
  from instruction_number have action_code: "pair_left_code(n) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_valid_instruction_code_def
    using instruction_number tail action_code
    by (simp add: COMP_1 pr_pair_left_code_apply pr_valid_action_apply)
qed

definition pr_normalize_instruction_code :: i where
  "pr_normalize_instruction_code \<equiv>
    COMP(pr_if_zero,
      [pr_valid_instruction_code,
       CONSTANT(default_instruction_code),
       PROJ(0)])"

lemma pr_normalize_instruction_code_in_prim_rec [TC]:
  "pr_normalize_instruction_code \<in> prim_rec"
  unfolding pr_normalize_instruction_code_def by typecheck

lemma pr_normalize_instruction_code_apply:
  assumes instruction_number: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_normalize_instruction_code`Cons(n,l) =
    normalize_instruction_code(n)"
  unfolding pr_normalize_instruction_code_def
    normalize_instruction_code_def
  using instruction_number tail default_instruction_code_type
  by (simp add: COMP_3 CONSTANT PROJ_0 pr_if_zero_apply
      pr_valid_instruction_code_apply)

end
