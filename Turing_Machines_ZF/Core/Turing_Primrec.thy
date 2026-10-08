(*  Title:      Turing_Primrec.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Coding\<close>

theory Turing_Primrec
  imports
    Turing_Code_Operations
    "ZF-Induct.Primrec"
begin

text \<open>This theory constructs primitive-recursive numerical operations
for pairing and finite-list codes. Each certificate consists of a member of
prim_rec and an application theorem identifying its value with the
corresponding code operation. These results do not construct a Turing
machine that implements the operations.\<close>

subsection \<open>Composition and Projection\<close>

lemma COMP_2:
  assumes inputs: "l \<in> list(nat)"
  shows "COMP(g,[f,h])`l = g`[f`l,h`l]"
  using inputs unfolding COMP_def by simp

lemma COMP_3:
  assumes inputs: "l \<in> list(nat)"
  shows "COMP(g,[f,h,k])`l = g`[f`l,h`l,k`l]"
  using inputs unfolding COMP_def by simp

lemma PROJ_1 [simp]:
  assumes first: "x \<in> nat"
    and second: "y \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "PROJ(1)`Cons(x,Cons(y,l)) = y"
  using first second tail unfolding PROJ_def by simp

lemma PROJ_2 [simp]:
  assumes first: "x \<in> nat"
    and second: "y \<in> nat"
    and third: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "PROJ(2)`Cons(x,Cons(y,Cons(z,l))) = z"
  using first second third tail unfolding PROJ_def by simp

lemma PROJ_3 [simp]:
  assumes first: "x \<in> nat"
    and second: "y \<in> nat"
    and third: "z \<in> nat"
    and fourth: "w \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "PROJ(succ(2))`Cons(x,Cons(y,Cons(z,Cons(w,l)))) = w"
  using first second third fourth tail unfolding PROJ_def by simp

subsection \<open>Arithmetic\<close>

definition pr_pred :: i where
  "pr_pred \<equiv> PREC(CONSTANT(0),PROJ(1))"

lemma pr_pred_in_prim_rec [TC]:
  "pr_pred \<in> prim_rec"
  unfolding pr_pred_def by typecheck

lemma pr_pred_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_pred`Cons(n,l) = pred(n)"
  using natural
proof (induct n rule: nat_induct)
  case 0
  with tail show ?case
    unfolding pr_pred_def by (simp add: PREC_0 CONSTANT)
next
  case (succ n)
  with tail show ?case
    unfolding pr_pred_def by (simp add: PREC_succ)
qed

definition pr_add :: i where
  "pr_add \<equiv> PREC(PROJ(0),SC)"

lemma pr_add_in_prim_rec [TC]:
  "pr_add \<in> prim_rec"
  unfolding pr_add_def by typecheck

lemma pr_add_apply:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_add`Cons(m,Cons(n,l)) = m #+ n"
  using first
proof (induct m rule: nat_induct)
  case 0
  with second tail show ?case
    unfolding pr_add_def by (simp add: PREC_0 PROJ_0)
next
  case (succ m)
  with second tail show ?case
    unfolding pr_add_def by (simp add: PREC_succ SC)
qed

definition pr_double :: i where
  "pr_double \<equiv> COMP(pr_add,[PROJ(0),PROJ(0)])"

lemma pr_double_in_prim_rec [TC]:
  "pr_double \<in> prim_rec"
  unfolding pr_double_def by typecheck

lemma pr_double_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_double`Cons(n,l) = n #+ n"
  unfolding pr_double_def using natural tail
  by (simp add: COMP_2 PROJ_0 pr_add_apply)

definition pr_reverse_diff :: i where
  "pr_reverse_diff \<equiv>
    PREC(PROJ(0),COMP(pr_pred,[PROJ(0)]))"

lemma pr_reverse_diff_in_prim_rec [TC]:
  "pr_reverse_diff \<in> prim_rec"
  unfolding pr_reverse_diff_def by typecheck

lemma pr_reverse_diff_apply:
  assumes subtrahend: "n \<in> nat"
    and minuend: "m \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_reverse_diff`Cons(n,Cons(m,l)) = m #- n"
  using subtrahend
proof (induct n rule: nat_induct)
  case 0
  with minuend tail show ?case
    unfolding pr_reverse_diff_def
    by (simp add: PREC_0 PROJ_0)
next
  case (succ n)
  with minuend tail show ?case
    unfolding pr_reverse_diff_def
    by (simp add: PREC_succ COMP_1 PROJ_def pr_pred_apply
        diff_succ_eq_pred)
qed

definition pr_diff :: i where
  "pr_diff \<equiv>
    COMP(pr_reverse_diff,[PROJ(1),PROJ(0)])"

lemma pr_diff_in_prim_rec [TC]:
  "pr_diff \<in> prim_rec"
  unfolding pr_diff_def by typecheck

lemma pr_diff_apply:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_diff`Cons(m,Cons(n,l)) = m #- n"
  unfolding pr_diff_def
  using first second tail
  by (simp add: COMP_2 pr_reverse_diff_apply PROJ_0)

lemma succ_diff_succ:
  assumes index: "j \<in> nat"
    and total: "n \<in> nat"
    and bounded: "succ(j) \<le> n"
  shows "succ(n #- succ(j)) = n #- j"
proof -
  from bounded have less: "j < n"
    by (rule succ_leE)
  from total index have comparison:
    "\<not> n \<le> j \<longleftrightarrow> j < n"
    using not_le_iff_lt[OF nat_into_Ord nat_into_Ord] by simp
  from less comparison have not_le: "\<not> n \<le> j"
    by simp
  from index total not_le have nonzero: "n #- j \<noteq> 0"
    by (simp add: diff_is_0_lemma)
  have difference: "n #- j \<in> nat"
    by typecheck
  from difference show ?thesis
  proof (cases rule: natE)
    case 0
    with nonzero show ?thesis by contradiction
  next
    case (succ d)
    then show ?thesis by (simp add: diff_succ_eq_pred)
  qed
qed

subsection \<open>Conditionals\<close>

definition pr_is_zero :: i where
  "pr_is_zero \<equiv> PREC(CONSTANT(1),CONSTANT(0))"

lemma pr_is_zero_in_prim_rec [TC]:
  "pr_is_zero \<in> prim_rec"
  unfolding pr_is_zero_def by typecheck

lemma pr_is_zero_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_is_zero`Cons(n,l) = (if n = 0 then 1 else 0)"
  using natural
proof (cases rule: natE)
  case 0
  with tail show ?thesis
    unfolding pr_is_zero_def by (simp add: PREC_0 CONSTANT)
next
  case (succ m)
  with tail show ?thesis
    unfolding pr_is_zero_def by (simp add: PREC_succ CONSTANT)
qed

definition pr_positive :: i where
  "pr_positive \<equiv> PREC(CONSTANT(0),CONSTANT(1))"

lemma pr_positive_in_prim_rec [TC]:
  "pr_positive \<in> prim_rec"
  unfolding pr_positive_def by typecheck

lemma pr_positive_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_positive`Cons(n,l) = (if n = 0 then 0 else 1)"
  using natural
proof (cases rule: natE)
  case 0
  with tail show ?thesis
    unfolding pr_positive_def by (simp add: PREC_0 CONSTANT)
next
  case (succ m)
  with tail show ?thesis
    unfolding pr_positive_def by (simp add: PREC_succ CONSTANT)
qed

definition pr_if_zero :: i where
  "pr_if_zero \<equiv> PREC(PROJ(0),PROJ(succ(2)))"

lemma pr_if_zero_in_prim_rec [TC]:
  "pr_if_zero \<in> prim_rec"
  unfolding pr_if_zero_def by typecheck

lemma pr_if_zero_apply:
  assumes condition: "c \<in> nat"
    and zero: "z \<in> nat"
    and successor: "s \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_if_zero`Cons(c,Cons(z,Cons(s,l))) =
    (if c = 0 then z else s)"
  using condition
proof (cases rule: natE)
  case 0
  with zero successor tail show ?thesis
    unfolding pr_if_zero_def by (simp add: PREC_0 PROJ_0)
next
  case (succ n)
  with zero successor tail show ?thesis
    unfolding pr_if_zero_def by (simp add: PREC_succ)
qed

definition pr_le :: i where
  "pr_le \<equiv> COMP(pr_is_zero,[pr_diff])"

lemma pr_le_in_prim_rec [TC]:
  "pr_le \<in> prim_rec"
  unfolding pr_le_def by typecheck

lemma pr_le_apply:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_le`Cons(m,Cons(n,l)) = (if m \<le> n then 1 else 0)"
  unfolding pr_le_def
  using first second tail
  by (simp add: COMP_1 pr_diff_apply pr_is_zero_apply diff_is_0_lemma)

subsection \<open>Cantor Pairing\<close>

definition pr_triangle_step :: i where
  "pr_triangle_step \<equiv>
    COMP(pr_add,[PROJ(0),COMP(SC,[PROJ(1)])])"

lemma pr_triangle_step_in_prim_rec [TC]:
  "pr_triangle_step \<in> prim_rec"
  unfolding pr_triangle_step_def by typecheck

definition pr_triangle :: i where
  "pr_triangle \<equiv> PREC(CONSTANT(0),pr_triangle_step)"

lemma pr_triangle_in_prim_rec [TC]:
  "pr_triangle \<in> prim_rec"
  unfolding pr_triangle_def by typecheck

lemma pr_triangle_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_triangle`Cons(n,l) = triangle(n)"
  using natural
proof (induct n rule: nat_induct)
  case 0
  with tail show ?case
    unfolding pr_triangle_def by (simp add: PREC_0 CONSTANT)
next
  case (succ n)
  from succ.hyps(1) have triangle_natural: "triangle(n) \<in> nat"
    by (rule triangle_type)
  from succ tail triangle_natural show ?case
    unfolding pr_triangle_def pr_triangle_step_def
    by (simp add: PREC_succ COMP_2 COMP_1 PROJ_def SC pr_add_apply)
qed

definition pr_pair_code :: i where
  "pr_pair_code \<equiv>
    COMP(pr_add,[COMP(pr_triangle,[pr_add]),PROJ(1)])"

theorem pr_pair_code_in_prim_rec [TC]:
  "pr_pair_code \<in> prim_rec"
  unfolding pr_pair_code_def by typecheck

theorem pr_pair_code_apply:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_pair_code`Cons(m,Cons(n,l)) = pair_code(m,n)"
  unfolding pr_pair_code_def pair_code_def
  using first second tail
  by (simp add: COMP_2 COMP_1 pr_add_apply pr_triangle_apply PROJ_0)

subsection \<open>Cantor Projections\<close>

definition pr_equal_core :: i where
  "pr_equal_core \<equiv> COMP(pr_add,[pr_diff,pr_reverse_diff])"

lemma pr_equal_core_in_prim_rec [TC]:
  "pr_equal_core \<in> prim_rec"
  unfolding pr_equal_core_def by typecheck

definition pr_equal :: i where
  "pr_equal \<equiv> COMP(pr_is_zero,[pr_equal_core])"

lemma pr_equal_in_prim_rec [TC]:
  "pr_equal \<in> prim_rec"
  unfolding pr_equal_def by typecheck

lemma pr_equal_apply:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_equal`Cons(m,Cons(n,l)) = (if m = n then 1 else 0)"
proof -
  have difference:
    "(m #- n) #+ (n #- m) = 0 \<longleftrightarrow> m = n"
    using first second
    by (auto simp add: diff_is_0_lemma intro: le_anti_sym)
  show ?thesis
    unfolding pr_equal_def pr_equal_core_def
    using first second tail difference
    by (simp add: COMP_2 COMP_1 pr_add_apply pr_diff_apply
        pr_reverse_diff_apply pr_is_zero_apply)
qed

definition pr_diagonal_end :: i where
  "pr_diagonal_end \<equiv>
    COMP(pr_add,[COMP(pr_triangle,[PROJ(0)]),PROJ(0)])"

lemma pr_diagonal_end_in_prim_rec [TC]:
  "pr_diagonal_end \<in> prim_rec"
  unfolding pr_diagonal_end_def by typecheck

definition pr_pair_diagonal_step :: i where
  "pr_pair_diagonal_step \<equiv>
    COMP(pr_if_zero,
      [COMP(pr_equal,[PROJ(1),pr_diagonal_end]),
       PROJ(0),
       COMP(SC,[PROJ(0)])])"

lemma pr_pair_diagonal_step_in_prim_rec [TC]:
  "pr_pair_diagonal_step \<in> prim_rec"
  unfolding pr_pair_diagonal_step_def by typecheck

definition pr_pair_diagonal :: i where
  "pr_pair_diagonal \<equiv>
    PREC(CONSTANT(0),pr_pair_diagonal_step)"

lemma pr_pair_diagonal_in_prim_rec [TC]:
  "pr_pair_diagonal \<in> prim_rec"
  unfolding pr_pair_diagonal_def by typecheck

lemma pr_pair_diagonal_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_pair_diagonal`Cons(n,l) = pair_diagonal(n)"
  using natural
proof (induct n rule: nat_induct)
  case 0
  with tail show ?case
    unfolding pr_pair_diagonal_def by (simp add: PREC_0 CONSTANT)
next
  case (succ n)
  from succ.hyps(1) have diagonal_natural: "pair_diagonal(n) \<in> nat"
    by (rule pair_diagonal_type)
  from succ tail diagonal_natural show ?case
    unfolding pr_pair_diagonal_def pr_pair_diagonal_step_def
      pr_diagonal_end_def
    by (simp add: PREC_succ COMP_3 COMP_2 COMP_1 PROJ_def SC
        pr_if_zero_apply pr_equal_apply pr_add_apply pr_triangle_apply)
qed

definition pr_pair_right :: i where
  "pr_pair_right \<equiv>
    COMP(pr_diff,[PROJ(0),COMP(pr_triangle,[pr_pair_diagonal])])"

lemma pr_pair_right_in_prim_rec [TC]:
  "pr_pair_right \<in> prim_rec"
  unfolding pr_pair_right_def by typecheck

lemma pr_pair_right_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_pair_right`Cons(n,l) = snd(pair_decode(n))"
  unfolding pr_pair_right_def
  using natural tail pair_right_code_decode[OF natural]
  unfolding pair_right_code_def
  by (simp add: COMP_2 COMP_1 pr_diff_apply pr_triangle_apply
      pr_pair_diagonal_apply PROJ_0)

definition pr_pair_left :: i where
  "pr_pair_left \<equiv>
    COMP(pr_diff,[pr_pair_diagonal,pr_pair_right])"

lemma pr_pair_left_in_prim_rec [TC]:
  "pr_pair_left \<in> prim_rec"
  unfolding pr_pair_left_def by typecheck

lemma pr_pair_left_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_pair_left`Cons(n,l) = fst(pair_decode(n))"
  unfolding pr_pair_left_def
  using natural tail pair_left_code_decode[OF natural]
    pair_right_code_decode[OF natural]
  unfolding pair_left_code_def
  by (simp add: COMP_2 pr_diff_apply pr_pair_diagonal_apply
      pr_pair_right_apply)

corollary pr_pair_right_code_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_pair_right`Cons(n,l) = pair_right_code(n)"
  using pr_pair_right_apply[OF natural tail]
    pair_right_code_decode[OF natural]
  by simp

corollary pr_pair_left_code_apply:
  assumes natural: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_pair_left`Cons(n,l) = pair_left_code(n)"
  using pr_pair_left_apply[OF natural tail]
    pair_left_code_decode[OF natural]
  by simp

subsection \<open>Coded Natural Lists\<close>

definition pr_list_cons :: i where
  "pr_list_cons \<equiv> COMP(SC,[pr_pair_code])"

lemma pr_list_cons_in_prim_rec [TC]:
  "pr_list_cons \<in> prim_rec"
  unfolding pr_list_cons_def by typecheck

lemma pr_list_cons_apply:
  assumes element: "a \<in> nat"
    and tail_code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_list_cons`Cons(a,Cons(c,l)) = code_cons(a,c)"
  unfolding pr_list_cons_def code_cons_def
  using element tail_code tail
  by (simp add: COMP_1 SC pr_pair_code_apply)

definition pr_list_head :: i where
  "pr_list_head \<equiv>
    COMP(pr_if_zero,
      [PROJ(0),CONSTANT(0),
       COMP(pr_pair_left,[COMP(pr_pred,[PROJ(0)])])])"

lemma pr_list_head_in_prim_rec [TC]:
  "pr_list_head \<in> prim_rec"
  unfolding pr_list_head_def by typecheck

lemma pr_list_head_apply:
  assumes natural: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_list_head`Cons(c,l) = code_head(c)"
  using natural
proof (cases rule: natE)
  case 0
  with tail show ?thesis
    unfolding pr_list_head_def code_head_def
    by (simp add: COMP_3 COMP_1 CONSTANT PROJ_0 pr_if_zero_apply)
next
  case (succ n)
  with tail show ?thesis
    unfolding pr_list_head_def code_head_def
    by (simp add: COMP_3 COMP_1 CONSTANT PROJ_0 pr_if_zero_apply
        pr_pred_apply pr_pair_left_apply)
qed

definition pr_list_tail :: i where
  "pr_list_tail \<equiv>
    COMP(pr_if_zero,
      [PROJ(0),CONSTANT(0),
       COMP(pr_pair_right,[COMP(pr_pred,[PROJ(0)])])])"

lemma pr_list_tail_in_prim_rec [TC]:
  "pr_list_tail \<in> prim_rec"
  unfolding pr_list_tail_def by typecheck

lemma pr_list_tail_apply:
  assumes natural: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_list_tail`Cons(c,l) = code_tail(c)"
  using natural
proof (cases rule: natE)
  case 0
  with tail show ?thesis
    unfolding pr_list_tail_def code_tail_def
    by (simp add: COMP_3 COMP_1 CONSTANT PROJ_0 pr_if_zero_apply)
next
  case (succ n)
  with tail show ?thesis
    unfolding pr_list_tail_def code_tail_def
    by (simp add: COMP_3 COMP_1 CONSTANT PROJ_0 pr_if_zero_apply
        pr_pred_apply pr_pair_right_apply)
qed

definition pr_list_drop :: i where
  "pr_list_drop \<equiv>
    PREC(PROJ(0),COMP(pr_list_tail,[PROJ(0)]))"

lemma pr_list_drop_in_prim_rec [TC]:
  "pr_list_drop \<in> prim_rec"
  unfolding pr_list_drop_def by typecheck

lemma pr_list_drop_apply:
  assumes count: "k \<in> nat"
    and code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_list_drop`Cons(k,Cons(c,l)) = code_drop(k,c)"
  using count
proof (induct k rule: nat_induct)
  case 0
  with code tail show ?case
    unfolding pr_list_drop_def by (simp add: PREC_0 PROJ_0)
next
  case (succ k)
  from succ.hyps(1) code have dropped: "code_drop(k,c) \<in> nat"
    by (rule code_drop_type)
  from succ code tail dropped show ?case
    unfolding pr_list_drop_def
    by (simp add: PREC_succ COMP_1 PROJ_def pr_list_tail_apply)
qed

definition pr_list_nth :: i where
  "pr_list_nth \<equiv> COMP(pr_list_head,[pr_list_drop])"

lemma pr_list_nth_in_prim_rec [TC]:
  "pr_list_nth \<in> prim_rec"
  unfolding pr_list_nth_def by typecheck

lemma pr_list_nth_apply:
  assumes count: "k \<in> nat"
    and code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_list_nth`Cons(k,Cons(c,l)) = code_nth(k,c)"
  unfolding pr_list_nth_def code_nth_def
  using count code tail
  by (simp add: COMP_1 pr_list_drop_apply pr_list_head_apply
      code_drop_type)

definition pr_list_has_index :: i where
  "pr_list_has_index \<equiv>
    COMP(pr_positive,[pr_list_drop])"

lemma pr_list_has_index_in_prim_rec [TC]:
  "pr_list_has_index \<in> prim_rec"
  unfolding pr_list_has_index_def by typecheck

lemma pr_list_has_index_apply:
  assumes count: "k \<in> nat"
    and code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_list_has_index`Cons(k,Cons(c,l)) = code_has_index(k,c)"
  unfolding pr_list_has_index_def code_has_index_def
  using count code tail
  by (simp add: COMP_1 pr_list_drop_apply pr_positive_apply
      code_drop_type)


end
