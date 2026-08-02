(*  Title:      Turing_Primrec.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Coding\<close>

theory Turing_Primrec
  imports
    Turing_Coding
    "ZF-Induct.Primrec"
begin

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

consts pair_diagonal :: "i \<Rightarrow> i"

primrec
  "pair_diagonal(0) = 0"
  "pair_diagonal(succ(n)) =
    (if n = triangle(pair_diagonal(n)) #+ pair_diagonal(n) then
      succ(pair_diagonal(n))
    else
      pair_diagonal(n))"

lemma pair_diagonal_type [TC]:
  assumes natural: "n \<in> nat"
  shows "pair_diagonal(n) \<in> nat"
  using natural by (induct n rule: nat_induct) simp_all

lemma pair_diagonal_decode:
  assumes natural: "n \<in> nat"
  shows "pair_diagonal(n) =
    fst(pair_decode(n)) #+ snd(pair_decode(n))"
  using natural
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ n)
  from succ.hyps(1) have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have first: "fst(pair_decode(n)) \<in> nat"
    and second: "snd(pair_decode(n)) \<in> nat"
    by typecheck+
  from pair_code_decode[OF succ.hyps(1)] have code:
    "pair_code(fst(pair_decode(n)),snd(pair_decode(n))) = n" .
  from first show ?case
  proof (cases rule: natE)
    case 0
    from code 0 second have end_of_diagonal:
      "n = triangle(snd(pair_decode(n))) #+ snd(pair_decode(n))"
      unfolding pair_code_def by simp
    from succ.hyps(2) 0 second have diagonal:
      "pair_diagonal(n) = snd(pair_decode(n))"
      by simp
    from end_of_diagonal diagonal have at_end:
      "n = triangle(pair_diagonal(n)) #+ pair_diagonal(n)"
      by simp
    from 0 have next_pair:
      "pair_decode(succ(n)) =
        \<langle>succ(snd(pair_decode(n))),0\<rangle>"
      by (simp add: pair_step_def)
    from at_end have next_diagonal:
      "pair_diagonal(succ(n)) = succ(pair_diagonal(n))"
      by simp
    from diagonal next_pair next_diagonal second show ?thesis
      by simp
  next
    case (succ m)
    let ?s = "fst(pair_decode(n)) #+ snd(pair_decode(n))"
    have sum_natural: "?s \<in> nat"
      using first second by typecheck
    have not_end:
      "n \<noteq> triangle(?s) #+ ?s"
    proof
      assume at_end: "n = triangle(?s) #+ ?s"
      from code have
        "triangle(?s) #+ snd(pair_decode(n)) = n"
        unfolding pair_code_def .
      also from at_end have "... = triangle(?s) #+ ?s" .
      finally have equal:
        "snd(pair_decode(n)) = ?s"
        using second sum_natural
        by (rule add_left_cancel[OF refl])
      from equal succ second show False
        by (simp add: add_ac)
    qed
    from succ.hyps(2) have diagonal:
      "pair_diagonal(n) = ?s" .
    from not_end diagonal have not_at_end:
      "n \<noteq> triangle(pair_diagonal(n)) #+ pair_diagonal(n)"
      by simp
    from succ have next_pair:
      "pair_decode(succ(n)) =
        \<langle>m,succ(snd(pair_decode(n)))\<rangle>"
      by (simp add: pair_step_def)
    from not_at_end have next_diagonal:
      "pair_diagonal(succ(n)) = pair_diagonal(n)"
      by simp
    from diagonal next_pair next_diagonal succ second show ?thesis
      by (simp add: add_ac)
  qed
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

definition pair_right_code :: "i \<Rightarrow> i" where
  "pair_right_code(n) \<equiv>
    n #- triangle(pair_diagonal(n))"

definition pair_left_code :: "i \<Rightarrow> i" where
  "pair_left_code(n) \<equiv>
    pair_diagonal(n) #- pair_right_code(n)"

lemma pair_right_code_type [TC]:
  "pair_right_code(n) \<in> nat"
  unfolding pair_right_code_def by typecheck

lemma pair_left_code_type [TC]:
  "pair_left_code(n) \<in> nat"
  unfolding pair_left_code_def by typecheck

theorem pair_right_code_decode:
  assumes natural: "n \<in> nat"
  shows "pair_right_code(n) = snd(pair_decode(n))"
proof -
  from natural have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have first: "fst(pair_decode(n)) \<in> nat"
    and second: "snd(pair_decode(n)) \<in> nat"
    by typecheck+
  from pair_code_decode[OF natural] have code:
    "n = triangle(fst(pair_decode(n)) #+ snd(pair_decode(n))) #+
      snd(pair_decode(n))"
    unfolding pair_code_def by (rule sym)
  have "pair_right_code(n) =
      (triangle(fst(pair_decode(n)) #+ snd(pair_decode(n))) #+
        snd(pair_decode(n))) #-
      triangle(fst(pair_decode(n)) #+ snd(pair_decode(n)))"
    unfolding pair_right_code_def
    using code pair_diagonal_decode[OF natural] by simp
  also from second have "... = snd(pair_decode(n))"
    by (simp add: diff_add_inverse)
  finally show ?thesis .
qed

theorem pair_left_code_decode:
  assumes natural: "n \<in> nat"
  shows "pair_left_code(n) = fst(pair_decode(n))"
proof -
  from natural have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have first: "fst(pair_decode(n)) \<in> nat"
    and second: "snd(pair_decode(n)) \<in> nat"
    by typecheck+
  show ?thesis
    unfolding pair_left_code_def
    using pair_diagonal_decode[OF natural]
      pair_right_code_decode[OF natural] first second
    by (simp add: diff_add_inverse2 add_ac)
qed

lemma pair_right_code_pair_code:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
  shows "pair_right_code(pair_code(m,n)) = n"
  using pair_right_code_decode[OF pair_code_type[OF first second]]
    pair_decode_code[OF first second]
  by simp

lemma pair_left_code_pair_code:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
  shows "pair_left_code(pair_code(m,n)) = m"
  using pair_left_code_decode[OF pair_code_type[OF first second]]
    pair_decode_code[OF first second]
  by simp

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

definition code_cons :: "[i,i] \<Rightarrow> i" where
  "code_cons(a,c) \<equiv> succ(pair_code(a,c))"

definition code_head :: "i \<Rightarrow> i" where
  "code_head(c) \<equiv>
    if c = 0 then 0 else fst(pair_decode(pred(c)))"

definition code_tail :: "i \<Rightarrow> i" where
  "code_tail(c) \<equiv>
    if c = 0 then 0 else snd(pair_decode(pred(c)))"

lemma code_cons_type [TC]:
  assumes element: "a \<in> nat"
    and tail: "c \<in> nat"
  shows "code_cons(a,c) \<in> nat"
  using element tail unfolding code_cons_def by typecheck

lemma code_head_type [TC]:
  assumes natural: "c \<in> nat"
  shows "code_head(c) \<in> nat"
  using natural
proof (cases rule: natE)
  case 0
  then show ?thesis unfolding code_head_def by simp
next
  case (succ n)
  from succ(1) have "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  with succ natural show ?thesis unfolding code_head_def by typecheck
qed

lemma code_tail_type [TC]:
  assumes natural: "c \<in> nat"
  shows "code_tail(c) \<in> nat"
  using natural
proof (cases rule: natE)
  case 0
  then show ?thesis unfolding code_tail_def by simp
next
  case (succ n)
  from succ(1) have "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  with succ natural show ?thesis unfolding code_tail_def by typecheck
qed

lemma code_cons_encode [simp]:
  "code_cons(a,nat_list_encode(l)) =
    nat_list_encode(Cons(a,l))"
  unfolding code_cons_def by simp

lemma code_head_encode:
  assumes list: "l \<in> list(nat)"
  shows "code_head(nat_list_encode(l)) = hd(l)"
  using list
proof (induct l rule: list.induct)
  case Nil
  then show ?case unfolding code_head_def by simp
next
  case (Cons a l)
  from Cons.hyps(2) have tail_code: "nat_list_encode(l) \<in> nat"
    by (rule nat_list_encode_type)
  from Cons tail_code show ?case
    unfolding code_head_def by (simp add: pair_decode_code)
qed

lemma code_tail_encode:
  assumes list: "l \<in> list(nat)"
  shows "code_tail(nat_list_encode(l)) = nat_list_encode(tl(l))"
  using list
proof (induct l rule: list.induct)
  case Nil
  then show ?case unfolding code_tail_def by simp
next
  case (Cons a l)
  from Cons.hyps(2) have tail_code: "nat_list_encode(l) \<in> nat"
    by (rule nat_list_encode_type)
  from Cons tail_code show ?case
    unfolding code_tail_def by (simp add: pair_decode_code)
qed

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

consts code_drop :: "[i,i] \<Rightarrow> i"

primrec
  "code_drop(0,c) = c"
  "code_drop(succ(k),c) = code_tail(code_drop(k,c))"

lemma code_drop_type [TC]:
  assumes count: "k \<in> nat"
    and code: "c \<in> nat"
  shows "code_drop(k,c) \<in> nat"
  using count code
  by (induct k rule: nat_induct) (simp_all add: code_tail_type)

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

lemma code_drop_encode:
  assumes count: "k \<in> nat"
    and list: "l \<in> list(nat)"
  shows "code_drop(k,nat_list_encode(l)) =
    nat_list_encode(drop(k,l))"
  using count
proof (induct k rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ k)
  from succ.hyps(1) list have dropped: "drop(k,l) \<in> list(nat)"
    by typecheck
  from succ list dropped show ?case
    by (simp add: code_tail_encode drop_succ)
qed

definition code_nth :: "[i,i] \<Rightarrow> i" where
  "code_nth(k,c) \<equiv> code_head(code_drop(k,c))"

lemma code_nth_type [TC]:
  assumes count: "k \<in> nat"
    and code: "c \<in> nat"
  shows "code_nth(k,c) \<in> nat"
  using count code unfolding code_nth_def by typecheck

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

lemma hd_eq_nth_zero:
  assumes list: "l \<in> list(A)"
  shows "hd(l) = nth(0,l)"
  using list by (cases rule: list.cases) simp_all

lemma code_nth_encode:
  assumes count: "k \<in> nat"
    and list: "l \<in> list(nat)"
  shows "code_nth(k,nat_list_encode(l)) = nth(k,l)"
proof -
  from count list have dropped: "drop(k,l) \<in> list(nat)"
    by typecheck
  from nth_drop[OF count] list have nth:
    "nth(0,drop(k,l)) = nth(k,l)"
    using count by simp
  show ?thesis
    unfolding code_nth_def
    using code_drop_encode[OF count list]
      code_head_encode[OF dropped] hd_eq_nth_zero[OF dropped] nth
    by simp
qed

definition code_has_index :: "[i,i] \<Rightarrow> i" where
  "code_has_index(k,c) \<equiv>
    if code_drop(k,c) = 0 then 0 else 1"

lemma code_has_index_type [TC]:
  "code_has_index(k,c) \<in> nat"
  unfolding code_has_index_def by typecheck

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

lemma nat_list_encode_zero_iff:
  assumes list: "l \<in> list(nat)"
  shows "nat_list_encode(l) = 0 \<longleftrightarrow> l = []"
  using list by (cases rule: list.cases) simp_all

lemma drop_eq_Nil_iff:
  assumes count: "k \<in> nat"
    and list: "l \<in> list(A)"
  shows "drop(k,l) = [] \<longleftrightarrow> length(l) \<le> k"
proof
  assume empty: "drop(k,l) = []"
  from length_drop[OF count, rule_format, OF list] empty
  have "length(l) #- k = 0" by simp
  with count list show "length(l) \<le> k"
    by (simp add: diff_is_0_lemma)
next
  assume "length(l) \<le> k"
  with count list show "drop(k,l) = []"
    by (rule drop_all)
qed

lemma code_has_index_encode:
  assumes count: "k \<in> nat"
    and list: "l \<in> list(nat)"
  shows "code_has_index(k,nat_list_encode(l)) =
    (if k < length(l) then 1 else 0)"
proof -
  from list have length: "length(l) \<in> nat"
    by typecheck
  from count length have not_le:
    "\<not> length(l) \<le> k \<longleftrightarrow> k < length(l)"
    using not_le_iff_lt[OF nat_into_Ord nat_into_Ord] by simp
  show ?thesis
    unfolding code_has_index_def
    using code_drop_encode[OF count list]
      nat_list_encode_zero_iff[OF drop_type[OF count list]]
      drop_eq_Nil_iff[OF count list] not_le
    by auto
qed

end
