(*  Title:      Turing_Evaluator_Primrec.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Evaluation\<close>

theory Turing_Evaluator_Primrec
  imports Turing_Evaluator Turing_Primrec
begin

text \<open>The one-step evaluator and its finite iteration have
primitive-recursive certificates. In particular, pr_code_steps_apply
identifies the certificate with code_steps at every natural time bound.
This is a result about numerical evaluation, not a universal machine.\<close>

subsection \<open>Tape Inspection\<close>

definition pr_code_scan :: i where
  "pr_code_scan \<equiv>
    COMP(pr_list_head,[pr_pair_right])"

lemma pr_code_scan_in_prim_rec [TC]:
  "pr_code_scan \<in> prim_rec"
  unfolding pr_code_scan_def by typecheck

lemma pr_code_scan_apply:
  assumes tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_scan`Cons(t,l) = code_scan(t)"
proof -
  from tape_code have right: "pair_right_code(t) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_code_scan_def code_scan_def
    using tape_code tail right pair_right_code_decode[OF tape_code]
    by (simp add: COMP_1 pr_pair_right_apply pr_list_head_apply)
qed

subsection \<open>Tape Actions\<close>

definition pr_update_write_blank :: i where
  "pr_update_write_blank \<equiv>
    COMP(pr_pair_code,
      [pr_pair_left,
       COMP(pr_list_cons,
         [CONSTANT(blank_symbol),
          COMP(pr_list_tail,[pr_pair_right])])])"

lemma pr_update_write_blank_in_prim_rec [TC]:
  "pr_update_write_blank \<in> prim_rec"
  unfolding pr_update_write_blank_def by typecheck

lemma pr_update_write_blank_apply:
  assumes tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_update_write_blank`Cons(t,l) =
    pair_code(pair_left_code(t),
      code_cons(blank_symbol,code_tail(pair_right_code(t))))"
proof -
  from tape_code have left: "pair_left_code(t) \<in> nat"
    and right: "pair_right_code(t) \<in> nat"
    by typecheck+
  from right have right_tail: "code_tail(pair_right_code(t)) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_update_write_blank_def
    using tape_code tail left right right_tail
      pair_left_code_decode[OF tape_code]
      pair_right_code_decode[OF tape_code]
    by (simp add: COMP_2 COMP_1 CONSTANT
        pr_pair_left_apply pr_pair_right_apply pr_list_tail_apply
        pr_list_cons_apply pr_pair_code_apply)
qed

definition pr_update_write_one :: i where
  "pr_update_write_one \<equiv>
    COMP(pr_pair_code,
      [pr_pair_left,
       COMP(pr_list_cons,
         [CONSTANT(one_symbol),
          COMP(pr_list_tail,[pr_pair_right])])])"

lemma pr_update_write_one_in_prim_rec [TC]:
  "pr_update_write_one \<in> prim_rec"
  unfolding pr_update_write_one_def by typecheck

lemma pr_update_write_one_apply:
  assumes tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_update_write_one`Cons(t,l) =
    pair_code(pair_left_code(t),
      code_cons(one_symbol,code_tail(pair_right_code(t))))"
proof -
  from tape_code have left: "pair_left_code(t) \<in> nat"
    and right: "pair_right_code(t) \<in> nat"
    by typecheck+
  from right have right_tail: "code_tail(pair_right_code(t)) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_update_write_one_def
    using tape_code tail left right right_tail
      pair_left_code_decode[OF tape_code]
      pair_right_code_decode[OF tape_code]
    by (simp add: COMP_2 COMP_1 CONSTANT
        pr_pair_left_apply pr_pair_right_apply pr_list_tail_apply
        pr_list_cons_apply pr_pair_code_apply)
qed

definition pr_update_move_left :: i where
  "pr_update_move_left \<equiv>
    COMP(pr_pair_code,
      [COMP(pr_list_tail,[pr_pair_left]),
       COMP(pr_list_cons,
         [COMP(pr_list_head,[pr_pair_left]),
          pr_pair_right])])"

lemma pr_update_move_left_in_prim_rec [TC]:
  "pr_update_move_left \<in> prim_rec"
  unfolding pr_update_move_left_def by typecheck

lemma pr_update_move_left_apply:
  assumes tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_update_move_left`Cons(t,l) =
    pair_code(code_tail(pair_left_code(t)),
      code_cons(code_head(pair_left_code(t)),pair_right_code(t)))"
proof -
  from tape_code have left: "pair_left_code(t) \<in> nat"
    and right: "pair_right_code(t) \<in> nat"
    by typecheck+
  from left have left_head: "code_head(pair_left_code(t)) \<in> nat"
    and left_tail: "code_tail(pair_left_code(t)) \<in> nat"
    by typecheck+
  show ?thesis
    unfolding pr_update_move_left_def
    using tape_code tail left right left_head left_tail
      pair_left_code_decode[OF tape_code]
      pair_right_code_decode[OF tape_code]
    by (simp add: COMP_2 COMP_1
        pr_pair_left_apply pr_pair_right_apply pr_list_head_apply
        pr_list_tail_apply pr_list_cons_apply pr_pair_code_apply)
qed

definition pr_update_move_right :: i where
  "pr_update_move_right \<equiv>
    COMP(pr_pair_code,
      [COMP(pr_list_cons,
         [COMP(pr_list_head,[pr_pair_right]),
          pr_pair_left]),
       COMP(pr_list_tail,[pr_pair_right])])"

lemma pr_update_move_right_in_prim_rec [TC]:
  "pr_update_move_right \<in> prim_rec"
  unfolding pr_update_move_right_def by typecheck

lemma pr_update_move_right_apply:
  assumes tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_update_move_right`Cons(t,l) =
    pair_code(code_cons(code_head(pair_right_code(t)),pair_left_code(t)),
      code_tail(pair_right_code(t)))"
proof -
  from tape_code have left: "pair_left_code(t) \<in> nat"
    and right: "pair_right_code(t) \<in> nat"
    by typecheck+
  from right have right_head: "code_head(pair_right_code(t)) \<in> nat"
    and right_tail: "code_tail(pair_right_code(t)) \<in> nat"
    by typecheck+
  show ?thesis
    unfolding pr_update_move_right_def
    using tape_code tail left right right_head right_tail
      pair_left_code_decode[OF tape_code]
      pair_right_code_decode[OF tape_code]
    by (simp add: COMP_2 COMP_1
        pr_pair_left_apply pr_pair_right_apply pr_list_head_apply
        pr_list_tail_apply pr_list_cons_apply pr_pair_code_apply)
qed

definition pr_action_test :: "i \<Rightarrow> i" where
  "pr_action_test(k) \<equiv>
    COMP(pr_equal,[PROJ(0),CONSTANT(k)])"

lemma pr_action_test_in_prim_rec [TC]:
  assumes natural: "k \<in> nat"
  shows "pr_action_test(k) \<in> prim_rec"
  using natural unfolding pr_action_test_def by typecheck

lemma pr_action_test_apply:
  assumes action_code: "a \<in> nat"
    and constant: "k \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_action_test(k)`Cons(a,l) =
    (if a = k then 1 else 0)"
  unfolding pr_action_test_def
  using action_code constant tail
  by (simp add: COMP_2 CONSTANT PROJ_0 pr_equal_apply)

definition pr_update_move_right_case :: i where
  "pr_update_move_right_case \<equiv>
    COMP(pr_if_zero,
      [pr_action_test(move_right),
       PROJ(1),
       COMP(pr_update_move_right,[PROJ(1)])])"

lemma pr_update_move_right_case_in_prim_rec [TC]:
  "pr_update_move_right_case \<in> prim_rec"
  unfolding pr_update_move_right_case_def by typecheck

lemma pr_update_move_right_case_apply:
  assumes action_code: "a \<in> nat"
    and tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_update_move_right_case`Cons(a,Cons(t,l)) =
    (if a = move_right then
      pair_code(code_cons(code_head(pair_right_code(t)),pair_left_code(t)),
        code_tail(pair_right_code(t)))
    else t)"
  unfolding pr_update_move_right_case_def
  using action_code tape_code tail
  by (simp add: COMP_3 COMP_1
      pr_if_zero_apply pr_action_test_apply pr_update_move_right_apply)

definition pr_update_move_left_case :: i where
  "pr_update_move_left_case \<equiv>
    COMP(pr_if_zero,
      [pr_action_test(move_left),
       pr_update_move_right_case,
       COMP(pr_update_move_left,[PROJ(1)])])"

lemma pr_update_move_left_case_in_prim_rec [TC]:
  "pr_update_move_left_case \<in> prim_rec"
  unfolding pr_update_move_left_case_def by typecheck

lemma pr_update_move_left_case_apply:
  assumes action_code: "a \<in> nat"
    and tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_update_move_left_case`Cons(a,Cons(t,l)) =
    (if a = move_left then
      pair_code(code_tail(pair_left_code(t)),
        code_cons(code_head(pair_left_code(t)),pair_right_code(t)))
    else if a = move_right then
      pair_code(code_cons(code_head(pair_right_code(t)),pair_left_code(t)),
        code_tail(pair_right_code(t)))
    else t)"
  unfolding pr_update_move_left_case_def
  using action_code tape_code tail
  by (simp add: COMP_3 COMP_1
      pr_if_zero_apply pr_action_test_apply pr_update_move_left_apply
      pr_update_move_right_case_apply)

definition pr_update_write_one_case :: i where
  "pr_update_write_one_case \<equiv>
    COMP(pr_if_zero,
      [pr_action_test(write_one),
       pr_update_move_left_case,
       COMP(pr_update_write_one,[PROJ(1)])])"

lemma pr_update_write_one_case_in_prim_rec [TC]:
  "pr_update_write_one_case \<in> prim_rec"
  unfolding pr_update_write_one_case_def by typecheck

lemma pr_update_write_one_case_apply:
  assumes action_code: "a \<in> nat"
    and tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_update_write_one_case`Cons(a,Cons(t,l)) =
    (if a = write_one then
      pair_code(pair_left_code(t),
        code_cons(one_symbol,code_tail(pair_right_code(t))))
    else if a = move_left then
      pair_code(code_tail(pair_left_code(t)),
        code_cons(code_head(pair_left_code(t)),pair_right_code(t)))
    else if a = move_right then
      pair_code(code_cons(code_head(pair_right_code(t)),pair_left_code(t)),
        code_tail(pair_right_code(t)))
    else t)"
  unfolding pr_update_write_one_case_def
  using action_code tape_code tail
  by (simp add: COMP_3 COMP_1
      pr_if_zero_apply pr_action_test_apply pr_update_write_one_apply
      pr_update_move_left_case_apply)

definition pr_code_update :: i where
  "pr_code_update \<equiv>
    COMP(pr_if_zero,
      [pr_action_test(write_blank),
       pr_update_write_one_case,
       COMP(pr_update_write_blank,[PROJ(1)])])"

lemma pr_code_update_in_prim_rec [TC]:
  "pr_code_update \<in> prim_rec"
  unfolding pr_code_update_def by typecheck

lemma pr_code_update_apply:
  assumes action_code: "a \<in> nat"
    and tape_code: "t \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_update`Cons(a,Cons(t,l)) = code_update(a,t)"
  unfolding pr_code_update_def code_update_def
  using action_code tape_code tail
  by (simp add: COMP_3 COMP_1
      pr_if_zero_apply pr_action_test_apply pr_update_write_blank_apply
      pr_update_write_one_case_apply)

subsection \<open>Instruction Selection\<close>

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

definition pr_slot :: i where
  "pr_slot \<equiv>
    COMP(pr_add,
      [COMP(pr_add,
         [COMP(pr_pred,[PROJ(0)]),
          COMP(pr_pred,[PROJ(0)])]),
       PROJ(1)])"

lemma pr_slot_in_prim_rec [TC]:
  "pr_slot \<in> prim_rec"
  unfolding pr_slot_def by typecheck

lemma pr_slot_apply:
  assumes state: "q \<in> nat"
    and scanned: "b \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_slot`Cons(q,Cons(b,l)) = slot(q,b)"
  unfolding pr_slot_def slot_def
  using state scanned tail
  by (simp add: COMP_2 COMP_1 PROJ_0 pr_add_apply pr_pred_apply
      add_assoc)

definition pr_fetch_slot :: i where
  "pr_fetch_slot \<equiv>
    COMP(pr_slot,[PROJ(1),PROJ(2)])"

lemma pr_fetch_slot_in_prim_rec [TC]:
  "pr_fetch_slot \<in> prim_rec"
  unfolding pr_fetch_slot_def by typecheck

lemma pr_fetch_slot_apply:
  assumes machine_number: "e \<in> nat"
    and state: "q \<in> nat"
    and scanned: "b \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_fetch_slot`Cons(e,Cons(q,Cons(b,l))) = slot(q,b)"
  unfolding pr_fetch_slot_def
  using machine_number state scanned tail
  by (simp add: COMP_2 pr_slot_apply)

definition pr_fetch_present :: i where
  "pr_fetch_present \<equiv>
    COMP(pr_list_has_index,[pr_fetch_slot,PROJ(0)])"

lemma pr_fetch_present_in_prim_rec [TC]:
  "pr_fetch_present \<in> prim_rec"
  unfolding pr_fetch_present_def by typecheck

lemma pr_fetch_present_apply:
  assumes machine_number: "e \<in> nat"
    and state: "q \<in> nat"
    and scanned: "b \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_fetch_present`Cons(e,Cons(q,Cons(b,l))) =
    code_has_index(slot(q,b),e)"
proof -
  from state scanned have position: "slot(q,b) \<in> nat"
    by (rule slot_natural)
  show ?thesis
    unfolding pr_fetch_present_def
    using machine_number state scanned tail position
    by (simp add: COMP_2 PROJ_0 pr_fetch_slot_apply
        pr_list_has_index_apply)
qed

definition pr_fetch_instruction :: i where
  "pr_fetch_instruction \<equiv>
    COMP(pr_normalize_instruction_code,
      [COMP(pr_list_nth,[pr_fetch_slot,PROJ(0)])])"

lemma pr_fetch_instruction_in_prim_rec [TC]:
  "pr_fetch_instruction \<in> prim_rec"
  unfolding pr_fetch_instruction_def by typecheck

lemma pr_fetch_instruction_apply:
  assumes machine_number: "e \<in> nat"
    and state: "q \<in> nat"
    and scanned: "b \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_fetch_instruction`Cons(e,Cons(q,Cons(b,l))) =
    normalize_instruction_code(code_nth(slot(q,b),e))"
proof -
  from state scanned have position: "slot(q,b) \<in> nat"
    by (rule slot_natural)
  from position machine_number have selected: "code_nth(slot(q,b),e) \<in> nat"
    by (rule code_nth_type)
  show ?thesis
    unfolding pr_fetch_instruction_def
    using machine_number state scanned tail position selected
    by (simp add: COMP_2 COMP_1 PROJ_0 pr_fetch_slot_apply
        pr_list_nth_apply pr_normalize_instruction_code_apply)
qed

definition pr_fetch_nonfinal :: i where
  "pr_fetch_nonfinal \<equiv>
    COMP(pr_if_zero,
      [pr_fetch_present,
       CONSTANT(default_instruction_code),
       pr_fetch_instruction])"

lemma pr_fetch_nonfinal_in_prim_rec [TC]:
  "pr_fetch_nonfinal \<in> prim_rec"
  unfolding pr_fetch_nonfinal_def by typecheck

lemma pr_fetch_nonfinal_apply:
  assumes machine_number: "e \<in> nat"
    and state: "q \<in> nat"
    and scanned: "b \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_fetch_nonfinal`Cons(e,Cons(q,Cons(b,l))) =
    (if code_has_index(slot(q,b),e) = 0 then
      default_instruction_code
    else normalize_instruction_code(code_nth(slot(q,b),e)))"
proof -
  have present: "code_has_index(slot(q,b),e) \<in> nat"
    by typecheck
  have selected:
    "normalize_instruction_code(code_nth(slot(q,b),e)) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_fetch_nonfinal_def
    using machine_number state scanned tail present selected
      default_instruction_code_type
    by (simp add: COMP_3 CONSTANT pr_if_zero_apply
        pr_fetch_present_apply pr_fetch_instruction_apply)
qed

definition pr_code_fetch :: i where
  "pr_code_fetch \<equiv>
    COMP(pr_if_zero,
      [PROJ(1),
       CONSTANT(default_instruction_code),
       pr_fetch_nonfinal])"

lemma pr_code_fetch_in_prim_rec [TC]:
  "pr_code_fetch \<in> prim_rec"
  unfolding pr_code_fetch_def by typecheck

lemma pr_code_fetch_apply:
  assumes machine_number: "e \<in> nat"
    and state: "q \<in> nat"
    and scanned: "b \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_fetch`Cons(e,Cons(q,Cons(b,l))) =
    code_fetch(e,q,b)"
  unfolding pr_code_fetch_def code_fetch_def
  using machine_number state scanned tail default_instruction_code_type
  by (simp add: COMP_3 CONSTANT pr_if_zero_apply
      pr_fetch_nonfinal_apply)

subsection \<open>One-Step Evaluation\<close>

definition pr_step_tape :: i where
  "pr_step_tape \<equiv>
    COMP(pr_pair_right,[PROJ(1)])"

lemma pr_step_tape_in_prim_rec [TC]:
  "pr_step_tape \<in> prim_rec"
  unfolding pr_step_tape_def by typecheck

lemma pr_step_tape_apply:
  assumes machine_number: "e \<in> nat"
    and configuration_code: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_step_tape`Cons(e,Cons(z,l)) = pair_right_code(z)"
  unfolding pr_step_tape_def
  using machine_number configuration_code tail
  by (simp add: COMP_1 pr_pair_right_code_apply)

definition pr_step_instruction :: i where
  "pr_step_instruction \<equiv>
    COMP(pr_code_fetch,
      [PROJ(0),
       COMP(pr_pair_left,[PROJ(1)]),
       COMP(pr_code_scan,[pr_step_tape])])"

lemma pr_step_instruction_in_prim_rec [TC]:
  "pr_step_instruction \<in> prim_rec"
  unfolding pr_step_instruction_def by typecheck

lemma pr_step_instruction_apply:
  assumes machine_number: "e \<in> nat"
    and configuration_code: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_step_instruction`Cons(e,Cons(z,l)) =
    code_fetch(e,pair_left_code(z),code_scan(pair_right_code(z)))"
proof -
  from configuration_code have state: "pair_left_code(z) \<in> nat"
    and tape: "pair_right_code(z) \<in> nat"
    by typecheck+
  from tape have scanned: "code_scan(pair_right_code(z)) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_step_instruction_def
    using machine_number configuration_code tail state tape scanned
    by (simp add: COMP_3 COMP_1 PROJ_0
        pr_pair_left_code_apply pr_step_tape_apply
        pr_code_scan_apply pr_code_fetch_apply)
qed

definition pr_step_updated_tape :: i where
  "pr_step_updated_tape \<equiv>
    COMP(pr_code_update,
      [COMP(pr_pair_left,[pr_step_instruction]),
       pr_step_tape])"

lemma pr_step_updated_tape_in_prim_rec [TC]:
  "pr_step_updated_tape \<in> prim_rec"
  unfolding pr_step_updated_tape_def by typecheck

lemma pr_step_updated_tape_apply:
  assumes machine_number: "e \<in> nat"
    and configuration_code: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_step_updated_tape`Cons(e,Cons(z,l)) =
    code_update(
      pair_left_code(
        code_fetch(e,pair_left_code(z),code_scan(pair_right_code(z)))),
      pair_right_code(z))"
proof -
  let ?ins =
    "code_fetch(e,pair_left_code(z),code_scan(pair_right_code(z)))"
  have instruction_number: "?ins \<in> nat"
    by typecheck
  from configuration_code have tape: "pair_right_code(z) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_step_updated_tape_def
    using machine_number configuration_code tail instruction_number tape
    by (simp add: COMP_2 COMP_1 pr_step_instruction_apply
        pr_pair_left_code_apply pr_step_tape_apply pr_code_update_apply)
qed

definition pr_code_step :: i where
  "pr_code_step \<equiv>
    COMP(pr_pair_code,
      [COMP(pr_pair_right,[pr_step_instruction]),
       pr_step_updated_tape])"

lemma pr_code_step_in_prim_rec [TC]:
  "pr_code_step \<in> prim_rec"
  unfolding pr_code_step_def by typecheck

lemma pr_code_step_apply:
  assumes machine_number: "e \<in> nat"
    and configuration_code: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_step`Cons(e,Cons(z,l)) = code_step(e,z)"
proof -
  let ?ins =
    "code_fetch(e,pair_left_code(z),code_scan(pair_right_code(z)))"
  have instruction_number: "?ins \<in> nat"
    by typecheck
  have updated:
    "code_update(pair_left_code(?ins),pair_right_code(z)) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_code_step_def code_step_def Let_def
    using machine_number configuration_code tail instruction_number updated
    by (simp add: COMP_2 COMP_1 pr_step_instruction_apply
        pr_pair_right_code_apply pr_step_updated_tape_apply
        pr_pair_code_apply)
qed

subsection \<open>Finite Evaluation\<close>

definition pr_code_steps :: i where
  "pr_code_steps \<equiv>
    PREC(PROJ(1),
      COMP(pr_code_step,[PROJ(2),PROJ(0)]))"

lemma pr_code_steps_in_prim_rec [TC]:
  "pr_code_steps \<in> prim_rec"
  unfolding pr_code_steps_def by typecheck

lemma pr_code_steps_apply:
  assumes time: "n \<in> nat"
    and machine_number: "e \<in> nat"
    and configuration_code: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_steps`Cons(n,Cons(e,Cons(z,l))) =
    code_steps(n,e,z)"
  using time
proof (induct n rule: nat_induct)
  case 0
  with machine_number configuration_code tail show ?case
    unfolding pr_code_steps_def
    by (simp add: PREC_0)
next
  case (succ n)
  from succ.hyps(1) configuration_code have previous:
    "code_steps(n,e,z) \<in> nat"
    by (rule code_steps_type)
  from succ machine_number configuration_code tail previous show ?case
    unfolding pr_code_steps_def
    by (simp add: PREC_succ COMP_2 PROJ_0 pr_code_step_apply)
qed

definition pr_code_is_final :: i where
  "pr_code_is_final \<equiv>
    COMP(pr_is_zero,[pr_pair_left])"

lemma pr_code_is_final_in_prim_rec [TC]:
  "pr_code_is_final \<in> prim_rec"
  unfolding pr_code_is_final_def by typecheck

lemma pr_code_is_final_apply:
  assumes configuration_code: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_is_final`Cons(z,l) = code_is_final(z)"
  unfolding pr_code_is_final_def code_is_final_def
  using configuration_code tail
  by (simp add: COMP_1 pr_pair_left_code_apply pr_is_zero_apply)

definition pr_code_halts_at :: i where
  "pr_code_halts_at \<equiv>
    COMP(pr_code_is_final,[pr_code_steps])"

lemma pr_code_halts_at_in_prim_rec [TC]:
  "pr_code_halts_at \<in> prim_rec"
  unfolding pr_code_halts_at_def by typecheck

lemma pr_code_halts_at_apply:
  assumes time: "n \<in> nat"
    and machine_number: "e \<in> nat"
    and configuration_code: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_halts_at`Cons(n,Cons(e,Cons(z,l))) =
    code_halts_at(n,e,z)"
proof -
  from time configuration_code have evaluated: "code_steps(n,e,z) \<in> nat"
    by (rule code_steps_type)
  show ?thesis
    unfolding pr_code_halts_at_def code_halts_at_def
    using time machine_number configuration_code tail evaluated
    by (simp add: COMP_1 pr_code_steps_apply pr_code_is_final_apply)
qed

definition pr_code_initial_configuration :: i where
  "pr_code_initial_configuration \<equiv>
    COMP(pr_pair_code,
      [CONSTANT(initial_state),
       COMP(pr_pair_code,[CONSTANT(0),PROJ(0)])])"

lemma pr_code_initial_configuration_in_prim_rec [TC]:
  "pr_code_initial_configuration \<in> prim_rec"
  unfolding pr_code_initial_configuration_def by typecheck

lemma pr_code_initial_configuration_apply:
  assumes input_code: "x \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_initial_configuration`Cons(x,l) =
    code_initial_configuration(x)"
  unfolding pr_code_initial_configuration_def
    code_initial_configuration_def
  using input_code tail
  by (simp add: COMP_2 CONSTANT PROJ_0 pr_pair_code_apply)

definition pr_code_halts_blank_at :: i where
  "pr_code_halts_blank_at \<equiv>
    COMP(pr_code_halts_at,
      [PROJ(0),PROJ(1),CONSTANT(code_blank_configuration)])"

lemma pr_code_halts_blank_at_in_prim_rec [TC]:
  "pr_code_halts_blank_at \<in> prim_rec"
  unfolding pr_code_halts_blank_at_def by typecheck

lemma pr_code_halts_blank_at_apply:
  assumes time: "n \<in> nat"
    and machine_number: "e \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_halts_blank_at`Cons(n,Cons(e,l)) =
    code_halts_blank_at(n,e)"
  unfolding pr_code_halts_blank_at_def code_halts_blank_at_def
  using time machine_number tail code_blank_configuration_type
  by (simp add: COMP_3 CONSTANT PROJ_0 pr_code_halts_at_apply)

end
