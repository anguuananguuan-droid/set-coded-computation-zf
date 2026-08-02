(*  Title:      Turing_Transformations_Primrec.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Machine Transformations\<close>

theory Turing_Transformations_Primrec
  imports
    Turing_Transformations
    Turing_Evaluator_Primrec
begin

subsection \<open>State Shifting\<close>

definition pr_shift_state :: i where
  "pr_shift_state \<equiv>
    COMP(pr_if_zero,[PROJ(1),CONSTANT(final_state),pr_add])"

lemma pr_shift_state_in_prim_rec [TC]:
  "pr_shift_state \<in> prim_rec"
  unfolding pr_shift_state_def by typecheck

lemma pr_shift_state_apply:
  assumes offset: "k \<in> nat"
    and state: "q \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_shift_state`Cons(k,Cons(q,l)) = shift_state(k,q)"
  unfolding pr_shift_state_def shift_state_def
  using offset state tail
  by (simp add: COMP_3 CONSTANT PROJ_0 pr_if_zero_apply pr_add_apply)

subsection \<open>Instruction Shifting\<close>

definition code_shift_instruction :: "[i,i] \<Rightarrow> i" where
  "code_shift_instruction(k,z) \<equiv>
    let u = normalize_instruction_code(z)
    in pair_code(pair_left_code(u),
         shift_state(k,pair_right_code(u)))"

lemma code_shift_instruction_type [TC]:
  assumes offset: "k \<in> nat"
    and instruction_number: "z \<in> nat"
  shows "code_shift_instruction(k,z) \<in> nat"
  unfolding code_shift_instruction_def Let_def
  using offset instruction_number by typecheck

lemma code_shift_instruction_correct:
  assumes offset: "k \<in> nat"
    and instruction_number: "z \<in> nat"
  shows "code_shift_instruction(k,z) =
    encode_instruction(shift_instruction(k,decode_instruction(z)))"
proof -
  from instruction_number have instruction:
    "decode_instruction(z) \<in> instruction"
    by (rule decode_instruction_type)
  from normalize_instruction_code_correct[of z]
  have normalized:
    "normalize_instruction_code(z) =
      encode_instruction(decode_instruction(z))" .
  from encode_instruction_components[OF instruction]
  have action:
      "pair_left_code(normalize_instruction_code(z)) =
        fst(decode_instruction(z))"
    and state:
      "pair_right_code(normalize_instruction_code(z)) =
        snd(decode_instruction(z))"
    using normalized by simp_all
  show ?thesis
    unfolding code_shift_instruction_def Let_def shift_instruction_def
      encode_instruction_def
    using action state by simp
qed

definition pr_shift_normalized_instruction :: i where
  "pr_shift_normalized_instruction \<equiv>
    COMP(pr_normalize_instruction_code,[PROJ(1)])"

lemma pr_shift_normalized_instruction_in_prim_rec [TC]:
  "pr_shift_normalized_instruction \<in> prim_rec"
  unfolding pr_shift_normalized_instruction_def by typecheck

lemma pr_shift_normalized_instruction_apply:
  assumes offset: "k \<in> nat"
    and instruction_number: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_shift_normalized_instruction`Cons(k,Cons(z,l)) =
    normalize_instruction_code(z)"
  unfolding pr_shift_normalized_instruction_def
  using offset instruction_number tail
  by (simp add: COMP_1 pr_normalize_instruction_code_apply)

definition pr_code_shift_instruction :: i where
  "pr_code_shift_instruction \<equiv>
    COMP(pr_pair_code,
      [COMP(pr_pair_left,[pr_shift_normalized_instruction]),
       COMP(pr_shift_state,
         [PROJ(0),
          COMP(pr_pair_right,[pr_shift_normalized_instruction])])])"

lemma pr_code_shift_instruction_in_prim_rec [TC]:
  "pr_code_shift_instruction \<in> prim_rec"
  unfolding pr_code_shift_instruction_def by typecheck

lemma pr_code_shift_instruction_apply:
  assumes offset: "k \<in> nat"
    and instruction_number: "z \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_shift_instruction`Cons(k,Cons(z,l)) =
    code_shift_instruction(k,z)"
proof -
  have normalized: "normalize_instruction_code(z) \<in> nat"
    by typecheck
  then have action:
      "pair_left_code(normalize_instruction_code(z)) \<in> nat"
    and state:
      "pair_right_code(normalize_instruction_code(z)) \<in> nat"
    by typecheck+
  from offset state have shifted:
    "shift_state(k,pair_right_code(normalize_instruction_code(z)))
      \<in> nat"
    unfolding shift_state_def by typecheck
  show ?thesis
    unfolding pr_code_shift_instruction_def code_shift_instruction_def
      Let_def
    using offset instruction_number tail normalized action state shifted
    by (simp add: COMP_2 COMP_1 PROJ_0
        pr_shift_normalized_instruction_apply pr_pair_left_code_apply
        pr_pair_right_code_apply pr_shift_state_apply
        pr_pair_code_apply)
qed

subsection \<open>Machine Shifting\<close>

lemma drop_before_length:
  assumes index: "i \<in> nat"
    and codes: "l \<in> list(nat)"
    and present: "i < length(l)"
  shows "drop(i,l) = Cons(nth(i,l),drop(succ(i),l))"
proof -
  from present have index_member: "i \<in> length(l)"
    unfolding lt_def by simp
  from drop_length[OF codes, rule_format, OF index_member]
  obtain z zs where dropped: "drop(i,l) = Cons(z,zs)"
    by blast
  from nth_drop[OF index] codes have
    "nth(0,drop(i,l)) = nth(i,l)"
    using index by simp
  with dropped
  have head: "nth(i,l) = z"
    by simp
  from dropped have tail: "drop(succ(i),l) = zs"
    unfolding drop_succ by simp
  from dropped head tail show ?thesis by simp
qed

consts code_shift_machine_aux :: "[i,i,i] \<Rightarrow> i"

primrec
  "code_shift_machine_aux(0,k,e) = 0"
  "code_shift_machine_aux(succ(j),k,e) =
    (let i = e #- succ(j)
     in if code_has_index(i,e) = 0 then
          code_shift_machine_aux(j,k,e)
        else
          code_cons(code_shift_instruction(k,code_nth(i,e)),
            code_shift_machine_aux(j,k,e)))"

lemma code_shift_machine_aux_type [TC]:
  assumes count: "j \<in> nat"
    and offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
  shows "code_shift_machine_aux(j,k,e) \<in> nat"
  using count
proof (induct j rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ j)
  from machine_number succ.hyps(1) have index:
    "e #- succ(j) \<in> nat"
    by typecheck
  from index machine_number have selected:
    "code_nth(e #- succ(j),e) \<in> nat"
    by typecheck
  from offset selected have shifted:
    "code_shift_instruction(k,code_nth(e #- succ(j),e)) \<in> nat"
    by typecheck
  from succ shifted show ?case
    by (simp add: Let_def code_cons_type)
qed

lemma code_shift_machine_aux_correct:
  assumes count: "j \<in> nat"
    and offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
    and bounded: "j \<le> e"
  shows "code_shift_machine_aux(j,k,e) =
    nat_list_encode(
      map(\<lambda>z. code_shift_instruction(k,z),
        drop(e #- j,nat_list_decode(e))))"
  using count bounded
proof (induct j rule: nat_induct)
  case 0
  let ?xs = "nat_list_decode(e)"
  from machine_number have codes: "?xs \<in> list(nat)"
    by typecheck
  from length_nat_list_decode_le[OF machine_number]
  have exhausted: "length(?xs) \<le> e" .
  from drop_all[OF machine_number, rule_format, OF codes exhausted]
  have empty: "drop(e,?xs) = []" .
  from empty machine_number show ?case by simp
next
  case (succ j)
  let ?xs = "nat_list_decode(e)"
  let ?i = "e #- succ(j)"
  from machine_number have codes: "?xs \<in> list(nat)"
    by typecheck
  from machine_number have roundtrip: "nat_list_encode(?xs) = e"
    by (rule nat_list_encode_decode)
  from succ.prems have "j < e"
    by (rule succ_leE)
  then have prior_bound: "j \<le> e"
    by (rule leI)
  from succ.hyps(2)[OF prior_bound] have previous:
    "code_shift_machine_aux(j,k,e) =
      nat_list_encode(
        map(\<lambda>z. code_shift_instruction(k,z),
          drop(e #- j,?xs)))" .
  from succ_diff_succ[OF succ.hyps(1) machine_number succ.prems]
  have next_index: "succ(?i) = e #- j" .
  from machine_number succ.hyps(1) have index: "?i \<in> nat"
    by typecheck
  from index codes have remainder: "drop(?i,?xs) \<in> list(nat)"
    by typecheck
  show ?case
  proof (cases "?i < length(?xs)")
    case True
    from code_has_index_encode[OF index codes] True roundtrip
    have present: "code_has_index(?i,e) = 1"
      by simp
    from code_nth_encode[OF index codes] roundtrip
    have selected: "code_nth(?i,e) = nth(?i,?xs)"
      by simp
    from drop_before_length[OF index codes True]
    have decomposed:
      "drop(?i,?xs) = Cons(nth(?i,?xs),drop(succ(?i),?xs))" .
    from codes True have selected_natural: "nth(?i,?xs) \<in> nat"
      by typecheck
    from previous present selected decomposed next_index
      selected_natural remainder
    show ?thesis by (simp add: Let_def)
  next
    case False
    from codes have length_natural: "length(?xs) \<in> nat"
      by typecheck
    from index length_natural False have exhausted:
      "length(?xs) \<le> ?i"
      by (simp add: not_lt_iff_le)
    from index have index_le_next: "?i \<le> succ(?i)"
      by (simp add: le_succ_iff)
    from exhausted index_le_next have exhausted_next:
      "length(?xs) \<le> succ(?i)"
      by (rule le_trans)
    from code_has_index_encode[OF index codes] False roundtrip
    have absent: "code_has_index(?i,e) = 0"
      by simp
    from drop_all[OF index, rule_format, OF codes exhausted]
    have current_empty: "drop(?i,?xs) = []" .
    from drop_all[OF nat_succI[OF index], rule_format,
        OF codes exhausted_next]
    have previous_empty: "drop(succ(?i),?xs) = []" .
    from previous absent current_empty previous_empty next_index
    show ?thesis by (simp add: Let_def)
  qed
qed

definition code_shift_machine :: "[i,i] \<Rightarrow> i" where
  "code_shift_machine(k,e) \<equiv> code_shift_machine_aux(e,k,e)"

lemma code_shift_machine_type [TC]:
  assumes offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
  shows "code_shift_machine(k,e) \<in> nat"
  using offset machine_number unfolding code_shift_machine_def by typecheck

lemma code_shift_machine_stream:
  assumes offset: "k \<in> nat"
    and codes: "l \<in> list(nat)"
  shows "map(\<lambda>z. code_shift_instruction(k,z),l) =
    machine_code_list(shift_machine(k,decode_machine_list(l)))"
  using codes
  unfolding machine_code_list_def shift_machine_def decode_machine_list_def
proof (induct l rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons z l)
  from Cons.hyps(1) have instruction_number: "z \<in> nat" .
  from code_shift_instruction_correct[OF offset instruction_number]
  have head: "code_shift_instruction(k,z) =
    encode_instruction(shift_instruction(k,decode_instruction(z)))" .
  from Cons head show ?case by simp
qed

theorem code_shift_machine_correct:
  assumes offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
  shows "code_shift_machine(k,e) =
    encode_machine(shift_machine(k,decode_machine(e)))"
proof -
  let ?l = "nat_list_decode(e)"
  from machine_number have codes: "?l \<in> list(nat)"
    by typecheck
  from machine_number have reflexive: "e \<le> e"
    by (rule nat_into_Ord[THEN le_refl])
  from code_shift_machine_aux_correct[
      OF machine_number offset machine_number reflexive]
  have transformed:
    "code_shift_machine(k,e) =
      nat_list_encode(map(\<lambda>z. code_shift_instruction(k,z),?l))"
    unfolding code_shift_machine_def by simp
  from code_shift_machine_stream[OF offset codes] have stream:
    "map(\<lambda>z. code_shift_instruction(k,z),?l) =
      machine_code_list(shift_machine(k,decode_machine_list(?l)))" .
  from transformed stream
  show ?thesis
    unfolding encode_machine_def decode_machine_def by simp
qed

lemma code_shift_machine_in_machine_code:
  assumes offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
  shows "code_shift_machine(k,e) \<in> machine_code"
proof -
  from shift_machine_type[
      OF offset decode_machine_type[OF machine_number]]
  have shifted: "shift_machine(k,decode_machine(e)) \<in> machine" .
  from code_shift_machine_correct[OF offset machine_number]
    encode_machine_type[OF shifted]
  show ?thesis by simp
qed

theorem decode_code_shift_machine:
  assumes offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
  shows "decode_machine(code_shift_machine(k,e)) =
    shift_machine(k,decode_machine(e))"
proof -
  from shift_machine_type[
      OF offset decode_machine_type[OF machine_number]]
  have shifted: "shift_machine(k,decode_machine(e)) \<in> machine" .
  from code_shift_machine_correct[OF offset machine_number]
    decode_encode_machine[OF shifted]
  show ?thesis by simp
qed

definition pr_code_shift_reverse_index :: i where
  "pr_code_shift_reverse_index \<equiv>
    COMP(pr_diff,[PROJ(succ(2)),COMP(SC,[PROJ(1)])])"

lemma pr_code_shift_reverse_index_in_prim_rec [TC]:
  "pr_code_shift_reverse_index \<in> prim_rec"
  unfolding pr_code_shift_reverse_index_def by typecheck

lemma pr_code_shift_reverse_index_apply:
  assumes result: "r \<in> nat"
    and index: "j \<in> nat"
    and offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_shift_reverse_index`
      Cons(r,Cons(j,Cons(k,Cons(e,l)))) = e #- succ(j)"
  unfolding pr_code_shift_reverse_index_def
  using result index offset machine_number tail
  by (simp add: COMP_2 COMP_1 SC pr_diff_apply)

definition pr_code_shift_machine_step :: i where
  "pr_code_shift_machine_step \<equiv>
    COMP(pr_if_zero,
      [COMP(pr_list_has_index,
         [pr_code_shift_reverse_index,PROJ(succ(2))]),
       PROJ(0),
       COMP(pr_list_cons,
         [COMP(pr_code_shift_instruction,
            [PROJ(2),
             COMP(pr_list_nth,
               [pr_code_shift_reverse_index,PROJ(succ(2))])]),
          PROJ(0)])])"

lemma pr_code_shift_machine_step_in_prim_rec [TC]:
  "pr_code_shift_machine_step \<in> prim_rec"
  unfolding pr_code_shift_machine_step_def by typecheck

lemma pr_code_shift_machine_step_apply:
  assumes result: "r \<in> nat"
    and index: "j \<in> nat"
    and offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_shift_machine_step`
      Cons(r,Cons(j,Cons(k,Cons(e,l)))) =
    (let i = e #- succ(j)
     in if code_has_index(i,e) = 0 then r
     else code_cons(code_shift_instruction(k,code_nth(i,e)),r))"
proof -
  have reverse_index: "e #- succ(j) \<in> nat"
    by typecheck
  have present: "code_has_index(e #- succ(j),e) \<in> nat"
    by typecheck
  from reverse_index machine_number have selected:
    "code_nth(e #- succ(j),e) \<in> nat"
    by typecheck
  from code_shift_instruction_type[OF offset selected]
  have shifted:
    "code_shift_instruction(k,code_nth(e #- succ(j),e)) \<in> nat" .
  from shifted result have cons:
    "code_cons(code_shift_instruction(k,code_nth(e #- succ(j),e)),r)
      \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_code_shift_machine_step_def
    using result index offset machine_number tail present selected shifted cons
    by (simp add: Let_def COMP_3 COMP_2 COMP_1 PROJ_0
        pr_code_shift_reverse_index_apply
        pr_list_has_index_apply pr_list_nth_apply
        pr_code_shift_instruction_apply pr_list_cons_apply
        pr_if_zero_apply)
qed

definition pr_code_shift_machine_aux :: i where
  "pr_code_shift_machine_aux \<equiv>
    PREC(CONSTANT(0),pr_code_shift_machine_step)"

lemma pr_code_shift_machine_aux_in_prim_rec [TC]:
  "pr_code_shift_machine_aux \<in> prim_rec"
  unfolding pr_code_shift_machine_aux_def by typecheck

lemma pr_code_shift_machine_aux_apply:
  assumes count: "j \<in> nat"
    and offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_shift_machine_aux`
      Cons(j,Cons(k,Cons(e,l))) = code_shift_machine_aux(j,k,e)"
  using count
proof (induct j rule: nat_induct)
  case 0
  with offset machine_number tail show ?case
    unfolding pr_code_shift_machine_aux_def
    by (simp add: PREC_0 CONSTANT)
next
  case (succ j)
  from code_shift_machine_aux_type[
      OF succ.hyps(1) offset machine_number]
  have previous: "code_shift_machine_aux(j,k,e) \<in> nat" .
  from succ offset machine_number tail previous show ?case
    unfolding pr_code_shift_machine_aux_def
    by (simp add: PREC_succ pr_code_shift_machine_step_apply)
qed

definition pr_code_shift_machine :: i where
  "pr_code_shift_machine \<equiv>
    COMP(pr_code_shift_machine_aux,
      [PROJ(1),PROJ(0),PROJ(1)])"

lemma pr_code_shift_machine_in_prim_rec [TC]:
  "pr_code_shift_machine \<in> prim_rec"
  unfolding pr_code_shift_machine_def by typecheck

lemma pr_code_shift_machine_apply:
  assumes offset: "k \<in> nat"
    and machine_number: "e \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_shift_machine`Cons(k,Cons(e,l)) = code_shift_machine(k,e)"
  unfolding pr_code_shift_machine_def code_shift_machine_def
  using offset machine_number tail
  by (simp add: COMP_3 PROJ_0 pr_code_shift_machine_aux_apply)

subsection \<open>Numeral Loader Prefixes\<close>

lemma rev_numeral_input [simp]:
  assumes natural: "n \<in> nat"
  shows "rev(numeral_input(n)) = numeral_input(n)"
  using natural unfolding numeral_input_def
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ n)
  from repeat_succ_app[OF succ.hyps(1), of one_symbol]
  have append:
    "repeat(one_symbol,n) @ [one_symbol] =
      repeat(one_symbol,succ(n))"
    by simp
  from succ.hyps(2) append show ?case by simp
qed

lemma write_symbol_one [simp]:
  "write_symbol(one_symbol) = write_one"
  unfolding write_symbol_def by simp

lemma loader_actions_numeral_zero [simp]:
  "loader_actions(numeral_input(0)) = []"
  unfolding loader_actions_def numeral_input_def by simp

lemma loader_actions_numeral_succ [simp]:
  assumes natural: "n \<in> nat"
  shows "loader_actions(numeral_input(succ(n))) =
    Cons(move_left,
      Cons(write_one,loader_actions(numeral_input(n))))"
  using rev_numeral_input[OF natural]
    rev_numeral_input[OF nat_succI[OF natural]]
  unfolding loader_actions_def numeral_input_def
  by simp

definition loader_block :: "i \<Rightarrow> i" where
  "loader_block(q) \<equiv>
    Cons(\<langle>move_left,succ(q)\<rangle>,
      Cons(\<langle>move_left,succ(q)\<rangle>,
        Cons(\<langle>write_one,succ(succ(q))\<rangle>,
          Cons(\<langle>write_one,succ(succ(q))\<rangle>,[]))))"

lemma loader_block_type [TC]:
  assumes state: "q \<in> nat"
  shows "loader_block(q) \<in> list(instruction)"
  using state unfolding loader_block_def instruction_def by typecheck

definition code_loader_move :: "i \<Rightarrow> i" where
  "code_loader_move(i) \<equiv>
    pair_code(move_left,succ(succ(i #+ i)))"

definition code_loader_write :: "i \<Rightarrow> i" where
  "code_loader_write(i) \<equiv>
    pair_code(write_one,succ(succ(succ(i #+ i))))"

lemma code_loader_move_type [TC]:
  assumes index: "i \<in> nat"
  shows "code_loader_move(i) \<in> nat"
  using index unfolding code_loader_move_def by typecheck

lemma code_loader_write_type [TC]:
  assumes index: "i \<in> nat"
  shows "code_loader_write(i) \<in> nat"
  using index unfolding code_loader_write_def by typecheck

definition code_prepend_loader_block :: "[i,i] \<Rightarrow> i" where
  "code_prepend_loader_block(i,c) \<equiv>
    code_cons(code_loader_move(i),
      code_cons(code_loader_move(i),
        code_cons(code_loader_write(i),
          code_cons(code_loader_write(i),c))))"

lemma code_prepend_loader_block_type [TC]:
  assumes index: "i \<in> nat"
    and code: "c \<in> nat"
  shows "code_prepend_loader_block(i,c) \<in> nat"
  using index code unfolding code_prepend_loader_block_def by typecheck

lemma code_prepend_loader_block_correct:
  assumes index: "i \<in> nat"
    and machine_M: "M \<in> machine"
  shows "code_prepend_loader_block(i,encode_machine(M)) =
    encode_machine(loader_block(succ(i #+ i)) @ M)"
proof -
  from machine_M have instructions: "M \<in> list(instruction)"
    unfolding machine_def .
  from index have state: "succ(i #+ i) \<in> nat"
    by typecheck
  from loader_block_type[OF state] have block:
    "loader_block(succ(i #+ i)) \<in> list(instruction)" .
  from block have split:
    "machine_code_list(loader_block(succ(i #+ i)) @ M) =
      machine_code_list(loader_block(succ(i #+ i))) @
        machine_code_list(M)"
    unfolding machine_code_list_def by (rule map_app_distrib)
  from split show ?thesis
    unfolding code_prepend_loader_block_def code_loader_move_def
      code_loader_write_def encode_machine_def machine_code_list_def
      loader_block_def encode_instruction_def
    using index instructions by (simp add: code_cons_def)
qed

consts code_loader_prefix_aux :: "[i,i,i] \<Rightarrow> i"

primrec
  "code_loader_prefix_aux(0,n,c) = c"
  "code_loader_prefix_aux(succ(j),n,c) =
    code_prepend_loader_block(n #- succ(j),
      code_loader_prefix_aux(j,n,c))"

lemma code_loader_prefix_aux_type [TC]:
  assumes count: "j \<in> nat"
    and total: "n \<in> nat"
    and code: "c \<in> nat"
  shows "code_loader_prefix_aux(j,n,c) \<in> nat"
  using count total code
  by (induct j rule: nat_induct)
    (simp_all add: code_prepend_loader_block_type)

lemma code_loader_prefix_aux_correct:
  assumes count: "j \<in> nat"
    and total: "n \<in> nat"
    and machine_M: "M \<in> machine"
    and bounded: "j \<le> n"
  shows "code_loader_prefix_aux(j,n,encode_machine(M)) =
    encode_machine(
      compile_actions(loader_actions(numeral_input(j)),
        succ((n #- j) #+ (n #- j))) @ M)"
  using count total machine_M bounded
proof (induct j arbitrary: M rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ j)
  note index = succ.hyps(1)
  note prefix_IH = succ.hyps(2)
  note total = succ.prems(1)
  note machine_M = succ.prems(2)
  note bounded = succ.prems(3)
  let ?i = "n #- succ(j)"
  let ?q = "succ(?i #+ ?i)"
  let ?qnext = "succ((n #- j) #+ (n #- j))"
  from bounded have less: "j < n"
    by (rule succ_leE)
  then have prior_bound: "j \<le> n"
    by (rule leI)
  from prefix_IH[OF total machine_M prior_bound] have prefix:
    "code_loader_prefix_aux(j,n,encode_machine(M)) =
      encode_machine(
        compile_actions(loader_actions(numeral_input(j)),?qnext) @ M)" .
  from succ_diff_succ[OF index total bounded] have difference:
    "succ(?i) = n #- j" .
  then have difference_sym: "n #- j = succ(?i)"
    by (rule sym)
  from index total have reverse_index: "?i \<in> nat"
    by typecheck
  then have current_state: "?q \<in> nat"
    by typecheck
  from difference_sym reverse_index have next_state:
    "succ(succ(?q)) = ?qnext"
    by simp
  from numeral_input_type[OF index] have input:
    "numeral_input(j) \<in> list(symbol)" .
  from loader_actions_type[OF input] have actions:
    "loader_actions(numeral_input(j)) \<in> list(action)" .
  from compile_actions_type[OF actions, of ?qnext]
    next_state current_state
  have compiled:
    "compile_actions(loader_actions(numeral_input(j)),?qnext)
      \<in> list(instruction)"
    by simp
  from machine_M have instructions: "M \<in> list(instruction)"
    unfolding machine_def .
  from compiled instructions have suffix:
    "compile_actions(loader_actions(numeral_input(j)),?qnext) @ M
      \<in> machine"
    unfolding machine_def by typecheck
  from code_prepend_loader_block_correct[OF reverse_index suffix]
    prefix
  have prepended:
    "code_prepend_loader_block(?i,
        code_loader_prefix_aux(j,n,encode_machine(M))) =
      encode_machine(loader_block(?q) @
        (compile_actions(loader_actions(numeral_input(j)),?qnext) @ M))"
    by simp
  from loader_actions_numeral_succ[OF index] current_state next_state
  have compiled_step:
    "compile_actions(loader_actions(numeral_input(succ(j))),?q) =
      loader_block(?q) @
        compile_actions(loader_actions(numeral_input(j)),?qnext)"
    unfolding loader_block_def by simp
  from loader_block_type[OF current_state] compiled instructions
  have associated:
    "loader_block(?q) @
        (compile_actions(loader_actions(numeral_input(j)),?qnext) @ M) =
      compile_actions(loader_actions(numeral_input(succ(j))),?q) @ M"
    using compiled_step by (simp add: app_assoc)
  from prepended associated show ?case by simp
qed

definition code_loader_prefix :: "[i,i] \<Rightarrow> i" where
  "code_loader_prefix(n,c) \<equiv>
    code_loader_prefix_aux(n,n,c)"

lemma code_loader_prefix_type [TC]:
  assumes count: "n \<in> nat"
    and code: "c \<in> nat"
  shows "code_loader_prefix(n,c) \<in> nat"
  using count code unfolding code_loader_prefix_def by typecheck

lemma code_loader_prefix_correct:
  assumes natural: "n \<in> nat"
    and machine_M: "M \<in> machine"
  shows "code_loader_prefix(n,encode_machine(M)) =
    encode_machine(
      compile_actions(loader_actions(numeral_input(n)),initial_state) @ M)"
proof -
  from natural have reflexive: "n \<le> n"
    by (rule nat_into_Ord[THEN le_refl])
  from code_loader_prefix_aux_correct[
      OF natural natural machine_M reflexive]
  show ?thesis
    unfolding code_loader_prefix_def by simp
qed

subsection \<open>Primitive-Recursive Loader Prefixes\<close>

definition pr_code_loader_move :: i where
  "pr_code_loader_move \<equiv>
    COMP(pr_pair_code,
      [CONSTANT(move_left),
       COMP(SC,[COMP(SC,[pr_double])])])"

lemma pr_code_loader_move_in_prim_rec [TC]:
  "pr_code_loader_move \<in> prim_rec"
  unfolding pr_code_loader_move_def by typecheck

lemma pr_code_loader_move_apply:
  assumes index: "i \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_loader_move`Cons(i,l) = code_loader_move(i)"
proof -
  from index have target: "succ(succ(i #+ i)) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_code_loader_move_def code_loader_move_def
    using index tail target
    by (simp add: COMP_2 COMP_1 CONSTANT SC pr_double_apply
        pr_pair_code_apply)
qed

definition pr_code_loader_write :: i where
  "pr_code_loader_write \<equiv>
    COMP(pr_pair_code,
      [CONSTANT(write_one),
       COMP(SC,[COMP(SC,[COMP(SC,[pr_double])])])])"

lemma pr_code_loader_write_in_prim_rec [TC]:
  "pr_code_loader_write \<in> prim_rec"
  unfolding pr_code_loader_write_def by typecheck

lemma pr_code_loader_write_apply:
  assumes index: "i \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_loader_write`Cons(i,l) = code_loader_write(i)"
proof -
  from index have target: "succ(succ(succ(i #+ i))) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_code_loader_write_def code_loader_write_def
    using index tail target
    by (simp add: COMP_2 COMP_1 CONSTANT SC pr_double_apply
        pr_pair_code_apply)
qed

definition pr_code_prepend_loader_block :: i where
  "pr_code_prepend_loader_block \<equiv>
    COMP(pr_list_cons,
      [pr_code_loader_move,
       COMP(pr_list_cons,
         [pr_code_loader_move,
          COMP(pr_list_cons,
            [pr_code_loader_write,
             COMP(pr_list_cons,[pr_code_loader_write,PROJ(1)])])])])"

lemma pr_code_prepend_loader_block_in_prim_rec [TC]:
  "pr_code_prepend_loader_block \<in> prim_rec"
  unfolding pr_code_prepend_loader_block_def by typecheck

lemma pr_code_prepend_loader_block_apply:
  assumes index: "i \<in> nat"
    and code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_prepend_loader_block`Cons(i,Cons(c,l)) =
    code_prepend_loader_block(i,c)"
proof -
  from code_loader_move_type[OF index] have move:
    "code_loader_move(i) \<in> nat" .
  from code_loader_write_type[OF index] have write_code:
    "code_loader_write(i) \<in> nat" .
  show ?thesis
    unfolding pr_code_prepend_loader_block_def
      code_prepend_loader_block_def
    using index code tail move write_code
    by (simp add: COMP_2 PROJ_1 pr_code_loader_move_apply
        pr_code_loader_write_apply pr_list_cons_apply)
qed

definition pr_loader_reverse_index :: i where
  "pr_loader_reverse_index \<equiv>
    COMP(pr_diff,[PROJ(2),COMP(SC,[PROJ(1)])])"

lemma pr_loader_reverse_index_in_prim_rec [TC]:
  "pr_loader_reverse_index \<in> prim_rec"
  unfolding pr_loader_reverse_index_def by typecheck

lemma pr_loader_reverse_index_apply:
  assumes result: "r \<in> nat"
    and index: "j \<in> nat"
    and total: "n \<in> nat"
    and code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_loader_reverse_index`
      Cons(r,Cons(j,Cons(n,Cons(c,l)))) = n #- succ(j)"
  unfolding pr_loader_reverse_index_def
  using result index total code tail
  by (simp add: COMP_2 COMP_1 SC pr_diff_apply)

definition pr_code_loader_prefix_step :: i where
  "pr_code_loader_prefix_step \<equiv>
    COMP(pr_code_prepend_loader_block,
      [pr_loader_reverse_index,PROJ(0)])"

lemma pr_code_loader_prefix_step_in_prim_rec [TC]:
  "pr_code_loader_prefix_step \<in> prim_rec"
  unfolding pr_code_loader_prefix_step_def by typecheck

lemma pr_code_loader_prefix_step_apply:
  assumes result: "r \<in> nat"
    and index: "j \<in> nat"
    and total: "n \<in> nat"
    and code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_loader_prefix_step`
      Cons(r,Cons(j,Cons(n,Cons(c,l)))) =
    code_prepend_loader_block(n #- succ(j),r)"
proof -
  have reverse_index: "n #- succ(j) \<in> nat"
    by typecheck
  show ?thesis
    unfolding pr_code_loader_prefix_step_def
    using result index total code tail reverse_index
    by (simp add: COMP_2 PROJ_0 pr_loader_reverse_index_apply
        pr_code_prepend_loader_block_apply)
qed

definition pr_code_loader_prefix_aux :: i where
  "pr_code_loader_prefix_aux \<equiv>
    PREC(PROJ(1),pr_code_loader_prefix_step)"

lemma pr_code_loader_prefix_aux_in_prim_rec [TC]:
  "pr_code_loader_prefix_aux \<in> prim_rec"
  unfolding pr_code_loader_prefix_aux_def by typecheck

lemma pr_code_loader_prefix_aux_apply:
  assumes count: "j \<in> nat"
    and total: "n \<in> nat"
    and code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_loader_prefix_aux`
      Cons(j,Cons(n,Cons(c,l))) = code_loader_prefix_aux(j,n,c)"
  using count
proof (induct j rule: nat_induct)
  case 0
  with total code tail show ?case
    unfolding pr_code_loader_prefix_aux_def
    by (simp add: PREC_0 PROJ_1)
next
  case (succ j)
  from code_loader_prefix_aux_type[OF succ.hyps(1) total code]
  have previous: "code_loader_prefix_aux(j,n,c) \<in> nat" .
  from succ total code tail previous show ?case
    unfolding pr_code_loader_prefix_aux_def
    by (simp add: PREC_succ pr_code_loader_prefix_step_apply)
qed

definition pr_code_loader_prefix :: i where
  "pr_code_loader_prefix \<equiv>
    COMP(pr_code_loader_prefix_aux,
      [PROJ(0),PROJ(0),PROJ(1)])"

lemma pr_code_loader_prefix_in_prim_rec [TC]:
  "pr_code_loader_prefix \<in> prim_rec"
  unfolding pr_code_loader_prefix_def by typecheck

lemma pr_code_loader_prefix_apply:
  assumes count: "n \<in> nat"
    and code: "c \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_code_loader_prefix`Cons(n,Cons(c,l)) =
    code_loader_prefix(n,c)"
  unfolding pr_code_loader_prefix_def code_loader_prefix_def
  using count code tail
  by (simp add: COMP_3 PROJ_0 pr_code_loader_prefix_aux_apply)

subsection \<open>Primitive-Recursive Hardwiring\<close>

definition hardwire_code :: "[i,i] \<Rightarrow> i" where
  "hardwire_code(e,n) \<equiv>
    code_loader_prefix(n,code_shift_machine(n #+ n,e))"

lemma hardwire_code_type [TC]:
  assumes machine_number: "e \<in> nat"
    and input_number: "n \<in> nat"
  shows "hardwire_code(e,n) \<in> nat"
  using machine_number input_number unfolding hardwire_code_def by typecheck

theorem hardwire_code_correct:
  assumes machine_number: "e \<in> nat"
    and input_number: "n \<in> nat"
  shows "hardwire_code(e,n) =
    encode_machine(hardwire(decode_machine(e),numeral_input(n)))"
proof -
  let ?M = "decode_machine(e)"
  let ?k = "n #+ n"
  from decode_machine_type[OF machine_number] have machine_M:
    "?M \<in> machine" .
  from input_number have offset: "?k \<in> nat"
    by typecheck
  from shift_machine_type[OF offset machine_M] have shifted:
    "shift_machine(?k,?M) \<in> machine" .
  from code_shift_machine_correct[OF offset machine_number]
  have shifted_code:
    "code_shift_machine(?k,e) = encode_machine(shift_machine(?k,?M))" .
  from code_loader_prefix_correct[OF input_number shifted]
    shifted_code
  have compiled:
    "code_loader_prefix(n,code_shift_machine(?k,e)) =
      encode_machine(
        compile_actions(loader_actions(numeral_input(n)),initial_state) @
          shift_machine(?k,?M))"
    by simp
  from length_loader_actions[OF numeral_input_type[OF input_number]]
    input_number
  have offset_length:
    "length(loader_actions(numeral_input(n))) = ?k"
    by simp
  from compiled offset_length show ?thesis
    unfolding hardwire_code_def hardwire_def Let_def by simp
qed

lemma hardwire_code_in_machine_code:
  assumes machine_number: "e \<in> nat"
    and input_number: "n \<in> nat"
  shows "hardwire_code(e,n) \<in> machine_code"
proof -
  from decode_machine_type[OF machine_number]
    numeral_input_type[OF input_number]
  have transformed:
    "hardwire(decode_machine(e),numeral_input(n)) \<in> machine"
    by typecheck
  from hardwire_code_correct[OF machine_number input_number]
    encode_machine_type[OF transformed]
  show ?thesis by simp
qed

theorem decode_hardwire_code:
  assumes machine_number: "e \<in> nat"
    and input_number: "n \<in> nat"
  shows "decode_machine(hardwire_code(e,n)) =
    hardwire(decode_machine(e),numeral_input(n))"
proof -
  from decode_machine_type[OF machine_number]
    numeral_input_type[OF input_number]
  have transformed:
    "hardwire(decode_machine(e),numeral_input(n)) \<in> machine"
    by typecheck
  from hardwire_code_correct[OF machine_number input_number]
    decode_encode_machine[OF transformed]
  show ?thesis by simp
qed

definition pr_hardwire_code :: i where
  "pr_hardwire_code \<equiv>
    COMP(pr_code_loader_prefix,
      [PROJ(1),
       COMP(pr_code_shift_machine,
         [COMP(pr_double,[PROJ(1)]),PROJ(0)])])"

lemma pr_hardwire_code_in_prim_rec [TC]:
  "pr_hardwire_code \<in> prim_rec"
  unfolding pr_hardwire_code_def by typecheck

lemma pr_hardwire_code_apply:
  assumes machine_number: "e \<in> nat"
    and input_number: "n \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_hardwire_code`Cons(e,Cons(n,l)) = hardwire_code(e,n)"
proof -
  from input_number have offset: "n #+ n \<in> nat"
    by typecheck
  from code_shift_machine_type[OF offset machine_number]
  have shifted: "code_shift_machine(n #+ n,e) \<in> nat" .
  show ?thesis
    unfolding pr_hardwire_code_def hardwire_code_def
    using machine_number input_number tail offset shifted
    by (simp add: COMP_2 COMP_1 PROJ_0 pr_double_apply
        pr_code_shift_machine_apply pr_code_loader_prefix_apply)
qed

definition self_hardwire_code :: "i \<Rightarrow> i" where
  "self_hardwire_code(e) \<equiv> hardwire_code(e,e)"

lemma self_hardwire_code_type [TC]:
  assumes natural: "e \<in> nat"
  shows "self_hardwire_code(e) \<in> nat"
  using natural unfolding self_hardwire_code_def by typecheck

definition pr_self_hardwire_code :: i where
  "pr_self_hardwire_code \<equiv>
    COMP(pr_hardwire_code,[PROJ(0),PROJ(0)])"

lemma pr_self_hardwire_code_in_prim_rec [TC]:
  "pr_self_hardwire_code \<in> prim_rec"
  unfolding pr_self_hardwire_code_def by typecheck

lemma pr_self_hardwire_code_apply:
  assumes natural: "e \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_self_hardwire_code`Cons(e,l) = self_hardwire_code(e)"
  unfolding pr_self_hardwire_code_def self_hardwire_code_def
  using natural tail
  by (simp add: COMP_2 PROJ_0 pr_hardwire_code_apply)

theorem self_hardwire_reduction:
  assumes natural: "e \<in> nat"
  shows "e \<in> self_halting \<longleftrightarrow>
    self_hardwire_code(e) \<in> blank_halting"
proof -
  from decode_hardwire_code[OF natural natural]
  have decoded:
    "decode_machine(self_hardwire_code(e)) =
      hardwire(decode_machine(e),numeral_input(e))"
    unfolding self_hardwire_code_def .
  from hardwire_halts_iff[
      OF decode_machine_type[OF natural] numeral_input_type[OF natural]]
    decoded self_halting_iff[OF natural]
    self_hardwire_code_type[OF natural]
    blank_halting_iff[OF self_hardwire_code_type[OF natural]]
  show ?thesis by simp
qed

end
