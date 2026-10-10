(*  Title:      Turing_Machine_Name_Primrec.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Machine Names\<close>

theory Turing_Machine_Name_Primrec
  imports Turing_Name_Primrec "Set_Coded_Computation_ZF.Turing_Evaluator_Primrec"
begin

definition pr_instr_name_from_fields :: i where
  "pr_instr_name_from_fields \<equiv>
    COMP(pr_formula_exists,
      [COMP(pr_formula_and,
        [COMP(pr_nat_name_code,[PROJ(0)]),
         COMP(pr_formula_exists,
           [COMP(pr_formula_and,
             [COMP(pr_nat_name_code,[PROJ(1)]),
              CONSTANT(formula_code(pair_fm(1,0,2)))])])])])"

lemma pr_instr_name_from_fields_in_prim_rec [TC]:
  "pr_instr_name_from_fields \<in> prim_rec"
  unfolding pr_instr_name_from_fields_def
  by (typecheck add: formula_code_type)

lemma pr_instr_name_from_fields_apply:
  assumes a: "a \<in> nat" and b: "b \<in> nat"
    and tail: "l \<in> list(nat)"
  shows "pr_instr_name_from_fields`Cons(a,Cons(b,l)) =
    formula_code(instr_name_fm(\<langle>a,b\<rangle>))"
proof -
  have pair: "pair_fm(1,0,2) \<in> formula" by typecheck
  from a b have left: "nat_name_fm(a) \<in> formula"
    and right: "nat_name_fm(b) \<in> formula" by (auto intro: nat_name_fm_type)
  from right pair have inner: "And(nat_name_fm(b),pair_fm(1,0,2)) \<in> formula"
    by typecheck
  from inner have inner_ex: "Exists(And(nat_name_fm(b),pair_fm(1,0,2))) \<in> formula"
    by typecheck
  from left inner_ex have outer:
    "And(nat_name_fm(a),Exists(And(nat_name_fm(b),pair_fm(1,0,2)))) \<in> formula"
    by typecheck
  from a b tail pair left right inner inner_ex outer show ?thesis
    unfolding pr_instr_name_from_fields_def instr_name_fm_def
    by (simp add: COMP_1 COMP_2 PROJ_0 PROJ_1 CONSTANT
        pr_nat_name_code_apply pr_formula_and_apply
        pr_formula_exists_apply formula_code_type)
qed

definition pr_instr_name_code :: i where
  "pr_instr_name_code \<equiv>
    COMP(pr_instr_name_from_fields,
      [COMP(pr_pair_left,[pr_normalize_instruction_code]),
       COMP(pr_pair_right,[pr_normalize_instruction_code])])"

lemma pr_instr_name_code_in_prim_rec [TC]:
  "pr_instr_name_code \<in> prim_rec"
  unfolding pr_instr_name_code_def by typecheck

lemma pr_instr_name_code_apply:
  assumes n: "n \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_instr_name_code`Cons(n,l) =
    formula_code(instr_name_fm(decode_instruction(n)))"
proof -
  from n have ins: "decode_instruction(n) \<in> instruction"
    by (rule decode_instruction_type)
  from ins have a: "fst(decode_instruction(n)) \<in> nat"
    and b: "snd(decode_instruction(n)) \<in> nat"
    unfolding instruction_def using action_subset_nat by auto
  have normalized:
    "normalize_instruction_code(n) =
      pair_code(fst(decode_instruction(n)),snd(decode_instruction(n)))"
    unfolding normalize_instruction_code_correct encode_instruction_def by simp
  from a b normalized have left:
    "pair_left_code(normalize_instruction_code(n)) = fst(decode_instruction(n))"
    and right:
    "pair_right_code(normalize_instruction_code(n)) = snd(decode_instruction(n))"
    by (simp_all add: pair_left_code_pair_code pair_right_code_pair_code)
  from ins have pair:
    "\<langle>fst(decode_instruction(n)),snd(decode_instruction(n))\<rangle> =
      decode_instruction(n)"
    unfolding instruction_def by (rule Pair_fst_snd_eq)
  from n tail a b left right pair show ?thesis
    unfolding pr_instr_name_code_def
    by (simp add: COMP_2 COMP_1 pr_normalize_instruction_code_apply
        pr_pair_left_code_apply pr_pair_right_code_apply
        pr_instr_name_from_fields_apply normalize_instruction_code_type)
qed

lemma drop_at_index:
  assumes k: "k \<in> nat" and l: "l \<in> list(A)"
  shows "drop(k,l) =
    (if k < length(l) then Cons(nth(k,l),drop(succ(k),l)) else [])"
proof (cases "k < length(l)")
  case True
  from l k have dropped: "drop(k,l) \<in> list(A)" by typecheck
  from True k l have nonempty: "drop(k,l) \<noteq> []"
    using drop_eq_Nil_iff[OF k l]
    by (simp add: not_le_iff_lt)
  from dropped nonempty obtain a t where d: "drop(k,l) = Cons(a,t)"
    by (cases rule: list.cases) auto
  from k l have nth: "nth(0,drop(k,l)) = nth(k,l)"
    using nth_drop[OF k] by simp
  from d nth have a: "a = nth(k,l)" by simp
  from d have t: "t = drop(succ(k),l)" by (simp add: drop_succ)
  from True d a t show ?thesis by simp
next
  case False
  from k l False have "length(l) \<le> k"
    by (simp add: not_lt_iff_le)
  with k l have "drop(k,l) = []" by (rule drop_all)
  with False show ?thesis by simp
qed

lemma code_nth_decode:
  assumes e: "e \<in> nat" and k: "k \<in> nat"
  shows "code_nth(k,e) = nth(k,nat_list_decode(e))"
proof -
  from e have l: "nat_list_decode(e) \<in> list(nat)"
    by (rule nat_list_decode_type)
  from code_nth_encode[OF k l] nat_list_encode_decode[OF e]
  show ?thesis by simp
qed

lemma code_has_index_decode:
  assumes e: "e \<in> nat" and k: "k \<in> nat"
  shows "code_has_index(k,e) =
    (if k < length(nat_list_decode(e)) then 1 else 0)"
proof -
  from e have l: "nat_list_decode(e) \<in> list(nat)"
    by (rule nat_list_decode_type)
  from code_has_index_encode[OF k l] nat_list_encode_decode[OF e]
  show ?thesis by simp
qed

lemma decode_machine_length:
  assumes e: "e \<in> nat"
  shows "length(decode_machine(e)) = length(nat_list_decode(e))"
  unfolding decode_machine_def decode_machine_list_def
  using nat_list_decode_type[OF e] by simp

lemma decode_machine_nth:
  assumes e: "e \<in> nat" and k: "k \<in> nat"
    and index: "k < length(decode_machine(e))"
  shows "nth(k,decode_machine(e)) =
    decode_instruction(code_nth(k,e))"
proof -
  from e have l: "nat_list_decode(e) \<in> list(nat)"
    by (rule nat_list_decode_type)
  from index decode_machine_length[OF e] have bound:
    "k < length(nat_list_decode(e))" by simp
  from e k index l bound show ?thesis
    unfolding decode_machine_def decode_machine_list_def
    by (simp add: code_nth_decode[OF e k])
qed

definition pr_machine_reverse_index :: i where
  "pr_machine_reverse_index \<equiv>
    COMP(pr_diff,[PROJ(2),COMP(SC,[PROJ(1)])])"

lemma pr_machine_reverse_index_in_prim_rec [TC]:
  "pr_machine_reverse_index \<in> prim_rec"
  unfolding pr_machine_reverse_index_def by typecheck

lemma pr_machine_reverse_index_apply:
  assumes acc: "r \<in> nat" and count: "k \<in> nat"
    and machine: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_machine_reverse_index`Cons(r,Cons(k,Cons(e,l))) =
    e #- succ(k)"
  using acc count machine tail unfolding pr_machine_reverse_index_def
  by (simp add: COMP_2 COMP_1 PROJ_0 PROJ_1 PROJ_2 SC pr_diff_apply)

definition pr_machine_present :: i where
  "pr_machine_present \<equiv>
    COMP(pr_list_has_index,[pr_machine_reverse_index,PROJ(2)])"

lemma pr_machine_present_in_prim_rec [TC]:
  "pr_machine_present \<in> prim_rec"
  unfolding pr_machine_present_def by typecheck

lemma pr_machine_present_apply:
  assumes acc: "r \<in> nat" and count: "k \<in> nat"
    and machine: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_machine_present`Cons(r,Cons(k,Cons(e,l))) =
    code_has_index(e #- succ(k),e)"
  using acc count machine tail unfolding pr_machine_present_def
  by (simp add: COMP_2 PROJ_2 pr_machine_reverse_index_apply
      pr_list_has_index_apply)

definition pr_machine_element :: i where
  "pr_machine_element \<equiv>
    COMP(pr_list_nth,[pr_machine_reverse_index,PROJ(2)])"

lemma pr_machine_element_in_prim_rec [TC]:
  "pr_machine_element \<in> prim_rec"
  unfolding pr_machine_element_def by typecheck

lemma pr_machine_element_apply:
  assumes acc: "r \<in> nat" and count: "k \<in> nat"
    and machine: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_machine_element`Cons(r,Cons(k,Cons(e,l))) =
    code_nth(e #- succ(k),e)"
  using acc count machine tail unfolding pr_machine_element_def
  by (simp add: COMP_2 PROJ_2 pr_machine_reverse_index_apply
      pr_list_nth_apply)

definition pr_machine_name_step :: i where
  "pr_machine_name_step \<equiv>
    COMP(pr_if_zero,
      [pr_machine_present,PROJ(0),
       COMP(pr_list_name_cons,
         [COMP(pr_instr_name_code,[pr_machine_element]),PROJ(0)])])"

lemma pr_machine_name_step_in_prim_rec [TC]:
  "pr_machine_name_step \<in> prim_rec"
  unfolding pr_machine_name_step_def by typecheck

lemma pr_machine_name_step_apply:
  assumes q: "q \<in> formula" and k: "k \<in> nat"
    and e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_machine_name_step`Cons(formula_code(q),Cons(k,Cons(e,l))) =
    (if code_has_index(e #- succ(k),e) = 0 then formula_code(q)
     else formula_code(Exists(And(
       instr_name_fm(decode_instruction(code_nth(e #- succ(k),e))),
       Exists(And(q,Cons_fm(1,0,2)))))))"
proof -
  let ?j = "e #- succ(k)"
  from e k have j: "?j \<in> nat" by typecheck
  from j e have selected: "code_nth(?j,e) \<in> nat"
    by (rule code_nth_type)
  from selected have ins: "decode_instruction(code_nth(?j,e)) \<in> instruction"
    by (rule decode_instruction_type)
  from ins have item:
    "instr_name_fm(decode_instruction(code_nth(?j,e))) \<in> formula"
    by (rule instr_name_fm_type)
  have cons: "Cons_fm(1,0,2) \<in> formula" by typecheck
  from q cons have inner: "Exists(And(q,Cons_fm(1,0,2))) \<in> formula"
    by typecheck
  from item inner have combined:
    "Exists(And(instr_name_fm(decode_instruction(code_nth(?j,e))),
      Exists(And(q,Cons_fm(1,0,2))))) \<in> formula"
    by typecheck
  from q k e tail j selected item inner combined show ?thesis
    unfolding pr_machine_name_step_def
    by (simp add: COMP_3 COMP_2 COMP_1 PROJ_0 CONSTANT
        pr_machine_present_apply pr_machine_element_apply
        pr_instr_name_code_apply pr_list_name_cons_apply
        pr_if_zero_apply formula_code_type code_has_index_type)
qed

definition pr_machine_name_iter :: i where
  "pr_machine_name_iter \<equiv>
    PREC(CONSTANT(formula_code(Nil_fm(0))),pr_machine_name_step)"

lemma pr_machine_name_iter_in_prim_rec [TC]:
  "pr_machine_name_iter \<in> prim_rec"
  unfolding pr_machine_name_iter_def by (typecheck add: formula_code_type)

theorem pr_machine_name_iter_apply:
  assumes e: "e \<in> nat" and n: "n \<in> nat"
    and bound: "n \<le> e" and tail: "l \<in> list(nat)"
  shows "pr_machine_name_iter`Cons(n,Cons(e,l)) =
    formula_code(list_name_fm(instr_name_fm,
      drop(e #- n,decode_machine(e))))"
  using n bound
proof (induct n rule: nat_induct)
  case 0
  from e have machine: "decode_machine(e) \<in> list(instruction)"
    using decode_machine_type[OF e] unfolding machine_def by simp
  from decode_machine_length[OF e] length_nat_list_decode_le[OF e]
  have length: "length(decode_machine(e)) \<le> e" by simp
  from drop_all[OF e machine length] have empty:
    "drop(e,decode_machine(e)) = []" .
  from e tail empty show ?case
    unfolding pr_machine_name_iter_def
    by (simp add: PREC_0 CONSTANT)
next
  case (succ k)
  let ?P = "decode_machine(e)"
  let ?j = "e #- succ(k)"
  let ?t = "drop(succ(?j),?P)"
  let ?Q = "list_name_fm(instr_name_fm,?t)"
  from succ.prems have kbound: "k \<le> e"
    by (blast intro: leI dest: succ_leE)
  from succ.hyps(2)[OF kbound] have previous:
    "pr_machine_name_iter`Cons(k,Cons(e,l)) = formula_code(?Q)"
    using succ_diff_succ[OF succ.hyps(1) e succ.prems] by simp
  from e have machine: "?P \<in> list(instruction)"
    using decode_machine_type[OF e] unfolding machine_def by simp
  from succ.hyps(1) e have j: "?j \<in> nat" by typecheck
  from j machine have suffix: "?t \<in> list(instruction)" by typecheck
  from suffix have named: "?Q \<in> formula"
    by (rule list_name_fm_type) (rule instr_name_fm_type)
  from code_has_index_decode[OF e j] decode_machine_length[OF e]
  have present:
    "code_has_index(?j,e) = (if ?j < length(?P) then 1 else 0)"
    by simp
  have iteration:
    "pr_machine_name_iter`Cons(succ(k),Cons(e,l)) =
      pr_machine_name_step`Cons(
        pr_machine_name_iter`Cons(k,Cons(e,l)),Cons(k,Cons(e,l)))"
    unfolding pr_machine_name_iter_def
    using succ.hyps(1) e tail by (simp add: PREC_succ)
  from pr_machine_name_step_apply[OF named succ.hyps(1) e tail]
  have step:
    "pr_machine_name_step`Cons(formula_code(?Q),Cons(k,Cons(e,l))) =
      (if code_has_index(?j,e) = 0 then formula_code(?Q)
       else formula_code(Exists(And(
         instr_name_fm(decode_instruction(code_nth(?j,e))),
         Exists(And(?Q,Cons_fm(1,0,2)))))))" .
  show ?case
  proof (cases "?j < length(?P)")
    case True
    from drop_at_index[OF j machine] True have current:
      "drop(?j,?P) = Cons(nth(?j,?P),?t)" by simp
    from decode_machine_nth[OF e j True] have head:
      "decode_instruction(code_nth(?j,e)) = nth(?j,?P)" by simp
    from iteration previous step present current head True show ?thesis
      by simp
  next
    case False
    from drop_at_index[OF j machine] False have current:
      "drop(?j,?P) = []" by simp
    from current have tail_empty: "?t = []" by (simp add: drop_succ)
    from iteration previous step present current tail_empty False show ?thesis
      by simp
  qed
qed

definition pr_machine_name_code :: i where
  "pr_machine_name_code \<equiv>
    COMP(pr_machine_name_iter,[PROJ(0),PROJ(0)])"

lemma pr_machine_name_code_in_prim_rec [TC]:
  "pr_machine_name_code \<in> prim_rec"
  unfolding pr_machine_name_code_def by typecheck

theorem pr_machine_name_code_apply:
  assumes e: "e \<in> nat" and tail: "l \<in> list(nat)"
  shows "pr_machine_name_code`Cons(e,l) =
    formula_code(list_name_fm(instr_name_fm,decode_machine(e)))"
proof -
  from e have iter:
    "pr_machine_name_iter`[e,e] =
      formula_code(list_name_fm(instr_name_fm,decode_machine(e)))"
    using pr_machine_name_iter_apply[OF e e] by simp
  from e tail iter show ?thesis
    unfolding pr_machine_name_code_def by (simp add: COMP_2 PROJ_0)
qed

end
