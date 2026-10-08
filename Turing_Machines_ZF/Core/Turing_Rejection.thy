(*  Title:      Turing_Rejection.thy
    Author:     Tang Ziyi
*)

section \<open>Rejection Transformation\<close>

theory Turing_Rejection
  imports Turing_Decidability
begin

text \<open>Given a machine M, the construction reserves a fresh control
state above the states and instruction slots used by M. Transitions that
would terminate M enter that state. A blank scanned there terminates the
new machine; a 1 makes it loop. The projection lemmas relate runs of the
new machine to runs of M, including termination caused by a missing
instruction. The final theorem instantiates halting_diagonal with this
explicit finite instruction list.\<close>

subsection \<open>Control-State Bounds\<close>

consts control_bound :: "i \<Rightarrow> i"

primrec
  "control_bound([]) = 2"
  "control_bound(Cons(ins,M)) =
    succ(snd(ins) #+ control_bound(M))"

lemma control_bound_type [TC]:
  assumes machine_M: "M \<in> machine"
  shows "control_bound(M) \<in> nat"
  using machine_M unfolding machine_def
proof (induct M rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons ins M)
  note instruction = Cons.hyps(1)
  note tail = Cons.hyps(2)
  note bound_IH = Cons.hyps(3)
  from instruction have target: "snd(ins) \<in> nat"
    unfolding instruction_def by typecheck
  from bound_IH target show ?case
    by simp
qed

lemma one_lt_control_bound:
  assumes machine_M: "M \<in> machine"
  shows "1 < control_bound(M)"
  using machine_M unfolding machine_def
proof (induct M rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons ins M)
  note instruction = Cons.hyps(1)
  note tail = Cons.hyps(2)
  note bound_IH = Cons.hyps(3)
  from instruction have target: "snd(ins) \<in> nat"
    unfolding instruction_def by typecheck
  from tail have tail_machine: "M \<in> machine"
    unfolding machine_def .
  from control_bound_type[OF tail_machine] have bound_natural:
    "control_bound(M) \<in> nat" .
  from bound_natural have bound_le_sum:
    "control_bound(M) \<le> snd(ins) #+ control_bound(M)"
    by (rule add_le_self2)
  from bound_IH bound_le_sum have one_lt_sum:
    "1 < snd(ins) #+ control_bound(M)"
    by (rule lt_trans2)
  have zero_lt_one: "0 < 1" by simp
  from zero_lt_one one_lt_sum have
    "0 < snd(ins) #+ control_bound(M)"
    by (rule lt_trans)
  then show ?case by simp
qed

lemma length_lt_control_bound:
  assumes machine_M: "M \<in> machine"
  shows "length(M) < control_bound(M)"
  using machine_M unfolding machine_def
proof (induct M rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons ins M)
  note instruction = Cons.hyps(1)
  note tail = Cons.hyps(2)
  note bound_IH = Cons.hyps(3)
  from instruction have target: "snd(ins) \<in> nat"
    unfolding instruction_def by typecheck
  from tail have tail_machine: "M \<in> machine"
    unfolding machine_def .
  from control_bound_type[OF tail_machine] have bound_natural:
    "control_bound(M) \<in> nat" .
  from bound_natural have bound_le_sum:
    "control_bound(M) \<le> snd(ins) #+ control_bound(M)"
    by (rule add_le_self2)
  from bound_IH bound_le_sum have
    "length(M) < snd(ins) #+ control_bound(M)"
    by (rule lt_trans2)
  with target bound_natural show ?case by simp
qed

lemma control_bound_target:
  assumes machine_M: "M \<in> machine"
    and member: "ins \<in> set_of_list(M)"
  shows "snd(ins) < control_bound(M)"
  using machine_M member unfolding machine_def
proof (induct M rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons head M)
  note head_instruction = Cons.hyps(1)
  note tail = Cons.hyps(2)
  note bound_IH = Cons.hyps(3)
  from Cons.prems have occurrence:
    "ins = head \<or> ins \<in> set_of_list(M)"
    by simp
  from head_instruction have head_target: "snd(head) \<in> nat"
    unfolding instruction_def by typecheck
  from tail have tail_machine: "M \<in> machine"
    unfolding machine_def .
  show ?case
  proof (cases "ins = head")
    case True
    from head_target have
      "snd(head) \<le> snd(head) #+ control_bound(M)"
      by (rule add_le_self)
    with True head_target control_bound_type[OF tail_machine]
    show ?thesis by simp
  next
    case False
    with occurrence have tail_member: "ins \<in> set_of_list(M)"
      by blast
    from bound_IH[OF tail_member] have
      "snd(ins) < control_bound(M)" .
    also from control_bound_type[OF tail_machine] have
      "... \<le> snd(head) #+ control_bound(M)"
      by (rule add_le_self2)
    finally show ?thesis by simp
  qed
qed

lemma nth_in_set_of_list:
  assumes list: "xs \<in> list(A)"
    and natural: "j \<in> nat"
    and in_range: "j < length(xs)"
  shows "nth(j,xs) \<in> set_of_list(xs)"
  using list natural in_range set_of_list_conv_nth[OF list]
  by auto

lemma fetch_target_below_control:
  assumes machine_M: "M \<in> machine"
    and state: "q \<in> control_bound(M)"
    and nonfinal: "q \<noteq> final_state"
    and scanned: "b \<in> symbol"
  shows "snd(fetch(M,q,b)) < control_bound(M)"
proof (cases "slot(q,b) < length(M)")
  case True
  from machine_M have instructions: "M \<in> list(instruction)"
    unfolding machine_def .
  from machine_M have control: "control_bound(M) \<in> nat"
    by (rule control_bound_type)
  from state control have natural: "q \<in> nat"
    by (blast intro: Ord_trans)
  from slot_type[OF natural scanned] have slot_natural:
    "slot(q,b) \<in> nat" .
  from nth_in_set_of_list[OF instructions slot_natural True]
  have member: "nth(slot(q,b),M) \<in> set_of_list(M)" .
  from control_bound_target[OF machine_M member]
  show ?thesis using nonfinal True by simp
next
  case False
  have zero_lt_one: "0 < 1" by simp
  from zero_lt_one one_lt_control_bound[OF machine_M]
  have positive: "0 < control_bound(M)"
    by (rule lt_trans)
  show ?thesis using False positive by simp
qed

lemma step_state_below_control:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and state: "fst(c) \<in> control_bound(M)"
    and nonfinal: "fst(c) \<noteq> final_state"
  shows "fst(step(M,c)) \<in> control_bound(M)"
proof -
  from configuration have tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck
  from scan_type[OF tape] have scanned: "scan(snd(c)) \<in> symbol" .
  from fetch_target_below_control[
      OF machine_M state nonfinal scanned]
  have "snd(fetch(M,fst(c),scan(snd(c)))) < control_bound(M)" .
  then have "snd(fetch(M,fst(c),scan(snd(c)))) \<in> control_bound(M)"
    by (rule ltD)
  then show ?thesis
    unfolding step_def Let_def by simp
qed

lemma steps_state_below_control:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and initial: "fst(c) \<in> control_bound(M)"
    and time: "n \<in> nat"
    and nonfinal: "fst(steps(M,c,n)) \<noteq> final_state"
  shows "fst(steps(M,c,n)) \<in> control_bound(M)"
  using time nonfinal
proof (induct n rule: nat_induct)
  case 0
  with initial show ?case by simp
next
  case (succ n)
  from steps_type[OF machine_M configuration succ.hyps(1)]
  have current: "steps(M,c,n) \<in> configuration" .
  have current_nonfinal:
    "fst(steps(M,c,n)) \<noteq> final_state"
  proof
    assume current_final:
      "fst(steps(M,c,n)) = final_state"
    from step_final_configuration[OF current current_final] current_final
    have endpoint_final:
      "fst(steps(M,c,succ(n))) = final_state"
      by simp
    from succ.prems endpoint_final show False by contradiction
  qed
  from succ.hyps(2)[OF current_nonfinal] have current_below:
    "fst(steps(M,c,n)) \<in> control_bound(M)" .
  from step_state_below_control[
      OF machine_M current current_below current_nonfinal]
  show ?case by simp
qed

subsection \<open>Rejection Transform\<close>

definition redirect_final :: "[i,i] \<Rightarrow> i" where
  "redirect_final(k,ins) \<equiv>
    \<langle>fst(ins),if snd(ins) = final_state then k else snd(ins)\<rangle>"

definition rejecting_entry :: "[i,i] \<Rightarrow> i" where
  "rejecting_entry(M,j) \<equiv>
    let k = control_bound(M)
    in if j < length(M) then
         redirect_final(k,nth(j,M))
       else if j = slot(k,blank_symbol) then
         \<langle>nop,final_state\<rangle>
       else
         \<langle>nop,k\<rangle>"

definition rejecting_machine :: "i \<Rightarrow> i" where
  "rejecting_machine(M) \<equiv>
    map(\<lambda>j. rejecting_entry(M,j),
      upt(0,2 #* control_bound(M)))"

lemma redirect_final_type [TC]:
  assumes control: "k \<in> nat"
    and instruction: "ins \<in> instruction"
  shows "redirect_final(k,ins) \<in> instruction"
  using control instruction unfolding redirect_final_def instruction_def
  by typecheck

lemma redirect_final_nonfinal_eq:
  assumes instruction: "ins \<in> instruction"
    and nonfinal: "snd(ins) \<noteq> final_state"
  shows "redirect_final(k,ins) = ins"
proof -
  from instruction have pair: "\<langle>fst(ins),snd(ins)\<rangle> = ins"
    unfolding instruction_def by (rule Pair_fst_snd_eq)
  from nonfinal pair show ?thesis
    unfolding redirect_final_def by simp
qed

lemma rejecting_entry_type [TC]:
  assumes machine_M: "M \<in> machine"
    and natural: "j \<in> nat"
  shows "rejecting_entry(M,j) \<in> instruction"
proof -
  from machine_M have instructions: "M \<in> list(instruction)"
    unfolding machine_def .
  from machine_M have control: "control_bound(M) \<in> nat"
    by (rule control_bound_type)
  show ?thesis
  proof (cases "j < length(M)")
    case True
    from nth_type[OF instructions True] have
      "nth(j,M) \<in> instruction" .
    with control True show ?thesis
      unfolding rejecting_entry_def Let_def
      by (simp add: redirect_final_type)
  next
    case False
    with control show ?thesis
      unfolding rejecting_entry_def Let_def instruction_def
      by simp
  qed
qed

lemma rejecting_machine_type [TC]:
  assumes machine_M: "M \<in> machine"
  shows "rejecting_machine(M) \<in> machine"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by (rule control_bound_type)
  have indices:
    "upt(0,2 #* control_bound(M)) \<in> list(nat)"
    using control by typecheck
  have "map(\<lambda>j. rejecting_entry(M,j),
      upt(0,2 #* control_bound(M))) \<in> list(instruction)"
    using indices by (rule map_type) (rule rejecting_entry_type[OF machine_M])
  then show ?thesis
    unfolding rejecting_machine_def machine_def .
qed

lemma length_rejecting_machine [simp]:
  assumes machine_M: "M \<in> machine"
  shows "length(rejecting_machine(M)) = 2 #* control_bound(M)"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by (rule control_bound_type)
  show ?thesis
    unfolding rejecting_machine_def using control by simp
qed

lemma nth_rejecting_machine:
  assumes machine_M: "M \<in> machine"
    and natural: "j \<in> nat"
    and in_range: "j < 2 #* control_bound(M)"
  shows "nth(j,rejecting_machine(M)) = rejecting_entry(M,j)"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by (rule control_bound_type)
  have indices:
    "upt(0,2 #* control_bound(M)) \<in> list(nat)"
    using control by typecheck
  from natural in_range control show ?thesis
    unfolding rejecting_machine_def
    using nth_map[OF indices, of j "\<lambda>j. rejecting_entry(M,j)"]
    by simp
qed

subsection \<open>Slot Bounds\<close>

lemma slot_lt_twice_state:
  assumes state: "q \<in> nat"
    and nonfinal: "q \<noteq> final_state"
    and scanned: "b \<in> symbol"
  shows "slot(q,b) < 2 #* q"
  using state
proof (cases rule: natE)
  case 0
  with nonfinal show ?thesis by contradiction
next
  case (succ p)
  from scanned have "b = blank_symbol \<or> b = one_symbol"
    unfolding symbol_def by auto
  with succ show ?thesis
    unfolding slot_def by (auto simp add: add_ac)
qed

lemma slot_before_later_state:
  assumes later: "k \<in> nat"
    and earlier: "q \<in> k"
    and nonfinal: "q \<noteq> final_state"
    and scanned: "b \<in> symbol"
  shows "slot(q,b) < slot(k,blank_symbol)"
  using later earlier
proof (cases rule: natE)
  case 0
  with earlier show ?thesis by simp
next
  case (succ r)
  from earlier succ have state: "q \<in> nat"
    by (blast intro: Ord_trans)
  from earlier succ have state_le: "q \<le> r"
    by (auto simp add: le_iff intro: ltI nat_into_Ord)
  from mult_le_mono1[OF state_le succ(1), of 2]
  have twice_le: "2 #* q \<le> 2 #* r"
    by (simp add: mult_commute)
  from slot_lt_twice_state[OF state nonfinal scanned] twice_le
  have "slot(q,b) < 2 #* r"
    by (rule lt_trans2)
  with succ show ?thesis by simp
qed

lemma slot_control_in_range:
  assumes machine_M: "M \<in> machine"
    and state: "q \<in> succ(control_bound(M))"
    and nonfinal: "q \<noteq> final_state"
    and scanned: "b \<in> symbol"
  shows "slot(q,b) < 2 #* control_bound(M)"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by (rule control_bound_type)
  from state control have state_natural: "q \<in> nat"
    by (blast intro: Ord_trans)
  from state have below_or_control:
    "q \<in> control_bound(M) \<or> q = control_bound(M)"
    by auto
  show ?thesis
  proof (cases "q = control_bound(M)")
    case True
    from slot_lt_twice_state[OF state_natural nonfinal scanned]
    show ?thesis using True by simp
  next
    case False
    with below_or_control have below: "q \<in> control_bound(M)"
      by blast
    from one_lt_control_bound[OF machine_M] have control_nonfinal:
      "control_bound(M) \<noteq> final_state"
      by auto
    from slot_before_later_state[OF control below nonfinal scanned]
    have before: "slot(q,b) < slot(control_bound(M),blank_symbol)" .
    from slot_lt_twice_state[OF control control_nonfinal symbol_type(1)]
    have checker_in_range:
      "slot(control_bound(M),blank_symbol) <
        2 #* control_bound(M)" .
    from before checker_in_range show ?thesis
      by (rule lt_trans)
  qed
qed

lemma state_le_blank_slot:
  assumes state: "k \<in> nat"
    and above_initial: "1 < k"
  shows "k \<le> slot(k,blank_symbol)"
  using state
proof (cases rule: natE)
  case 0
  with above_initial show ?thesis by simp
next
  case (succ r)
  from succ have r_natural: "r \<in> nat" by simp
  from succ have k_successor: "k = succ(r)" by simp
  from r_natural show ?thesis
  proof (cases rule: natE)
    case 0
    with k_successor above_initial show ?thesis by simp
  next
    case (succ s)
    with k_successor show ?thesis
      unfolding slot_def by (simp add: add_le_self)
  qed
qed

lemma checker_slot_after_machine:
  assumes machine_M: "M \<in> machine"
    and scanned: "b \<in> symbol"
  shows "\<not> slot(control_bound(M),b) < length(M)"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by (rule control_bound_type)
  from length_lt_control_bound[OF machine_M] have
    length_le_control: "length(M) \<le> control_bound(M)"
    by (rule leI)
  from state_le_blank_slot[OF control one_lt_control_bound[OF machine_M]]
  have control_le_blank:
    "control_bound(M) \<le> slot(control_bound(M),blank_symbol)" .
  from length_le_control control_le_blank have length_le_blank:
    "length(M) \<le> slot(control_bound(M),blank_symbol)"
    by (rule le_trans)
  from scanned have cases:
    "b = blank_symbol \<or> b = one_symbol"
    unfolding symbol_def by auto
  from cases have blank_le_scanned:
    "slot(control_bound(M),blank_symbol) \<le>
      slot(control_bound(M),b)"
    unfolding slot_def by auto
  from length_le_blank blank_le_scanned have
    "length(M) \<le> slot(control_bound(M),b)"
    by (rule le_trans)
  then show ?thesis by (rule le_imp_not_lt)
qed

lemma fetch_rejecting_machine:
  assumes machine_M: "M \<in> machine"
    and state: "q \<in> control_bound(M)"
    and nonfinal: "q \<noteq> final_state"
    and scanned: "b \<in> symbol"
  shows "fetch(rejecting_machine(M),q,b) =
    redirect_final(control_bound(M),fetch(M,q,b))"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by (rule control_bound_type)
  from state control have natural: "q \<in> nat"
    by (blast intro: Ord_trans)
  from slot_type[OF natural scanned] have slot_natural:
    "slot(q,b) \<in> nat" .
  from state have bounded:
    "q \<in> succ(control_bound(M))"
    by (rule succI2)
  from slot_control_in_range[OF machine_M bounded nonfinal scanned]
  have slot_range:
    "slot(q,b) < 2 #* control_bound(M)" .
  from nth_rejecting_machine[OF machine_M slot_natural slot_range]
  have table_entry:
    "nth(slot(q,b),rejecting_machine(M)) =
      rejecting_entry(M,slot(q,b))" .
  from slot_range length_rejecting_machine[OF machine_M]
  have transformed_range:
    "slot(q,b) < length(rejecting_machine(M))"
    by simp
  from fetch_in_range[OF nonfinal transformed_range]
  have transformed_fetch:
    "fetch(rejecting_machine(M),q,b) =
      nth(slot(q,b),rejecting_machine(M))" .
  from slot_before_later_state[OF control state nonfinal scanned]
  have before_checker:
    "slot(q,b) \<noteq> slot(control_bound(M),blank_symbol)"
    by auto
  show ?thesis
  proof (cases "slot(q,b) < length(M)")
    case True
    from transformed_fetch table_entry True nonfinal show ?thesis
      unfolding rejecting_entry_def Let_def redirect_final_def
      by simp
  next
    case False
    from transformed_fetch table_entry before_checker False show ?thesis
      unfolding rejecting_entry_def Let_def redirect_final_def
      by simp
  qed
qed

lemma fetch_rejecting_checker:
  assumes machine_M: "M \<in> machine"
    and scanned: "b \<in> symbol"
  shows "fetch(rejecting_machine(M),control_bound(M),b) =
    (if b = blank_symbol then \<langle>nop,final_state\<rangle>
     else \<langle>nop,control_bound(M)\<rangle>)"
proof -
  let ?k = "control_bound(M)"
  from machine_M have control: "?k \<in> nat"
    by (rule control_bound_type)
  from one_lt_control_bound[OF machine_M] have nonfinal:
    "?k \<noteq> final_state"
    by auto
  from slot_type[OF control scanned] have slot_natural:
    "slot(?k,b) \<in> nat" .
  from slot_control_in_range[OF machine_M succI1 nonfinal scanned]
  have slot_range: "slot(?k,b) < 2 #* ?k" .
  from nth_rejecting_machine[OF machine_M slot_natural slot_range]
  have table_entry:
    "nth(slot(?k,b),rejecting_machine(M)) =
      rejecting_entry(M,slot(?k,b))" .
  from slot_range length_rejecting_machine[OF machine_M]
  have transformed_range:
    "slot(?k,b) < length(rejecting_machine(M))"
    by simp
  from fetch_in_range[OF nonfinal transformed_range]
  have transformed_fetch:
    "fetch(rejecting_machine(M),?k,b) =
      nth(slot(?k,b),rejecting_machine(M))" .
  from checker_slot_after_machine[OF machine_M scanned]
  have after_original: "\<not> slot(?k,b) < length(M)" .
  from scanned have cases:
    "b = blank_symbol \<or> b = one_symbol"
    unfolding symbol_def by auto
  from transformed_fetch table_entry after_original cases
  show ?thesis
    unfolding rejecting_entry_def Let_def slot_def
    by (auto simp add: add_ac)
qed

subsection \<open>Semantic Projection\<close>

definition erase_state :: "[i,i] \<Rightarrow> i" where
  "erase_state(k,q) \<equiv>
    if q = k then final_state else q"

definition erase_configuration :: "[i,i] \<Rightarrow> i" where
  "erase_configuration(k,c) \<equiv>
    \<langle>erase_state(k,fst(c)),snd(c)\<rangle>"

lemma erase_state_control [simp]:
  "erase_state(k,k) = final_state"
  unfolding erase_state_def by simp

lemma erase_state_below [simp]:
  assumes below: "q \<in> k"
  shows "erase_state(k,q) = q"
  using below unfolding erase_state_def
  by (auto dest: mem_imp_not_eq)

lemma erase_configuration_pair [simp]:
  "erase_configuration(k,\<langle>q,t\<rangle>) =
    \<langle>erase_state(k,q),t\<rangle>"
  unfolding erase_configuration_def by simp

lemma erase_configuration_type [TC]:
  assumes control: "k \<in> nat"
    and configuration: "c \<in> configuration"
  shows "erase_configuration(k,c) \<in> configuration"
proof -
  from configuration have state: "fst(c) \<in> nat"
    and tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck+
  show ?thesis
    unfolding erase_configuration_def erase_state_def configuration_def
    using control state tape by typecheck
qed

lemma erase_redirect_final:
  assumes below: "snd(ins) < k"
  shows "erase_state(k,snd(redirect_final(k,ins))) = snd(ins)"
proof -
  from below have target_not_control: "snd(ins) \<noteq> k"
    by auto
  show ?thesis
    unfolding erase_state_def redirect_final_def
    using target_not_control by auto
qed

lemma redirect_final_target_bound:
  assumes control: "k \<in> nat"
    and below: "snd(ins) < k"
  shows "snd(redirect_final(k,ins)) \<in> succ(k)"
proof (cases "snd(ins) = final_state")
  case True
  then show ?thesis
    unfolding redirect_final_def by simp
next
  case False
  from below have "snd(ins) \<in> k"
    by (rule ltD)
  with False show ?thesis
    unfolding redirect_final_def by auto
qed

lemma erase_configuration_below [simp]:
  assumes configuration: "c \<in> configuration"
    and below: "fst(c) \<in> k"
  shows "erase_configuration(k,c) = c"
proof -
  from configuration have pair: "\<langle>fst(c),snd(c)\<rangle> = c"
    unfolding configuration_def by (rule Pair_fst_snd_eq)
  show ?thesis
    unfolding erase_configuration_def erase_state_def
    using below pair by (auto dest: mem_imp_not_eq)
qed

lemma step_rejecting_running:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and state: "fst(c) \<in> control_bound(M)"
    and nonfinal: "fst(c) \<noteq> final_state"
  shows "erase_configuration(control_bound(M),
      step(rejecting_machine(M),c)) = step(M,c)"
proof -
  from configuration have tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck
  from scan_type[OF tape] have scanned:
    "scan(snd(c)) \<in> symbol" .
  from fetch_rejecting_machine[OF machine_M state nonfinal scanned]
  have transformed_fetch:
    "fetch(rejecting_machine(M),fst(c),scan(snd(c))) =
      redirect_final(control_bound(M),
        fetch(M,fst(c),scan(snd(c))))" .
  from fetch_target_below_control[OF machine_M state nonfinal scanned]
  have target:
    "snd(fetch(M,fst(c),scan(snd(c)))) < control_bound(M)" .
  from erase_redirect_final[OF target] have erased_target:
    "erase_state(control_bound(M),
      snd(redirect_final(control_bound(M),
        fetch(M,fst(c),scan(snd(c)))))) =
      snd(fetch(M,fst(c),scan(snd(c))))" .
  show ?thesis
    unfolding erase_configuration_def step_def Let_def
    using transformed_fetch erased_target
    unfolding redirect_final_def by simp
qed

lemma step_rejecting_checker:
  assumes machine_M: "M \<in> machine"
    and tape: "t \<in> tape"
  shows "erase_configuration(control_bound(M),
      step(rejecting_machine(M),
        \<langle>control_bound(M),t\<rangle>)) =
    \<langle>final_state,t\<rangle>"
proof -
  from scan_type[OF tape] have scanned: "scan(t) \<in> symbol" .
  from scanned have cases:
    "scan(t) = blank_symbol \<or> scan(t) = one_symbol"
    unfolding symbol_def by auto
  from fetch_rejecting_checker[OF machine_M scanned] cases
  show ?thesis
    unfolding step_def Let_def erase_configuration_def erase_state_def
      tm_update_def
    by auto
qed

lemma step_rejecting_erases:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and bounded: "fst(c) \<in> succ(control_bound(M))"
  shows "erase_configuration(control_bound(M),
      step(rejecting_machine(M),c)) =
    step(M,erase_configuration(control_bound(M),c))"
proof -
  from configuration obtain q t where tape: "t \<in> tape"
    and representation: "c = \<langle>q,t\<rangle>"
    unfolding configuration_def by auto
  from bounded representation have state_bounded:
    "q \<in> succ(control_bound(M))"
    by simp
  show ?thesis
  proof (cases "q = final_state")
    case True
    from one_lt_control_bound[OF machine_M] have control_nonzero:
      "control_bound(M) \<noteq> final_state"
      by auto
    from True control_nonzero show ?thesis
      unfolding representation
      unfolding erase_configuration_def erase_state_def
      by simp
  next
    case False
    show ?thesis
    proof (cases "q = control_bound(M)")
      case True
      from True representation have checker_configuration:
        "c = \<langle>control_bound(M),t\<rangle>"
        by simp
      from step_rejecting_checker[OF machine_M tape]
      show ?thesis
        unfolding checker_configuration by simp
    next
      case control_False: False
      from state_bounded control_False have below:
        "q \<in> control_bound(M)"
        by auto
      from representation below have state_below:
        "fst(c) \<in> control_bound(M)"
        by simp
      from representation False have state_nonfinal:
        "fst(c) \<noteq> final_state"
        by simp
      from step_rejecting_running[
          OF machine_M configuration state_below state_nonfinal]
        erase_configuration_below[OF configuration state_below]
      show ?thesis by simp
    qed
  qed
qed

lemma step_rejecting_bounded:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and bounded: "fst(c) \<in> succ(control_bound(M))"
  shows "fst(step(rejecting_machine(M),c)) \<in>
    succ(control_bound(M))"
proof -
  let ?k = "control_bound(M)"
  from machine_M have control: "?k \<in> nat"
    by (rule control_bound_type)
  from control have zero_bounded: "0 \<in> succ(?k)"
    by (rule nat_0_le[THEN ltD])
  from configuration obtain q t where tape: "t \<in> tape"
    and representation: "c = \<langle>q,t\<rangle>"
    unfolding configuration_def by auto
  from bounded representation have state_bounded:
    "q \<in> succ(?k)"
    by simp
  show ?thesis
  proof (cases "q = final_state")
    case True
    with representation zero_bounded show ?thesis by simp
  next
    case nonfinal: False
    show ?thesis
    proof (cases "q = ?k")
      case True
      from scan_type[OF tape] have scanned: "scan(t) \<in> symbol" .
      from scanned have symbols:
        "scan(t) = blank_symbol \<or> scan(t) = one_symbol"
        unfolding symbol_def by auto
      from fetch_rejecting_checker[OF machine_M scanned]
        symbols True zero_bounded
      show ?thesis
        unfolding representation step_def Let_def by auto
    next
      case control_False: False
      from state_bounded control_False have below: "q \<in> ?k"
        by auto
      from scan_type[OF tape] have scanned: "scan(t) \<in> symbol" .
      from fetch_rejecting_machine[OF machine_M below nonfinal scanned]
      have transformed_fetch:
        "fetch(rejecting_machine(M),q,scan(t)) =
          redirect_final(?k,fetch(M,q,scan(t)))" .
      from fetch_target_below_control[OF machine_M below nonfinal scanned]
      have target_below:
        "snd(fetch(M,q,scan(t))) < ?k" .
      from redirect_final_target_bound[OF control target_below]
      have target_bounded:
        "snd(redirect_final(?k,fetch(M,q,scan(t)))) \<in> succ(?k)"
        .
      from transformed_fetch target_bounded show ?thesis
        unfolding representation step_def Let_def by simp
    qed
  qed
qed

lemma steps_rejecting_bounded:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and bounded: "fst(c) \<in> succ(control_bound(M))"
    and time: "n \<in> nat"
  shows "fst(steps(rejecting_machine(M),c,n)) \<in>
    succ(control_bound(M))"
  using time
proof (induct n rule: nat_induct)
  case 0
  with bounded show ?case by simp
next
  case (succ n)
  from rejecting_machine_type[OF machine_M] configuration succ.hyps(1)
  have current_configuration:
    "steps(rejecting_machine(M),c,n) \<in> configuration"
    by (rule steps_type)
  from step_rejecting_bounded[
      OF machine_M current_configuration succ.hyps(2)]
  show ?case by simp
qed

lemma steps_rejecting_erases:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and bounded: "fst(c) \<in> succ(control_bound(M))"
    and time: "n \<in> nat"
  shows "erase_configuration(control_bound(M),
      steps(rejecting_machine(M),c,n)) =
    steps(M,erase_configuration(control_bound(M),c),n)"
  using time
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ n)
  from rejecting_machine_type[OF machine_M] configuration succ.hyps(1)
  have current_configuration:
    "steps(rejecting_machine(M),c,n) \<in> configuration"
    by (rule steps_type)
  from steps_rejecting_bounded[
      OF machine_M configuration bounded succ.hyps(1)]
  have current_bounded:
    "fst(steps(rejecting_machine(M),c,n)) \<in>
      succ(control_bound(M))" .
  have "erase_configuration(control_bound(M),
      steps(rejecting_machine(M),c,succ(n))) =
    erase_configuration(control_bound(M),
      step(rejecting_machine(M),
        steps(rejecting_machine(M),c,n)))"
    by simp
  also from step_rejecting_erases[
      OF machine_M current_configuration current_bounded]
  have "... = step(M,erase_configuration(control_bound(M),
      steps(rejecting_machine(M),c,n)))" .
  also from succ.hyps(2) have
    "... = step(M,
      steps(M,erase_configuration(control_bound(M),c),n))"
    by simp
  also have "... =
      steps(M,erase_configuration(control_bound(M),c),succ(n))"
    by simp
  finally show ?case .
qed

lemma redirect_final_nonfinal:
  assumes control_nonfinal: "k \<noteq> final_state"
  shows "snd(redirect_final(k,ins)) \<noteq> final_state"
  using control_nonfinal unfolding redirect_final_def by auto

lemma step_rejecting_final_blank:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and bounded: "fst(c) \<in> succ(control_bound(M))"
    and final_blank:
      "fst(c) = final_state \<Longrightarrow>
        scan(snd(c)) = blank_symbol"
    and next_final:
      "fst(step(rejecting_machine(M),c)) = final_state"
  shows "scan(snd(step(rejecting_machine(M),c))) = blank_symbol"
proof -
  let ?k = "control_bound(M)"
  from one_lt_control_bound[OF machine_M] have control_nonfinal:
    "?k \<noteq> final_state"
    by auto
  from configuration obtain q t where tape: "t \<in> tape"
    and representation: "c = \<langle>q,t\<rangle>"
    unfolding configuration_def by auto
  from bounded representation have state_bounded: "q \<in> succ(?k)"
    by simp
  show ?thesis
  proof (cases "q = final_state")
    case True
    from final_blank True representation have scanned:
      "scan(t) = blank_symbol"
      by simp
    from True representation scanned show ?thesis by simp
  next
    case nonfinal: False
    show ?thesis
    proof (cases "q = ?k")
      case True
      from scan_type[OF tape] have scanned_type: "scan(t) \<in> symbol" .
      from scanned_type have scanned_cases:
        "scan(t) = blank_symbol \<or> scan(t) = one_symbol"
        unfolding symbol_def by auto
      from fetch_rejecting_checker[OF machine_M scanned_type]
        scanned_cases True representation next_final control_nonfinal
      show ?thesis
        unfolding step_def Let_def tm_update_def by auto
    next
      case control_False: False
      from state_bounded control_False have below: "q \<in> ?k"
        by auto
      from scan_type[OF tape] have scanned_type: "scan(t) \<in> symbol" .
      from fetch_rejecting_machine[OF machine_M below nonfinal scanned_type]
      have transformed_fetch:
        "fetch(rejecting_machine(M),q,scan(t)) =
          redirect_final(?k,fetch(M,q,scan(t)))" .
      from redirect_final_nonfinal[OF control_nonfinal, of
          "fetch(M,q,scan(t))"]
      have transformed_nonfinal:
        "snd(redirect_final(?k,fetch(M,q,scan(t)))) \<noteq> final_state" .
      from transformed_fetch transformed_nonfinal representation next_final
      show ?thesis
        unfolding step_def Let_def by simp
    qed
  qed
qed

lemma steps_rejecting_final_blank:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and bounded: "fst(c) \<in> succ(control_bound(M))"
    and initial_final_blank:
      "fst(c) = final_state \<Longrightarrow>
        scan(snd(c)) = blank_symbol"
    and time: "n \<in> nat"
    and final:
      "fst(steps(rejecting_machine(M),c,n)) = final_state"
  shows "scan(snd(steps(rejecting_machine(M),c,n))) = blank_symbol"
  using time final
proof (induct n rule: nat_induct)
  case 0
  from 0 initial_final_blank show ?case by simp
next
  case (succ n)
  from rejecting_machine_type[OF machine_M] configuration succ.hyps(1)
  have current_configuration:
    "steps(rejecting_machine(M),c,n) \<in> configuration"
    by (rule steps_type)
  from steps_rejecting_bounded[
      OF machine_M configuration bounded succ.hyps(1)]
  have current_bounded:
    "fst(steps(rejecting_machine(M),c,n)) \<in>
      succ(control_bound(M))" .
  from step_rejecting_final_blank[
      OF machine_M current_configuration current_bounded succ.hyps(2)]
    succ.prems
  show ?case by simp
qed

lemma initial_state_below_control:
  assumes machine_M: "M \<in> machine"
  shows "initial_state \<in> control_bound(M)"
  using one_lt_control_bound[OF machine_M] by (rule ltD)

lemma steps_rejecting_initial_bounded:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and time: "n \<in> nat"
  shows "fst(steps(rejecting_machine(M),initial_config(x),n)) \<in>
    succ(control_bound(M))"
proof -
  from initial_state_below_control[OF machine_M] have bounded:
    "fst(initial_config(x)) \<in> succ(control_bound(M))"
    by auto
  from steps_rejecting_bounded[
      OF machine_M initial_config_type[OF input] bounded time]
  show ?thesis .
qed

lemma steps_rejecting_initial_erases:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and time: "n \<in> nat"
  shows "erase_configuration(control_bound(M),
      steps(rejecting_machine(M),initial_config(x),n)) =
    steps(M,initial_config(x),n)"
proof -
  from initial_state_below_control[OF machine_M] have below:
    "fst(initial_config(x)) \<in> control_bound(M)"
    by simp
  from below have bounded:
    "fst(initial_config(x)) \<in> succ(control_bound(M))"
    by auto
  from erase_configuration_below[OF initial_config_type[OF input] below]
  have initial_erases:
    "erase_configuration(control_bound(M),initial_config(x)) =
      initial_config(x)" .
  from steps_rejecting_erases[
      OF machine_M initial_config_type[OF input] bounded time]
    initial_erases
  show ?thesis by simp
qed

lemma steps_rejecting_initial_final_blank:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and time: "n \<in> nat"
    and final:
      "fst(steps(rejecting_machine(M),initial_config(x),n)) = final_state"
  shows "scan(snd(steps(rejecting_machine(M),initial_config(x),n))) =
    blank_symbol"
proof -
  from initial_state_below_control[OF machine_M] have bounded:
    "fst(initial_config(x)) \<in> succ(control_bound(M))"
    by auto
  have initial_not_final:
    "fst(initial_config(x)) = final_state \<Longrightarrow>
      scan(snd(initial_config(x))) = blank_symbol"
    by simp
  from steps_rejecting_final_blank[
      OF machine_M initial_config_type[OF input] bounded
        initial_not_final time final]
  show ?thesis .
qed

lemma step_rejecting_checker_blank:
  assumes machine_M: "M \<in> machine"
    and tape: "t \<in> tape"
    and blank: "scan(t) = blank_symbol"
  shows "step(rejecting_machine(M),
      \<langle>control_bound(M),t\<rangle>) =
    \<langle>final_state,t\<rangle>"
proof -
  from fetch_rejecting_checker[OF machine_M symbol_type(1)]
  have checker_fetch:
    "fetch(rejecting_machine(M),control_bound(M),blank_symbol) =
      \<langle>nop,final_state\<rangle>"
    by simp
  from blank checker_fetch show ?thesis
    unfolding step_def Let_def tm_update_def by simp
qed

lemma rejecting_machine_halts_imp_yields_blank:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and halts: "halts_on(rejecting_machine(M),x)"
  shows "yields(M,x,blank_symbol)"
proof -
  from halts obtain n where time: "n \<in> nat"
    and transformed_final:
      "fst(steps(rejecting_machine(M),initial_config(x),n)) =
        final_state"
    unfolding halts_on_def by auto
  from steps_rejecting_initial_erases[OF machine_M input time]
  have projection:
    "erase_configuration(control_bound(M),
      steps(rejecting_machine(M),initial_config(x),n)) =
      steps(M,initial_config(x),n)" .
  from projection have reverse_projection:
    "steps(M,initial_config(x),n) =
      erase_configuration(control_bound(M),
        steps(rejecting_machine(M),initial_config(x),n))"
    by (rule sym)
  from one_lt_control_bound[OF machine_M] have control_nonfinal:
    "control_bound(M) \<noteq> final_state"
    by auto
  from transformed_final control_nonfinal have original_final:
    "fst(steps(M,initial_config(x),n)) = final_state"
    by (simp add: reverse_projection erase_configuration_def erase_state_def)
  from steps_rejecting_initial_final_blank[
      OF machine_M input time transformed_final]
  have transformed_blank:
    "scan(snd(steps(rejecting_machine(M),initial_config(x),n))) =
      blank_symbol" .
  from transformed_blank have original_blank:
    "scan(snd(steps(M,initial_config(x),n))) = blank_symbol"
    by (simp add: reverse_projection erase_configuration_def)
  show "yields(M,x,blank_symbol)"
    unfolding yields_def
    using machine_M input time original_final original_blank
    by auto
qed

lemma yields_blank_imp_rejecting_machine_halts:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and rejection: "yields(M,x,blank_symbol)"
  shows "halts_on(rejecting_machine(M),x)"
proof -
  from rejection obtain n where time: "n \<in> nat"
    and original_final:
      "fst(steps(M,initial_config(x),n)) = final_state"
    and original_blank:
      "scan(snd(steps(M,initial_config(x),n))) = blank_symbol"
    unfolding yields_def by auto
  let ?z = "steps(rejecting_machine(M),initial_config(x),n)"
  from rejecting_machine_type[OF machine_M]
    initial_config_type[OF input] time
  have transformed_configuration: "?z \<in> configuration"
    by (rule steps_type)
  from transformed_configuration have transformed_tape:
    "snd(?z) \<in> tape"
    unfolding configuration_def by typecheck
  from transformed_configuration have transformed_pair:
    "\<langle>fst(?z),snd(?z)\<rangle> = ?z"
    unfolding configuration_def by (rule Pair_fst_snd_eq)
  from steps_rejecting_initial_erases[OF machine_M input time]
  have projection:
    "erase_configuration(control_bound(M),?z) =
      steps(M,initial_config(x),n)" .
  from projection original_final have erased_configuration_final:
    "fst(erase_configuration(control_bound(M),?z)) = final_state"
    by simp
  from erased_configuration_final have erased_final:
    "erase_state(control_bound(M),fst(?z)) = final_state"
    unfolding erase_configuration_def by simp
  from erased_final have state_cases:
    "fst(?z) = final_state \<or>
      fst(?z) = control_bound(M)"
    unfolding erase_state_def by auto
  from projection original_blank have erased_configuration_blank:
    "scan(snd(erase_configuration(control_bound(M),?z))) = blank_symbol"
    by simp
  from erased_configuration_blank have transformed_blank:
    "scan(snd(?z)) = blank_symbol"
    unfolding erase_configuration_def by simp
  show "halts_on(rejecting_machine(M),x)"
  proof (cases "fst(?z) = final_state")
    case True
    show ?thesis
      unfolding halts_on_def
      using rejecting_machine_type[OF machine_M] input time True
      by auto
  next
    case False
    with state_cases have checker:
      "fst(?z) = control_bound(M)"
      by blast
    from transformed_pair checker have checker_configuration:
      "?z = \<langle>control_bound(M),snd(?z)\<rangle>"
      by simp
    from step_rejecting_checker_blank[
      OF machine_M transformed_tape transformed_blank]
    have next_final:
      "fst(steps(rejecting_machine(M),initial_config(x),succ(n))) =
        final_state"
      unfolding checker_configuration[symmetric] by simp
    from time have next_time: "succ(n) \<in> nat"
      by simp
    show ?thesis
      unfolding halts_on_def
      using rejecting_machine_type[OF machine_M] input next_time next_final
      by blast
  qed
qed

theorem rejecting_machine_halts_iff_yields_blank:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
  shows "halts_on(rejecting_machine(M),x) \<longleftrightarrow>
    yields(M,x,blank_symbol)"
proof
  assume "halts_on(rejecting_machine(M),x)"
  then show "yields(M,x,blank_symbol)"
    by (rule rejecting_machine_halts_imp_yields_blank[
      OF machine_M input])
next
  assume "yields(M,x,blank_symbol)"
  then show "halts_on(rejecting_machine(M),x)"
    by (rule yields_blank_imp_rejecting_machine_halts[
      OF machine_M input])
qed

theorem rejecting_machine_halts_iff_rejects_number:
  assumes machine_M: "M \<in> machine"
    and natural: "n \<in> nat"
  shows "halts_on(rejecting_machine(M),numeral_input(n)) \<longleftrightarrow>
    rejects_number(M,n)"
  unfolding rejects_number_def
  using rejecting_machine_halts_iff_yields_blank[
    OF machine_M numeral_input_type[OF natural]] .

interpretation rejection_diagonal: halting_diagonal rejecting_machine
proof
  fix D
  assume "D \<in> machine"
  then show "rejecting_machine(D) \<in> machine"
    by (rule rejecting_machine_type)
next
  fix D n
  assume machine_D: "D \<in> machine"
    and natural: "n \<in> nat"
  show "halts_on(rejecting_machine(D),numeral_input(n)) \<longleftrightarrow>
    rejects_number(D,n)"
    by (rule rejecting_machine_halts_iff_rejects_number[
      OF machine_D natural])
qed

theorem self_halting_not_tm_decidable:
  "\<not> tm_decidable(self_halting)"
  by (rule rejection_diagonal.self_halting_not_tm_decidable)

end
