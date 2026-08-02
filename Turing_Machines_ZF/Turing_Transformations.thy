(*  Title:      Turing_Transformations.thy
    Author:     Tang Ziyi
*)

section \<open>Machine Transformations\<close>

theory Turing_Transformations
  imports Turing_Decidability
begin

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
    by (blast intro: Ord_trans Ord_nat)
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
    by (blast intro: Ord_trans Ord_nat)
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
    by (blast intro: Ord_trans Ord_nat)
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
    by (blast intro: Ord_trans Ord_nat)
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
      update_def
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
        unfolding step_def Let_def update_def by auto
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
    unfolding step_def Let_def update_def by simp
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

subsection \<open>Input Loading\<close>

definition write_symbol :: "i \<Rightarrow> i" where
  "write_symbol(b) \<equiv>
    if b = blank_symbol then write_blank else write_one"

lemma write_symbol_type [TC]:
  assumes scanned: "b \<in> symbol"
  shows "write_symbol(b) \<in> action"
  using scanned unfolding write_symbol_def symbol_def by auto

lemma update_write_symbol:
  assumes scanned: "b \<in> symbol"
  shows "update(write_symbol(b),\<langle>l,r\<rangle>) =
    \<langle>l,Cons(b,tl(r))\<rangle>"
  using scanned unfolding write_symbol_def symbol_def by auto

lemma empty_left_tape_type [TC]:
  assumes right: "r \<in> list(symbol)"
  shows "\<langle>[],r\<rangle> \<in> tape"
proof (rule tapeI)
  show "[] \<in> list(symbol)" by simp
  show "r \<in> list(symbol)" by (rule right)
qed

consts action_semantics :: "i \<Rightarrow> i"

primrec
  "action_semantics([]) = id(tape)"
  "action_semantics(Cons(a,A)) =
    (\<lambda>t\<in>tape. action_semantics(A)`update(a,t))"

definition execute_actions :: "[i,i] \<Rightarrow> i" where
  "execute_actions(A,t) \<equiv> action_semantics(A)`t"

lemma action_semantics_type [TC]:
  assumes actions: "A \<in> list(action)"
  shows "action_semantics(A) \<in> tape \<rightarrow> tape"
  using actions
proof (induct A rule: list.induct)
  case Nil
  then show ?case by (simp add: id_type)
next
  case (Cons a A)
  note current_action = Cons.hyps(1)
  note tail_actions = Cons.hyps(2)
  note semantics_IH = Cons.hyps(3)
  have "(\<lambda>t\<in>tape. action_semantics(A)`update(a,t))
      \<in> tape \<rightarrow> tape"
  proof (rule lam_type)
    fix t
    assume tape: "t \<in> tape"
    from tape have "update(a,t) \<in> tape"
      by (rule update_type)
    with semantics_IH show "action_semantics(A)`update(a,t) \<in> tape"
      by (rule apply_type)
  qed
  then show ?case by simp
qed

lemma execute_actions_Nil [simp]:
  assumes tape: "t \<in> tape"
  shows "execute_actions([],t) = t"
  using tape unfolding execute_actions_def by simp

lemma execute_actions_Cons [simp]:
  assumes tape: "t \<in> tape"
  shows "execute_actions(Cons(a,A),t) =
    execute_actions(A,update(a,t))"
  using tape update_type[OF tape]
  unfolding execute_actions_def by simp

lemma execute_actions_type [TC]:
  assumes actions: "A \<in> list(action)"
    and tape: "t \<in> tape"
  shows "execute_actions(A,t) \<in> tape"
  using action_semantics_type[OF actions] tape
  unfolding execute_actions_def by (rule apply_type)

consts load_actions :: "i \<Rightarrow> i"

primrec
  "load_actions([]) = []"
  "load_actions(Cons(b,bs)) =
    Cons(move_left,Cons(write_symbol(b),load_actions(bs)))"

definition loader_actions :: "i \<Rightarrow> i" where
  "loader_actions(x) \<equiv> load_actions(rev(x))"

lemma load_actions_type [TC]:
  assumes symbols: "xs \<in> list(symbol)"
  shows "load_actions(xs) \<in> list(action)"
  using symbols
  by (induct xs rule: list.induct) (auto intro: write_symbol_type)

lemma loader_actions_type [TC]:
  assumes input: "x \<in> list(symbol)"
  shows "loader_actions(x) \<in> list(action)"
  using input unfolding loader_actions_def by typecheck

lemma length_load_actions [simp]:
  assumes symbols: "xs \<in> list(symbol)"
  shows "length(load_actions(xs)) = 2 #* length(xs)"
  using symbols
  by (induct xs rule: list.induct) simp_all

lemma length_loader_actions [simp]:
  assumes input: "x \<in> list(symbol)"
  shows "length(loader_actions(x)) = 2 #* length(x)"
  using input unfolding loader_actions_def by simp

lemma execute_load_actions:
  assumes symbols: "xs \<in> list(symbol)"
    and right: "r \<in> list(symbol)"
  shows "execute_actions(load_actions(xs),\<langle>[],r\<rangle>) =
    \<langle>[],rev(xs) @ r\<rangle>"
  using symbols right
proof (induct xs arbitrary: r rule: list.induct)
  case Nil
  from Nil.prems have initial_tape: "\<langle>[],r\<rangle> \<in> tape"
    by (rule empty_left_tape_type)
  from initial_tape show ?case by simp
next
  case (Cons b bs)
  note scanned = Cons.hyps(1)
  note tail_symbols = Cons.hyps(2)
  note execution_IH = Cons.hyps(3)
  from tail_symbols have reversed_tail:
    "rev(bs) \<in> list(symbol)"
    by (rule rev_type)
  from Cons.prems have right_symbols: "r \<in> list(symbol)" .
  from right_symbols have moved_right:
    "Cons(blank_symbol,r) \<in> list(symbol)"
    by typecheck
  from right_symbols have initial_tape: "\<langle>[],r\<rangle> \<in> tape"
    by (rule empty_left_tape_type)
  from moved_right have moved_tape:
    "\<langle>[],Cons(blank_symbol,r)\<rangle> \<in> tape"
    by (rule empty_left_tape_type)
  from scanned right_symbols have written_right:
    "Cons(b,r) \<in> list(symbol)"
    by typecheck
  from written_right have written_tape:
    "\<langle>[],Cons(b,r)\<rangle> \<in> tape"
    by (rule empty_left_tape_type)
  from execution_IH[OF written_right] have tail_execution:
    "execute_actions(load_actions(bs),\<langle>[],Cons(b,r)\<rangle>) =
      \<langle>[],rev(bs) @ Cons(b,r)\<rangle>" .
  from initial_tape moved_tape written_tape scanned reversed_tail
    tail_execution
  show ?case
    by (simp add: update_write_symbol app_assoc)
qed

theorem execute_loader_actions:
  assumes input: "x \<in> list(symbol)"
  shows "execute_actions(loader_actions(x),\<langle>[],[]\<rangle>) =
    \<langle>[],x\<rangle>"
proof -
  have blank_tape: "\<langle>[],[]\<rangle> \<in> tape"
    by (rule empty_left_tape_type) simp
  from input blank_tape show ?thesis
    unfolding loader_actions_def
    by (simp add: execute_load_actions)
qed

subsection \<open>Compiled Action Sequences\<close>

consts action_compiler :: "i \<Rightarrow> i"

primrec
  "action_compiler([]) = (\<lambda>q\<in>nat. [])"
  "action_compiler(Cons(a,A)) =
    (\<lambda>q\<in>nat.
      Cons(\<langle>a,succ(q)\<rangle>,
        Cons(\<langle>a,succ(q)\<rangle>,
          action_compiler(A)`succ(q))))"

definition compile_actions :: "[i,i] \<Rightarrow> i" where
  "compile_actions(A,q) \<equiv> action_compiler(A)`q"

lemma action_compiler_type [TC]:
  assumes actions: "A \<in> list(action)"
  shows "action_compiler(A) \<in> nat \<rightarrow> list(instruction)"
  using actions
proof (induct A rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  note current_action = Cons.hyps(1)
  note tail_actions = Cons.hyps(2)
  note compiler_IH = Cons.hyps(3)
  show ?case
  proof (simp, rule lam_type)
    fix q
    assume state: "q \<in> nat"
    from state have next_state: "succ(q) \<in> nat" by simp
    from current_action next_state have instruction:
      "\<langle>a,succ(q)\<rangle> \<in> instruction"
      unfolding instruction_def by typecheck
    from compiler_IH next_state have tail:
      "action_compiler(A)`succ(q) \<in> list(instruction)"
      by (rule apply_type)
    from instruction tail show
      "Cons(\<langle>a,succ(q)\<rangle>,
        Cons(\<langle>a,succ(q)\<rangle>,
          action_compiler(A)`succ(q))) \<in> list(instruction)"
      by typecheck
  qed
qed

lemma compile_actions_Nil [simp]:
  assumes state: "q \<in> nat"
  shows "compile_actions([],q) = []"
  using state unfolding compile_actions_def by simp

lemma compile_actions_Cons [simp]:
  assumes state: "q \<in> nat"
  shows "compile_actions(Cons(a,A),q) =
    Cons(\<langle>a,succ(q)\<rangle>,
      Cons(\<langle>a,succ(q)\<rangle>,
        compile_actions(A,succ(q))))"
  using state unfolding compile_actions_def by simp

lemma compile_actions_type [TC]:
  assumes actions: "A \<in> list(action)"
    and state: "q \<in> nat"
  shows "compile_actions(A,q) \<in> list(instruction)"
  using action_compiler_type[OF actions] state
  unfolding compile_actions_def by (rule apply_type)

lemma length_compile_actions [simp]:
  assumes actions: "A \<in> list(action)"
    and state: "q \<in> nat"
  shows "length(compile_actions(A,q)) = 2 #* length(A)"
  using actions state
proof (induct A arbitrary: q rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  note tail_actions = Cons.hyps(2)
  note length_IH = Cons.hyps(3)
  from Cons.prems have state: "q \<in> nat" .
  from state have next_state: "succ(q) \<in> nat" by simp
  from length_IH[OF next_state] state show ?case by simp
qed

lemma fetch_compiled_action:
  assumes index: "i \<in> nat"
    and prefix: "P \<in> list(instruction)"
    and prefix_length: "length(P) = 2 #* i"
    and current_action: "a \<in> action"
    and tail_actions: "A \<in> list(action)"
    and suffix: "N \<in> list(instruction)"
    and scanned: "b \<in> symbol"
  shows "fetch(P @ compile_actions(Cons(a,A),succ(i)) @ N,
      succ(i),b) = \<langle>a,succ(succ(i))\<rangle>"
proof -
  let ?ins = "\<langle>a,succ(succ(i))\<rangle>"
  let ?T = "compile_actions(A,succ(succ(i))) @ N"
  let ?C = "P @ Cons(?ins,Cons(?ins,?T))"
  from index have next_state: "succ(succ(i)) \<in> nat"
    by typecheck
  from compile_actions_type[OF tail_actions next_state] suffix
  have tail: "?T \<in> list(instruction)"
    by typecheck
  from current_action next_state have instruction:
    "?ins \<in> instruction"
    unfolding instruction_def by typecheck
  from instruction tail have body:
    "Cons(?ins,Cons(?ins,?T)) \<in> list(instruction)"
    by typecheck
  from prefix have prefix_length_natural: "length(P) \<in> nat"
    by typecheck
  from tail have tail_length_natural: "length(?T) \<in> nat"
    by typecheck
  have machine_shape:
    "P @ compile_actions(Cons(a,A),succ(i)) @ N = ?C"
    using index by simp
  from prefix body have machine_length:
    "length(?C) = length(P) #+ succ(succ(length(?T)))"
    by simp
  from scanned have symbol_cases:
    "b = blank_symbol \<or> b = one_symbol"
    unfolding symbol_def by auto
  show ?thesis
  proof (cases rule: disjE[OF symbol_cases])
    case 1
    from index prefix_length 1 have slot:
      "slot(succ(i),b) = length(P)"
      by simp
    from prefix_length_natural tail_length_natural machine_length
    have in_range: "length(P) < length(?C)"
      by simp
    have not_before: "\<not> length(P) < length(P)"
      by blast
    from nth_append[OF prefix, of "length(P)"]
      prefix_length_natural not_before
    have selected: "nth(length(P),?C) = ?ins"
      by simp
    from 1 slot in_range selected show ?thesis
      unfolding machine_shape fetch_def by simp
  next
    case 2
    from index prefix_length 2 have slot:
      "slot(succ(i),b) = succ(length(P))"
      by simp
    from prefix_length_natural tail_length_natural machine_length
    have in_range: "succ(length(P)) < length(?C)"
      by simp
    from prefix_length_natural have not_before:
      "\<not> succ(length(P)) < length(P)"
      by simp
    from nth_append[OF prefix, of "succ(length(P))"]
      prefix_length_natural not_before
    have selected: "nth(succ(length(P)),?C) = ?ins"
      by simp
    from 2 slot in_range selected show ?thesis
      unfolding machine_shape fetch_def by simp
  qed
qed

lemma step_compiled_action:
  assumes index: "i \<in> nat"
    and prefix: "P \<in> list(instruction)"
    and prefix_length: "length(P) = 2 #* i"
    and current_action: "a \<in> action"
    and tail_actions: "A \<in> list(action)"
    and suffix: "N \<in> list(instruction)"
    and tape: "t \<in> tape"
  shows "step(P @ compile_actions(Cons(a,A),succ(i)) @ N,
      \<langle>succ(i),t\<rangle>) =
    \<langle>succ(succ(i)),update(a,t)\<rangle>"
proof -
  from scan_type[OF tape] have scanned: "scan(t) \<in> symbol" .
  from fetch_compiled_action[
      OF index prefix prefix_length current_action tail_actions suffix
        scanned]
  have fetched:
    "fetch(P @ compile_actions(Cons(a,A),succ(i)) @ N,
      succ(i),scan(t)) = \<langle>a,succ(succ(i))\<rangle>" .
  from fetched show ?thesis
    unfolding step_def Let_def by simp
qed

lemma steps_compiled_actions:
  assumes index: "i \<in> nat"
    and prefix: "P \<in> list(instruction)"
    and prefix_length: "length(P) = 2 #* i"
    and actions: "A \<in> list(action)"
    and suffix: "N \<in> list(instruction)"
    and tape: "t \<in> tape"
  shows "steps(P @ compile_actions(A,succ(i)) @ N,
      \<langle>succ(i),t\<rangle>,length(A)) =
    \<langle>succ(i #+ length(A)),execute_actions(A,t)\<rangle>"
  using actions index prefix prefix_length tape
proof (induct A arbitrary: i P t rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  note current_action = Cons.hyps(1)
  note tail_actions = Cons.hyps(2)
  note execution_IH = Cons.hyps(3)
  note index = Cons.prems(1)
  note prefix = Cons.prems(2)
  note prefix_length = Cons.prems(3)
  note tape = Cons.prems(4)
  let ?ins = "\<langle>a,succ(succ(i))\<rangle>"
  let ?P = "P @ Cons(?ins,Cons(?ins,[]))"
  let ?M = "P @ compile_actions(Cons(a,A),succ(i)) @ N"
  from index have next_index: "succ(i) \<in> nat"
    by typecheck
  from current_action next_index have instruction:
    "?ins \<in> instruction"
    unfolding instruction_def by typecheck
  from prefix instruction have extended_prefix:
    "?P \<in> list(instruction)"
    by typecheck
  from index prefix prefix_length instruction have extended_length:
    "length(?P) = 2 #* succ(i)"
    by simp
  from tape have updated_tape: "update(a,t) \<in> tape"
    by (rule update_type)
  from step_compiled_action[
      OF index prefix prefix_length current_action tail_actions suffix tape]
  have first_step:
    "step(?M,\<langle>succ(i),t\<rangle>) =
      \<langle>succ(succ(i)),update(a,t)\<rangle>" .
  have machine_shape:
    "?M = ?P @ compile_actions(A,succ(succ(i))) @ N"
    using index prefix extended_prefix by (simp add: app_assoc)
  from execution_IH[
      OF next_index extended_prefix extended_length updated_tape]
  have tail_execution:
    "steps(?P @ compile_actions(A,succ(succ(i))) @ N,
      \<langle>succ(succ(i)),update(a,t)\<rangle>,length(A)) =
      \<langle>succ(succ(i) #+ length(A)),
        execute_actions(A,update(a,t))\<rangle>" .
  from tail_actions have tail_length: "length(A) \<in> nat"
    by typecheck
  have split_execution:
    "steps(?M,\<langle>succ(i),t\<rangle>,succ(length(A))) =
      steps(?M,step(?M,\<langle>succ(i),t\<rangle>),length(A))"
    using steps_add[OF nat_1I tail_length,
      of ?M "\<langle>succ(i),t\<rangle>"] tail_length
    by simp
  from split_execution first_step machine_shape tail_execution
    index tape
  show ?case by simp
qed

subsection \<open>State Shifting\<close>

definition shift_state :: "[i,i] \<Rightarrow> i" where
  "shift_state(k,q) \<equiv>
    if q = final_state then final_state else k #+ q"

definition shift_instruction :: "[i,i] \<Rightarrow> i" where
  "shift_instruction(k,ins) \<equiv>
    \<langle>fst(ins),shift_state(k,snd(ins))\<rangle>"

definition shift_machine :: "[i,i] \<Rightarrow> i" where
  "shift_machine(k,M) \<equiv>
    map(\<lambda>ins. shift_instruction(k,ins),M)"

definition shift_configuration :: "[i,i] \<Rightarrow> i" where
  "shift_configuration(k,c) \<equiv>
    \<langle>shift_state(k,fst(c)),snd(c)\<rangle>"

lemma shift_state_type [TC]:
  assumes offset: "k \<in> nat"
    and state: "q \<in> nat"
  shows "shift_state(k,q) \<in> nat"
  using offset state unfolding shift_state_def by typecheck

lemma shift_state_final [simp]:
  "shift_state(k,final_state) = final_state"
  unfolding shift_state_def by simp

lemma shift_state_nonfinal [simp]:
  assumes offset: "k \<in> nat"
    and state: "q \<in> nat"
    and nonfinal: "q \<noteq> final_state"
  shows "shift_state(k,q) \<noteq> final_state"
  using offset state nonfinal unfolding shift_state_def by auto

lemma shift_state_final_iff [simp]:
  assumes offset: "k \<in> nat"
    and state: "q \<in> nat"
  shows "shift_state(k,q) = final_state \<longleftrightarrow>
    q = final_state"
  using offset state unfolding shift_state_def by auto

lemma slot_shift_state:
  assumes offset: "k \<in> nat"
    and state: "q \<in> nat"
    and nonfinal: "q \<noteq> final_state"
  shows "slot(shift_state(k,q),b) =
    2 #* k #+ slot(q,b)"
  using state
proof (cases rule: natE)
  case 0
  with nonfinal show ?thesis by simp
next
  case (succ r)
  with offset show ?thesis
    unfolding shift_state_def slot_def
    by (simp add: add_mult_distrib_left add_ac)
qed

lemma shift_instruction_type [TC]:
  assumes offset: "k \<in> nat"
    and instruction: "ins \<in> instruction"
  shows "shift_instruction(k,ins) \<in> instruction"
  using offset instruction
  unfolding shift_instruction_def instruction_def by typecheck

lemma fst_shift_instruction [simp]:
  "fst(shift_instruction(k,ins)) = fst(ins)"
  unfolding shift_instruction_def by simp

lemma snd_shift_instruction [simp]:
  "snd(shift_instruction(k,ins)) = shift_state(k,snd(ins))"
  unfolding shift_instruction_def by simp

lemma shift_instruction_default [simp]:
  "shift_instruction(k,\<langle>nop,final_state\<rangle>) =
    \<langle>nop,final_state\<rangle>"
  unfolding shift_instruction_def by simp

lemma shift_machine_type [TC]:
  assumes offset: "k \<in> nat"
    and machine_M: "M \<in> machine"
  shows "shift_machine(k,M) \<in> machine"
proof -
  from machine_M have instructions: "M \<in> list(instruction)"
    unfolding machine_def .
  have "map(\<lambda>ins. shift_instruction(k,ins),M)
      \<in> list(instruction)"
    using instructions
    by (rule map_type) (rule shift_instruction_type[OF offset])
  then show ?thesis unfolding shift_machine_def machine_def .
qed

lemma length_shift_machine [simp]:
  assumes machine_M: "M \<in> machine"
  shows "length(shift_machine(k,M)) = length(M)"
  using machine_M unfolding shift_machine_def machine_def by simp

lemma nth_shift_machine:
  assumes offset: "k \<in> nat"
    and machine_M: "M \<in> machine"
    and natural: "j \<in> nat"
    and in_range: "j < length(M)"
  shows "nth(j,shift_machine(k,M)) =
    shift_instruction(k,nth(j,M))"
proof -
  from machine_M have instructions: "M \<in> list(instruction)"
    unfolding machine_def .
  from natural in_range instructions show ?thesis
    unfolding shift_machine_def by simp
qed

lemma shift_configuration_type [TC]:
  assumes offset: "k \<in> nat"
    and configuration: "c \<in> configuration"
  shows "shift_configuration(k,c) \<in> configuration"
  using offset configuration
  unfolding shift_configuration_def configuration_def by typecheck

lemma shift_configuration_pair [simp]:
  "shift_configuration(k,\<langle>q,t\<rangle>) =
    \<langle>shift_state(k,q),t\<rangle>"
  unfolding shift_configuration_def by simp

lemma fst_shift_configuration [simp]:
  "fst(shift_configuration(k,c)) = shift_state(k,fst(c))"
  unfolding shift_configuration_def by simp

lemma snd_shift_configuration [simp]:
  "snd(shift_configuration(k,c)) = snd(c)"
  unfolding shift_configuration_def by simp

lemma shift_configuration_final_iff [simp]:
  assumes offset: "k \<in> nat"
    and configuration: "c \<in> configuration"
  shows "fst(shift_configuration(k,c)) = final_state
    \<longleftrightarrow> fst(c) = final_state"
proof -
  from configuration have state: "fst(c) \<in> nat"
    unfolding configuration_def by typecheck
  from shift_state_final_iff[OF offset state]
  show ?thesis by simp
qed

lemma shifted_slot_in_range_iff:
  assumes offset: "k \<in> nat"
    and machine_M: "M \<in> machine"
    and state: "q \<in> nat"
    and nonfinal: "q \<noteq> final_state"
    and scanned: "b \<in> symbol"
  shows "slot(shift_state(k,q),b) < 2 #* k #+ length(M)
    \<longleftrightarrow> slot(q,b) < length(M)"
proof -
  from slot_type[OF state scanned] have slot_natural:
    "slot(q,b) \<in> nat" .
  from machine_M have length_natural: "length(M) \<in> nat"
    unfolding machine_def by typecheck
  have shifted_slot:
    "slot(shift_state(k,q),b) = 2 #* k #+ slot(q,b)"
    by (rule slot_shift_state[OF offset state nonfinal])
  show ?thesis
    unfolding shifted_slot
  proof
    assume shifted_less:
      "2 #* k #+ slot(q,b) < 2 #* k #+ length(M)"
    from shifted_less slot_natural length_natural
    show "slot(q,b) < length(M)"
      by (rule add_lt_elim1)
  next
    assume original_less: "slot(q,b) < length(M)"
    from original_less length_natural show
      "2 #* k #+ slot(q,b) < 2 #* k #+ length(M)"
      by (rule add_lt_mono2)
  qed
qed

lemma fetch_shifted_tail:
  assumes offset: "k \<in> nat"
    and prefix: "P \<in> list(instruction)"
    and prefix_length: "length(P) = 2 #* k"
    and machine_M: "M \<in> machine"
    and state: "q \<in> nat"
    and scanned: "b \<in> symbol"
  shows "fetch(P @ shift_machine(k,M),shift_state(k,q),b) =
    shift_instruction(k,fetch(M,q,b))"
proof (cases "q = final_state")
  case True
  then show ?thesis by simp
next
  case nonfinal: False
  let ?s = "slot(q,b)"
  let ?j = "2 #* k #+ ?s"
  from slot_type[OF state scanned] have slot_natural: "?s \<in> nat" .
  from offset have index_natural: "?j \<in> nat" by typecheck
  from shift_machine_type[OF offset machine_M] have shifted_machine:
    "shift_machine(k,M) \<in> machine" .
  then have shifted_instructions:
    "shift_machine(k,M) \<in> list(instruction)"
    unfolding machine_def .
  from length_app[OF prefix shifted_instructions] machine_M
  have combined_length:
    "length(P @ shift_machine(k,M)) =
      2 #* k #+ length(M)"
    using prefix_length by simp
  from slot_shift_state[OF offset state nonfinal] have shifted_slot:
    "slot(shift_state(k,q),b) = ?j" .
  from shift_state_nonfinal[OF offset state nonfinal] have
    shifted_nonfinal: "shift_state(k,q) \<noteq> final_state" .
  from shifted_slot_in_range_iff[
      OF offset machine_M state nonfinal scanned]
  have range_iff:
    "slot(shift_state(k,q),b) < 2 #* k #+ length(M)
      \<longleftrightarrow> ?s < length(M)" .
  show ?thesis
  proof (cases "?s < length(M)")
    case True
    with range_iff shifted_slot have shifted_in_range:
      "?j < 2 #* k #+ length(M)"
      by simp
    from offset have prefix_base_natural: "2 #* k \<in> nat"
      by typecheck
    from prefix_base_natural have prefix_le: "2 #* k \<le> ?j"
      by (rule add_le_self)
    from prefix_le prefix_length have prefix_bound:
      "length(P) \<le> ?j"
      by simp
    then have not_in_prefix: "\<not> ?j < length(P)"
      by (rule le_imp_not_lt)
    from nth_append[OF prefix, of ?j] index_natural
    have nth_appended:
      "nth(?j,P @ shift_machine(k,M)) =
        (if ?j < length(P) then nth(?j,P)
          else nth(?j #- length(P),shift_machine(k,M)))" .
    also from not_in_prefix have "... =
        nth(?j #- length(P),shift_machine(k,M))"
      by simp
    also from prefix_length slot_natural have "... =
        nth(?s,shift_machine(k,M))"
      by (simp add: diff_add_inverse)
    finally have nth_tail:
      "nth(?j,P @ shift_machine(k,M)) =
        nth(?s,shift_machine(k,M))" .
    from nth_shift_machine[OF offset machine_M slot_natural True]
    have shifted_instruction:
      "nth(?s,shift_machine(k,M)) =
        shift_instruction(k,nth(?s,M))" .
    from nonfinal shifted_nonfinal True shifted_in_range combined_length
      shifted_slot nth_tail shifted_instruction
    show ?thesis unfolding fetch_def by simp
  next
    case False
    with range_iff have shifted_out_of_range:
      "\<not> slot(shift_state(k,q),b) <
        2 #* k #+ length(M)"
      by simp
    from nonfinal shifted_nonfinal False shifted_out_of_range
      combined_length
    show ?thesis unfolding fetch_def by simp
  qed
qed

subsection \<open>Hardwired Inputs\<close>

definition hardwire :: "[i,i] \<Rightarrow> i" where
  "hardwire(M,x) \<equiv>
    let A = loader_actions(x);
        k = length(A)
    in compile_actions(A,initial_state) @ shift_machine(k,M)"

lemma hardwire_type [TC]:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
  shows "hardwire(M,x) \<in> machine"
proof -
  let ?A = "loader_actions(x)"
  let ?k = "length(?A)"
  from loader_actions_type[OF input] have actions:
    "?A \<in> list(action)" .
  from actions have offset: "?k \<in> nat"
    by typecheck
  from compile_actions_type[OF actions] have prefix:
    "compile_actions(?A,initial_state) \<in> list(instruction)"
    by simp
  from shift_machine_type[OF offset machine_M] have shifted:
    "shift_machine(?k,M) \<in> machine" .
  from shifted have shifted_instructions:
    "shift_machine(?k,M) \<in> list(instruction)"
    unfolding machine_def .
  from prefix shifted_instructions show ?thesis
    unfolding hardwire_def Let_def machine_def by typecheck
qed

lemma length_hardwire_prefix:
  assumes input: "x \<in> list(symbol)"
  shows "length(compile_actions(loader_actions(x),initial_state)) =
    2 #* length(loader_actions(x))"
  using loader_actions_type[OF input] by simp

lemma fetch_hardwire_shift:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and state: "q \<in> nat"
    and scanned: "b \<in> symbol"
  shows "fetch(hardwire(M,x),
      shift_state(length(loader_actions(x)),q),b) =
    shift_instruction(length(loader_actions(x)),fetch(M,q,b))"
proof -
  from loader_actions_type[OF input] have actions:
    "loader_actions(x) \<in> list(action)" .
  then have offset: "length(loader_actions(x)) \<in> nat"
    by typecheck
  from compile_actions_type[OF actions] have prefix:
    "compile_actions(loader_actions(x),initial_state)
      \<in> list(instruction)"
    by simp
  from length_hardwire_prefix[OF input] have prefix_length:
    "length(compile_actions(loader_actions(x),initial_state)) =
      2 #* length(loader_actions(x))" .
  show ?thesis
    unfolding hardwire_def Let_def
    by (rule fetch_shifted_tail[
      OF offset prefix prefix_length machine_M state scanned])
qed

lemma hardwire_loader_endpoint:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
  shows "steps(hardwire(M,x),initial_config([]),
      length(loader_actions(x))) =
    shift_configuration(length(loader_actions(x)),initial_config(x))"
proof -
  let ?A = "loader_actions(x)"
  let ?k = "length(?A)"
  from loader_actions_type[OF input] have actions:
    "?A \<in> list(action)" .
  then have offset: "?k \<in> nat"
    by typecheck
  from shift_machine_type[OF offset machine_M] have shifted_machine:
    "shift_machine(?k,M) \<in> machine" .
  then have suffix:
    "shift_machine(?k,M) \<in> list(instruction)"
    unfolding machine_def .
  have empty_prefix: "[] \<in> list(instruction)"
    by simp
  have empty_prefix_length: "length([]) = 2 #* 0"
    by simp
  have blank_tape: "\<langle>[],[]\<rangle> \<in> tape"
    unfolding tape_def by typecheck
  from steps_compiled_actions[
      OF nat_0I empty_prefix empty_prefix_length actions suffix blank_tape]
    offset
  have compiled:
    "steps(compile_actions(?A,initial_state) @ shift_machine(?k,M),
      initial_config([]),?k) =
      \<langle>succ(?k),execute_actions(?A,\<langle>[],[]\<rangle>)\<rangle>"
    by simp
  from execute_loader_actions[OF input] have loaded:
    "execute_actions(?A,\<langle>[],[]\<rangle>) = \<langle>[],x\<rangle>" .
  from compiled loaded offset show ?thesis
    unfolding hardwire_def Let_def shift_configuration_def shift_state_def
    by simp
qed

lemma step_hardwire_shift:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and configuration: "c \<in> configuration"
  shows "step(hardwire(M,x),
      shift_configuration(length(loader_actions(x)),c)) =
    shift_configuration(length(loader_actions(x)),step(M,c))"
proof -
  let ?k = "length(loader_actions(x))"
  from configuration have state: "fst(c) \<in> nat"
    and tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck+
  from scan_type[OF tape] have scanned:
    "scan(snd(c)) \<in> symbol" .
  from fetch_hardwire_shift[OF machine_M input state scanned]
  have shifted_fetch:
    "fetch(hardwire(M,x),shift_state(?k,fst(c)),scan(snd(c))) =
      shift_instruction(?k,fetch(M,fst(c),scan(snd(c))))" .
  from shifted_fetch show ?thesis
    unfolding step_def Let_def shift_configuration_def by simp
qed

lemma steps_hardwire_shift:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and configuration: "c \<in> configuration"
    and time: "n \<in> nat"
  shows "steps(hardwire(M,x),
      shift_configuration(length(loader_actions(x)),c),n) =
    shift_configuration(length(loader_actions(x)),steps(M,c,n))"
  using time
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ n)
  let ?k = "length(loader_actions(x))"
  from steps_type[OF machine_M configuration succ.hyps(1)]
  have current_configuration: "steps(M,c,n) \<in> configuration" .
  have "steps(hardwire(M,x),shift_configuration(?k,c),succ(n)) =
      step(hardwire(M,x),
        steps(hardwire(M,x),shift_configuration(?k,c),n))"
    by simp
  also from succ.hyps(2) have "... =
      step(hardwire(M,x),shift_configuration(?k,steps(M,c,n)))"
    by simp
  also from step_hardwire_shift[
      OF machine_M input current_configuration]
  have "... = shift_configuration(?k,step(M,steps(M,c,n)))" .
  also have "... = shift_configuration(?k,steps(M,c,succ(n)))"
    by simp
  finally show ?case .
qed

lemma steps_hardwire:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and time: "n \<in> nat"
  shows "steps(hardwire(M,x),initial_config([]),
      length(loader_actions(x)) #+ n) =
    shift_configuration(length(loader_actions(x)),
      steps(M,initial_config(x),n))"
proof -
  let ?k = "length(loader_actions(x))"
  from loader_actions_type[OF input] have actions:
    "loader_actions(x) \<in> list(action)" .
  then have offset: "?k \<in> nat"
    by typecheck
  from initial_config_type[OF input] have input_configuration:
    "initial_config(x) \<in> configuration" .
  from steps_add[OF offset time,
      of "hardwire(M,x)" "initial_config([])"]
  have split:
    "steps(hardwire(M,x),initial_config([]),?k #+ n) =
      steps(hardwire(M,x),
        steps(hardwire(M,x),initial_config([]),?k),n)" .
  from hardwire_loader_endpoint[OF machine_M input] have loaded:
    "steps(hardwire(M,x),initial_config([]),?k) =
      shift_configuration(?k,initial_config(x))" .
  from steps_hardwire_shift[
      OF machine_M input input_configuration time]
  have shifted:
    "steps(hardwire(M,x),
      shift_configuration(?k,initial_config(x)),n) =
      shift_configuration(?k,steps(M,initial_config(x),n))" .
  from split loaded shifted show ?thesis
    by simp
qed

theorem hardwire_halts_iff:
  assumes machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
  shows "halts_blank(hardwire(M,x)) \<longleftrightarrow> halts_on(M,x)"
proof -
  let ?A = "loader_actions(x)"
  let ?k = "length(?A)"
  let ?H = "hardwire(M,x)"
  let ?c0 = "initial_config([])"
  let ?cx = "initial_config(x)"
  from loader_actions_type[OF input] have actions:
    "?A \<in> list(action)" .
  then have offset: "?k \<in> nat"
    by typecheck
  from hardwire_type[OF machine_M input] have machine_H:
    "?H \<in> machine" .
  have blank_input: "[] \<in> list(symbol)"
    by simp
  from initial_config_type[OF blank_input] have blank_configuration:
    "?c0 \<in> configuration" .
  from initial_config_type[OF input] have input_configuration:
    "?cx \<in> configuration" .
  from hardwire_loader_endpoint[OF machine_M input] have loader_endpoint:
    "steps(?H,?c0,?k) = shift_configuration(?k,?cx)" .
  show ?thesis
  proof
    assume hardwired_halts: "halts_blank(?H)"
    then obtain n where time: "n \<in> nat"
      and hardwired_final:
        "fst(steps(?H,?c0,n)) = final_state"
      unfolding halts_on_def by auto
    have not_before_loader: "\<not> n \<le> ?k"
    proof
      assume before_loader: "n \<le> ?k"
      from steps_final_mono[
        OF machine_H blank_configuration time offset before_loader
          hardwired_final]
      have endpoint_final:
        "fst(steps(?H,?c0,?k)) = final_state" .
      from offset input_configuration have loader_nonfinal:
        "fst(shift_configuration(?k,?cx)) \<noteq> final_state"
        by simp
      from endpoint_final loader_endpoint loader_nonfinal
      show False by simp
    qed
    from time offset not_before_loader have offset_less: "?k < n"
      by (simp add: not_le_iff_lt)
    then have offset_le: "?k \<le> n"
      by (rule leI)
    let ?d = "n #- ?k"
    have difference: "?d \<in> nat"
      by typecheck
    from add_diff_inverse[OF offset_le time] have decomposition:
      "?k #+ ?d = n" .
    from steps_hardwire[OF machine_M input difference] decomposition
    have simulation:
      "steps(?H,?c0,n) =
        shift_configuration(?k,steps(M,?cx,?d))"
      by simp
    from steps_type[OF machine_M input_configuration difference]
    have original_configuration:
      "steps(M,?cx,?d) \<in> configuration" .
    from shift_configuration_final_iff[
        OF offset original_configuration]
      simulation hardwired_final
    have original_final:
      "fst(steps(M,?cx,?d)) = final_state"
      by simp
    show "halts_on(M,x)"
      unfolding halts_on_def
      using machine_M input difference original_final by blast
  next
    assume original_halts: "halts_on(M,x)"
    then obtain n where time: "n \<in> nat"
      and original_final:
        "fst(steps(M,?cx,n)) = final_state"
      unfolding halts_on_def by auto
    from steps_hardwire[OF machine_M input time] have simulation:
      "steps(?H,?c0,?k #+ n) =
        shift_configuration(?k,steps(M,?cx,n))" .
    from offset time have total_time: "?k #+ n \<in> nat"
      by typecheck
    from steps_type[OF machine_M input_configuration time]
    have original_configuration:
      "steps(M,?cx,n) \<in> configuration" .
    from shift_configuration_final_iff[
        OF offset original_configuration]
      simulation original_final
    have hardwired_final:
      "fst(steps(?H,?c0,?k #+ n)) = final_state"
      by simp
    show "halts_blank(?H)"
      unfolding halts_on_def
      using machine_H blank_input total_time hardwired_final by blast
  qed
qed

end
