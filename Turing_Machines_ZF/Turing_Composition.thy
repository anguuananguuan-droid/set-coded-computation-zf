(*  Title:      Turing_Composition.thy
    Author:     Tang Ziyi
*)

section \<open>Sequential Composition\<close>

theory Turing_Composition
  imports Turing_Transformations
begin

subsection \<open>Continuation Tables\<close>

definition continuation_entry :: "[i,i] \<Rightarrow> i" where
  "continuation_entry(M,j) \<equiv>
    if j < length(M) then
      redirect_final(succ(control_bound(M)),nth(j,M))
    else
      \<langle>nop,succ(control_bound(M))\<rangle>"

definition continuation_prefix :: "i \<Rightarrow> i" where
  "continuation_prefix(M) \<equiv>
    map(\<lambda>j. continuation_entry(M,j),
      upt(0,2 #* control_bound(M)))"

definition sequential_machine :: "[i,i] \<Rightarrow> i" where
  "sequential_machine(M,N) \<equiv>
    continuation_prefix(M) @ shift_machine(control_bound(M),N)"

lemma continuation_entry_type [TC]:
  assumes machine_M: "M \<in> machine"
    and natural: "j \<in> nat"
  shows "continuation_entry(M,j) \<in> instruction"
proof (cases "j < length(M)")
  case True
  from machine_M have instructions: "M \<in> list(instruction)"
    unfolding machine_def .
  from nth_type[OF instructions True] have
    "nth(j,M) \<in> instruction" .
  moreover from machine_M have
    "succ(control_bound(M)) \<in> nat"
    by typecheck
  ultimately show ?thesis using True
    unfolding continuation_entry_def
    by (simp add: redirect_final_type)
next
  case False
  from machine_M have control: "succ(control_bound(M)) \<in> nat"
    by typecheck
  have default:
    "\<langle>nop,succ(control_bound(M))\<rangle> \<in> instruction"
    unfolding instruction_def using control by typecheck
  from False default show ?thesis
    unfolding continuation_entry_def by simp
qed

lemma continuation_prefix_type [TC]:
  assumes machine_M: "M \<in> machine"
  shows "continuation_prefix(M) \<in> list(instruction)"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by typecheck
  have indices: "upt(0,2 #* control_bound(M)) \<in> list(nat)"
    using control by typecheck
  show ?thesis
    unfolding continuation_prefix_def
    using indices
    by (rule map_type) (rule continuation_entry_type[OF machine_M])
qed

lemma sequential_machine_type [TC]:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
  shows "sequential_machine(M,N) \<in> machine"
proof -
  from continuation_prefix_type[OF machine_M] have prefix:
    "continuation_prefix(M) \<in> list(instruction)" .
  from machine_M have control: "control_bound(M) \<in> nat"
    by typecheck
  from shift_machine_type[OF control machine_N] have shifted_machine:
    "shift_machine(control_bound(M),N) \<in> machine" .
  then have shifted:
    "shift_machine(control_bound(M),N) \<in> list(instruction)"
    unfolding machine_def .
  from prefix shifted show ?thesis
    unfolding sequential_machine_def machine_def by typecheck
qed

lemma length_continuation_prefix [simp]:
  assumes machine_M: "M \<in> machine"
  shows "length(continuation_prefix(M)) = 2 #* control_bound(M)"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by typecheck
  show ?thesis
    unfolding continuation_prefix_def using control by simp
qed

lemma length_sequential_machine [simp]:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
  shows "length(sequential_machine(M,N)) =
    2 #* control_bound(M) #+ length(N)"
proof -
  from continuation_prefix_type[OF machine_M] have prefix:
    "continuation_prefix(M) \<in> list(instruction)" .
  from machine_M have offset: "control_bound(M) \<in> nat"
    by typecheck
  from shift_machine_type[OF offset machine_N] have shifted_machine:
    "shift_machine(control_bound(M),N) \<in> machine" .
  then have shifted:
    "shift_machine(control_bound(M),N) \<in> list(instruction)"
    unfolding machine_def .
  from length_app[OF prefix shifted] machine_M machine_N
  show ?thesis unfolding sequential_machine_def by simp
qed

lemma nth_continuation_prefix:
  assumes machine_M: "M \<in> machine"
    and natural: "j \<in> nat"
    and in_range: "j < 2 #* control_bound(M)"
  shows "nth(j,continuation_prefix(M)) = continuation_entry(M,j)"
proof -
  from machine_M have control: "control_bound(M) \<in> nat"
    by typecheck
  have indices: "upt(0,2 #* control_bound(M)) \<in> list(nat)"
    using control by typecheck
  from natural in_range control show ?thesis
    unfolding continuation_prefix_def
    using nth_map[OF indices, of j "\<lambda>j. continuation_entry(M,j)"]
    by simp
qed

lemma fetch_sequential_prefix:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and state: "q \<in> control_bound(M)"
    and nonfinal: "q \<noteq> final_state"
    and scanned: "b \<in> symbol"
  shows "fetch(sequential_machine(M,N),q,b) =
    redirect_final(succ(control_bound(M)),fetch(M,q,b))"
proof -
  let ?j = "slot(q,b)"
  from machine_M have control: "control_bound(M) \<in> nat"
    by typecheck
  from state control have natural: "q \<in> nat"
    by (blast intro: Ord_trans Ord_nat)
  from slot_type[OF natural scanned] have index: "?j \<in> nat" .
  from slot_control_in_range[
      OF machine_M succI2[OF state] nonfinal scanned]
  have prefix_range: "?j < 2 #* control_bound(M)" .
  from nth_continuation_prefix[OF machine_M index prefix_range]
  have prefix_entry:
    "nth(?j,continuation_prefix(M)) = continuation_entry(M,?j)" .
  from continuation_prefix_type[OF machine_M] have prefix:
    "continuation_prefix(M) \<in> list(instruction)" .
  from nth_append[OF prefix, of ?j] index prefix_range
  have combined_entry:
    "nth(?j,sequential_machine(M,N)) = continuation_entry(M,?j)"
    unfolding sequential_machine_def using prefix_entry machine_M by simp
  from control have twice_control:
    "2 #* control_bound(M) \<in> nat"
    by typecheck
  from twice_control have prefix_le_combined:
    "2 #* control_bound(M) \<le>
      2 #* control_bound(M) #+ length(N)"
    by (rule add_le_self)
  from prefix_range prefix_le_combined have before_combined:
    "?j < 2 #* control_bound(M) #+ length(N)"
    by (rule lt_trans2)
  from length_sequential_machine[OF machine_M machine_N] have combined_length:
    "length(sequential_machine(M,N)) =
      2 #* control_bound(M) #+ length(N)" .
  from before_combined combined_length have combined_range:
    "?j < length(sequential_machine(M,N))"
    by simp
  from fetch_in_range[OF nonfinal combined_range] combined_entry
  have transformed:
    "fetch(sequential_machine(M,N),q,b) = continuation_entry(M,?j)"
    by simp
  show ?thesis
  proof (cases "?j < length(M)")
    case True
    from transformed True nonfinal show ?thesis
      unfolding continuation_entry_def fetch_def by simp
  next
    case False
    from transformed False nonfinal show ?thesis
      unfolding continuation_entry_def fetch_def redirect_final_def by simp
  qed
qed

lemma fetch_sequential_tail:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and state: "q \<in> nat"
    and scanned: "b \<in> symbol"
  shows "fetch(sequential_machine(M,N),
      shift_state(control_bound(M),q),b) =
    shift_instruction(control_bound(M),fetch(N,q,b))"
proof -
  from machine_M have offset: "control_bound(M) \<in> nat"
    by typecheck
  from continuation_prefix_type[OF machine_M] have prefix:
    "continuation_prefix(M) \<in> list(instruction)" .
  from length_continuation_prefix[OF machine_M] have prefix_length:
    "length(continuation_prefix(M)) = 2 #* control_bound(M)" .
  show ?thesis
    unfolding sequential_machine_def
    by (rule fetch_shifted_tail[
      OF offset prefix prefix_length machine_N state scanned])
qed

subsection \<open>First-Phase Simulation\<close>

lemma step_sequential_running:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
    and state: "fst(c) \<in> control_bound(M)"
    and nonfinal: "fst(c) \<noteq> final_state"
    and next_nonfinal: "fst(step(M,c)) \<noteq> final_state"
  shows "step(sequential_machine(M,N),c) = step(M,c)"
proof -
  from configuration have tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck
  from scan_type[OF tape] have scanned: "scan(snd(c)) \<in> symbol" .
  from fetch_sequential_prefix[
      OF machine_M machine_N state nonfinal scanned]
  have transformed:
    "fetch(sequential_machine(M,N),fst(c),scan(snd(c))) =
      redirect_final(succ(control_bound(M)),
        fetch(M,fst(c),scan(snd(c))))" .
  from fetch_type[OF machine_M] have fetched:
    "fetch(M,fst(c),scan(snd(c))) \<in> instruction" .
  from next_nonfinal have target_nonfinal:
    "snd(fetch(M,fst(c),scan(snd(c)))) \<noteq> final_state"
    unfolding step_def Let_def by simp
  from redirect_final_nonfinal_eq[OF fetched target_nonfinal] transformed
  show ?thesis
    unfolding step_def Let_def by simp
qed

lemma steps_sequential_running:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
    and initial: "fst(c) \<in> control_bound(M)"
    and time: "n \<in> nat"
    and nonfinal: "fst(steps(M,c,n)) \<noteq> final_state"
  shows "steps(sequential_machine(M,N),c,n) = steps(M,c,n)"
  using time nonfinal
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
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
  from steps_state_below_control[
      OF machine_M configuration initial succ.hyps(1) current_nonfinal]
  have current_below:
    "fst(steps(M,c,n)) \<in> control_bound(M)" .
  from succ.hyps(2)[OF current_nonfinal] have simulation:
    "steps(sequential_machine(M,N),c,n) = steps(M,c,n)" .
  from step_sequential_running[
      OF machine_M machine_N current current_below current_nonfinal]
    succ.prems simulation
  show ?case by simp
qed

lemma step_sequential_handoff:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
    and state: "fst(c) \<in> control_bound(M)"
    and nonfinal: "fst(c) \<noteq> final_state"
    and next_final: "fst(step(M,c)) = final_state"
  shows "step(sequential_machine(M,N),c) =
    shift_configuration(control_bound(M),
      \<langle>initial_state,snd(step(M,c))\<rangle>)"
proof -
  from machine_M have offset: "control_bound(M) \<in> nat"
    by typecheck
  from configuration have tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck
  from scan_type[OF tape] have scanned: "scan(snd(c)) \<in> symbol" .
  from fetch_sequential_prefix[
      OF machine_M machine_N state nonfinal scanned]
  have transformed:
    "fetch(sequential_machine(M,N),fst(c),scan(snd(c))) =
      redirect_final(succ(control_bound(M)),
        fetch(M,fst(c),scan(snd(c))))" .
  from next_final have target_final:
    "snd(fetch(M,fst(c),scan(snd(c)))) = final_state"
    unfolding step_def Let_def by simp
  from transformed target_final offset show ?thesis
    unfolding step_def Let_def redirect_final_def
      shift_configuration_def shift_state_def
    by simp
qed

lemma steps_sequential_handoff:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
    and initial_below: "fst(c) \<in> control_bound(M)"
    and initial_nonfinal: "fst(c) \<noteq> final_state"
    and time: "n \<in> nat"
    and final: "fst(steps(M,c,n)) = final_state"
  shows "\<exists>m\<in>succ(n).
    steps(sequential_machine(M,N),c,m) =
      shift_configuration(control_bound(M),
        \<langle>initial_state,snd(steps(M,c,n))\<rangle>)"
  using time final
proof (induct n rule: nat_induct)
  case 0
  with initial_nonfinal show ?case by simp
next
  case (succ n)
  let ?d = "steps(M,c,n)"
  from steps_type[OF machine_M configuration succ.hyps(1)]
  have current: "?d \<in> configuration" .
  show ?case
  proof (cases "fst(?d) = final_state")
    case True
    from step_final_configuration[OF current True] have absorbed:
      "steps(M,c,succ(n)) = ?d"
      by simp
    from succ.hyps(2)[OF True] obtain m where bounded: "m \<in> succ(n)"
      and reached:
        "steps(sequential_machine(M,N),c,m) =
          shift_configuration(control_bound(M),
            \<langle>initial_state,snd(?d)\<rangle>)"
      by auto
    from bounded reached absorbed succ.hyps(1) show ?thesis by auto
  next
    case False
    from steps_state_below_control[
      OF machine_M configuration initial_below succ.hyps(1) False]
    have current_below: "fst(?d) \<in> control_bound(M)" .
    from steps_sequential_running[
      OF machine_M machine_N configuration initial_below succ.hyps(1) False]
    have simulation:
      "steps(sequential_machine(M,N),c,n) = ?d" .
    from step_sequential_handoff[
      OF machine_M machine_N current current_below False]
      succ.prems
    have handoff:
      "step(sequential_machine(M,N),?d) =
        shift_configuration(control_bound(M),
          \<langle>initial_state,snd(step(M,?d))\<rangle>)"
      by simp
    have reached:
      "steps(sequential_machine(M,N),c,succ(n)) =
        shift_configuration(control_bound(M),
          \<langle>initial_state,snd(steps(M,c,succ(n)))\<rangle>)"
      using simulation handoff by simp
    from succ.hyps(1) reached show ?thesis by auto
  qed
qed

subsection \<open>Second-Phase Simulation\<close>

lemma step_sequential_shift:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
  shows "step(sequential_machine(M,N),shift_configuration(control_bound(M),c)) =
    shift_configuration(control_bound(M),step(N,c))"
proof -
  from configuration have state: "fst(c) \<in> nat"
    and tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck+
  from scan_type[OF tape] have scanned: "scan(snd(c)) \<in> symbol" .
  from fetch_sequential_tail[OF machine_M machine_N state scanned]
  show ?thesis
    unfolding step_def Let_def shift_configuration_def by simp
qed

lemma steps_sequential_shift:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
    and time: "n \<in> nat"
  shows "steps(sequential_machine(M,N),shift_configuration(control_bound(M),c),n) =
    shift_configuration(control_bound(M),steps(N,c,n))"
  using time
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ n)
  from steps_type[OF machine_N configuration succ.hyps(1)]
  have current: "steps(N,c,n) \<in> configuration" .
  have "steps(sequential_machine(M,N),
      shift_configuration(control_bound(M),c),succ(n)) =
    step(sequential_machine(M,N),
      steps(sequential_machine(M,N),
        shift_configuration(control_bound(M),c),n))"
    by simp
  also from succ.hyps(2) have "... =
    step(sequential_machine(M,N),
      shift_configuration(control_bound(M),steps(N,c,n)))"
    by simp
  also from step_sequential_shift[OF machine_M machine_N current]
  have "... = shift_configuration(control_bound(M),
      step(N,steps(N,c,n)))" .
  also have "... = shift_configuration(control_bound(M),
      steps(N,c,succ(n)))"
    by simp
  finally show ?case .
qed

lemma steps_sequential_after_handoff:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and next_configuration: "d \<in> configuration"
    and handoff_time: "m \<in> nat"
    and continuation_time: "n \<in> nat"
    and handoff:
      "steps(sequential_machine(M,N),c,m) =
        shift_configuration(control_bound(M),d)"
  shows "steps(sequential_machine(M,N),c,m #+ n) =
    shift_configuration(control_bound(M),steps(N,d,n))"
proof -
  from steps_add[OF handoff_time continuation_time,
      of "sequential_machine(M,N)" c]
  have split:
    "steps(sequential_machine(M,N),c,m #+ n) =
      steps(sequential_machine(M,N),
        steps(sequential_machine(M,N),c,m),n)" .
  from steps_sequential_shift[
      OF machine_M machine_N next_configuration continuation_time]
  have continuation:
    "steps(sequential_machine(M,N),
      shift_configuration(control_bound(M),d),n) =
      shift_configuration(control_bound(M),steps(N,d,n))" .
  from split handoff continuation show ?thesis by simp
qed

subsection \<open>Termination\<close>

theorem steps_sequential_after_halting:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
    and initial_below: "fst(c) \<in> control_bound(M)"
    and initial_nonfinal: "fst(c) \<noteq> final_state"
    and halting_time: "m \<in> nat"
    and final: "fst(steps(M,c,m)) = final_state"
    and continuation_time: "n \<in> nat"
  shows "\<exists>k\<in>nat.
    steps(sequential_machine(M,N),c,k #+ n) =
      shift_configuration(control_bound(M),
        steps(N,\<langle>initial_state,snd(steps(M,c,m))\<rangle>,n))"
proof -
  from steps_type[OF machine_M configuration halting_time]
  have endpoint: "steps(M,c,m) \<in> configuration" .
  then have tape: "snd(steps(M,c,m)) \<in> tape"
    unfolding configuration_def by typecheck
  have next_configuration:
    "\<langle>initial_state,snd(steps(M,c,m))\<rangle> \<in> configuration"
    unfolding configuration_def using tape by typecheck
  from steps_sequential_handoff[
      OF machine_M machine_N configuration initial_below initial_nonfinal
        halting_time final]
  obtain k where bounded: "k \<in> succ(m)"
    and handoff:
      "steps(sequential_machine(M,N),c,k) =
        shift_configuration(control_bound(M),
          \<langle>initial_state,snd(steps(M,c,m))\<rangle>)"
    by auto
  from bounded halting_time have handoff_time: "k \<in> nat"
    by (blast intro: Ord_trans Ord_nat)
  from steps_sequential_after_handoff[
      OF machine_M machine_N next_configuration handoff_time
        continuation_time handoff]
  have composed:
    "steps(sequential_machine(M,N),c,k #+ n) =
      shift_configuration(control_bound(M),
        steps(N,\<langle>initial_state,snd(steps(M,c,m))\<rangle>,n))" .
  from handoff_time composed show ?thesis by blast
qed

theorem steps_sequential_finalD:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
    and initial_below: "fst(c) \<in> control_bound(M)"
    and initial_nonfinal: "fst(c) \<noteq> final_state"
    and time: "n \<in> nat"
    and final:
      "fst(steps(sequential_machine(M,N),c,n)) = final_state"
  shows "fst(steps(M,c,n)) = final_state \<and>
    (\<exists>r\<in>nat.
      fst(steps(N,
        \<langle>initial_state,snd(steps(M,c,n))\<rangle>,r)) = final_state)"
proof -
  have source_final: "fst(steps(M,c,n)) = final_state"
  proof (rule ccontr)
    assume source_nonfinal:
      "fst(steps(M,c,n)) \<noteq> final_state"
    from steps_sequential_running[
      OF machine_M machine_N configuration initial_below time source_nonfinal]
    have simulation:
      "steps(sequential_machine(M,N),c,n) = steps(M,c,n)" .
    from final source_nonfinal simulation show False by simp
  qed
  from steps_sequential_handoff[
      OF machine_M machine_N configuration initial_below initial_nonfinal
        time source_final]
  obtain h where bounded: "h \<in> succ(n)"
    and handoff:
      "steps(sequential_machine(M,N),c,h) =
        shift_configuration(control_bound(M),
          \<langle>initial_state,snd(steps(M,c,n))\<rangle>)"
    by auto
  from bounded time have handoff_time: "h \<in> nat"
    by (blast intro: Ord_trans Ord_nat)
  from bounded time have ordered: "h \<le> n"
    by (auto simp add: le_iff intro: ltI nat_into_Ord)
  let ?r = "n #- h"
  have continuation_time: "?r \<in> nat" by typecheck
  from add_diff_inverse[OF ordered time] have decomposition:
    "h #+ ?r = n" .
  from steps_type[OF machine_M configuration time]
  have source_endpoint: "steps(M,c,n) \<in> configuration" .
  then have tape: "snd(steps(M,c,n)) \<in> tape"
    unfolding configuration_def by typecheck
  have next_configuration:
    "\<langle>initial_state,snd(steps(M,c,n))\<rangle> \<in> configuration"
    unfolding configuration_def using tape by typecheck
  from steps_sequential_after_handoff[
      OF machine_M machine_N next_configuration handoff_time
        continuation_time handoff]
  have simulation:
    "steps(sequential_machine(M,N),c,h #+ ?r) =
      shift_configuration(control_bound(M),
        steps(N,\<langle>initial_state,snd(steps(M,c,n))\<rangle>,?r))" .
  from steps_type[OF machine_N next_configuration continuation_time]
  have continuation_endpoint:
    "steps(N,\<langle>initial_state,snd(steps(M,c,n))\<rangle>,?r)
      \<in> configuration" .
  from machine_M have offset: "control_bound(M) \<in> nat"
    by typecheck
  from shift_configuration_final_iff[OF offset continuation_endpoint]
    simulation decomposition final
  have continuation_final:
    "fst(steps(N,
      \<langle>initial_state,snd(steps(M,c,n))\<rangle>,?r)) = final_state"
    by simp
  from source_final continuation_time continuation_final
  show ?thesis by blast
qed

theorem sequential_machine_terminates_iff:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and configuration: "c \<in> configuration"
    and initial_below: "fst(c) \<in> control_bound(M)"
    and initial_nonfinal: "fst(c) \<noteq> final_state"
  shows "(\<exists>n\<in>nat.
      fst(steps(sequential_machine(M,N),c,n)) = final_state) \<longleftrightarrow>
    (\<exists>m\<in>nat.
      fst(steps(M,c,m)) = final_state \<and>
      (\<exists>n\<in>nat.
        fst(steps(N,
          \<langle>initial_state,snd(steps(M,c,m))\<rangle>,n)) = final_state))"
proof
  assume composed:
    "\<exists>n\<in>nat.
      fst(steps(sequential_machine(M,N),c,n)) = final_state"
  then obtain n where time: "n \<in> nat"
    and final:
      "fst(steps(sequential_machine(M,N),c,n)) = final_state"
    by auto
  from steps_sequential_finalD[
      OF machine_M machine_N configuration initial_below initial_nonfinal
        time final]
  show "\<exists>m\<in>nat.
      fst(steps(M,c,m)) = final_state \<and>
      (\<exists>n\<in>nat.
        fst(steps(N,
          \<langle>initial_state,snd(steps(M,c,m))\<rangle>,n)) = final_state)"
    using time by blast
next
  assume phases:
    "\<exists>m\<in>nat.
      fst(steps(M,c,m)) = final_state \<and>
      (\<exists>n\<in>nat.
        fst(steps(N,
          \<langle>initial_state,snd(steps(M,c,m))\<rangle>,n)) = final_state)"
  then obtain m n where source_time: "m \<in> nat"
    and source_final: "fst(steps(M,c,m)) = final_state"
    and continuation_time: "n \<in> nat"
    and continuation_final:
      "fst(steps(N,
        \<langle>initial_state,snd(steps(M,c,m))\<rangle>,n)) = final_state"
    by auto
  from steps_sequential_after_halting[
      OF machine_M machine_N configuration initial_below initial_nonfinal
        source_time source_final continuation_time]
  obtain k where handoff_time: "k \<in> nat"
    and simulation:
      "steps(sequential_machine(M,N),c,k #+ n) =
        shift_configuration(control_bound(M),
          steps(N,\<langle>initial_state,snd(steps(M,c,m))\<rangle>,n))"
    by auto
  from source_time steps_type[OF machine_M configuration source_time]
  have next_configuration:
    "\<langle>initial_state,snd(steps(M,c,m))\<rangle> \<in> configuration"
    unfolding configuration_def by typecheck
  from steps_type[OF machine_N next_configuration continuation_time]
  have continuation_endpoint:
    "steps(N,\<langle>initial_state,snd(steps(M,c,m))\<rangle>,n)
      \<in> configuration" .
  from machine_M have offset: "control_bound(M) \<in> nat"
    by typecheck
  from shift_configuration_final_iff[OF offset continuation_endpoint]
    simulation continuation_final
  have composed_final:
    "fst(steps(sequential_machine(M,N),c,k #+ n)) = final_state"
    by simp
  from handoff_time continuation_time have total_time: "k #+ n \<in> nat"
    by typecheck
  from total_time composed_final show
    "\<exists>n\<in>nat.
      fst(steps(sequential_machine(M,N),c,n)) = final_state"
    by blast
qed

end
