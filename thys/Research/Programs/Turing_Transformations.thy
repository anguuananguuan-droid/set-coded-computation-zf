(*  Title:      Turing_Transformations.thy
    Author:     Tang Ziyi
*)

section \<open>Machine Transformations and Input Loading\<close>

theory Turing_Transformations
  imports "Set_Coded_Computation_ZF.Turing_Rejection"
begin

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
  shows "tm_update(write_symbol(b),\<langle>l,r\<rangle>) =
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
    (\<lambda>t\<in>tape. action_semantics(A)`tm_update(a,t))"

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
  have "(\<lambda>t\<in>tape. action_semantics(A)`tm_update(a,t))
      \<in> tape \<rightarrow> tape"
  proof (rule lam_type)
    fix t
    assume tape: "t \<in> tape"
    from tape have "tm_update(a,t) \<in> tape"
      by (rule tm_update_type)
    with semantics_IH show "action_semantics(A)`tm_update(a,t) \<in> tape"
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
    execute_actions(A,tm_update(a,t))"
  using tape tm_update_type[OF tape]
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
    \<langle>succ(succ(i)),tm_update(a,t)\<rangle>"
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
  from tape have updated_tape: "tm_update(a,t) \<in> tape"
    by (rule tm_update_type)
  from step_compiled_action[
      OF index prefix prefix_length current_action tail_actions suffix tape]
  have first_step:
    "step(?M,\<langle>succ(i),t\<rangle>) =
      \<langle>succ(succ(i)),tm_update(a,t)\<rangle>" .
  have machine_shape:
    "?M = ?P @ compile_actions(A,succ(succ(i))) @ N"
    using index prefix extended_prefix by (simp add: app_assoc)
  from execution_IH[
      OF next_index extended_prefix extended_length updated_tape]
  have tail_execution:
    "steps(?P @ compile_actions(A,succ(succ(i))) @ N,
      \<langle>succ(succ(i)),tm_update(a,t)\<rangle>,length(A)) =
      \<langle>succ(succ(i) #+ length(A)),
        execute_actions(A,tm_update(a,t))\<rangle>" .
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
