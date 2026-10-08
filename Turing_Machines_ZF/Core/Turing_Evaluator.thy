(*  Title:      Turing_Evaluator.thy
    Author:     Tang Ziyi
*)

section \<open>Numeric Evaluation\<close>

theory Turing_Evaluator
  imports Turing_Code_Operations
begin

subsection \<open>Configuration Codes\<close>

text \<open>The evaluator computes a configuration code from a machine
number and a configuration code. Its correctness theorems compare exact
encoded configurations, including their finite tape lists. At this stage
the evaluator is a set-theoretic function; primitive-recursive certificates
for the numerical operations follow in the next theory.\<close>

definition encode_tape :: "i \<Rightarrow> i" where
  "encode_tape(t) \<equiv>
    pair_code(nat_list_encode(fst(t)),nat_list_encode(snd(t)))"

definition encode_configuration :: "i \<Rightarrow> i" where
  "encode_configuration(c) \<equiv>
    pair_code(fst(c),encode_tape(snd(c)))"

lemma symbol_in_nat [TC]:
  "symbol \<in> nat"
  unfolding symbol_def by typecheck

lemma symbol_subset_nat:
  "symbol \<subseteq> nat"
  using symbol_in_nat Ord_nat by (blast dest: OrdmemD)

lemma tape_lists_natural:
  assumes tape: "t \<in> tape"
  shows "fst(t) \<in> list(nat)"
    and "snd(t) \<in> list(nat)"
proof -
  from tape have left: "fst(t) \<in> list(symbol)"
    and right: "snd(t) \<in> list(symbol)"
    by (rule tapeD)+
  from left show "fst(t) \<in> list(nat)"
    by (rule list_mono[OF symbol_subset_nat, THEN subsetD])
  from right show "snd(t) \<in> list(nat)"
    by (rule list_mono[OF symbol_subset_nat, THEN subsetD])
qed

lemma encode_tape_type [TC]:
  assumes tape: "t \<in> tape"
  shows "encode_tape(t) \<in> nat"
proof -
  from tape_lists_natural(1)[OF tape] have left_code:
    "nat_list_encode(fst(t)) \<in> nat"
    by (rule nat_list_encode_type)
  from tape_lists_natural(2)[OF tape] have right_code:
    "nat_list_encode(snd(t)) \<in> nat"
    by (rule nat_list_encode_type)
  from left_code right_code show ?thesis
    unfolding encode_tape_def by typecheck
qed

lemma encode_configuration_type [TC]:
  assumes configuration: "c \<in> configuration"
  shows "encode_configuration(c) \<in> nat"
proof -
  from configuration have state: "fst(c) \<in> nat"
    and tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck+
  from state encode_tape_type[OF tape] show ?thesis
    unfolding encode_configuration_def by typecheck
qed

lemma encode_tape_left:
  assumes tape: "t \<in> tape"
  shows "fst(pair_decode(encode_tape(t))) = nat_list_encode(fst(t))"
proof -
  from tape_lists_natural(1)[OF tape] have left: "fst(t) \<in> list(nat)" .
  from tape_lists_natural(2)[OF tape] have right: "snd(t) \<in> list(nat)" .
  from left have left_code: "nat_list_encode(fst(t)) \<in> nat"
    by (rule nat_list_encode_type)
  from right have right_code: "nat_list_encode(snd(t)) \<in> nat"
    by (rule nat_list_encode_type)
  show ?thesis
    unfolding encode_tape_def
    using pair_decode_code[OF left_code right_code] by simp
qed

lemma encode_tape_right:
  assumes tape: "t \<in> tape"
  shows "snd(pair_decode(encode_tape(t))) = nat_list_encode(snd(t))"
proof -
  from tape_lists_natural(1)[OF tape] have left: "fst(t) \<in> list(nat)" .
  from tape_lists_natural(2)[OF tape] have right: "snd(t) \<in> list(nat)" .
  from left have left_code: "nat_list_encode(fst(t)) \<in> nat"
    by (rule nat_list_encode_type)
  from right have right_code: "nat_list_encode(snd(t)) \<in> nat"
    by (rule nat_list_encode_type)
  show ?thesis
    unfolding encode_tape_def
    using pair_decode_code[OF left_code right_code] by simp
qed

lemma encode_tape_left_code:
  assumes tape: "t \<in> tape"
  shows "pair_left_code(encode_tape(t)) = nat_list_encode(fst(t))"
  using encode_tape_type[OF tape] encode_tape_left[OF tape]
    pair_left_code_decode by simp

lemma encode_tape_right_code:
  assumes tape: "t \<in> tape"
  shows "pair_right_code(encode_tape(t)) = nat_list_encode(snd(t))"
  using encode_tape_type[OF tape] encode_tape_right[OF tape]
    pair_right_code_decode by simp

lemma encode_configuration_state:
  assumes configuration: "c \<in> configuration"
  shows "pair_left_code(encode_configuration(c)) = fst(c)"
proof -
  from configuration have state: "fst(c) \<in> nat"
    and tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck+
  from state encode_tape_type[OF tape] show ?thesis
    unfolding encode_configuration_def
    using pair_decode_code pair_left_code_decode pair_code_type by simp
qed

lemma encode_configuration_tape:
  assumes configuration: "c \<in> configuration"
  shows "pair_right_code(encode_configuration(c)) = encode_tape(snd(c))"
proof -
  from configuration have state: "fst(c) \<in> nat"
    and tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck+
  from state encode_tape_type[OF tape] show ?thesis
    unfolding encode_configuration_def
    using pair_decode_code pair_right_code_decode pair_code_type by simp
qed

subsection \<open>Tape Evaluation\<close>

definition code_scan :: "i \<Rightarrow> i" where
  "code_scan(t) \<equiv> code_head(pair_right_code(t))"

definition code_update :: "[i,i] \<Rightarrow> i" where
  "code_update(a,t) \<equiv>
    if a = write_blank then
      pair_code(pair_left_code(t),
        code_cons(blank_symbol,code_tail(pair_right_code(t))))
    else if a = write_one then
      pair_code(pair_left_code(t),
        code_cons(one_symbol,code_tail(pair_right_code(t))))
    else if a = move_left then
      pair_code(code_tail(pair_left_code(t)),
        code_cons(code_head(pair_left_code(t)),pair_right_code(t)))
    else if a = move_right then
      pair_code(code_cons(code_head(pair_right_code(t)),pair_left_code(t)),
        code_tail(pair_right_code(t)))
    else t"

lemma code_scan_type [TC]:
  assumes natural: "t \<in> nat"
  shows "code_scan(t) \<in> nat"
proof -
  from natural have right: "pair_right_code(t) \<in> nat"
    by typecheck
  then show ?thesis unfolding code_scan_def by typecheck
qed

lemma code_update_type [TC]:
  assumes natural: "t \<in> nat"
  shows "code_update(a,t) \<in> nat"
proof -
  from natural have left: "pair_left_code(t) \<in> nat"
    and right: "pair_right_code(t) \<in> nat"
    by typecheck+
  from left right have left_head: "code_head(pair_left_code(t)) \<in> nat"
    and right_head: "code_head(pair_right_code(t)) \<in> nat"
    and left_tail: "code_tail(pair_left_code(t)) \<in> nat"
    and right_tail: "code_tail(pair_right_code(t)) \<in> nat"
    by typecheck+
  show ?thesis
    unfolding code_update_def
    using natural left right left_head right_head left_tail right_tail
    by typecheck
qed

theorem code_scan_encode:
  assumes tape: "t \<in> tape"
  shows "code_scan(encode_tape(t)) = scan(t)"
proof -
  from tape_lists_natural(2)[OF tape] have right: "snd(t) \<in> list(nat)" .
  show ?thesis
    unfolding code_scan_def scan_def
    using encode_tape_right_code[OF tape] code_head_encode[OF right]
    by simp
qed

theorem code_update_encode:
  assumes tape: "t \<in> tape"
  shows "code_update(a,encode_tape(t)) = encode_tape(tm_update(a,t))"
proof -
  from tape have left_symbols: "fst(t) \<in> list(symbol)"
    and right_symbols: "snd(t) \<in> list(symbol)"
    by (rule tapeD)+
  from tape_lists_natural(1)[OF tape] have left: "fst(t) \<in> list(nat)" .
  from tape_lists_natural(2)[OF tape] have right: "snd(t) \<in> list(nat)" .
  from left have left_code: "nat_list_encode(fst(t)) \<in> nat"
    by (rule nat_list_encode_type)
  from right have right_code: "nat_list_encode(snd(t)) \<in> nat"
    by (rule nat_list_encode_type)
  from left have left_tail: "tl(fst(t)) \<in> list(nat)"
    by (rule tl_type)
  from right have right_tail: "tl(snd(t)) \<in> list(nat)"
    by (rule tl_type)
  show ?thesis
    unfolding code_update_def tm_update_def encode_tape_def
    using encode_tape_left_code[OF tape] encode_tape_right_code[OF tape]
      code_head_encode[OF left] code_head_encode[OF right]
      code_tail_encode[OF left] code_tail_encode[OF right]
      pair_left_code_pair_code[OF left_code right_code]
      pair_right_code_pair_code[OF left_code right_code]
      left_symbols right_symbols left_tail right_tail
    by (auto simp add: code_cons_def)
qed

subsection \<open>Instruction Evaluation\<close>

definition default_instruction_code :: i where
  "default_instruction_code \<equiv>
    pair_code(nop,final_state)"

definition normalize_instruction_code :: "i \<Rightarrow> i" where
  "normalize_instruction_code(n) \<equiv>
    if n \<in> nat \<and> pair_left_code(n) \<in> action then n
    else default_instruction_code"

lemma default_instruction_code_type [TC]:
  "default_instruction_code \<in> nat"
  unfolding default_instruction_code_def by typecheck

lemma normalize_instruction_code_type [TC]:
  "normalize_instruction_code(n) \<in> nat"
  unfolding normalize_instruction_code_def
  using default_instruction_code_type by auto

theorem normalize_instruction_code_correct:
  "normalize_instruction_code(n) =
    encode_instruction(decode_instruction(n))"
proof (cases "n \<in> nat")
  case True
  from True have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have first: "fst(pair_decode(n)) \<in> nat"
    and second: "snd(pair_decode(n)) \<in> nat"
    by typecheck+
  from True have recover:
    "pair_code(fst(pair_decode(n)),snd(pair_decode(n))) = n"
    by (rule pair_code_decode)
  from True show ?thesis
    unfolding normalize_instruction_code_def decode_instruction_def
      encode_instruction_def default_instruction_code_def
    using pair_left_code_decode[OF True] recover first second
    by auto
next
  case False
  then show ?thesis
    unfolding normalize_instruction_code_def decode_instruction_def
      encode_instruction_def default_instruction_code_def
    by simp
qed

lemma slot_natural [TC]:
  assumes state: "q \<in> nat"
    and scanned: "b \<in> nat"
  shows "slot(q,b) \<in> nat"
  using state scanned unfolding slot_def by typecheck

definition code_fetch :: "[i,i,i] \<Rightarrow> i" where
  "code_fetch(e,q,b) \<equiv>
    if q = final_state then default_instruction_code
    else if code_has_index(slot(q,b),e) = 0 then
      default_instruction_code
    else normalize_instruction_code(code_nth(slot(q,b),e))"

lemma code_fetch_type [TC]:
  "code_fetch(e,q,b) \<in> nat"
  unfolding code_fetch_def by typecheck

theorem code_fetch_correct:
  assumes machine_number: "e \<in> nat"
    and state: "q \<in> nat"
    and scanned: "b \<in> symbol"
  shows "code_fetch(e,q,b) =
    encode_instruction(fetch(decode_machine(e),q,b))"
proof -
  let ?codes = "nat_list_decode(e)"
  from machine_number have codes: "?codes \<in> list(nat)"
    by (rule nat_list_decode_type)
  from codes have mapped_length:
    "length(map(decode_instruction,?codes)) = length(?codes)"
    by (rule length_map)
  from state scanned have position: "slot(q,b) \<in> nat"
    by (rule slot_type)
  from machine_number have roundtrip: "nat_list_encode(?codes) = e"
    by (rule nat_list_encode_decode)
  show ?thesis
  proof (cases "q = final_state")
    case True
    then show ?thesis
      unfolding code_fetch_def fetch_def default_instruction_code_def
        encode_instruction_def by simp
  next
    case False
    show ?thesis
    proof (cases "slot(q,b) < length(?codes)")
      case True
      from code_has_index_encode[OF position codes] True roundtrip have present:
        "code_has_index(slot(q,b),e) = 1"
        by simp
      from code_nth_encode[OF position codes] roundtrip have selected:
        "code_nth(slot(q,b),e) = nth(slot(q,b),?codes)"
        by simp
      from codes position True have mapped:
        "nth(slot(q,b),map(decode_instruction,?codes)) =
          decode_instruction(nth(slot(q,b),?codes))"
        by (rule nth_map)
      from False True present selected mapped mapped_length
        normalize_instruction_code_correct
      show ?thesis
        unfolding code_fetch_def fetch_def decode_machine_def
          decode_machine_list_def by simp
    next
      case False_range: False
      from code_has_index_encode[OF position codes] False_range roundtrip
      have absent: "code_has_index(slot(q,b),e) = 0"
        by simp
      from False False_range absent mapped_length show ?thesis
        unfolding code_fetch_def fetch_def decode_machine_def
          decode_machine_list_def default_instruction_code_def
          encode_instruction_def
        by simp
    qed
  qed
qed

subsection \<open>One-Step Evaluation\<close>

lemma encode_instruction_components:
  assumes instruction: "ins \<in> instruction"
  shows "pair_left_code(encode_instruction(ins)) = fst(ins)"
    and "pair_right_code(encode_instruction(ins)) = snd(ins)"
proof -
  from instruction have action: "fst(ins) \<in> action"
    and state: "snd(ins) \<in> nat"
    unfolding instruction_def by typecheck+
  from action action_subset_nat have natural_action: "fst(ins) \<in> nat"
    by blast
  from pair_left_code_pair_code[OF natural_action state]
  show "pair_left_code(encode_instruction(ins)) = fst(ins)"
    unfolding encode_instruction_def .
  from pair_right_code_pair_code[OF natural_action state]
  show "pair_right_code(encode_instruction(ins)) = snd(ins)"
    unfolding encode_instruction_def .
qed

definition code_step :: "[i,i] \<Rightarrow> i" where
  "code_step(e,z) \<equiv>
    let t = pair_right_code(z);
        ins = code_fetch(e,pair_left_code(z),code_scan(t))
    in pair_code(pair_right_code(ins),
         code_update(pair_left_code(ins),t))"

lemma code_step_type [TC]:
  "code_step(e,z) \<in> nat"
proof -
  have tape_code: "pair_right_code(z) \<in> nat"
    by typecheck
  have instruction_code:
    "code_fetch(e,pair_left_code(z),code_scan(pair_right_code(z))) \<in> nat"
    by typecheck
  from instruction_code have next_state:
    "pair_right_code(
      code_fetch(e,pair_left_code(z),code_scan(pair_right_code(z)))) \<in> nat"
    by typecheck
  from tape_code have updated:
    "code_update(
      pair_left_code(
        code_fetch(e,pair_left_code(z),code_scan(pair_right_code(z)))),
      pair_right_code(z)) \<in> nat"
    by (rule code_update_type)
  show ?thesis
    unfolding code_step_def Let_def
    using next_state updated by typecheck
qed

theorem code_step_correct:
  assumes machine_number: "e \<in> nat"
    and configuration: "c \<in> configuration"
  shows "code_step(e,encode_configuration(c)) =
    encode_configuration(step(decode_machine(e),c))"
proof -
  let ?ins =
    "fetch(decode_machine(e),fst(c),scan(snd(c)))"
  from configuration have state: "fst(c) \<in> nat"
    and tape: "snd(c) \<in> tape"
    unfolding configuration_def by typecheck+
  from tape have scanned: "scan(snd(c)) \<in> symbol"
    by (rule scan_type)
  from machine_number have decoded_machine: "decode_machine(e) \<in> machine"
    by (rule decode_machine_type)
  from decoded_machine have fetched: "?ins \<in> instruction"
    by (rule fetch_type)
  from code_fetch_correct[OF machine_number state scanned]
  have fetched_code:
    "code_fetch(e,fst(c),scan(snd(c))) = encode_instruction(?ins)" .
  from fetched_code encode_instruction_components(1)[OF fetched]
  have fetched_action:
    "pair_left_code(code_fetch(e,fst(c),scan(snd(c)))) = fst(?ins)"
    by simp
  from fetched_code encode_instruction_components(2)[OF fetched]
  have fetched_state:
    "pair_right_code(code_fetch(e,fst(c),scan(snd(c)))) = snd(?ins)"
    by simp
  have "code_step(e,encode_configuration(c)) =
      pair_code(snd(?ins),encode_tape(tm_update(fst(?ins),snd(c))))"
    unfolding code_step_def Let_def
    using encode_configuration_state[OF configuration]
      encode_configuration_tape[OF configuration]
      code_scan_encode[OF tape] fetched_action fetched_state
      code_update_encode[OF tape]
    by simp
  also have "... = encode_configuration(step(decode_machine(e),c))"
    unfolding step_def Let_def encode_configuration_def by simp
  finally show ?thesis .
qed

subsection \<open>Finite Evaluation\<close>

consts code_steps :: "[i,i,i] \<Rightarrow> i"

primrec
  "code_steps(0,e,z) = z"
  "code_steps(succ(n),e,z) = code_step(e,code_steps(n,e,z))"

lemma code_steps_type [TC]:
  assumes time: "n \<in> nat"
    and configuration_code: "z \<in> nat"
  shows "code_steps(n,e,z) \<in> nat"
  using time configuration_code
  by (induct n rule: nat_induct) (simp_all add: code_step_type)

theorem code_steps_correct:
  assumes time: "n \<in> nat"
    and machine_number: "e \<in> nat"
    and configuration: "c \<in> configuration"
  shows "code_steps(n,e,encode_configuration(c)) =
    encode_configuration(steps(decode_machine(e),c,n))"
  using time
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ n)
  from machine_number have machine: "decode_machine(e) \<in> machine"
    by (rule decode_machine_type)
  from machine configuration succ.hyps(1) have stepped:
    "steps(decode_machine(e),c,n) \<in> configuration"
    by (rule steps_type)
  from code_step_correct[OF machine_number stepped] succ.hyps(2)
  show ?case by simp
qed

definition code_is_final :: "i \<Rightarrow> i" where
  "code_is_final(z) \<equiv>
    if pair_left_code(z) = final_state then 1 else 0"

definition code_halts_at :: "[i,i,i] \<Rightarrow> i" where
  "code_halts_at(n,e,z) \<equiv>
    code_is_final(code_steps(n,e,z))"

lemma code_is_final_type [TC]:
  "code_is_final(z) \<in> nat"
  unfolding code_is_final_def by typecheck

lemma code_halts_at_type [TC]:
  "code_halts_at(n,e,z) \<in> nat"
  unfolding code_halts_at_def by typecheck

theorem code_steps_final_iff:
  assumes time: "n \<in> nat"
    and machine_number: "e \<in> nat"
    and configuration: "c \<in> configuration"
  shows "pair_left_code(code_steps(n,e,encode_configuration(c))) =
      final_state \<longleftrightarrow>
    fst(steps(decode_machine(e),c,n)) = final_state"
proof -
  from machine_number have machine: "decode_machine(e) \<in> machine"
    by (rule decode_machine_type)
  from machine configuration time have stepped:
    "steps(decode_machine(e),c,n) \<in> configuration"
    by (rule steps_type)
  show ?thesis
    using code_steps_correct[OF time machine_number configuration]
      encode_configuration_state[OF stepped]
    by simp
qed

theorem code_halts_at_correct:
  assumes time: "n \<in> nat"
    and machine_number: "e \<in> nat"
    and configuration: "c \<in> configuration"
  shows "code_halts_at(n,e,encode_configuration(c)) = 1 \<longleftrightarrow>
    fst(steps(decode_machine(e),c,n)) = final_state"
  unfolding code_halts_at_def code_is_final_def
  using code_steps_final_iff[OF time machine_number configuration]
  by auto

definition code_initial_configuration :: "i \<Rightarrow> i" where
  "code_initial_configuration(x) \<equiv>
    pair_code(initial_state,pair_code(0,x))"

definition code_blank_configuration :: i where
  "code_blank_configuration \<equiv>
    code_initial_configuration(0)"

lemma code_initial_configuration_type [TC]:
  assumes input_code: "x \<in> nat"
  shows "code_initial_configuration(x) \<in> nat"
  using input_code unfolding code_initial_configuration_def by typecheck

lemma code_blank_configuration_type [TC]:
  "code_blank_configuration \<in> nat"
  unfolding code_blank_configuration_def by typecheck

theorem code_initial_configuration_encode:
  assumes input: "x \<in> list(symbol)"
  shows "code_initial_configuration(nat_list_encode(x)) =
    encode_configuration(initial_config(x))"
proof -
  from input have natural_input: "x \<in> list(nat)"
    by (rule list_mono[OF symbol_subset_nat, THEN subsetD])
  show ?thesis
    unfolding code_initial_configuration_def encode_configuration_def
      encode_tape_def
    using nat_list_encode_type[OF natural_input]
    by simp
qed

theorem code_blank_configuration_correct:
  "code_blank_configuration =
    encode_configuration(initial_config([]))"
  unfolding code_blank_configuration_def
  using code_initial_configuration_encode[of "[]"]
  by simp

definition code_halts_blank_at :: "[i,i] \<Rightarrow> i" where
  "code_halts_blank_at(n,e) \<equiv>
    code_halts_at(n,e,code_blank_configuration)"

lemma code_halts_blank_at_type [TC]:
  "code_halts_blank_at(n,e) \<in> nat"
  unfolding code_halts_blank_at_def by typecheck

theorem halts_on_iff_code_steps:
  assumes machine_number: "e \<in> nat"
    and input: "x \<in> list(symbol)"
  shows "halts_on(decode_machine(e),x) \<longleftrightarrow>
    (\<exists>n\<in>nat.
      pair_left_code(
        code_steps(n,e,encode_configuration(initial_config(x)))) =
      final_state)"
proof
  assume halts: "halts_on(decode_machine(e),x)"
  then obtain n where time: "n \<in> nat"
    and final:
      "fst(steps(decode_machine(e),initial_config(x),n)) = final_state"
    unfolding halts_on_def by auto
  from input have initial: "initial_config(x) \<in> configuration"
    by (rule initial_config_type)
  have equivalence:
    "pair_left_code(
      code_steps(n,e,encode_configuration(initial_config(x)))) =
      final_state \<longleftrightarrow>
      fst(steps(decode_machine(e),initial_config(x),n)) = final_state"
    by (rule code_steps_final_iff[OF time machine_number initial])
  from equivalence final have coded_final:
    "pair_left_code(
      code_steps(n,e,encode_configuration(initial_config(x)))) =
      final_state"
    by (rule iffD2)
  show "\<exists>n\<in>nat.
    pair_left_code(
      code_steps(n,e,encode_configuration(initial_config(x)))) =
    final_state"
  proof (rule bexI)
    show "pair_left_code(
      code_steps(n,e,encode_configuration(initial_config(x)))) =
      final_state"
      by (rule coded_final)
    show "n \<in> nat" by (rule time)
  qed
next
  assume coded:
    "\<exists>n\<in>nat.
      pair_left_code(
        code_steps(n,e,encode_configuration(initial_config(x)))) =
      final_state"
  then obtain n where time: "n \<in> nat"
    and final:
      "pair_left_code(
        code_steps(n,e,encode_configuration(initial_config(x)))) =
      final_state"
    by auto
  from input have initial: "initial_config(x) \<in> configuration"
    by (rule initial_config_type)
  have equivalence:
    "pair_left_code(
      code_steps(n,e,encode_configuration(initial_config(x)))) =
      final_state \<longleftrightarrow>
      fst(steps(decode_machine(e),initial_config(x),n)) = final_state"
    by (rule code_steps_final_iff[OF time machine_number initial])
  from equivalence final
  have external:
    "fst(steps(decode_machine(e),initial_config(x),n)) = final_state"
    by (rule iffD1)
  from machine_number have machine: "decode_machine(e) \<in> machine"
    by (rule decode_machine_type)
  show "halts_on(decode_machine(e),x)"
    unfolding halts_on_def
  proof (intro conjI)
    show "decode_machine(e) \<in> machine" by (rule machine)
    show "x \<in> list(symbol)" by (rule input)
    show "\<exists>n\<in>nat.
      fst(steps(decode_machine(e),initial_config(x),n)) = final_state"
    proof (rule bexI)
      show "fst(steps(decode_machine(e),initial_config(x),n)) = final_state"
        by (rule external)
      show "n \<in> nat" by (rule time)
    qed
  qed
qed

corollary halts_blank_iff_code_steps:
  assumes machine_number: "e \<in> nat"
  shows "halts_blank(decode_machine(e)) \<longleftrightarrow>
    (\<exists>n\<in>nat.
      pair_left_code(
        code_steps(n,e,encode_configuration(initial_config([])))) =
      final_state)"
  using machine_number
  by (rule halts_on_iff_code_steps) typecheck

corollary halts_blank_iff_code_halts_at:
  assumes machine_number: "e \<in> nat"
  shows "halts_blank(decode_machine(e)) \<longleftrightarrow>
    (\<exists>n\<in>nat. code_halts_blank_at(n,e) = 1)"
  unfolding code_halts_blank_at_def code_halts_at_def code_is_final_def
  using halts_blank_iff_code_steps[OF machine_number]
    code_blank_configuration_correct
  by simp

end
