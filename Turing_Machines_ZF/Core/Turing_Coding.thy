(*  Title:      Turing_Coding.thy
    Author:     Tang Ziyi
*)

section \<open>Machine Coding\<close>

theory Turing_Coding
  imports Turing_Machine
begin

subsection \<open>Natural Pairing\<close>

text \<open>The pairing code enumerates diagonals of nat times nat. The
inverse follows the same diagonals by iteration; the two directions are
proved inverse on natural numbers.\<close>

consts triangle :: "i \<Rightarrow> i"

primrec
  "triangle(0) = 0"
  "triangle(succ(n)) = triangle(n) #+ succ(n)"

definition pair_code :: "[i,i] \<Rightarrow> i" where
  "pair_code(m,n) \<equiv> triangle(m #+ n) #+ n"

definition pair_step :: "i \<Rightarrow> i" where
  "pair_step(p) \<equiv>
    if fst(p) = 0 then
      \<langle>succ(snd(p)),0\<rangle>
    else
      \<langle>pred(fst(p)),succ(snd(p))\<rangle>"

consts pair_decode :: "i \<Rightarrow> i"

primrec
  "pair_decode(0) = \<langle>0,0\<rangle>"
  "pair_decode(succ(n)) = pair_step(pair_decode(n))"

definition pair_number :: "i \<Rightarrow> i" where
  "pair_number(p) \<equiv> pair_code(fst(p),snd(p))"

lemma triangle_type [TC]:
  assumes natural: "n \<in> nat"
  shows "triangle(n) \<in> nat"
  using natural by (induct n rule: nat_induct) simp_all

lemma pair_code_type [TC]:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
  shows "pair_code(m,n) \<in> nat"
  using first second unfolding pair_code_def by typecheck

lemma pair_step_type [TC]:
  assumes pair: "p \<in> nat \<times> nat"
  shows "pair_step(p) \<in> nat \<times> nat"
proof -
  from pair have first: "fst(p) \<in> nat"
    and second: "snd(p) \<in> nat"
    by typecheck+
  show ?thesis
    unfolding pair_step_def using first second by typecheck
qed

lemma pair_decode_type [TC]:
  assumes natural: "n \<in> nat"
  shows "pair_decode(n) \<in> nat \<times> nat"
  using natural by (induct n rule: nat_induct) (simp_all add: pair_step_type)

lemma pair_number_type [TC]:
  assumes pair: "p \<in> nat \<times> nat"
  shows "pair_number(p) \<in> nat"
  using pair unfolding pair_number_def by typecheck

lemma pair_number_step:
  assumes pair: "p \<in> nat \<times> nat"
  shows "pair_number(pair_step(p)) = succ(pair_number(p))"
proof -
  from pair have first: "fst(p) \<in> nat"
    and second: "snd(p) \<in> nat"
    by typecheck+
  from first show ?thesis
  proof (cases rule: natE)
    case 0
    with second show ?thesis
      unfolding pair_number_def pair_step_def pair_code_def
      by simp
  next
    case (succ m)
    with second show ?thesis
      unfolding pair_number_def pair_step_def pair_code_def
      by (simp add: add_ac)
  qed
qed

lemma pair_number_decode:
  assumes natural: "n \<in> nat"
  shows "pair_number(pair_decode(n)) = n"
  using natural
proof (induct n rule: nat_induct)
  case 0
  then show ?case
    unfolding pair_number_def pair_code_def by simp
next
  case (succ n)
  from succ.hyps(1) have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  have "pair_number(pair_decode(succ(n))) =
      pair_number(pair_step(pair_decode(n)))"
    by simp
  also from decoded have "... = succ(pair_number(pair_decode(n)))"
    by (rule pair_number_step)
  also from succ.hyps(2) have "... = succ(n)"
    by simp
  finally show ?case .
qed

definition pair_prev :: "i \<Rightarrow> i" where
  "pair_prev(p) \<equiv>
    if snd(p) = 0 then
      \<langle>0,pred(fst(p))\<rangle>
    else
      \<langle>succ(fst(p)),pred(snd(p))\<rangle>"

lemma pair_prev_type [TC]:
  assumes pair: "p \<in> nat \<times> nat"
  shows "pair_prev(p) \<in> nat \<times> nat"
proof -
  from pair have first: "fst(p) \<in> nat"
    and second: "snd(p) \<in> nat"
    by typecheck+
  show ?thesis
    unfolding pair_prev_def using first second by typecheck
qed

lemma triangle_eq_zero:
  assumes natural: "n \<in> nat"
  shows "triangle(n) = 0 \<longleftrightarrow> n = 0"
  using natural by (induct n rule: nat_induct) simp_all

lemma pair_number_zero:
  assumes pair: "p \<in> nat \<times> nat"
  shows "pair_number(p) = 0 \<longleftrightarrow> p = \<langle>0,0\<rangle>"
proof -
  from pair have first: "fst(p) \<in> nat"
    and second: "snd(p) \<in> nat"
    by typecheck+
  from pair have recover: "\<langle>fst(p),snd(p)\<rangle> = p"
    by (rule Pair_fst_snd_eq)
  show ?thesis
    unfolding pair_number_def pair_code_def
    using first second recover triangle_eq_zero
    by auto
qed

lemma pair_step_prev:
  assumes pair: "p \<in> nat \<times> nat"
    and nonzero: "p \<noteq> \<langle>0,0\<rangle>"
  shows "pair_step(pair_prev(p)) = p"
proof -
  from pair have first: "fst(p) \<in> nat"
    and second: "snd(p) \<in> nat"
    by typecheck+
  from pair have recover: "\<langle>fst(p),snd(p)\<rangle> = p"
    by (rule Pair_fst_snd_eq)
  show ?thesis
  proof (cases "snd(p) = 0")
    case True
    from first show ?thesis
    proof (cases rule: natE)
      case 0
      with True nonzero recover show ?thesis by auto
    next
      case (succ m)
      show ?thesis
        unfolding pair_prev_def pair_step_def
        using True succ recover by simp
    qed
  next
    case False
    from second show ?thesis
    proof (cases rule: natE)
      case 0
      with False show ?thesis by contradiction
    next
      case (succ n)
      show ?thesis
        unfolding pair_prev_def pair_step_def
        using False succ recover by simp
    qed
  qed
qed

lemma pair_decode_number_aux:
  assumes natural: "n \<in> nat"
  shows "\<forall>p\<in>nat \<times> nat.
    pair_number(p) = n \<longrightarrow> pair_decode(n) = p"
  using natural
proof (induct n rule: nat_induct)
  case 0
  show ?case
  proof (intro ballI impI)
    fix p
    assume pair: "p \<in> nat \<times> nat"
      and number: "pair_number(p) = 0"
    from pair_number_zero[OF pair] number have "p = \<langle>0,0\<rangle>"
      by simp
    then show "pair_decode(0) = p" by simp
  qed
next
  case (succ n)
  show ?case
  proof (intro ballI impI)
    fix p
    assume pair: "p \<in> nat \<times> nat"
      and number: "pair_number(p) = succ(n)"
    have nonzero: "p \<noteq> \<langle>0,0\<rangle>"
    proof
      assume "p = \<langle>0,0\<rangle>"
      with pair_number_zero[OF pair]
      have "pair_number(p) = 0" by simp
      with number show False by simp
    qed
    let ?q = "pair_prev(p)"
    from pair have previous: "?q \<in> nat \<times> nat"
      by (rule pair_prev_type)
    from pair nonzero have step_previous: "pair_step(?q) = p"
      by (rule pair_step_prev)
    have previous_number: "pair_number(?q) = n"
    proof -
      from pair_number_step[OF previous]
      have "succ(pair_number(?q)) = pair_number(pair_step(?q))"
        by (rule sym)
      also from step_previous have "... = pair_number(p)" by simp
      also from number have "... = succ(n)" .
      finally show ?thesis by simp
    qed
    from succ.hyps(2) previous have previous_imp:
      "pair_number(?q) = n \<longrightarrow> pair_decode(n) = ?q"
      by (rule bspec)
    from previous_imp previous_number
    have decoded_previous: "pair_decode(n) = ?q"
      by (rule mp)
    have "pair_decode(succ(n)) = pair_step(pair_decode(n))"
      by simp
    also from decoded_previous have "... = pair_step(?q)" by simp
    also from step_previous have "... = p" .
    finally show "pair_decode(succ(n)) = p" .
  qed
qed

lemma pair_decode_number:
  assumes pair: "p \<in> nat \<times> nat"
  shows "pair_decode(pair_number(p)) = p"
proof -
  from pair have natural: "pair_number(p) \<in> nat"
    by (rule pair_number_type)
  from pair_decode_number_aux[OF natural] pair show ?thesis
    by blast
qed

theorem pair_decode_code:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
  shows "pair_decode(pair_code(m,n)) = \<langle>m,n\<rangle>"
proof -
  from first second have pair: "\<langle>m,n\<rangle> \<in> nat \<times> nat"
    by typecheck
  from pair_decode_number[OF pair] show ?thesis
    unfolding pair_number_def by simp
qed

theorem pair_code_decode:
  assumes natural: "n \<in> nat"
  shows "pair_code(fst(pair_decode(n)),snd(pair_decode(n))) = n"
  using pair_number_decode[OF natural]
  unfolding pair_number_def .

lemma pair_decode_iterates:
  assumes natural: "n \<in> nat"
  shows "pair_decode(n) = pair_step^n (\<langle>0,0\<rangle>)"
  using natural by (induct n rule: nat_induct) simp_all

theorem pair_number_bij:
  "(\<lambda>p\<in>nat \<times> nat. pair_number(p))
    \<in> bij(nat \<times> nat,nat)"
proof (rule lam_bijective)
  fix p
  assume "p \<in> nat \<times> nat"
  then show "pair_number(p) \<in> nat"
    by (rule pair_number_type)
next
  fix n
  assume "n \<in> nat"
  then show "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
next
  fix p
  assume "p \<in> nat \<times> nat"
  then show "pair_decode(pair_number(p)) = p"
    by (rule pair_decode_number)
next
  fix n
  assume "n \<in> nat"
  then show "pair_number(pair_decode(n)) = n"
    by (rule pair_number_decode)
qed

lemma pair_code_second_le:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
  shows "n \<le> pair_code(m,n)"
  using first second unfolding pair_code_def
  by (simp add: add_le_self2)

lemma pair_decode_second_le:
  assumes natural: "n \<in> nat"
  shows "snd(pair_decode(n)) \<le> n"
proof -
  from natural have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have first: "fst(pair_decode(n)) \<in> nat"
    and second: "snd(pair_decode(n)) \<in> nat"
    by typecheck+
  from pair_code_second_le[OF first second]
    pair_code_decode[OF natural]
  show ?thesis by simp
qed

lemma pair_decode_second_in_succ:
  assumes natural: "n \<in> nat"
  shows "snd(pair_decode(n)) \<in> succ(n)"
proof -
  from pair_decode_second_le[OF natural]
  have less: "snd(pair_decode(n)) < succ(n)" .
  from nat_into_Ord[OF natural] have ordinal: "Ord(succ(n))"
    by (rule Ord_succ)
  from Ord_mem_iff_lt[OF ordinal] less show ?thesis
    by (rule iffD2)
qed

subsection \<open>Natural Lists\<close>

consts nat_list_encode :: "i \<Rightarrow> i"

primrec
  "nat_list_encode([]) = 0"
  "nat_list_encode(Cons(a,l)) =
    succ(pair_code(a,nat_list_encode(l)))"

definition nat_list_decode :: "i \<Rightarrow> i" where
  "nat_list_decode(n) \<equiv>
    wfrec(Memrel(nat),n,
      \<lambda>k f. nat_case([],
        \<lambda>m. Cons(fst(pair_decode(m)),f`snd(pair_decode(m))),k))"

lemmas nat_list_decode_unfold =
  def_wfrec [OF nat_list_decode_def wf_Memrel]

lemma nat_list_encode_type [TC]:
  assumes list: "l \<in> list(nat)"
  shows "nat_list_encode(l) \<in> nat"
  using list by (induct l rule: list.induct) simp_all

lemma nat_list_decode_zero [simp]:
  "nat_list_decode(0) = []"
  by (rule nat_list_decode_unfold [THEN trans]) simp

lemma nat_list_decode_succ [simp]:
  assumes natural: "n \<in> nat"
  shows "nat_list_decode(succ(n)) =
    Cons(fst(pair_decode(n)),nat_list_decode(snd(pair_decode(n))))"
proof -
  from natural have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have tail_natural: "snd(pair_decode(n)) \<in> nat"
    by typecheck
  from natural have tail: "snd(pair_decode(n)) \<in> succ(n)"
    by (rule pair_decode_second_in_succ)
  show ?thesis
    apply (rule nat_list_decode_unfold [THEN trans])
    using natural tail tail_natural
    apply (simp add: vimage_singleton_iff)
    done
qed

lemma nat_list_decode_type [TC]:
  assumes natural: "n \<in> nat"
  shows "nat_list_decode(n) \<in> list(nat)"
  using natural
proof (induct n rule: complete_induct_rule)
  case (less n)
  note smaller = less.hyps(2)
  from less.hyps(1) show ?case
  proof (cases rule: natE)
    case 0
    then show ?thesis by simp
  next
    case (succ k)
    from succ(1) have decoded: "pair_decode(k) \<in> nat \<times> nat"
      by (rule pair_decode_type)
    from decoded have head: "fst(pair_decode(k)) \<in> nat"
      and tail_natural: "snd(pair_decode(k)) \<in> nat"
      by typecheck+
    from succ(1) have tail_before:
      "snd(pair_decode(k)) \<in> succ(k)"
      by (rule pair_decode_second_in_succ)
    from smaller tail_before succ
    have tail: "nat_list_decode(snd(pair_decode(k))) \<in> list(nat)"
      by blast
    from succ head tail show ?thesis by simp
  qed
qed

theorem nat_list_decode_encode:
  assumes list: "l \<in> list(nat)"
  shows "nat_list_decode(nat_list_encode(l)) = l"
  using list
proof (induct l rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  from Cons.hyps(2) have tail_code: "nat_list_encode(l) \<in> nat"
    by (rule nat_list_encode_type)
  from Cons.hyps tail_code show ?case
    by (simp add: pair_decode_code)
qed

theorem nat_list_encode_decode:
  assumes natural: "n \<in> nat"
  shows "nat_list_encode(nat_list_decode(n)) = n"
  using natural
proof (induct n rule: complete_induct_rule)
  case (less n)
  note smaller = less.hyps(2)
  from less.hyps(1) show ?case
  proof (cases rule: natE)
    case 0
    then show ?thesis by simp
  next
    case (succ k)
    from succ(1) have decoded: "pair_decode(k) \<in> nat \<times> nat"
      by (rule pair_decode_type)
    from decoded have head: "fst(pair_decode(k)) \<in> nat"
      and tail_natural: "snd(pair_decode(k)) \<in> nat"
      by typecheck+
    from succ(1) have tail_before:
      "snd(pair_decode(k)) \<in> succ(k)"
      by (rule pair_decode_second_in_succ)
    from smaller tail_before succ have tail_roundtrip:
      "nat_list_encode(nat_list_decode(snd(pair_decode(k)))) =
        snd(pair_decode(k))"
      by blast
    from pair_code_decode[OF succ(1)] have code_roundtrip:
      "pair_code(fst(pair_decode(k)),snd(pair_decode(k))) = k" .
    from succ head tail_natural tail_roundtrip code_roundtrip
    show ?thesis by simp
  qed
qed

lemma length_nat_list_encode_le:
  assumes list: "l \<in> list(nat)"
  shows "length(l) \<le> nat_list_encode(l)"
  using list
proof (induct l rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  from Cons.hyps(2) have tail_code: "nat_list_encode(l) \<in> nat"
    by (rule nat_list_encode_type)
  from pair_code_second_le[OF Cons.hyps(1) tail_code] have code_bound:
    "nat_list_encode(l) \<le> pair_code(a,nat_list_encode(l))" .
  from Cons.hyps(3) code_bound have length_bound:
    "length(l) \<le> pair_code(a,nat_list_encode(l))"
    by (rule le_trans)
  from length_bound show ?case by simp
qed

lemma length_nat_list_decode_le:
  assumes natural: "n \<in> nat"
  shows "length(nat_list_decode(n)) \<le> n"
proof -
  from natural have decoded: "nat_list_decode(n) \<in> list(nat)"
    by (rule nat_list_decode_type)
  from length_nat_list_encode_le[OF decoded]
    nat_list_encode_decode[OF natural]
  show ?thesis by simp
qed

theorem nat_list_encode_bij:
  "(\<lambda>l\<in>list(nat). nat_list_encode(l))
    \<in> bij(list(nat),nat)"
proof (rule lam_bijective)
  fix l
  assume "l \<in> list(nat)"
  then show "nat_list_encode(l) \<in> nat"
    by (rule nat_list_encode_type)
next
  fix n
  assume "n \<in> nat"
  then show "nat_list_decode(n) \<in> list(nat)"
    by (rule nat_list_decode_type)
next
  fix l
  assume "l \<in> list(nat)"
  then show "nat_list_decode(nat_list_encode(l)) = l"
    by (rule nat_list_decode_encode)
next
  fix n
  assume "n \<in> nat"
  then show "nat_list_encode(nat_list_decode(n)) = n"
    by (rule nat_list_encode_decode)
qed

subsection \<open>Instruction Streams\<close>

text \<open>An instruction code whose action field is outside the five valid
actions decodes to a no-op instruction targeting the final state. Thus
decoding is defined for every natural number. The canonical codes are
identified separately.\<close>

definition encode_instruction :: "i \<Rightarrow> i" where
  "encode_instruction(ins) \<equiv> pair_code(fst(ins),snd(ins))"

definition decode_instruction :: "i \<Rightarrow> i" where
  "decode_instruction(n) \<equiv>
    if n \<in> nat \<and> fst(pair_decode(n)) \<in> action then
      pair_decode(n)
    else
      \<langle>nop,final_state\<rangle>"

definition instruction_code :: i where
  "instruction_code \<equiv>
    {n\<in>nat. fst(pair_decode(n)) \<in> action}"

lemma action_in_nat [TC]:
  "action \<in> nat"
  unfolding action_def by typecheck

lemma action_subset_nat:
  "action \<subseteq> nat"
  using action_in_nat Ord_nat by (blast dest: OrdmemD)

lemma instruction_code_subset_nat:
  "instruction_code \<subseteq> nat"
  unfolding instruction_code_def by blast

lemma encode_instruction_type [TC]:
  assumes instruction: "ins \<in> instruction"
  shows "encode_instruction(ins) \<in> instruction_code"
proof -
  from instruction have action_field: "fst(ins) \<in> action"
    and state_field: "snd(ins) \<in> nat"
    unfolding instruction_def by typecheck+
  from action_field action_subset_nat have natural_action: "fst(ins) \<in> nat"
    by blast
  from natural_action state_field have code_natural:
    "encode_instruction(ins) \<in> nat"
    unfolding encode_instruction_def by typecheck
  from pair_decode_code[OF natural_action state_field] action_field
    code_natural
  show ?thesis
    unfolding instruction_code_def encode_instruction_def by simp
qed

lemma decode_instruction_type [TC]:
  assumes natural: "n \<in> nat"
  shows "decode_instruction(n) \<in> instruction"
proof -
  from natural have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have pair_recover:
    "\<langle>fst(pair_decode(n)),snd(pair_decode(n))\<rangle> = pair_decode(n)"
    by (rule Pair_fst_snd_eq)
  show ?thesis
    unfolding decode_instruction_def instruction_def
    using natural decoded pair_recover by auto
qed

theorem decode_encode_instruction:
  assumes instruction: "ins \<in> instruction"
  shows "decode_instruction(encode_instruction(ins)) = ins"
proof -
  from instruction have action_field: "fst(ins) \<in> action"
    and state_field: "snd(ins) \<in> nat"
    unfolding instruction_def by typecheck+
  from action_field action_subset_nat have natural_action: "fst(ins) \<in> nat"
    by blast
  from natural_action state_field have natural_code:
    "pair_code(fst(ins),snd(ins)) \<in> nat"
    by (rule pair_code_type)
  from instruction have recover: "\<langle>fst(ins),snd(ins)\<rangle> = ins"
    unfolding instruction_def by (rule Pair_fst_snd_eq)
  show ?thesis
    unfolding decode_instruction_def encode_instruction_def
    using pair_decode_code[OF natural_action state_field]
      natural_code action_field recover
    by simp
qed

theorem encode_decode_instruction:
  assumes code: "n \<in> instruction_code"
  shows "encode_instruction(decode_instruction(n)) = n"
proof -
  from code have natural: "n \<in> nat"
    and action_field: "fst(pair_decode(n)) \<in> action"
    unfolding instruction_code_def by auto
  show ?thesis
    unfolding encode_instruction_def decode_instruction_def
    using pair_code_decode[OF natural] natural action_field by simp
qed

definition machine_code_list :: "i \<Rightarrow> i" where
  "machine_code_list(M) \<equiv> map(encode_instruction,M)"

definition decode_machine_list :: "i \<Rightarrow> i" where
  "decode_machine_list(l) \<equiv> map(decode_instruction,l)"

lemma machine_code_list_type [TC]:
  assumes machine_M: "M \<in> machine"
  shows "machine_code_list(M) \<in> list(instruction_code)"
proof -
  from machine_M have instructions: "M \<in> list(instruction)"
    unfolding machine_def .
  show ?thesis
    unfolding machine_code_list_def
    using instructions by (rule map_type) (rule encode_instruction_type)
qed

lemma machine_code_list_natural:
  assumes machine_M: "M \<in> machine"
  shows "machine_code_list(M) \<in> list(nat)"
proof -
  from machine_code_list_type[OF machine_M]
  show ?thesis
    by (rule list_mono[OF instruction_code_subset_nat, THEN subsetD])
qed

lemma decode_machine_list_type [TC]:
  assumes codes: "l \<in> list(nat)"
  shows "decode_machine_list(l) \<in> machine"
proof -
  have "map(decode_instruction,l) \<in> list(instruction)"
    using codes by (rule map_type) (rule decode_instruction_type)
  then show ?thesis
    unfolding decode_machine_list_def machine_def .
qed

theorem decode_machine_list_code:
  assumes machine_M: "M \<in> machine"
  shows "decode_machine_list(machine_code_list(M)) = M"
  using machine_M
  unfolding machine_def machine_code_list_def decode_machine_list_def
proof (induct M rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons ins M)
  then show ?case by (simp add: decode_encode_instruction)
qed

theorem machine_code_list_decode:
  assumes codes: "l \<in> list(instruction_code)"
  shows "machine_code_list(decode_machine_list(l)) = l"
  using codes unfolding machine_code_list_def decode_machine_list_def
proof (induct l rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons n l)
  from Cons show ?case by (simp add: encode_decode_instruction)
qed

subsection \<open>Machine Numbers\<close>

text \<open>Machines are encoded as finite lists of instruction numbers.
Canonical codes give a bijection with machines, while the total decoder
also accepts noncanonical natural numbers. The latter convention lets the
self-halting predicate quantify over all natural numbers.\<close>

definition encode_machine :: "i \<Rightarrow> i" where
  "encode_machine(M) \<equiv> nat_list_encode(machine_code_list(M))"

definition decode_machine :: "i \<Rightarrow> i" where
  "decode_machine(n) \<equiv>
    decode_machine_list(nat_list_decode(n))"

definition machine_code :: i where
  "machine_code \<equiv>
    {n\<in>nat. nat_list_decode(n) \<in> list(instruction_code)}"

lemma machine_code_subset_nat:
  "machine_code \<subseteq> nat"
  unfolding machine_code_def by blast

lemma encode_machine_type [TC]:
  assumes machine_M: "M \<in> machine"
  shows "encode_machine(M) \<in> machine_code"
proof -
  from machine_code_list_type[OF machine_M] have codes:
    "machine_code_list(M) \<in> list(instruction_code)" .
  from machine_code_list_natural[OF machine_M] have natural_codes:
    "machine_code_list(M) \<in> list(nat)" .
  from natural_codes
  have natural: "encode_machine(M) \<in> nat"
    unfolding encode_machine_def by (rule nat_list_encode_type)
  from nat_list_decode_encode[OF natural_codes] have decoded:
    "nat_list_decode(nat_list_encode(machine_code_list(M))) =
      machine_code_list(M)" .
  from codes natural decoded show ?thesis
    unfolding machine_code_def encode_machine_def by simp
qed

lemma decode_machine_type [TC]:
  assumes natural: "n \<in> nat"
  shows "decode_machine(n) \<in> machine"
proof -
  from natural have "nat_list_decode(n) \<in> list(nat)"
    by (rule nat_list_decode_type)
  then show ?thesis
    unfolding decode_machine_def by (rule decode_machine_list_type)
qed

theorem decode_encode_machine:
  assumes machine_M: "M \<in> machine"
  shows "decode_machine(encode_machine(M)) = M"
proof -
  from machine_code_list_natural[OF machine_M] show ?thesis
    unfolding decode_machine_def encode_machine_def
    by (simp add: nat_list_decode_encode decode_machine_list_code
        machine_M)
qed

theorem encode_decode_machine:
  assumes code: "n \<in> machine_code"
  shows "encode_machine(decode_machine(n)) = n"
proof -
  from code have natural: "n \<in> nat"
    and codes: "nat_list_decode(n) \<in> list(instruction_code)"
    unfolding machine_code_def by auto
  show ?thesis
    unfolding encode_machine_def decode_machine_def
    using machine_code_list_decode[OF codes]
      nat_list_encode_decode[OF natural]
    by simp
qed

theorem machine_numbering_bij:
  "(\<lambda>M\<in>machine. encode_machine(M))
    \<in> bij(machine,machine_code)"
proof (rule lam_bijective)
  fix M
  assume "M \<in> machine"
  then show "encode_machine(M) \<in> machine_code"
    by (rule encode_machine_type)
next
  fix n
  assume "n \<in> machine_code"
  with machine_code_subset_nat have "n \<in> nat" by blast
  then show "decode_machine(n) \<in> machine"
    by (rule decode_machine_type)
next
  fix M
  assume "M \<in> machine"
  then show "decode_machine(encode_machine(M)) = M"
    by (rule decode_encode_machine)
next
  fix n
  assume "n \<in> machine_code"
  then show "encode_machine(decode_machine(n)) = n"
    by (rule encode_decode_machine)
qed

theorem decode_machine_surj:
  "(\<lambda>n\<in>nat. decode_machine(n))
    \<in> surj(nat,machine)"
proof (rule lam_surjective)
  fix n
  assume "n \<in> nat"
  then show "decode_machine(n) \<in> machine"
    by (rule decode_machine_type)
next
  fix M
  assume "M \<in> machine"
  then have "encode_machine(M) \<in> machine_code"
    by (rule encode_machine_type)
  with machine_code_subset_nat show "encode_machine(M) \<in> nat"
    by blast
next
  fix M
  assume "M \<in> machine"
  then show "decode_machine(encode_machine(M)) = M"
    by (rule decode_encode_machine)
qed

end
