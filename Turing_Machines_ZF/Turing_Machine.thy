(*  Title:      Turing_Machine.thy
    Author:     Tang Ziyi
*)

section \<open>Set-Coded Turing Machines\<close>

theory Turing_Machine
  imports ZF
begin

subsection \<open>Machine Representation\<close>

definition symbol :: i where
  "symbol \<equiv> 2"

definition action :: i where
  "action \<equiv> succ(succ(succ(2)))"

abbreviation (input) blank_symbol :: i where
  "blank_symbol \<equiv> 0"

abbreviation (input) one_symbol :: i where
  "one_symbol \<equiv> 1"

abbreviation (input) final_state :: i where
  "final_state \<equiv> 0"

abbreviation (input) initial_state :: i where
  "initial_state \<equiv> 1"

abbreviation (input) write_blank :: i where
  "write_blank \<equiv> 0"

abbreviation (input) write_one :: i where
  "write_one \<equiv> 1"

abbreviation (input) move_left :: i where
  "move_left \<equiv> 2"

abbreviation (input) move_right :: i where
  "move_right \<equiv> succ(2)"

abbreviation (input) nop :: i where
  "nop \<equiv> succ(succ(2))"

definition tape :: i where
  "tape \<equiv> list(symbol) \<times> list(symbol)"

definition instruction :: i where
  "instruction \<equiv> action \<times> nat"

definition machine :: i where
  "machine \<equiv> list(instruction)"

definition configuration :: i where
  "configuration \<equiv> nat \<times> tape"

lemma symbol_type [simp,TC]:
  shows "blank_symbol \<in> symbol"
    and "one_symbol \<in> symbol"
  unfolding symbol_def by (simp_all add: succ_def)

lemma action_type [simp,TC]:
  shows "write_blank \<in> action"
    and "write_one \<in> action"
    and "move_left \<in> action"
    and "move_right \<in> action"
    and "nop \<in> action"
  unfolding action_def by (simp_all add: succ_def)

lemma tapeI [intro]:
  assumes left: "l \<in> list(symbol)"
    and right: "r \<in> list(symbol)"
  shows "\<langle>l,r\<rangle> \<in> tape"
  using left right unfolding tape_def by typecheck

lemma tapeD:
  assumes tape: "t \<in> tape"
  shows "fst(t) \<in> list(symbol)"
    and "snd(t) \<in> list(symbol)"
  using tape unfolding tape_def by typecheck+

subsection \<open>Tape Semantics\<close>

definition scan :: "i \<Rightarrow> i" where
  "scan(t) \<equiv> hd(snd(t))"

lemma hd_symbol_type:
  assumes symbols: "xs \<in> list(symbol)"
  shows "hd(xs) \<in> symbol"
  using symbols
  by (erule_tac a=xs in list.cases) auto

lemma scan_type [TC]:
  assumes tape: "t \<in> tape"
  shows "scan(t) \<in> symbol"
proof -
  from tape have "snd(t) \<in> list(symbol)" by (rule tapeD)
  then show ?thesis
    unfolding scan_def by (rule hd_symbol_type)
qed

lemma scan_pair [simp]:
  "scan(\<langle>l,r\<rangle>) = hd(r)"
  unfolding scan_def by simp

definition update :: "[i,i] \<Rightarrow> i" where
  "update(a,t) \<equiv>
    if a = write_blank then
      \<langle>fst(t),Cons(blank_symbol,tl(snd(t)))\<rangle>
    else if a = write_one then
      \<langle>fst(t),Cons(one_symbol,tl(snd(t)))\<rangle>
    else if a = move_left then
      \<langle>tl(fst(t)),Cons(hd(fst(t)),snd(t))\<rangle>
    else if a = move_right then
      \<langle>Cons(hd(snd(t)),fst(t)),tl(snd(t))\<rangle>
    else t"

lemma update_type [TC]:
  assumes tape: "t \<in> tape"
  shows "update(a,t) \<in> tape"
proof -
  from tape
  have left: "fst(t) \<in> list(symbol)"
    and right: "snd(t) \<in> list(symbol)"
    by (rule tapeD)+
  from left have left_head: "hd(fst(t)) \<in> symbol"
    by (rule hd_symbol_type)
  from right have right_head: "hd(snd(t)) \<in> symbol"
    by (rule hd_symbol_type)
  from left have left_tail: "tl(fst(t)) \<in> list(symbol)"
    by (rule tl_type)
  from right have right_tail: "tl(snd(t)) \<in> list(symbol)"
    by (rule tl_type)
  show ?thesis
    unfolding update_def
    using tape left right left_head right_head left_tail right_tail
    by (auto intro: tapeI)
qed

lemma update_write_blank [simp]:
  "update(write_blank,t) =
    \<langle>fst(t),Cons(blank_symbol,tl(snd(t)))\<rangle>"
  unfolding update_def by simp

lemma update_write_one [simp]:
  "update(write_one,t) =
    \<langle>fst(t),Cons(one_symbol,tl(snd(t)))\<rangle>"
  unfolding update_def by simp

lemma update_move_left [simp]:
  "update(move_left,t) =
    \<langle>tl(fst(t)),Cons(hd(fst(t)),snd(t))\<rangle>"
  unfolding update_def by simp

lemma update_move_right [simp]:
  "update(move_right,t) =
    \<langle>Cons(hd(snd(t)),fst(t)),tl(snd(t))\<rangle>"
  unfolding update_def by simp

lemma update_nop [simp]:
  "update(nop,t) = t"
  unfolding update_def by simp

subsection \<open>One-Step Semantics\<close>

definition slot :: "[i,i] \<Rightarrow> i" where
  "slot(q,b) \<equiv> 2 #* pred(q) #+ b"

lemma slot_type [TC]:
  assumes state: "q \<in> nat"
    and scanned: "b \<in> symbol"
  shows "slot(q,b) \<in> nat"
  using state scanned unfolding slot_def symbol_def by typecheck

lemma slot_succ [simp]:
  assumes state: "q \<in> nat"
  shows "slot(succ(q),b) = 2 #* q #+ b"
  using state unfolding slot_def by simp

definition fetch :: "[i,i,i] \<Rightarrow> i" where
  "fetch(M,q,b) \<equiv>
    if q = final_state then \<langle>nop,final_state\<rangle>
    else if slot(q,b) < length(M) then
      nth(slot(q,b),M)
    else \<langle>nop,final_state\<rangle>"

lemma fetch_type [TC]:
  assumes machine: "M \<in> machine"
  shows "fetch(M,q,b) \<in> instruction"
  using machine
  unfolding fetch_def machine_def instruction_def
  by (auto intro: nth_type)

lemma fetch_final [simp]:
  "fetch(M,final_state,b) = \<langle>nop,final_state\<rangle>"
  unfolding fetch_def by simp

lemma fetch_in_range [simp]:
  assumes nonfinal: "q \<noteq> final_state"
    and in_range: "slot(q,b) < length(M)"
  shows "fetch(M,q,b) = nth(slot(q,b),M)"
  using nonfinal in_range unfolding fetch_def by simp

lemma fetch_out_of_range [simp]:
  assumes out_of_range: "\<not> slot(q,b) < length(M)"
  shows "fetch(M,q,b) = \<langle>nop,final_state\<rangle>"
  using out_of_range unfolding fetch_def by simp

definition step :: "[i,i] \<Rightarrow> i" where
  "step(M,c) \<equiv>
    let ins = fetch(M,fst(c),scan(snd(c)))
    in \<langle>snd(ins),update(fst(ins),snd(c))\<rangle>"

lemma step_type [TC]:
  assumes machine: "M \<in> machine"
    and configuration: "c \<in> configuration"
  shows "step(M,c) \<in> configuration"
proof -
  have fetched_instruction:
    "fetch(M,fst(c),scan(snd(c))) \<in> instruction"
    using machine by (rule fetch_type)
  have current_tape: "snd(c) \<in> tape"
    using configuration unfolding configuration_def by typecheck
  show ?thesis
    unfolding step_def Let_def configuration_def
    using fetched_instruction current_tape
    unfolding instruction_def by typecheck
qed

lemma step_pair [simp]:
  "step(M,\<langle>q,t\<rangle>) =
    \<langle>snd(fetch(M,q,scan(t))),
      update(fst(fetch(M,q,scan(t))),t)\<rangle>"
  unfolding step_def Let_def by simp

lemma step_final [simp]:
  "step(M,\<langle>final_state,t\<rangle>) = \<langle>final_state,t\<rangle>"
  unfolding step_def Let_def by simp

subsection \<open>Finite Computations\<close>

definition steps :: "[i,i,i] \<Rightarrow> i" where
  "steps(M,c,n) \<equiv> (\<lambda>x. step(M,x))^n (c)"

lemma steps_0 [simp]:
  "steps(M,c,0) = c"
  unfolding steps_def by simp

lemma steps_succ [simp]:
  "steps(M,c,succ(n)) = step(M,steps(M,c,n))"
  unfolding steps_def by simp

lemma steps_type [TC]:
  assumes machine: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and time: "n \<in> nat"
  shows "steps(M,c,n) \<in> configuration"
  unfolding steps_def
proof (rule iterates_type)
  show "n \<in> nat" by (rule time)
  show "c \<in> configuration" by (rule configuration)
  fix x
  assume "x \<in> configuration"
  with machine show "step(M,x) \<in> configuration"
    by (rule step_type)
qed

lemma steps_add:
  assumes m_nat: "m \<in> nat"
    and n_nat: "n \<in> nat"
  shows "steps(M,c,m #+ n) = steps(M,steps(M,c,m),n)"
proof -
  from n_nat show ?thesis
  proof (induct n rule: nat_induct)
    case 0
    with m_nat show ?case by simp
  next
    case (succ n)
    with m_nat show ?case by simp
  qed
qed

lemma steps_final [simp]:
  assumes time: "n \<in> nat"
  shows "steps(M,\<langle>final_state,t\<rangle>,n) =
    \<langle>final_state,t\<rangle>"
  using time unfolding steps_def
  by (rule iterates_triv) simp

lemma steps_final_mono:
  assumes machine_M: "M \<in> machine"
    and configuration: "c \<in> configuration"
    and earlier: "m \<in> nat"
    and later: "n \<in> nat"
    and ordered: "m \<le> n"
    and final: "fst(steps(M,c,m)) = final_state"
  shows "fst(steps(M,c,n)) = final_state"
proof -
  let ?d = "n #- m"
  let ?z = "steps(M,c,m)"
  have difference: "?d \<in> nat"
    by typecheck
  from add_diff_inverse[OF ordered later] have decomposition:
    "m #+ ?d = n" .
  from steps_type[OF machine_M configuration earlier]
  have reached: "?z \<in> configuration" .
  from reached have pair:
    "\<langle>fst(?z),snd(?z)\<rangle> = ?z"
    unfolding configuration_def by (rule Pair_fst_snd_eq)
  from pair final have final_pair:
    "?z = \<langle>final_state,snd(?z)\<rangle>"
    by simp
  from steps_final[OF difference, of M "snd(?z)"] final_pair
  have absorbed: "steps(M,?z,?d) = ?z"
    by simp
  from steps_add[OF earlier difference, of M c]
  have split:
    "steps(M,c,m #+ ?d) = steps(M,?z,?d)" .
  from decomposition split absorbed final show ?thesis
    by simp
qed

definition finite_run :: "[i,i,i] \<Rightarrow> o" where
  "finite_run(M,n,r) \<equiv>
    relation(r) \<and>
    function(r) \<and>
    domain(r) = succ(n) \<and>
    (\<forall>k\<in>n. r`succ(k) = step(M,r`k))"

lemma finite_run_iff_steps:
  assumes time: "n \<in> nat"
  shows "finite_run(M,n,r) \<and> r`0 = c \<longleftrightarrow>
    r = (\<lambda>k\<in>succ(n). steps(M,c,k))"
proof
  assume run: "finite_run(M,n,r) \<and> r`0 = c"
  then have relational: "relation(r)"
    and functional: "function(r)"
    and domain: "domain(r) = succ(n)"
    and initial: "r`0 = c"
    and next_step: "\<And>k. k \<in> n \<Longrightarrow> r`succ(k) = step(M,r`k)"
    unfolding finite_run_def by auto
  from function_imp_Pi[OF functional relational] domain
  have run_type: "r \<in> succ(n) \<rightarrow> range(r)"
    by simp
  have canonical_type:
    "(\<lambda>k\<in>succ(n). steps(M,c,k))
      \<in> succ(n) \<rightarrow> {steps(M,c,k). k \<in> succ(n)}"
    by (rule lam_funtype)
  have trace_at:
    "\<And>k. k \<in> succ(n) \<Longrightarrow> r`k = steps(M,c,k)"
  proof -
    fix k
    assume within: "k \<in> succ(n)"
    with time have natural: "k \<in> nat"
      by (blast intro: Ord_trans Ord_nat)
    from natural within show "r`k = steps(M,c,k)"
    proof (induct k rule: nat_induct)
      case 0
      with initial show ?case by simp
    next
      case (succ k)
      from succ.prems time have before_end: "k \<in> n"
        by (blast intro: Ord_trans nat_into_Ord)
      then have within: "k \<in> succ(n)" by auto
      from next_step[OF before_end] succ.hyps(2)[OF within]
      show ?case by simp
    qed
  qed
  show "r = (\<lambda>k\<in>succ(n). steps(M,c,k))"
  proof (rule fun_extension)
    show "r \<in> succ(n) \<rightarrow> range(r)"
      by (rule run_type)
    show "(\<lambda>k\<in>succ(n). steps(M,c,k))
        \<in> succ(n) \<rightarrow> {steps(M,c,k). k \<in> succ(n)}"
      by (rule canonical_type)
    fix k
    assume "k \<in> succ(n)"
    with trace_at show "r`k = (\<lambda>k\<in>succ(n). steps(M,c,k))`k"
      by simp
  qed
next
  assume canonical: "r = (\<lambda>k\<in>succ(n). steps(M,c,k))"
  have next_step:
    "\<And>k. k \<in> n \<Longrightarrow>
      (\<lambda>j\<in>succ(n). steps(M,c,j))`succ(k) =
      step(M,(\<lambda>j\<in>succ(n). steps(M,c,j))`k)"
  proof -
    fix k
    assume before_end: "k \<in> n"
    then have within: "k \<in> succ(n)"
      by (rule succI2)
    from before_end nat_into_Ord[OF time]
    have next_within: "succ(k) \<in> succ(n)"
      by (simp add: Ord_succ_mem_iff)
    show "(\<lambda>j\<in>succ(n). steps(M,c,j))`succ(k) =
      step(M,(\<lambda>j\<in>succ(n). steps(M,c,j))`k)"
      using within next_within by simp
  qed
  from time have zero_within: "0 \<in> succ(n)"
    by (rule nat_0_le [THEN ltD])
  have initial: "(\<lambda>k\<in>succ(n). steps(M,c,k))`0 = c"
    using zero_within by simp
  show "finite_run(M,n,r) \<and> r`0 = c"
    unfolding canonical finite_run_def
    using next_step initial
    by (auto intro: relation_lam function_lam)
qed

subsection \<open>Halting\<close>

abbreviation initial_config :: "i \<Rightarrow> i" where
  "initial_config(x) \<equiv> \<langle>initial_state,\<langle>[],x\<rangle>\<rangle>"

lemma initial_config_type [TC]:
  assumes input: "x \<in> list(symbol)"
  shows "initial_config(x) \<in> configuration"
  using input unfolding configuration_def tape_def by typecheck

definition halts_on :: "[i,i] \<Rightarrow> o" where
  "halts_on(M,x) \<equiv>
    M \<in> machine \<and>
    x \<in> list(symbol) \<and>
    (\<exists>n\<in>nat.
      fst(steps(M,initial_config(x),n)) = final_state)"

theorem halts_on_iff_finite_run:
  "halts_on(M,x) \<longleftrightarrow>
    M \<in> machine \<and>
    x \<in> list(symbol) \<and>
    (\<exists>n\<in>nat. \<exists>r.
      finite_run(M,n,r) \<and>
      r`0 = initial_config(x) \<and>
      fst(r`n) = final_state)"
proof
  assume halts: "halts_on(M,x)"
  then obtain n where
    machine: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and time: "n \<in> nat"
    and final: "fst(steps(M,initial_config(x),n)) = final_state"
    unfolding halts_on_def by auto
  let ?r = "\<lambda>k\<in>succ(n). steps(M,initial_config(x),k)"
  have run: "finite_run(M,n,?r) \<and> ?r`0 = initial_config(x)"
    using finite_run_iff_steps[OF time, of M ?r "initial_config(x)"]
    by simp
  have endpoint: "?r`n = steps(M,initial_config(x),n)"
    using time by simp
  have final_run: "fst(?r`n) = final_state"
    using endpoint final by simp
  show "M \<in> machine \<and>
    x \<in> list(symbol) \<and>
    (\<exists>n\<in>nat. \<exists>r.
      finite_run(M,n,r) \<and>
      r`0 = initial_config(x) \<and>
      fst(r`n) = final_state)"
    using machine input time run final_run by blast
next
  assume witness:
    "M \<in> machine \<and>
      x \<in> list(symbol) \<and>
      (\<exists>n\<in>nat. \<exists>r.
        finite_run(M,n,r) \<and>
        r`0 = initial_config(x) \<and>
        fst(r`n) = final_state)"
  then obtain n r where
    machine: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and time: "n \<in> nat"
    and run: "finite_run(M,n,r)"
    and initial: "r`0 = initial_config(x)"
    and final: "fst(r`n) = final_state"
    by auto
  from finite_run_iff_steps[OF time, of M r "initial_config(x)"]
    run initial
  have canonical:
    "r = (\<lambda>k\<in>succ(n). steps(M,initial_config(x),k))"
    by blast
  have endpoint: "r`n = steps(M,initial_config(x),n)"
    unfolding canonical using time by simp
  have final_step:
    "fst(steps(M,initial_config(x),n)) = final_state"
    using final endpoint by simp
  show "halts_on(M,x)"
    unfolding halts_on_def
    using machine input time final_step by blast
qed

abbreviation halts_blank :: "i \<Rightarrow> o" where
  "halts_blank(M) \<equiv> halts_on(M,[])"

end
