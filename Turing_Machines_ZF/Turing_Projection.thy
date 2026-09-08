(*  Title:      Turing_Projection.thy
    Author:     Tang Ziyi
*)

section \<open>Total Argument Projection\<close>

theory Turing_Projection
  imports Turing_Storage
begin

abbreviation (input) kp_next where "kp_next \<equiv> succ(2)"
abbreviation (input) kp_move where "kp_move \<equiv> succ(succ(2))"
abbreviation (input) kp_return_blanks where "kp_return_blanks \<equiv> succ(succ(succ(2)))"
abbreviation (input) kp_erase where "kp_erase \<equiv> succ(succ(succ(succ(2))))"
abbreviation (input) kp_rewind where "kp_rewind \<equiv> succ(succ(succ(succ(succ(2)))))"

text \<open>The first positive block is retained while all later arguments
are erased. Its remaining strokes provide a boundary for rewinding across
the erased workspace. Empty input is handled before this return scan.\<close>

definition keep_first_machine :: i where
  "keep_first_machine \<equiv>
   [\<langle>nop,final_state\<rangle>,\<langle>move_right,2\<rangle>,
    \<langle>move_right,kp_next\<rangle>,\<langle>move_right,2\<rangle>,
    \<langle>move_left,kp_return_blanks\<rangle>,\<langle>write_blank,kp_move\<rangle>,
    \<langle>move_right,kp_erase\<rangle>,\<langle>move_right,kp_erase\<rangle>,
    \<langle>move_left,kp_return_blanks\<rangle>,\<langle>move_left,kp_rewind\<rangle>,
    \<langle>move_right,kp_next\<rangle>,\<langle>write_blank,kp_move\<rangle>,
    \<langle>move_right,final_state\<rangle>,\<langle>move_left,kp_rewind\<rangle>]"

lemma keep_first_machine_type [TC]: "keep_first_machine \<in> machine"
  unfolding keep_first_machine_def machine_def instruction_def by typecheck

lemma fetch_keep_first [simp]:
  "fetch(keep_first_machine,1,0) = \<langle>nop,final_state\<rangle>"
  "fetch(keep_first_machine,1,1) = \<langle>move_right,2\<rangle>"
  "fetch(keep_first_machine,2,0) = \<langle>move_right,kp_next\<rangle>"
  "fetch(keep_first_machine,2,1) = \<langle>move_right,2\<rangle>"
  "fetch(keep_first_machine,kp_next,0) = \<langle>move_left,kp_return_blanks\<rangle>"
  "fetch(keep_first_machine,kp_next,1) = \<langle>write_blank,kp_move\<rangle>"
  "fetch(keep_first_machine,kp_move,0) = \<langle>move_right,kp_erase\<rangle>"
  "fetch(keep_first_machine,kp_return_blanks,0) = \<langle>move_left,kp_return_blanks\<rangle>"
  "fetch(keep_first_machine,kp_return_blanks,1) = \<langle>move_left,kp_rewind\<rangle>"
  "fetch(keep_first_machine,kp_erase,0) = \<langle>move_right,kp_next\<rangle>"
  "fetch(keep_first_machine,kp_erase,1) = \<langle>write_blank,kp_move\<rangle>"
  "fetch(keep_first_machine,kp_rewind,0) = \<langle>move_right,final_state\<rangle>"
  "fetch(keep_first_machine,kp_rewind,1) = \<langle>move_left,kp_rewind\<rangle>"
  by (simp_all add: keep_first_machine_def fetch_def slot_def)

lemma keep_first_computes_Cons:
  assumes n: "n \<in> nat" and ns: "ns \<in> list(nat)"
  shows "computes_tape(keep_first_machine,arguments(Cons(n,ns)),numeral_input(succ(n)))"
proof -
  let ?tail = "arguments(ns)"
  let ?x = "numeral_input(succ(n))"
  let ?k = "succ(length(?tail))"
  let ?pad = "repeat(blank_symbol,?k)"
  have tail: "?tail \<in> list(symbol)" using ns by typecheck
  have k: "?k \<in> nat" using tail by typecheck
  have pad: "?pad \<in> list(symbol)" using k by typecheck
  have x: "?x \<in> list(symbol)" using n by typecheck
  have input: "arguments(Cons(n,ns)) \<in> list(symbol)" using n ns by typecheck
  have first: "reaches(keep_first_machine,initial_config(arguments(Cons(n,ns))),
    \<langle>2,\<langle>[one_symbol],numeral_input(n) @ Cons(blank_symbol,?tail)\<rangle>\<rangle>)"
    by (rule bexI[of _ 1]) simp_all
  have seek: "reaches(keep_first_machine,
    \<langle>2,\<langle>[one_symbol],numeral_input(n) @ Cons(blank_symbol,?tail)\<rangle>\<rangle>,
    \<langle>2,\<langle>?x,Cons(blank_symbol,?tail)\<rangle>\<rangle>)"
    using scan_right_ones[OF fetch_keep_first(4) n, of "[one_symbol]" "Cons(blank_symbol,?tail)"]
      numeral_append_cons[OF n, of "[]"] numeral_input_type[OF n] by simp
  have cross: "reaches(keep_first_machine,\<langle>2,\<langle>?x,Cons(blank_symbol,?tail)\<rangle>\<rangle>,
    \<langle>kp_next,\<langle>Cons(blank_symbol,?x),?tail\<rangle>\<rangle>)"
    by (rule bexI[of _ 1]) simp_all
  have erase: "reaches(keep_first_machine,\<langle>kp_next,\<langle>Cons(blank_symbol,?x),?tail\<rangle>\<rangle>,
    \<langle>kp_next,\<langle>?pad @ ?x,[]\<rangle>\<rangle>)"
    using erase_arguments[OF fetch_keep_first(6) fetch_keep_first(11) fetch_keep_first(7)
      fetch_keep_first(10) ns, of "Cons(blank_symbol,?x)"] tail
    by (simp add: repeat_append_cons)
  have return_blanks: "reaches(keep_first_machine,\<langle>kp_next,\<langle>?pad @ ?x,[]\<rangle>\<rangle>,
    \<langle>kp_return_blanks,\<langle>numeral_input(n),Cons(one_symbol,?pad)\<rangle>\<rangle>)"
    using enter_left_repeated[OF _ fetch_keep_first(8) k, where p=kp_next and l="?x" and r="[]"] pad by simp
  have rewind: "reaches(keep_first_machine,
    \<langle>kp_return_blanks,\<langle>numeral_input(n),Cons(one_symbol,?pad)\<rangle>\<rangle>,
    \<langle>kp_rewind,\<langle>[],Cons(blank_symbol,?x @ ?pad)\<rangle>\<rangle>)"
    using enter_left_ones[OF _ fetch_keep_first(13) n, where p=kp_return_blanks and l="[]" and r="Cons(one_symbol,?pad)"]
      numeral_input_type[OF n] numeral_append_cons[OF n, of ?pad] by simp
  have exit: "reaches(keep_first_machine,\<langle>kp_rewind,\<langle>[],Cons(blank_symbol,?x @ ?pad)\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[blank_symbol],?x @ ?pad\<rangle>\<rangle>)"
    by (rule bexI[of _ 1]) simp_all
  have start: "config_eq(initial_config(arguments(Cons(n,ns))),initial_config(arguments(Cons(n,ns))))"
    by (rule config_eq_refl[OF initial_config_type[OF input]])
  have right: "half_tape_eq(?x @ ?pad,?x)"
    using half_tape_eq_append[OF x half_tape_eq_blank_repeat[OF k]] x by simp
  have finish: "config_eq(\<langle>final_state,\<langle>[blank_symbol],?x @ ?pad\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[],?x\<rangle>\<rangle>)"
    using x pad right unfolding config_eq_def tape_eq_def configuration_def tape_def by auto
  show ?thesis by (rule computes_tape_from_reaches[OF keep_first_machine_type input x start
    reaches_trans[OF first reaches_trans[OF seek reaches_trans[OF cross
      reaches_trans[OF erase reaches_trans[OF return_blanks reaches_trans[OF rewind exit]]]]]] finish])
qed

lemma keep_first_computes_Nil: "computes_tape(keep_first_machine,[],[])"
proof -
  have eq: "config_eq(steps(keep_first_machine,initial_config([]),1),\<langle>final_state,\<langle>[],[]\<rangle>\<rangle>)"
    unfolding config_eq_def tape_eq_def configuration_def tape_def by simp
  from eq keep_first_machine_type show ?thesis
    unfolding computes_tape_def by (auto intro!: bexI[of _ 1])
qed

definition tm_realises_arguments :: "[i,i] \<Rightarrow> o" where
  "tm_realises_arguments(M,f) \<equiv> M \<in> machine \<and> f \<in> list(nat) \<rightarrow> nat \<and>
    (\<forall>ns\<in>list(nat). computes_tape(M,arguments(ns),numeral_input(f`ns)))"

text \<open>This interface quantifies over all argument lists, including empty
lists and arguments beyond a function's usual arity. It matches ZF-Induct's
total list-based primitive-recursive functions without an arity assumption.\<close>

theorem keep_first_realises_SC: "tm_realises_arguments(keep_first_machine,SC)"
proof -
  have computes: "\<And>ns. ns \<in> list(nat) \<Longrightarrow>
    computes_tape(keep_first_machine,arguments(ns),numeral_input(SC`ns))"
  proof -
    fix ns assume ns: "ns \<in> list(nat)"
    from ns show "computes_tape(keep_first_machine,arguments(ns),numeral_input(SC`ns))"
    proof (cases rule: list.cases)
      case Nil then show ?thesis by (simp add: SC_def keep_first_computes_Nil)
    next
      case (Cons n ns)
      from keep_first_computes_Cons[OF Cons(2,3)] Cons show ?thesis by (simp add: SC_def)
    qed
  qed
  show ?thesis unfolding tm_realises_arguments_def using keep_first_machine_type computes
    by (auto intro: prim_rec_into_fun)
qed

definition predecessor_machine :: i where
  "predecessor_machine \<equiv>
   [\<langle>nop,final_state\<rangle>,\<langle>write_blank,2\<rangle>,
    \<langle>move_right,final_state\<rangle>,\<langle>move_right,final_state\<rangle>]"

lemma predecessor_machine_type [TC]: "predecessor_machine \<in> machine"
  unfolding predecessor_machine_def machine_def instruction_def by typecheck

lemma predecessor_computes:
  assumes n: "n \<in> nat"
  shows "computes_number(predecessor_machine,n,pred(n))"
  using n
proof (cases rule: natE)
  case 0
  have eq: "config_eq(steps(predecessor_machine,initial_config([]),1),\<langle>final_state,\<langle>[],[]\<rangle>\<rangle>)"
    unfolding config_eq_def tape_eq_def configuration_def tape_def
    by (simp add: predecessor_machine_def fetch_def slot_def)
  from eq predecessor_machine_type 0 show ?thesis
    unfolding computes_number_def by (auto intro!: bexI[of _ 1])
next
  case (succ k)
  have eq: "config_eq(steps(predecessor_machine,initial_config(numeral_input(n)),2),
    \<langle>final_state,\<langle>[],numeral_input(k)\<rangle>\<rangle>)"
    using numeral_input_type[OF succ(1)] succ(2)
    unfolding config_eq_def tape_eq_def configuration_def tape_def
    by (simp add: predecessor_machine_def fetch_def slot_def)
  from eq predecessor_machine_type succ n show ?thesis
    unfolding computes_number_def by (auto intro!: bexI[of _ 2])
qed

definition first_projection_machine :: i where
  "first_projection_machine \<equiv> sequential_machine(keep_first_machine,predecessor_machine)"

lemma first_projection_machine_type [TC]: "first_projection_machine \<in> machine"
  unfolding first_projection_machine_def by typecheck

lemma first_projection_computes:
  assumes ns: "ns \<in> list(nat)"
  shows "computes_tape(first_projection_machine,arguments(ns),numeral_input(PROJ(0)`ns))"
proof -
  from keep_first_realises_SC ns
  have first: "computes_tape(keep_first_machine,arguments(ns),numeral_input(SC`ns))"
    unfolding tm_realises_arguments_def by blast
  have num: "SC`ns \<in> nat" using ns by typecheck
  from predecessor_computes[OF num] computes_number_iff_tape
  have second: "computes_tape(predecessor_machine,numeral_input(SC`ns),numeral_input(pred(SC`ns)))" by blast
  have value: "pred(SC`ns) = PROJ(0)`ns"
    using ns by (cases rule: list.cases) (simp_all add: SC_def PROJ_def)
  from computes_tape_sequential[OF first second] value
  show ?thesis unfolding first_projection_machine_def by simp
qed

consts projection_machine :: "i \<Rightarrow> i"
primrec
  "projection_machine(0) = first_projection_machine"
  "projection_machine(succ(i)) = sequential_machine(drop_argument_machine,projection_machine(i))"

lemma projection_machine_type [TC]:
  "i \<in> nat \<Longrightarrow> projection_machine(i) \<in> machine"
  by (induct i rule: nat_induct)
    (auto intro: sequential_machine_type first_projection_machine_type drop_argument_machine_type)

lemma projection_computes:
  assumes i: "i \<in> nat" and ns: "ns \<in> list(nat)"
  shows "computes_tape(projection_machine(i),arguments(ns),numeral_input(PROJ(i)`ns))"
  using i ns
proof (induct i arbitrary: ns rule: nat_induct)
  case 0 then show ?case by (simp add: first_projection_computes)
next
  case (succ i)
  have tail: "tl(ns) \<in> list(nat)" using succ.prems by (rule tl_type)
  have value: "PROJ(i)`tl(ns) = PROJ(succ(i))`ns"
    using succ.prems
    by (cases rule: list.cases) (simp_all add: PROJ_def succ.hyps(1))
  from computes_tape_sequential[OF drop_argument_computes[OF succ.prems] succ.hyps(2)[OF tail]] value
  show ?case by simp
qed

theorem projection_realises_PROJ:
  "i \<in> nat \<Longrightarrow> tm_realises_arguments(projection_machine(i),PROJ(i))"
  unfolding tm_realises_arguments_def
  using projection_machine_type projection_computes by (auto intro: prim_rec_into_fun)

end
