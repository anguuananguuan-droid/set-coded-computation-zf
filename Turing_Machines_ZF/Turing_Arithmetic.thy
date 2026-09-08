(*  Title:      Turing_Arithmetic.thy
    Author:     Tang Ziyi
*)

section \<open>Concrete Addition and Numerical Composition\<close>

theory Turing_Arithmetic
  imports Turing_Copy Turing_Primrec
begin

abbreviation (input) add_rewind where "add_rewind \<equiv> succ(2)"
abbreviation (input) add_erase_first where "add_erase_first \<equiv> succ(succ(2))"
abbreviation (input) add_move_first where "add_move_first \<equiv> succ(succ(succ(2)))"
abbreviation (input) add_erase_second where "add_erase_second \<equiv> succ(succ(succ(succ(2))))"
abbreviation (input) add_move_second where "add_move_second \<equiv> succ(succ(succ(succ(succ(2)))))"
abbreviation (input) add_erase_third where "add_erase_third \<equiv> succ(succ(succ(succ(succ(succ(2))))))"
abbreviation (input) add_move_third where "add_move_third \<equiv> succ(succ(succ(succ(succ(succ(succ(2)))))))"

text \<open>The separator between the positive blocks is replaced by a stroke.
The joined block has n+m+3 strokes. Rewinding and erasing its first three
strokes leaves the ordinary unary output n+m, including when both inputs
are zero. The head finishes at the start of that output.\<close>

definition addition_machine :: i where
  "addition_machine \<equiv>
   [\<langle>write_one,2\<rangle>,\<langle>move_right,initial_state\<rangle>,
    \<langle>move_left,add_rewind\<rangle>,\<langle>move_left,add_rewind\<rangle>,
    \<langle>move_right,add_erase_first\<rangle>,\<langle>move_left,add_rewind\<rangle>,
    \<langle>write_blank,add_move_first\<rangle>,\<langle>write_blank,add_move_first\<rangle>,
    \<langle>move_right,add_erase_second\<rangle>,\<langle>move_right,add_erase_second\<rangle>,
    \<langle>write_blank,add_move_second\<rangle>,\<langle>write_blank,add_move_second\<rangle>,
    \<langle>move_right,add_erase_third\<rangle>,\<langle>move_right,add_erase_third\<rangle>,
    \<langle>write_blank,add_move_third\<rangle>,\<langle>write_blank,add_move_third\<rangle>,
    \<langle>move_right,final_state\<rangle>,\<langle>move_right,final_state\<rangle>]"

lemma addition_machine_type [TC]: "addition_machine \<in> machine"
  unfolding addition_machine_def machine_def instruction_def by typecheck

lemma fetch_addition [simp]:
  "fetch(addition_machine,1,0) = \<langle>write_one,2\<rangle>"
  "fetch(addition_machine,1,1) = \<langle>move_right,initial_state\<rangle>"
  "fetch(addition_machine,2,0) = \<langle>move_left,add_rewind\<rangle>"
  "fetch(addition_machine,2,1) = \<langle>move_left,add_rewind\<rangle>"
  "fetch(addition_machine,add_rewind,0) = \<langle>move_right,add_erase_first\<rangle>"
  "fetch(addition_machine,add_rewind,1) = \<langle>move_left,add_rewind\<rangle>"
  "fetch(addition_machine,add_erase_first,1) = \<langle>write_blank,add_move_first\<rangle>"
  "fetch(addition_machine,add_move_first,0) = \<langle>move_right,add_erase_second\<rangle>"
  "fetch(addition_machine,add_erase_second,1) = \<langle>write_blank,add_move_second\<rangle>"
  "fetch(addition_machine,add_move_second,0) = \<langle>move_right,add_erase_third\<rangle>"
  "fetch(addition_machine,add_erase_third,1) = \<langle>write_blank,add_move_third\<rangle>"
  "fetch(addition_machine,add_move_third,0) = \<langle>move_right,final_state\<rangle>"
  by (simp_all add: addition_machine_def fetch_def slot_def)

lemma addition_run:
  assumes n: "n \<in> nat" and m: "m \<in> nat"
  shows "reaches(addition_machine,
    initial_config(numeral_input(succ(n)) @ Cons(blank_symbol,numeral_input(succ(m)))),
    \<langle>final_state,\<langle>[blank_symbol,blank_symbol,blank_symbol,blank_symbol],numeral_input(n #+ m)\<rangle>\<rangle>)"
proof -
  let ?x = "numeral_input(succ(n))"
  let ?y = "numeral_input(succ(m))"
  let ?sum = "numeral_input(succ(succ(succ(n #+ m))))"
  have x: "?x \<in> list(symbol)" using n by typecheck
  have seek: "reaches(addition_machine,initial_config(?x @ Cons(blank_symbol,?y)),
    \<langle>initial_state,\<langle>?x,Cons(blank_symbol,?y)\<rangle>\<rangle>)"
    using scan_right_ones[OF fetch_addition(2) nat_succI[OF n], of "[]" "Cons(blank_symbol,?y)"] x by simp
  have fill: "reaches(addition_machine,\<langle>initial_state,\<langle>?x,Cons(blank_symbol,?y)\<rangle>\<rangle>,
    \<langle>2,\<langle>?x,Cons(one_symbol,?y)\<rangle>\<rangle>)"
    by (rule bexI[of _ 1]) simp_all
  have joined: "?x @ Cons(one_symbol,?y) = ?sum"
    using n m by (simp add: numeral_append_cons numeral_append)
  have rewind: "reaches(addition_machine,\<langle>2,\<langle>?x,Cons(one_symbol,?y)\<rangle>\<rangle>,
    \<langle>add_rewind,\<langle>[],Cons(blank_symbol,?sum)\<rangle>\<rangle>)"
    using enter_left_ones[OF _ fetch_addition(6) nat_succI[OF n], where
        p=2 and l="[]" and r="Cons(one_symbol,?y)"] x joined by simp
  have erase: "reaches(addition_machine,\<langle>add_rewind,\<langle>[],Cons(blank_symbol,?sum)\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[blank_symbol,blank_symbol,blank_symbol,blank_symbol],numeral_input(n #+ m)\<rangle>\<rangle>)"
    by (rule bexI[of _ "succ(succ(succ(succ(succ(2)))))"]) simp_all
  show ?thesis by (rule reaches_trans[OF seek reaches_trans[OF fill reaches_trans[OF rewind erase]]])
qed

theorem addition_computes:
  assumes n: "n \<in> nat" and m: "m \<in> nat"
  shows "computes_tape(addition_machine,arguments([n,m]),numeral_input(n #+ m))"
proof -
  let ?x = "numeral_input(succ(n)) @ Cons(blank_symbol,numeral_input(succ(m)))"
  let ?y = "numeral_input(n #+ m)"
  let ?blanks = "[blank_symbol,blank_symbol,blank_symbol,blank_symbol]"
  have x: "?x \<in> list(symbol)" using n m by typecheck
  have args: "arguments([n,m]) = ?x @ [blank_symbol]"
    using numeral_input_type[OF n] by (simp add: app_assoc)
  have input: "arguments([n,m]) \<in> list(symbol)" using n m by typecheck
  have y: "?y \<in> list(symbol)" by typecheck
  have right: "half_tape_eq(?x,arguments([n,m]))"
    using half_tape_eq_sym[OF half_tape_eq_trailing_blank[OF x]] args by simp
  have start: "config_eq(initial_config(?x),initial_config(arguments([n,m])))"
    using x input right unfolding config_eq_def tape_eq_def configuration_def tape_def by auto
  have blanks: "half_tape_eq(?blanks,[])"
    using half_tape_eq_blank_repeat[of "succ(succ(2))"] by simp
  have finish: "config_eq(\<langle>final_state,\<langle>?blanks,?y\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[],?y\<rangle>\<rangle>)"
    using y blanks unfolding config_eq_def tape_eq_def configuration_def tape_def by auto
  show ?thesis by (rule computes_tape_from_reaches[OF addition_machine_type input y start
    addition_run[OF n m] finish])
qed

definition doubling_machine :: i where
  "doubling_machine \<equiv> sequential_machine(duplicate_arguments_machine,addition_machine)"

lemma doubling_machine_type [TC]: "doubling_machine \<in> machine"
  unfolding doubling_machine_def by typecheck

theorem doubling_computes:
  assumes n: "n \<in> nat"
  shows "computes_number(doubling_machine,n,n #+ n)"
  using computes_tape_sequential[OF duplicate_arguments_computes[OF n] addition_computes[OF n n]] n
  unfolding doubling_machine_def computes_number_iff_tape by auto

corollary doubling_realises_pr_double:
  "tm_realises_unary(doubling_machine,pr_double)"
  unfolding tm_realises_unary_def
  using doubling_computes doubling_machine_type prim_rec_into_fun[OF pr_double_in_prim_rec]
  by (auto simp add: pr_double_apply)

end
