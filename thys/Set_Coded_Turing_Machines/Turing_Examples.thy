(*  Title:      Turing_Examples.thy
    Author:     Tang Ziyi
*)

section \<open>Using the Machine Interface\<close>

theory Turing_Examples
  imports Turing_Tape
begin

text \<open>The machine scans right across a unary input, writes one at the
first blank cell, and halts there. Its two instructions belong to state 1.
The first is selected on blank, the second on one. The result theorem
specifies the complete final configuration, including the head position.
It does not impose a convention for returning the head to the input origin.\<close>

definition scan_append_machine :: i where
  "scan_append_machine \<equiv>
    [\<langle>write_one,final_state\<rangle>,\<langle>move_right,initial_state\<rangle>]"

lemma scan_append_machine_type [TC]: "scan_append_machine \<in> tm_machine"
  unfolding scan_append_machine_def tm_machine_def instruction_def by typecheck

lemma scan_append_fetch_blank [simp]:
  "fetch(scan_append_machine,initial_state,blank_symbol) =
    \<langle>write_one,final_state\<rangle>"
  by (simp add: scan_append_machine_def fetch_def slot_def)

lemma scan_append_fetch_one [simp]:
  "fetch(scan_append_machine,initial_state,one_symbol) =
    \<langle>move_right,initial_state\<rangle>"
  by (simp add: scan_append_machine_def fetch_def slot_def)

text \<open>The loop invariant allows an arbitrary stored left half-tape.
Each step transfers one input symbol to that half. Generalising the left
half before induction makes the invariant applicable after the first step.\<close>

lemma scan_append_loop:
  assumes n: "n \<in> nat" and left: "l \<in> list(symbol)"
  shows "steps(scan_append_machine,
      \<langle>initial_state,\<langle>l,numeral_input(n)\<rangle>\<rangle>,n) =
    \<langle>initial_state,\<langle>numeral_input(n) @ l,[]\<rangle>\<rangle>"
  using n left
proof (induct n arbitrary: l rule: nat_induct)
  case 0
  then show ?case by (simp add: numeral_input_def)
next
  case (succ n)
  have first: "steps(scan_append_machine,
      \<langle>initial_state,\<langle>l,numeral_input(succ(n))\<rangle>\<rangle>,1) =
    \<langle>initial_state,\<langle>Cons(one_symbol,l),numeral_input(n)\<rangle>\<rangle>"
    by (simp add: numeral_input_def)
  have left: "Cons(one_symbol,l) \<in> list(symbol)"
    using succ.prems by typecheck
  have rearrange:
    "numeral_input(n) @ Cons(one_symbol,l) = numeral_input(succ(n)) @ l"
    using repeat_succ_app[OF succ.hyps(1), of one_symbol]
      numeral_input_type[OF succ.hyps(1)]
    unfolding numeral_input_def by (simp add: app_assoc)
  from steps_add[OF nat_1I succ.hyps(1), of scan_append_machine
      "\<langle>initial_state,\<langle>l,numeral_input(succ(n))\<rangle>\<rangle>"]
    first succ.hyps(2)[OF left] rearrange succ.hyps(1)
  show ?case by simp
qed

theorem scan_append_result:
  assumes "n \<in> nat"
  shows "steps(scan_append_machine,initial_config(numeral_input(n)),succ(n)) =
    \<langle>final_state,\<langle>numeral_input(n),[one_symbol]\<rangle>\<rangle>"
  using scan_append_loop[OF assms, of "[]"] numeral_input_type[OF assms]
  by simp

corollary scan_append_halts:
  assumes "n \<in> nat"
  shows "halts_on(scan_append_machine,numeral_input(n))"
  by (rule halts_onI[OF scan_append_machine_type numeral_input_type[OF assms]
        nat_succI[OF assms]]) (simp only: scan_append_result[OF assms] fst_conv)

subsection \<open>Changing the finite representation\<close>

text \<open>Appending a stored blank does not change the observed run. The
same program proof applies through configuration equivalence, even though
the two stored final configurations need not be equal as sets.\<close>

theorem scan_append_padded_result:
  assumes n: "n \<in> nat"
  shows "config_eq(
    steps(scan_append_machine,initial_config(numeral_input(n) @ [blank_symbol]),succ(n)),
    \<langle>final_state,\<langle>numeral_input(n),[one_symbol]\<rangle>\<rangle>)"
proof -
  have input: "numeral_input(n) \<in> list(symbol)" by (rule numeral_input_type[OF n])
  have eq: "config_eq(initial_config(numeral_input(n) @ [blank_symbol]),
      initial_config(numeral_input(n)))"
    using input half_tape_eq_trailing_blank[OF input]
    unfolding config_eq_def configuration_def tape_eq_def tm_tape_def by auto
  from steps_config_eq[OF scan_append_machine_type eq nat_succI[OF n]]
    scan_append_result[OF n]
  show ?thesis by simp
qed

end
