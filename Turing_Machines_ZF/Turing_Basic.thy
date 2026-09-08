(*  Title:      Turing_Basic.thy
    Author:     Tang Ziyi
*)

section \<open>Basic Numerical Machines\<close>

theory Turing_Basic
  imports Turing_Reduction "ZF-Induct.Primrec"
begin

text \<open>These concrete finite machines exercise the numerical contract on
identity, growth, and erasure. In particular, erasure must work on every
natural input, including zero, without deleting represented tape cells.\<close>

lemma empty_machine_type [TC]: "[] \<in> machine"
  unfolding machine_def by typecheck

lemma identity_computes:
  assumes n: "n \<in> nat"
  shows "computes_number([],n,n)"
proof -
  have step: "steps([],initial_config(numeral_input(n)),1) =
    \<langle>final_state,\<langle>[],numeral_input(n)\<rangle>\<rangle>"
    by (simp add: fetch_def)
  have c: "\<langle>final_state,\<langle>[],numeral_input(n)\<rangle>\<rangle> \<in> configuration"
    using numeral_input_type[OF n] unfolding configuration_def by typecheck
  from config_eq_refl[OF c] step n empty_machine_type
  show ?thesis unfolding computes_number_def by (auto intro!: bexI[of _ 1])
qed

definition successor_machine :: i where
  "successor_machine \<equiv>
    [\<langle>move_left,2\<rangle>,\<langle>move_left,2\<rangle>,
     \<langle>write_one,final_state\<rangle>,\<langle>write_one,final_state\<rangle>]"

lemma successor_machine_type [TC]: "successor_machine \<in> machine"
  unfolding successor_machine_def machine_def instruction_def by typecheck

lemma successor_computes:
  assumes n: "n \<in> nat"
  shows "computes_number(successor_machine,n,succ(n))"
proof -
  have step: "steps(successor_machine,initial_config(numeral_input(n)),2) =
    \<langle>final_state,\<langle>[],numeral_input(succ(n))\<rangle>\<rangle>"
    using n
    by (induct n rule: nat_induct)
      (simp_all add: successor_machine_def numeral_input_def fetch_def slot_def)
  have c: "\<langle>final_state,\<langle>[],numeral_input(succ(n))\<rangle>\<rangle> \<in> configuration"
    using numeral_input_type[OF nat_succI[OF n]] unfolding configuration_def by typecheck
  from config_eq_refl[OF c] step n successor_machine_type
  show ?thesis unfolding computes_number_def by (auto intro!: bexI[of _ 2])
qed

definition zero_machine :: i where
  "zero_machine \<equiv>
    [\<langle>nop,final_state\<rangle>,\<langle>write_blank,2\<rangle>,
     \<langle>move_right,initial_state\<rangle>,\<langle>move_right,initial_state\<rangle>]"

lemma zero_machine_type [TC]: "zero_machine \<in> machine"
  unfolding zero_machine_def machine_def instruction_def by typecheck

lemma zero_machine_erases:
  assumes n: "n \<in> nat" and l: "l \<in> list(symbol)"
  shows "steps(zero_machine,\<langle>initial_state,\<langle>l,numeral_input(n)\<rangle>\<rangle>,n #+ n) =
    \<langle>initial_state,\<langle>repeat(blank_symbol,n) @ l,[]\<rangle>\<rangle>"
  using n l
proof (induct n arbitrary: l rule: nat_induct)
  case 0 then show ?case by (simp add: numeral_input_def)
next
  case (succ n)
  have two_steps:
    "steps(zero_machine,\<langle>initial_state,\<langle>l,numeral_input(succ(n))\<rangle>\<rangle>,2) =
      \<langle>initial_state,\<langle>Cons(blank_symbol,l),numeral_input(n)\<rangle>\<rangle>"
    by (simp add: zero_machine_def numeral_input_def fetch_def slot_def)
  have time: "n #+ n \<in> nat" by typecheck
  have split: "succ(n) #+ succ(n) = 2 #+ (n #+ n)"
    using succ.hyps(1) by simp
  from succ.prems have tail: "Cons(blank_symbol,l) \<in> list(symbol)" by typecheck
  from steps_add[OF nat_2I time, of zero_machine
      "\<langle>initial_state,\<langle>l,numeral_input(succ(n))\<rangle>\<rangle>"]
    two_steps succ.hyps(2)[OF tail] split
  have run:
    "steps(zero_machine,\<langle>initial_state,\<langle>l,numeral_input(succ(n))\<rangle>\<rangle>,succ(n) #+ succ(n)) =
      \<langle>initial_state,\<langle>repeat(blank_symbol,n) @ Cons(blank_symbol,l),[]\<rangle>\<rangle>"
    by simp
  have repeated: "repeat(blank_symbol,n) \<in> list(symbol)" using succ.hyps(1) by typecheck
  from repeat_succ_app[OF succ.hyps(1), of blank_symbol] repeated
  have lists: "repeat(blank_symbol,n) @ Cons(blank_symbol,l) = repeat(blank_symbol,succ(n)) @ l"
    by (simp add: app_assoc)
  from run lists show ?case by simp
qed

lemma half_tape_eq_blank_repeat:
  assumes n: "n \<in> nat"
  shows "half_tape_eq(repeat(blank_symbol,n),[])"
  using n
proof (induct n rule: nat_induct)
  case 0 then show ?case by simp
next
  case (succ n)
  from half_tape_eq_Cons[OF succ.hyps(2), of blank_symbol]
    half_tape_eq_blank
  show ?case by (auto intro: half_tape_eq_trans)
qed

theorem zero_computes:
  assumes n: "n \<in> nat"
  shows "computes_number(zero_machine,n,0)"
proof -
  have repeated: "repeat(blank_symbol,n) \<in> list(symbol)" using n by typecheck
  from zero_machine_erases[OF n, of "[]"] repeated
  have run: "steps(zero_machine,initial_config(numeral_input(n)),succ(n #+ n)) =
    \<langle>final_state,\<langle>repeat(blank_symbol,n),[]\<rangle>\<rangle>"
    by (simp add: zero_machine_def fetch_def slot_def)
  from repeated have tape: "\<langle>repeat(blank_symbol,n),[]\<rangle> \<in> tape"
    by (rule tapeI) typecheck
  have blank: "\<langle>[],[]\<rangle> \<in> tape" by (rule tapeI) typecheck+
  from tape blank half_tape_eq_blank_repeat[OF n]
  have eq: "tape_eq(\<langle>repeat(blank_symbol,n),[]\<rangle>,\<langle>[],[]\<rangle>)"
    unfolding tape_eq_def by simp
  from config_eq_pair[OF nat_0I eq] run n zero_machine_type
  show ?thesis unfolding computes_number_def numeral_input_def
    by (auto intro!: bexI[of _ "succ(n #+ n)"])
qed

corollary zero_realises_constant:
  "tm_realises_unary(zero_machine,CONSTANT(0))"
  unfolding tm_realises_unary_def
  using zero_computes zero_machine_type by (auto simp add: CONSTANT_def)

text \<open>This composition runs on the actual blank-padded tape left by
zero_machine; no list normalisation is performed between the programs.\<close>

corollary zero_then_successor_computes_one:
  assumes n: "n \<in> nat"
  shows "computes_number(sequential_machine(zero_machine,successor_machine),n,1)"
  using computes_number_sequential[OF zero_computes[OF n] successor_computes[OF nat_0I]]
  by simp

end
