(*  Title:      Turing_Realisation.thy
    Author:     Tang Ziyi
*)

section \<open>Concrete Realisers of the Primitive-Recursive Basis\<close>

theory Turing_Realisation
  imports Turing_Projection Turing_Arithmetic
begin

text \<open>Constants, all projections, and the list-based successor now have
finite machine witnesses. Closure under arbitrary COMP and PREC is a separate
remaining obligation; these base cases do not assume such a compiler.\<close>

definition erase_arguments_machine :: i where
  "erase_arguments_machine \<equiv>
   [\<langle>nop,final_state\<rangle>,\<langle>write_blank,2\<rangle>,
    \<langle>move_right,succ(2)\<rangle>,\<langle>move_right,succ(2)\<rangle>,
    \<langle>move_right,initial_state\<rangle>,\<langle>write_blank,2\<rangle>]"

lemma erase_arguments_machine_type [TC]: "erase_arguments_machine \<in> machine"
  unfolding erase_arguments_machine_def machine_def instruction_def by typecheck

lemma fetch_erase_arguments [simp]:
  "fetch(erase_arguments_machine,1,0) = \<langle>nop,final_state\<rangle>"
  "fetch(erase_arguments_machine,1,1) = \<langle>write_blank,2\<rangle>"
  "fetch(erase_arguments_machine,2,0) = \<langle>move_right,succ(2)\<rangle>"
  "fetch(erase_arguments_machine,succ(2),0) = \<langle>move_right,initial_state\<rangle>"
  "fetch(erase_arguments_machine,succ(2),1) = \<langle>write_blank,2\<rangle>"
  by (simp_all add: erase_arguments_machine_def fetch_def slot_def)

lemma erase_arguments_computes:
  assumes ns: "ns \<in> list(nat)"
  shows "computes_tape(erase_arguments_machine,arguments(ns),[])"
proof -
  let ?x = "arguments(ns)"
  let ?b = "repeat(blank_symbol,length(?x))"
  have x: "?x \<in> list(symbol)" using ns by typecheck
  have len: "length(?x) \<in> nat" using x by typecheck
  have b: "?b \<in> list(symbol)" using len by typecheck
  have run: "reaches(erase_arguments_machine,initial_config(?x),\<langle>initial_state,\<langle>?b,[]\<rangle>\<rangle>)"
    using erase_arguments[OF fetch_erase_arguments(2) fetch_erase_arguments(5)
      fetch_erase_arguments(3) fetch_erase_arguments(4) ns, of "[]"] b by simp
  have last: "reaches(erase_arguments_machine,\<langle>initial_state,\<langle>?b,[]\<rangle>\<rangle>,
    \<langle>final_state,\<langle>?b,[]\<rangle>\<rangle>)"
    by (rule bexI[of _ 1]) simp_all
  have start: "config_eq(initial_config(?x),initial_config(?x))"
    by (rule config_eq_refl[OF initial_config_type[OF x]])
  have finish: "config_eq(\<langle>final_state,\<langle>?b,[]\<rangle>\<rangle>,\<langle>final_state,\<langle>[],[]\<rangle>\<rangle>)"
    using b half_tape_eq_blank_repeat[OF len]
    unfolding config_eq_def tape_eq_def configuration_def tape_def by auto
  show ?thesis by (rule computes_tape_from_reaches[OF erase_arguments_machine_type x _ start
    reaches_trans[OF run last] finish]) typecheck
qed

consts numeral_machine :: "i \<Rightarrow> i"
primrec
  "numeral_machine(0) = []"
  "numeral_machine(succ(n)) = sequential_machine(numeral_machine(n),successor_machine)"

lemma numeral_machine_type [TC]:
  "n \<in> nat \<Longrightarrow> numeral_machine(n) \<in> machine"
  by (induct n rule: nat_induct)
    (auto intro: empty_machine_type sequential_machine_type successor_machine_type)

lemma numeral_machine_computes:
  "n \<in> nat \<Longrightarrow> computes_number(numeral_machine(n),0,n)"
proof (induct n rule: nat_induct)
  case 0 show ?case using identity_computes[OF nat_0I] by simp
next
  case (succ n)
  from computes_number_sequential[OF succ.hyps(2) successor_computes[OF succ.hyps(1)]]
  show ?case by simp
qed

definition constant_arguments_machine :: "i \<Rightarrow> i" where
  "constant_arguments_machine(n) \<equiv> sequential_machine(erase_arguments_machine,numeral_machine(n))"

lemma constant_arguments_machine_type [TC]:
  "n \<in> nat \<Longrightarrow> constant_arguments_machine(n) \<in> machine"
  unfolding constant_arguments_machine_def by typecheck

lemma constant_arguments_computes:
  assumes n: "n \<in> nat" and ns: "ns \<in> list(nat)"
  shows "computes_tape(constant_arguments_machine(n),arguments(ns),numeral_input(n))"
proof -
  from numeral_machine_computes[OF n] computes_number_iff_tape
  have num: "computes_tape(numeral_machine(n),[],numeral_input(n))" by auto
  from computes_tape_sequential[OF erase_arguments_computes[OF ns] num]
  show ?thesis unfolding constant_arguments_machine_def .
qed

theorem constant_arguments_realises_CONSTANT:
  "n \<in> nat \<Longrightarrow> tm_realises_arguments(constant_arguments_machine(n),CONSTANT(n))"
  unfolding tm_realises_arguments_def
  using constant_arguments_computes constant_arguments_machine_type
  by (auto simp add: CONSTANT_def)

lemma successor_arguments_computes:
  assumes n: "n \<in> nat"
  shows "computes_tape(successor_machine,numeral_input(n),arguments([n]))"
proof -
  from successor_computes[OF n] computes_number_iff_tape
  have run: "computes_tape(successor_machine,numeral_input(n),numeral_input(succ(n)))" by blast
  show ?thesis by (rule computes_tape_output_eq[OF run _ half_tape_eq_sym[OF arguments_singleton[OF n]]])
    (typecheck add: n)
qed

theorem argument_realiser_to_unary:
  assumes realiser: "tm_realises_arguments(M,f)"
  shows "tm_realises_unary(sequential_machine(successor_machine,M),f)"
proof -
  from realiser have M: "M \<in> machine" and f: "f \<in> list(nat) \<rightarrow> nat"
    and run: "\<And>ns. ns \<in> list(nat) \<Longrightarrow> computes_tape(M,arguments(ns),numeral_input(f`ns))"
    unfolding tm_realises_arguments_def by auto
  have computes: "\<And>n. n \<in> nat \<Longrightarrow> computes_number(sequential_machine(successor_machine,M),n,f`[n])"
  proof -
    fix n assume n: "n \<in> nat"
    have args: "[n] \<in> list(nat)" using n by typecheck
    have value: "f`[n] \<in> nat" by (rule apply_type[OF f args])
    from computes_tape_sequential[OF successor_arguments_computes[OF n] run[OF args]] n value
    show "computes_number(sequential_machine(successor_machine,M),n,f`[n])"
      by (simp add: computes_number_iff_tape)
  qed
  from f sequential_machine_type[OF successor_machine_type M] computes
  show ?thesis unfolding tm_realises_unary_def by blast
qed

end
