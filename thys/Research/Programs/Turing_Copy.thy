(*  Title:      Turing_Copy.thy
    Author:     Tang Ziyi
*)

section \<open>Copying a Unary Block with a Binary Machine\<close>

theory Turing_Copy
  imports Turing_Arguments
begin

abbreviation (input) cp_seek_original where "cp_seek_original \<equiv> succ(2)"
abbreviation (input) cp_seek_output where "cp_seek_output \<equiv> succ(succ(2))"
abbreviation (input) cp_return_output where "cp_return_output \<equiv> succ(succ(succ(2)))"
abbreviation (input) cp_return_mark where "cp_return_mark \<equiv> succ(succ(succ(succ(2))))"
abbreviation (input) cp_resume where "cp_resume \<equiv> succ(succ(succ(succ(succ(2)))))"
abbreviation (input) cp_rewind where "cp_rewind \<equiv> succ(succ(succ(succ(succ(succ(2))))))"

text \<open>A temporarily erased stroke marks the current source position.
The permanent blank between the blocks separates the return scans. Once
all source strokes have been copied, the machine rewinds to the first block.
Only the existing binary alphabet and single-tape instructions are used.\<close>

definition copy_machine :: i where
  "copy_machine \<equiv>
   [\<langle>move_left,cp_rewind\<rangle>,\<langle>write_blank,2\<rangle>,
    \<langle>move_right,cp_seek_original\<rangle>,\<langle>move_right,cp_seek_original\<rangle>,
    \<langle>move_right,cp_seek_output\<rangle>,\<langle>move_right,cp_seek_original\<rangle>,
    \<langle>write_one,cp_return_output\<rangle>,\<langle>move_right,cp_seek_output\<rangle>,
    \<langle>move_left,cp_return_mark\<rangle>,\<langle>move_left,cp_return_output\<rangle>,
    \<langle>write_one,cp_resume\<rangle>,\<langle>move_left,cp_return_mark\<rangle>,
    \<langle>move_right,initial_state\<rangle>,\<langle>move_right,initial_state\<rangle>,
    \<langle>move_right,final_state\<rangle>,\<langle>move_left,cp_rewind\<rangle>]"

lemma copy_machine_type [TC]: "copy_machine \<in> machine"
  unfolding copy_machine_def machine_def instruction_def by typecheck

lemma fetch_copy [simp]:
  "fetch(copy_machine,1,0) = \<langle>move_left,cp_rewind\<rangle>"
  "fetch(copy_machine,1,1) = \<langle>write_blank,2\<rangle>"
  "fetch(copy_machine,2,0) = \<langle>move_right,cp_seek_original\<rangle>"
  "fetch(copy_machine,2,1) = \<langle>move_right,cp_seek_original\<rangle>"
  "fetch(copy_machine,cp_seek_original,0) = \<langle>move_right,cp_seek_output\<rangle>"
  "fetch(copy_machine,cp_seek_original,1) = \<langle>move_right,cp_seek_original\<rangle>"
  "fetch(copy_machine,cp_seek_output,0) = \<langle>write_one,cp_return_output\<rangle>"
  "fetch(copy_machine,cp_seek_output,1) = \<langle>move_right,cp_seek_output\<rangle>"
  "fetch(copy_machine,cp_return_output,0) = \<langle>move_left,cp_return_mark\<rangle>"
  "fetch(copy_machine,cp_return_output,1) = \<langle>move_left,cp_return_output\<rangle>"
  "fetch(copy_machine,cp_return_mark,0) = \<langle>write_one,cp_resume\<rangle>"
  "fetch(copy_machine,cp_return_mark,1) = \<langle>move_left,cp_return_mark\<rangle>"
  "fetch(copy_machine,cp_resume,0) = \<langle>move_right,initial_state\<rangle>"
  "fetch(copy_machine,cp_resume,1) = \<langle>move_right,initial_state\<rangle>"
  "fetch(copy_machine,cp_rewind,0) = \<langle>move_right,final_state\<rangle>"
  "fetch(copy_machine,cp_rewind,1) = \<langle>move_left,cp_rewind\<rangle>"
  by (simp_all add: copy_machine_def fetch_def slot_def)

lemma copy_cycle:
  assumes i: "i \<in> nat" and j: "j \<in> nat"
  shows "reaches(copy_machine,
    \<langle>initial_state,\<langle>l,Cons(one_symbol,numeral_input(j) @ Cons(blank_symbol,numeral_input(i)))\<rangle>\<rangle>,
    \<langle>initial_state,\<langle>Cons(one_symbol,l),numeral_input(j) @ Cons(blank_symbol,numeral_input(succ(i)))\<rangle>\<rangle>)"
proof -
  let ?u = "numeral_input(j) @ Cons(blank_symbol,l)"
  let ?v = "numeral_input(i) @ Cons(blank_symbol,?u)"
  have mark: "reaches(copy_machine,
    \<langle>initial_state,\<langle>l,Cons(one_symbol,numeral_input(j) @ Cons(blank_symbol,numeral_input(i)))\<rangle>\<rangle>,
    \<langle>cp_seek_original,\<langle>Cons(blank_symbol,l),numeral_input(j) @ Cons(blank_symbol,numeral_input(i))\<rangle>\<rangle>)"
    by (rule bexI[of _ 2]) simp_all
  have source: "reaches(copy_machine,
    \<langle>cp_seek_original,\<langle>Cons(blank_symbol,l),numeral_input(j) @ Cons(blank_symbol,numeral_input(i))\<rangle>\<rangle>,
    \<langle>cp_seek_original,\<langle>?u,Cons(blank_symbol,numeral_input(i))\<rangle>\<rangle>)"
    by (rule scan_right_ones[OF fetch_copy(6) j])
  have seek_end: "reaches(copy_machine,
    \<langle>cp_seek_original,\<langle>?u,Cons(blank_symbol,numeral_input(i))\<rangle>\<rangle>,
    \<langle>cp_seek_output,\<langle>?v,[]\<rangle>\<rangle>)"
  proof (rule reaches_step_then)
    show "step(copy_machine,\<langle>cp_seek_original,\<langle>?u,Cons(blank_symbol,numeral_input(i))\<rangle>\<rangle>) =
      \<langle>cp_seek_output,\<langle>Cons(blank_symbol,?u),numeral_input(i)\<rangle>\<rangle>" by simp
    from scan_right_ones[OF fetch_copy(8) i, of "Cons(blank_symbol,?u)" "[]"]
      numeral_input_type[OF i]
    show "reaches(copy_machine,\<langle>cp_seek_output,\<langle>Cons(blank_symbol,?u),numeral_input(i)\<rangle>\<rangle>,
      \<langle>cp_seek_output,\<langle>?v,[]\<rangle>\<rangle>)" by simp
  qed
  have return_output: "reaches(copy_machine,\<langle>cp_seek_output,\<langle>?v,[]\<rangle>\<rangle>,
    \<langle>cp_return_output,\<langle>?u,Cons(blank_symbol,numeral_input(succ(i)))\<rangle>\<rangle>)"
  proof (rule reaches_step_then)
    show "step(copy_machine,\<langle>cp_seek_output,\<langle>?v,[]\<rangle>\<rangle>) =
      \<langle>cp_return_output,\<langle>?v,[one_symbol]\<rangle>\<rangle>" by simp
    from scan_left_ones[OF fetch_copy(10) i, of "Cons(blank_symbol,?u)" "[]"]
      numeral_input_type[OF i]
    show "reaches(copy_machine,\<langle>cp_return_output,\<langle>?v,[one_symbol]\<rangle>\<rangle>,
      \<langle>cp_return_output,\<langle>?u,Cons(blank_symbol,numeral_input(succ(i)))\<rangle>\<rangle>)" by simp
  qed
  have return_mark: "reaches(copy_machine,
    \<langle>cp_return_output,\<langle>?u,Cons(blank_symbol,numeral_input(succ(i)))\<rangle>\<rangle>,
    \<langle>cp_return_mark,\<langle>l,Cons(blank_symbol,numeral_input(j) @ Cons(blank_symbol,numeral_input(succ(i))))\<rangle>\<rangle>)"
    using enter_left_ones[OF _ fetch_copy(12) j, where p=cp_return_output and
        l="Cons(blank_symbol,l)" and r="Cons(blank_symbol,numeral_input(succ(i)))"] by simp
  have restore: "reaches(copy_machine,
    \<langle>cp_return_mark,\<langle>l,Cons(blank_symbol,numeral_input(j) @ Cons(blank_symbol,numeral_input(succ(i))))\<rangle>\<rangle>,
    \<langle>initial_state,\<langle>Cons(one_symbol,l),numeral_input(j) @ Cons(blank_symbol,numeral_input(succ(i)))\<rangle>\<rangle>)"
    by (rule bexI[of _ 2]) simp_all
  show ?thesis by (rule reaches_trans[OF mark reaches_trans[OF source
    reaches_trans[OF seek_end reaches_trans[OF return_output reaches_trans[OF return_mark restore]]]]])
qed

lemma copy_process:
  assumes n: "n \<in> nat" and i: "i \<in> nat"
  shows "reaches(copy_machine,\<langle>initial_state,\<langle>l,numeral_input(n) @ Cons(blank_symbol,numeral_input(i))\<rangle>\<rangle>,
    \<langle>initial_state,\<langle>numeral_input(n) @ l,Cons(blank_symbol,numeral_input(n #+ i))\<rangle>\<rangle>)"
  using n i
proof (induct n arbitrary: i l rule: nat_induct)
  case 0 then show ?case by (simp add: reaches_refl)
next
  case (succ n)
  have cycle: "reaches(copy_machine,
    \<langle>initial_state,\<langle>l,numeral_input(succ(n)) @ Cons(blank_symbol,numeral_input(i))\<rangle>\<rangle>,
    \<langle>initial_state,\<langle>Cons(one_symbol,l),numeral_input(n) @ Cons(blank_symbol,numeral_input(succ(i)))\<rangle>\<rangle>)"
    using copy_cycle[OF succ.prems succ.hyps(1), of l] by simp
  have rest: "reaches(copy_machine,
    \<langle>initial_state,\<langle>Cons(one_symbol,l),numeral_input(n) @ Cons(blank_symbol,numeral_input(succ(i)))\<rangle>\<rangle>,
    \<langle>initial_state,\<langle>numeral_input(succ(n)) @ l,Cons(blank_symbol,numeral_input(succ(n) #+ i))\<rangle>\<rangle>)"
    using succ.hyps(2)[OF nat_succI[OF succ.prems], of "Cons(one_symbol,l)"]
      numeral_append_cons[OF succ.hyps(1), of l] succ.hyps(1) succ.prems by simp
  show ?case by (rule reaches_trans[OF cycle rest])
qed

theorem copy_block_computes:
  assumes n: "n \<in> nat"
  shows "computes_tape(copy_machine,numeral_input(n),
    numeral_input(n) @ Cons(blank_symbol,numeral_input(n)))"
proof -
  let ?x = "numeral_input(n)"
  let ?y = "?x @ Cons(blank_symbol,?x)"
  have x: "?x \<in> list(symbol)" by (rule numeral_input_type[OF n])
  have y: "?y \<in> list(symbol)" using x by typecheck
  have process: "reaches(copy_machine,initial_config(?x @ [blank_symbol]),
    \<langle>initial_state,\<langle>?x,Cons(blank_symbol,?x)\<rangle>\<rangle>)"
    using copy_process[OF n nat_0I, of "[]"] n x by simp
  have rewind: "reaches(copy_machine,\<langle>initial_state,\<langle>?x,Cons(blank_symbol,?x)\<rangle>\<rangle>,
    \<langle>cp_rewind,\<langle>[],Cons(blank_symbol,?y)\<rangle>\<rangle>)"
    using enter_left_ones[OF _ fetch_copy(16) n, where p=initial_state and
      l="[]" and r="Cons(blank_symbol,?x)"] x by simp
  have exit: "reaches(copy_machine,\<langle>cp_rewind,\<langle>[],Cons(blank_symbol,?y)\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[blank_symbol],?y\<rangle>\<rangle>)"
    by (rule reaches_step_then) (simp, rule reaches_refl)
  have start: "config_eq(initial_config(?x @ [blank_symbol]),initial_config(?x))"
    using x half_tape_eq_trailing_blank[OF x]
    unfolding config_eq_def tape_eq_def configuration_def tape_def by auto
  have finish: "config_eq(\<langle>final_state,\<langle>[blank_symbol],?y\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[],?y\<rangle>\<rangle>)"
    using y unfolding config_eq_def tape_eq_def configuration_def tape_def by auto
  show ?thesis by (rule computes_tape_from_reaches[OF copy_machine_type x y start
    reaches_trans[OF process reaches_trans[OF rewind exit]] finish])
qed

definition duplicate_arguments_machine :: i where
  "duplicate_arguments_machine \<equiv> sequential_machine(successor_machine,copy_machine)"

lemma duplicate_arguments_machine_type [TC]: "duplicate_arguments_machine \<in> machine"
  unfolding duplicate_arguments_machine_def by typecheck

theorem duplicate_arguments_computes:
  assumes n: "n \<in> nat"
  shows "computes_tape(duplicate_arguments_machine,numeral_input(n),arguments([n,n]))"
proof -
  let ?x = "numeral_input(succ(n))"
  let ?y = "?x @ Cons(blank_symbol,?x)"
  from successor_computes[OF n] computes_number_iff_tape
  have first: "computes_tape(successor_machine,numeral_input(n),?x)" by blast
  from computes_tape_sequential[OF first copy_block_computes[OF nat_succI[OF n]]]
  have run: "computes_tape(duplicate_arguments_machine,numeral_input(n),?y)"
    unfolding duplicate_arguments_machine_def .
  have y: "?y \<in> list(symbol)" using n by typecheck
  have args: "arguments([n,n]) = ?y @ [blank_symbol]"
    using numeral_input_type[OF n] by (simp add: app_assoc)
  have eq: "half_tape_eq(?y,arguments([n,n]))"
    using half_tape_eq_sym[OF half_tape_eq_trailing_blank[OF y]] args by simp
  show ?thesis by (rule computes_tape_output_eq[OF run _ eq]) (typecheck add: n)
qed

end
