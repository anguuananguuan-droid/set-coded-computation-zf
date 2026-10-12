(*  Title:      Turing_Storage.thy
    Author:     Tang Ziyi
*)

section \<open>Argument Erasure and Storage Operations\<close>

theory Turing_Storage
  imports Turing_Arguments
begin

lemma repeat_append_cons:
  assumes n: "n \<in> nat"
  shows "repeat(a,n) @ Cons(a,l) = repeat(a,succ(n)) @ l"
proof -
  have "repeat(a,n) \<in> list({a})" using n by typecheck
  with repeat_succ_app[OF n, of a] show ?thesis by (simp add: app_assoc)
qed

lemma repeat_append:
  "\<lbrakk>n \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow> repeat(a,n) @ repeat(a,m) = repeat(a,n #+ m)"
  by (induct n rule: nat_induct) simp_all

lemma repeat_append_nested:
  "\<lbrakk>n \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow>
    repeat(a,n) @ (repeat(a,m) @ l) = repeat(a,n #+ m) @ l"
  by (induct n rule: nat_induct) simp_all

lemma scan_left_repeated:
  assumes loop: "fetch(M,q,a) = \<langle>move_left,q\<rangle>" and n: "n \<in> nat"
  shows "reaches(M,\<langle>q,\<langle>repeat(a,n) @ l,Cons(a,r)\<rangle>\<rangle>,
    \<langle>q,\<langle>tl(l),Cons(hd(l),repeat(a,succ(n)) @ r)\<rangle>\<rangle>)"
  using n
proof (induct n arbitrary: r rule: nat_induct)
  case 0
  show ?case by (rule bexI[of _ 1]) (simp_all add: loop)
next
  case (succ n)
  have first: "step(M,\<langle>q,\<langle>repeat(a,succ(n)) @ l,Cons(a,r)\<rangle>\<rangle>) =
    \<langle>q,\<langle>repeat(a,n) @ l,Cons(a,Cons(a,r))\<rangle>\<rangle>" by (simp add: loop)
  have rest: "reaches(M,\<langle>q,\<langle>repeat(a,n) @ l,Cons(a,Cons(a,r))\<rangle>\<rangle>,
    \<langle>q,\<langle>tl(l),Cons(hd(l),repeat(a,succ(succ(n))) @ r)\<rangle>\<rangle>)"
    using succ.hyps(2)[of "Cons(a,r)"] repeat_append_cons[OF nat_succI[OF succ.hyps(1)], of a r] by simp
  show ?case by (rule reaches_step_then[OF first rest])
qed

lemma enter_left_repeated:
  assumes entry: "fetch(M,p,hd(r)) = \<langle>move_left,q\<rangle>"
    and loop: "fetch(M,q,a) = \<langle>move_left,q\<rangle>" and n: "n \<in> nat"
  shows "reaches(M,\<langle>p,\<langle>repeat(a,n) @ l,r\<rangle>\<rangle>,
    \<langle>q,\<langle>tl(l),Cons(hd(l),repeat(a,n) @ r)\<rangle>\<rangle>)"
  using n
proof (cases rule: natE)
  case 0
  show ?thesis by (rule bexI[of _ 1]) (simp_all add: entry 0)
next
  case (succ k)
  have first: "step(M,\<langle>p,\<langle>repeat(a,n) @ l,r\<rangle>\<rangle>) =
    \<langle>q,\<langle>repeat(a,k) @ l,Cons(a,r)\<rangle>\<rangle>" using entry succ by simp
  have rest: "reaches(M,\<langle>q,\<langle>repeat(a,k) @ l,Cons(a,r)\<rangle>\<rangle>,
    \<langle>q,\<langle>tl(l),Cons(hd(l),repeat(a,n) @ r)\<rangle>\<rangle>)"
    using scan_left_repeated[OF loop succ(1), of l r] succ(2) by simp
  show ?thesis by (rule reaches_step_then[OF first rest])
qed

lemma erase_right_ones:
  assumes erase: "fetch(M,q,one_symbol) = \<langle>write_blank,w\<rangle>"
    and move: "fetch(M,w,blank_symbol) = \<langle>move_right,q\<rangle>" and n: "n \<in> nat"
  shows "reaches(M,\<langle>q,\<langle>l,numeral_input(n) @ r\<rangle>\<rangle>,
    \<langle>q,\<langle>repeat(blank_symbol,n) @ l,r\<rangle>\<rangle>)"
  using n
proof (induct n arbitrary: l rule: nat_induct)
  case 0 show ?case by (simp add: reaches_refl)
next
  case (succ n)
  have first: "reaches(M,\<langle>q,\<langle>l,numeral_input(succ(n)) @ r\<rangle>\<rangle>,
    \<langle>q,\<langle>Cons(blank_symbol,l),numeral_input(n) @ r\<rangle>\<rangle>)"
    by (rule bexI[of _ 2]) (simp_all add: erase move)
  have rest: "reaches(M,\<langle>q,\<langle>Cons(blank_symbol,l),numeral_input(n) @ r\<rangle>\<rangle>,
    \<langle>q,\<langle>repeat(blank_symbol,succ(n)) @ l,r\<rangle>\<rangle>)"
    using succ.hyps(2)[of "Cons(blank_symbol,l)"] repeat_append_cons[OF succ.hyps(1), of blank_symbol l] by simp
  show ?case by (rule reaches_trans[OF first rest])
qed

lemma erase_arguments:
  assumes entry: "fetch(M,p,one_symbol) = \<langle>write_blank,w\<rangle>"
    and erase: "fetch(M,q,one_symbol) = \<langle>write_blank,w\<rangle>"
    and move: "fetch(M,w,blank_symbol) = \<langle>move_right,q\<rangle>"
    and cross: "fetch(M,q,blank_symbol) = \<langle>move_right,p\<rangle>"
    and ns: "ns \<in> list(nat)"
  shows "reaches(M,\<langle>p,\<langle>l,arguments(ns)\<rangle>\<rangle>,
    \<langle>p,\<langle>repeat(blank_symbol,length(arguments(ns))) @ l,[]\<rangle>\<rangle>)"
  using ns
proof (induct ns arbitrary: l rule: list.induct)
  case Nil show ?case by (simp add: reaches_refl)
next
  case (Cons n ns)
  let ?tail = "arguments(ns)"
  let ?left = "Cons(blank_symbol,repeat(blank_symbol,n) @ Cons(blank_symbol,l))"
  have first: "reaches(M,\<langle>p,\<langle>l,arguments(Cons(n,ns))\<rangle>\<rangle>,
    \<langle>q,\<langle>Cons(blank_symbol,l),numeral_input(n) @ Cons(blank_symbol,?tail)\<rangle>\<rangle>)"
    by (rule bexI[of _ 2]) (simp_all add: entry move)
  have block: "reaches(M,\<langle>q,\<langle>Cons(blank_symbol,l),numeral_input(n) @ Cons(blank_symbol,?tail)\<rangle>\<rangle>,
    \<langle>q,\<langle>repeat(blank_symbol,n) @ Cons(blank_symbol,l),Cons(blank_symbol,?tail)\<rangle>\<rangle>)"
    by (rule erase_right_ones[OF erase move Cons.hyps(1)])
  have separator: "reaches(M,\<langle>q,\<langle>repeat(blank_symbol,n) @ Cons(blank_symbol,l),Cons(blank_symbol,?tail)\<rangle>\<rangle>,
    \<langle>p,\<langle>?left,?tail\<rangle>\<rangle>)"
    by (rule bexI[of _ 1]) (simp_all add: cross)
  have len: "length(?tail) \<in> nat" using Cons.hyps(2) by typecheck
  have algebra: "repeat(blank_symbol,length(?tail)) @ ?left =
    repeat(blank_symbol,length(arguments(Cons(n,ns)))) @ l"
    using Cons.hyps(1) len numeral_input_type[OF Cons.hyps(1)] arguments_type[OF Cons.hyps(2)]
    by (simp add: numeral_input_def length_repeat repeat_append_cons repeat_append_nested add_commute)
  have rest: "reaches(M,\<langle>p,\<langle>?left,?tail\<rangle>\<rangle>,
    \<langle>p,\<langle>repeat(blank_symbol,length(arguments(Cons(n,ns)))) @ l,[]\<rangle>\<rangle>)"
    using Cons.hyps(3)[of ?left] algebra by simp
  show ?case by (rule reaches_trans[OF first reaches_trans[OF block reaches_trans[OF separator rest]]])
qed

definition drop_argument_machine :: i where
  "drop_argument_machine \<equiv>
   [\<langle>move_right,final_state\<rangle>,\<langle>write_blank,2\<rangle>,
    \<langle>move_right,initial_state\<rangle>,\<langle>move_right,initial_state\<rangle>]"

lemma drop_argument_machine_type [TC]: "drop_argument_machine \<in> machine"
  unfolding drop_argument_machine_def machine_def instruction_def by typecheck

lemma fetch_drop_argument [simp]:
  "fetch(drop_argument_machine,1,0) = \<langle>move_right,final_state\<rangle>"
  "fetch(drop_argument_machine,1,1) = \<langle>write_blank,2\<rangle>"
  "fetch(drop_argument_machine,2,0) = \<langle>move_right,initial_state\<rangle>"
  by (simp_all add: drop_argument_machine_def fetch_def slot_def)

lemma drop_argument_computes_Cons:
  assumes n: "n \<in> nat" and ns: "ns \<in> list(nat)"
  shows "computes_tape(drop_argument_machine,arguments(Cons(n,ns)),arguments(ns))"
proof -
  let ?xs = "arguments(Cons(n,ns))"
  let ?ys = "arguments(ns)"
  let ?b = "repeat(blank_symbol,succ(succ(n)))"
  have input: "?xs \<in> list(symbol)" using n ns by typecheck
  have ys: "?ys \<in> list(symbol)" using ns by typecheck
  have erase: "reaches(drop_argument_machine,initial_config(?xs),
    \<langle>initial_state,\<langle>repeat(blank_symbol,succ(n)),Cons(blank_symbol,?ys)\<rangle>\<rangle>)"
    using erase_right_ones[OF fetch_drop_argument(2) fetch_drop_argument(3) nat_succI[OF n],
      of "[]" "Cons(blank_symbol,?ys)"] n repeat_type[OF _ n, of blank_symbol symbol] by simp
  have last: "reaches(drop_argument_machine,
    \<langle>initial_state,\<langle>repeat(blank_symbol,succ(n)),Cons(blank_symbol,?ys)\<rangle>\<rangle>,
    \<langle>final_state,\<langle>?b,?ys\<rangle>\<rangle>)"
    by (rule bexI[of _ 1]) simp_all
  have start: "config_eq(initial_config(?xs),initial_config(?xs))"
    by (rule config_eq_refl[OF initial_config_type[OF input]])
  have finish: "config_eq(\<langle>final_state,\<langle>?b,?ys\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[],?ys\<rangle>\<rangle>)"
    using n ys half_tape_eq_blank_repeat[OF nat_succI[OF nat_succI[OF n]]]
    unfolding config_eq_def tape_eq_def configuration_def tape_def by (auto intro: repeat_type)
  show ?thesis by (rule computes_tape_from_reaches[OF drop_argument_machine_type input ys start
    reaches_trans[OF erase last] finish])
qed

lemma drop_argument_computes_Nil:
  "computes_tape(drop_argument_machine,[],[])"
proof -
  have eq: "config_eq(steps(drop_argument_machine,initial_config([]),1),\<langle>final_state,\<langle>[],[]\<rangle>\<rangle>)"
    unfolding config_eq_def tape_eq_def configuration_def tape_def by simp
  from eq drop_argument_machine_type show ?thesis
    unfolding computes_tape_def by (auto intro!: bexI[of _ 1])
qed

lemma drop_argument_computes:
  assumes ns: "ns \<in> list(nat)"
  shows "computes_tape(drop_argument_machine,arguments(ns),arguments(tl(ns)))"
  using ns
proof (cases rule: list.cases)
  case Nil then show ?thesis by (simp add: drop_argument_computes_Nil)
next
  case (Cons n ns)
  from drop_argument_computes_Cons[OF Cons(2,3)] Cons(1) show ?thesis by simp
qed

end
