(*  Title:      Turing_Programs.thy
    Author:     Tang Ziyi
*)

section \<open>Finite Programs and Tape Transformations\<close>

theory Turing_Programs
  imports Turing_Basic
begin

abbreviation reaches :: "[i,i,i] \<Rightarrow> o" where
  "reaches(M,c,d) \<equiv> \<exists>k\<in>nat. steps(M,c,k) = d"

lemma reaches_refl: "reaches(M,c,c)"
  by (rule bexI[of _ 0]) auto

lemma reaches_step: "reaches(M,c,step(M,c))"
  by (rule bexI[of _ 1]) auto

lemma reaches_trans:
  assumes first: "reaches(M,c,d)" and second: "reaches(M,d,e)"
  shows "reaches(M,c,e)"
proof -
  from first second obtain m n where m: "m \<in> nat" and n: "n \<in> nat"
    and cd: "steps(M,c,m) = d" and de: "steps(M,d,n) = e" by auto
  from steps_add[OF m n, of M c] cd de
  show ?thesis by (auto intro!: bexI[of _ "m #+ n"])
qed

lemma reaches_step_then:
  "\<lbrakk>step(M,c) = d; reaches(M,d,e)\<rbrakk> \<Longrightarrow> reaches(M,c,e)"
  using reaches_step[of M c] by (blast intro: reaches_trans)

lemma numeral_input_zero [simp]: "numeral_input(0) = []"
  unfolding numeral_input_def by simp

lemma numeral_input_succ [simp]:
  "numeral_input(succ(n)) = Cons(one_symbol,numeral_input(n))"
  unfolding numeral_input_def by simp

lemma numeral_append_cons:
  assumes n: "n \<in> nat"
  shows "numeral_input(n) @ Cons(one_symbol,l) = numeral_input(succ(n)) @ l"
proof -
  from repeat_succ_app[OF n, of one_symbol] numeral_input_type[OF n]
  show ?thesis unfolding numeral_input_def by (simp add: app_assoc)
qed

lemma numeral_append:
  assumes n: "n \<in> nat" and m: "m \<in> nat"
  shows "numeral_input(n) @ numeral_input(m) = numeral_input(n #+ m)"
  using n by (induct n rule: nat_induct) (simp_all add: m)

lemma scan_right_ones:
  assumes loop: "fetch(M,q,one_symbol) = \<langle>move_right,q\<rangle>"
    and n: "n \<in> nat"
  shows "reaches(M,\<langle>q,\<langle>l,numeral_input(n) @ r\<rangle>\<rangle>,
    \<langle>q,\<langle>numeral_input(n) @ l,r\<rangle>\<rangle>)"
  using n
proof (induct n arbitrary: l rule: nat_induct)
  case 0 then show ?case by (simp add: reaches_refl)
next
  case (succ n)
  have first: "step(M,\<langle>q,\<langle>l,numeral_input(succ(n)) @ r\<rangle>\<rangle>) =
    \<langle>q,\<langle>Cons(one_symbol,l),numeral_input(n) @ r\<rangle>\<rangle>"
    by (simp add: loop)
  from succ.hyps(2)[of "Cons(one_symbol,l)"] numeral_append_cons[OF succ.hyps(1), of l]
  have rest: "reaches(M,\<langle>q,\<langle>Cons(one_symbol,l),numeral_input(n) @ r\<rangle>\<rangle>,
    \<langle>q,\<langle>numeral_input(succ(n)) @ l,r\<rangle>\<rangle>)" by simp
  show ?case by (rule reaches_step_then[OF first rest])
qed

lemma scan_left_ones:
  assumes loop: "fetch(M,q,one_symbol) = \<langle>move_left,q\<rangle>"
    and n: "n \<in> nat"
  shows "reaches(M,\<langle>q,\<langle>numeral_input(n) @ l,Cons(one_symbol,r)\<rangle>\<rangle>,
    \<langle>q,\<langle>tl(l),Cons(hd(l),numeral_input(succ(n)) @ r)\<rangle>\<rangle>)"
  using n
proof (induct n arbitrary: r rule: nat_induct)
  case 0
  show ?case by (rule reaches_step_then[of _ _ _ _])
    (simp add: loop, simp add: reaches_refl)
next
  case (succ n)
  have first: "step(M,\<langle>q,\<langle>numeral_input(succ(n)) @ l,Cons(one_symbol,r)\<rangle>\<rangle>) =
    \<langle>q,\<langle>numeral_input(n) @ l,Cons(one_symbol,Cons(one_symbol,r))\<rangle>\<rangle>"
    by (simp add: loop)
  from succ.hyps(2)[of "Cons(one_symbol,r)"] numeral_append_cons[OF nat_succI[OF succ.hyps(1)], of r]
  have rest: "reaches(M,\<langle>q,\<langle>numeral_input(n) @ l,Cons(one_symbol,Cons(one_symbol,r))\<rangle>\<rangle>,
    \<langle>q,\<langle>tl(l),Cons(hd(l),numeral_input(succ(succ(n))) @ r)\<rangle>\<rangle>)" by simp
  show ?case by (rule reaches_step_then[OF first rest])
qed

lemma enter_left_ones:
  assumes entry: "fetch(M,p,scan(\<langle>numeral_input(n) @ l,r\<rangle>)) = \<langle>move_left,q\<rangle>"
    and loop: "fetch(M,q,one_symbol) = \<langle>move_left,q\<rangle>"
    and n: "n \<in> nat"
  shows "reaches(M,\<langle>p,\<langle>numeral_input(n) @ l,r\<rangle>\<rangle>,
    \<langle>q,\<langle>tl(l),Cons(hd(l),numeral_input(n) @ r)\<rangle>\<rangle>)"
proof -
  have fetch_entry: "fetch(M,p,hd(r)) = \<langle>move_left,q\<rangle>" using entry by simp
  from n show ?thesis
  proof (cases rule: natE)
  case 0
  show ?thesis by (rule reaches_step_then)
    (simp add: fetch_entry 0, simp add: 0 reaches_refl)
next
  case (succ k)
  have first: "step(M,\<langle>p,\<langle>numeral_input(n) @ l,r\<rangle>\<rangle>) =
    \<langle>q,\<langle>numeral_input(k) @ l,Cons(one_symbol,r)\<rangle>\<rangle>"
    using fetch_entry succ by simp
  have rest: "reaches(M,\<langle>q,\<langle>numeral_input(k) @ l,Cons(one_symbol,r)\<rangle>\<rangle>,
    \<langle>q,\<langle>tl(l),Cons(hd(l),numeral_input(n) @ r)\<rangle>\<rangle>)"
    using scan_left_ones[OF loop succ(1), of l r] succ(2) by simp
  show ?thesis by (rule reaches_step_then[OF first rest])
  qed
qed

definition computes_tape :: "[i,i,i] \<Rightarrow> o" where
  "computes_tape(M,x,y) \<equiv> M \<in> machine \<and> x \<in> list(symbol) \<and>
    y \<in> list(symbol) \<and> (\<exists>k\<in>nat.
      config_eq(steps(M,initial_config(x),k),\<langle>final_state,\<langle>[],y\<rangle>\<rangle>))"

lemma computes_number_iff_tape:
  "computes_number(M,n,m) \<longleftrightarrow>
    n \<in> nat \<and> m \<in> nat \<and> computes_tape(M,numeral_input(n),numeral_input(m))"
  unfolding computes_number_def computes_tape_def using numeral_input_type by blast

lemma computes_tape_from_reaches:
  assumes M: "M \<in> machine" and x: "x \<in> list(symbol)" and y: "y \<in> list(symbol)"
    and start: "config_eq(c,initial_config(x))"
    and run: "reaches(M,c,d)"
    and finish: "config_eq(d,\<langle>final_state,\<langle>[],y\<rangle>\<rangle>)"
  shows "computes_tape(M,x,y)"
proof -
  from run obtain k where k: "k \<in> nat" and run_k: "steps(M,c,k) = d" by auto
  from steps_config_eq[OF M config_eq_sym[OF start] k] run_k
  have eq: "config_eq(steps(M,initial_config(x),k),d)" by simp
  from config_eq_trans[OF eq finish] M x y k
  show ?thesis unfolding computes_tape_def by blast
qed

lemma computes_tape_output_eq:
  assumes computation: "computes_tape(M,x,y)" and z: "z \<in> list(symbol)"
    and eq: "half_tape_eq(y,z)"
  shows "computes_tape(M,x,z)"
proof -
  from computation obtain k where M: "M \<in> machine" and x: "x \<in> list(symbol)"
    and y: "y \<in> list(symbol)" and k: "k \<in> nat"
    and out: "config_eq(steps(M,initial_config(x),k),\<langle>final_state,\<langle>[],y\<rangle>\<rangle>)"
    unfolding computes_tape_def by auto
  from y z eq have finals:
    "config_eq(\<langle>final_state,\<langle>[],y\<rangle>\<rangle>,\<langle>final_state,\<langle>[],z\<rangle>\<rangle>)"
    unfolding config_eq_def tape_eq_def configuration_def tape_def by auto
  from config_eq_trans[OF out finals] M x z k
  show ?thesis unfolding computes_tape_def by blast
qed

theorem computes_tape_sequential:
  assumes first: "computes_tape(R,x,y)" and second: "computes_tape(S,y,z)"
  shows "computes_tape(sequential_machine(R,S),x,z)"
proof -
  from first obtain k where R: "R \<in> machine" and x: "x \<in> list(symbol)"
    and k: "k \<in> nat"
    and out_R: "config_eq(steps(R,initial_config(x),k),\<langle>final_state,\<langle>[],y\<rangle>\<rangle>)"
    unfolding computes_tape_def by auto
  from second obtain l where S: "S \<in> machine" and z: "z \<in> list(symbol)"
    and l: "l \<in> nat"
    and out_S: "config_eq(steps(S,initial_config(y),l),\<langle>final_state,\<langle>[],z\<rangle>\<rangle>)"
    unfolding computes_tape_def by auto
  let ?c = "initial_config(x)"
  let ?d = "\<langle>initial_state,snd(steps(R,?c,k))\<rangle>"
  let ?e = "steps(S,?d,l)"
  have restart: "config_eq(?d,initial_config(y))"
  proof (rule config_eq_pair)
    show "initial_state \<in> nat" by simp
    from out_R show "tape_eq(snd(steps(R,?c,k)),\<langle>[],y\<rangle>)"
      unfolding config_eq_def by auto
  qed
  from steps_config_eq[OF S restart l] out_S
  have final_eq: "config_eq(?e,\<langle>final_state,\<langle>[],z\<rangle>\<rangle>)"
    by (rule config_eq_trans)
  have c: "?c \<in> configuration" by (rule initial_config_type[OF x])
  have bound: "fst(?c) \<in> control_bound(R)"
    using initial_state_below_control[OF R] by simp
  from out_R have final_R: "fst(steps(R,?c,k)) = final_state"
    unfolding config_eq_def by auto
  from steps_sequential_after_halting[OF R S c bound _ k final_R l]
  obtain h where h: "h \<in> nat"
    and sim: "steps(sequential_machine(R,S),?c,h #+ l) = shift_configuration(control_bound(R),?e)"
    by auto
  from final_eq have e: "?e \<in> configuration" and final_e: "fst(?e) = final_state"
    unfolding config_eq_def by auto
  from e have pair: "\<langle>fst(?e),snd(?e)\<rangle> = ?e"
    unfolding configuration_def by (rule Pair_fst_snd_eq)
  from pair final_e have shift: "shift_configuration(control_bound(R),?e) = ?e"
    unfolding shift_configuration_def by simp
  from sim shift final_eq have composed:
    "config_eq(steps(sequential_machine(R,S),?c,h #+ l),\<langle>final_state,\<langle>[],z\<rangle>\<rangle>)" by simp
  from sequential_machine_type[OF R S] x z add_type[of h l] composed
  show ?thesis unfolding computes_tape_def by blast
qed

end
