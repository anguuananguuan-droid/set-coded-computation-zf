(*  Title:      Turing_Reduction.thy
    Author:     Tang Ziyi
*)

section \<open>Machine Reductions\<close>

theory Turing_Reduction
  imports Turing_Composition "Set_Coded_Computation_ZF.Turing_Tape"
begin

subsection \<open>Numerical Computation\<close>

definition computes_number :: "[i,i,i] \<Rightarrow> o" where
  "computes_number(M,n,m) \<equiv>
    M \<in> machine \<and>
    n \<in> nat \<and>
    m \<in> nat \<and>
    (\<exists>k\<in>nat.
      config_eq(steps(M,initial_config(numeral_input(n)),k),
        \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>))"

lemma computes_number_machine:
  assumes computation: "computes_number(M,n,m)"
  shows "M \<in> machine"
  using computation unfolding computes_number_def by auto

lemma computes_number_input:
  assumes computation: "computes_number(M,n,m)"
  shows "n \<in> nat"
  using computation unfolding computes_number_def by auto

lemma computes_number_output:
  assumes computation: "computes_number(M,n,m)"
  shows "m \<in> nat"
  using computation unfolding computes_number_def by auto

lemma nth_repeat_one:
  assumes n: "n \<in> nat" and k: "k \<in> nat" and less: "k < n"
  shows "nth(k,numeral_input(n)) = one_symbol"
  using n k less unfolding numeral_input_def
proof (induct n arbitrary: k rule: nat_induct)
  case 0 then show ?case by simp
next
  case (succ n)
  then show ?case by (erule_tac n=k in natE) auto
qed

lemma numeral_tape_eq_unique:
  assumes m: "m \<in> nat" and n: "n \<in> nat"
    and eq: "half_tape_eq(numeral_input(m),numeral_input(n))"
  shows "m = n"
proof (rule Ord_linear_lt[OF nat_into_Ord[OF m] nat_into_Ord[OF n]])
  assume "m < n"
  from nth_repeat_one[OF n m this] eq m
    nth_eq_0[OF numeral_input_type[OF m] m]
  show ?thesis unfolding half_tape_eq_def by auto
next
  assume "m = n" then show ?thesis .
next
  assume "n < m"
  from nth_repeat_one[OF m n this] eq n
    nth_eq_0[OF numeral_input_type[OF n] n]
  show ?thesis unfolding half_tape_eq_def by auto
qed

lemma final_runs_equal:
  assumes M: "M \<in> machine" and c: "c \<in> configuration"
    and p: "p \<in> nat" and q: "q \<in> nat"
    and fp: "fst(steps(M,c,p)) = final_state"
    and fq: "fst(steps(M,c,q)) = final_state"
  shows "steps(M,c,p) = steps(M,c,q)"
proof (rule Ord_linear_le[OF nat_into_Ord[OF p] nat_into_Ord[OF q]])
  assume "p \<le> q"
  from steps_final_absorb[OF M c p q this fp] show ?thesis by simp
next
  assume "q \<le> p"
  from steps_final_absorb[OF M c q p this fq] show ?thesis .
qed

lemma computes_number_unique:
  assumes first: "computes_number(M,n,m)"
    and second: "computes_number(M,n,k)"
  shows "m = k"
proof -
  from first obtain p where M: "M \<in> machine" and n: "n \<in> nat"
    and m: "m \<in> nat" and p: "p \<in> nat"
    and out_m: "config_eq(steps(M,initial_config(numeral_input(n)),p),
      \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>)"
    unfolding computes_number_def by auto
  from second obtain q where k: "k \<in> nat" and q: "q \<in> nat"
    and out_k: "config_eq(steps(M,initial_config(numeral_input(n)),q),
      \<langle>final_state,\<langle>[],numeral_input(k)\<rangle>\<rangle>)"
    unfolding computes_number_def by auto
  from out_m out_k have fp: "fst(steps(M,initial_config(numeral_input(n)),p)) = 0"
    and fq: "fst(steps(M,initial_config(numeral_input(n)),q)) = 0"
    unfolding config_eq_def by auto
  from final_runs_equal[OF M initial_config_type[OF numeral_input_type[OF n]] p q fp fq]
    out_m out_k
  have "half_tape_eq(numeral_input(m),numeral_input(k))"
    unfolding config_eq_def tape_eq_def half_tape_eq_def by auto
  then show ?thesis by (rule numeral_tape_eq_unique[OF m k])
qed

text \<open>The former literal-output contract could only compute outputs at
least as large as the input. This invariant records the reason it was replaced.\<close>

lemma literal_numeral_output_not_smaller:
  assumes M: "M \<in> machine" and n: "n \<in> nat" and m: "m \<in> nat"
    and k: "k \<in> nat"
    and exact: "steps(M,initial_config(numeral_input(n)),k) =
      \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>"
  shows "n \<le> m"
  using steps_span_mono[OF M initial_config_type[OF numeral_input_type[OF n]] k]
    exact n m
  by (simp add: tape_span_def)

subsection \<open>Unary Realisation\<close>

definition tm_realises_unary :: "[i,i] \<Rightarrow> o" where
  "tm_realises_unary(M,f) \<equiv>
    M \<in> machine \<and>
    f \<in> list(nat) -> nat \<and>
    (\<forall>n\<in>nat. computes_number(M,n,f`[n]))"

lemma tm_realises_unary_machine:
  assumes realisation: "tm_realises_unary(M,f)"
  shows "M \<in> machine"
  using realisation unfolding tm_realises_unary_def by auto

lemma tm_realises_unary_function:
  assumes realisation: "tm_realises_unary(M,f)"
  shows "f \<in> list(nat) -> nat"
  using realisation unfolding tm_realises_unary_def by auto

lemma tm_realises_unary_apply:
  assumes realisation: "tm_realises_unary(M,f)"
    and natural: "n \<in> nat"
  shows "computes_number(M,n,f`[n])"
  using realisation natural unfolding tm_realises_unary_def by auto

subsection \<open>Sequential Evaluation\<close>

lemma computation_restart_eq:
  assumes out: "config_eq(c,\<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>)"
  shows "config_eq(\<langle>initial_state,snd(c)\<rangle>,initial_config(numeral_input(m)))"
proof (rule config_eq_pair)
  show "initial_state \<in> nat" by simp
  from out show "tape_eq(snd(c),\<langle>[],numeral_input(m)\<rangle>)"
    unfolding config_eq_def by auto
qed

theorem computes_number_sequential:
  assumes first: "computes_number(R,n,m)" and second: "computes_number(S,m,p)"
  shows "computes_number(sequential_machine(R,S),n,p)"
proof -
  from first obtain k where R: "R \<in> machine" and n: "n \<in> nat"
    and k: "k \<in> nat"
    and out_R: "config_eq(steps(R,initial_config(numeral_input(n)),k),
      \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>)"
    unfolding computes_number_def by auto
  from second obtain l where S: "S \<in> machine" and p: "p \<in> nat"
    and l: "l \<in> nat"
    and out_S: "config_eq(steps(S,initial_config(numeral_input(m)),l),
      \<langle>final_state,\<langle>[],numeral_input(p)\<rangle>\<rangle>)"
    unfolding computes_number_def by auto
  let ?c = "initial_config(numeral_input(n))"
  let ?d = "\<langle>initial_state,snd(steps(R,?c,k))\<rangle>"
  let ?z = "steps(S,?d,l)"
  from steps_config_eq[OF S computation_restart_eq[OF out_R] l] out_S
  have final_eq: "config_eq(?z,\<langle>final_state,\<langle>[],numeral_input(p)\<rangle>\<rangle>)"
    by (rule config_eq_trans)
  have c: "?c \<in> configuration" by (rule initial_config_type[OF numeral_input_type[OF n]])
  have bound: "fst(?c) \<in> control_bound(R)"
    using initial_state_below_control[OF R] by simp
  from out_R have final_R: "fst(steps(R,?c,k)) = final_state"
    unfolding config_eq_def by auto
  from steps_sequential_after_halting[OF R S c bound _ k final_R l]
  obtain h where h: "h \<in> nat"
    and sim: "steps(sequential_machine(R,S),?c,h #+ l) = shift_configuration(control_bound(R),?z)"
    by auto
  from final_eq have z: "?z \<in> configuration" and final_z: "fst(?z) = final_state"
    unfolding config_eq_def by auto
  from z have pair: "\<langle>fst(?z),snd(?z)\<rangle> = ?z"
    unfolding configuration_def by (rule Pair_fst_snd_eq)
  from pair final_z have shift: "shift_configuration(control_bound(R),?z) = ?z"
    unfolding shift_configuration_def by simp
  from sim shift final_eq have composed:
    "config_eq(steps(sequential_machine(R,S),?c,h #+ l),
      \<langle>final_state,\<langle>[],numeral_input(p)\<rangle>\<rangle>)" by simp
  from sequential_machine_type[OF R S] n p add_type[of h l] composed
  show ?thesis unfolding computes_number_def by blast
qed

lemma computes_number_then_yields:
  assumes computation: "computes_number(R,n,m)"
    and result: "yields(D,numeral_input(m),b)"
  shows "yields(sequential_machine(R,D),numeral_input(n),b)"
proof -
  from computation obtain k where R: "R \<in> machine" and n: "n \<in> nat"
    and m: "m \<in> nat" and k: "k \<in> nat"
    and out: "config_eq(steps(R,initial_config(numeral_input(n)),k),
      \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>)"
    unfolding computes_number_def by auto
  from result obtain l where D: "D \<in> machine" and b: "b \<in> symbol"
    and l: "l \<in> nat"
    and final: "fst(steps(D,initial_config(numeral_input(m)),l)) = final_state"
    and output_b: "scan(snd(steps(D,initial_config(numeral_input(m)),l))) = b"
    unfolding yields_def by auto
  let ?c = "initial_config(numeral_input(n))"
  let ?d = "\<langle>initial_state,snd(steps(R,?c,k))\<rangle>"
  from computation_restart_eq[OF out] have restart:
    "config_eq(?d,initial_config(numeral_input(m)))" .
  from steps_config_eq[OF D restart l] final output_b
  have final_d: "fst(steps(D,?d,l)) = final_state"
    and output_d: "scan(snd(steps(D,?d,l))) = b"
    by (auto dest: config_eq_observe)
  have c: "?c \<in> configuration" by (rule initial_config_type[OF numeral_input_type[OF n]])
  have bound: "fst(?c) \<in> control_bound(R)"
    using initial_state_below_control[OF R] by simp
  from out have final_R: "fst(steps(R,?c,k)) = final_state"
    unfolding config_eq_def by auto
  from steps_sequential_after_halting[OF R D c bound _ k final_R l]
  obtain h where h: "h \<in> nat"
    and sim: "steps(sequential_machine(R,D),?c,h #+ l) =
      shift_configuration(control_bound(R),steps(D,?d,l))" by auto
  from restart have d: "?d \<in> configuration" unfolding config_eq_def by auto
  from R have offset: "control_bound(R) \<in> nat" by typecheck
  from shift_configuration_final_iff[OF offset steps_type[OF D d l]] sim final_d
  have final_composed: "fst(steps(sequential_machine(R,D),?c,h #+ l)) = final_state" by simp
  from sim output_d have output_composed:
    "scan(snd(steps(sequential_machine(R,D),?c,h #+ l))) = b" by simp
  from sequential_machine_type[OF R D] numeral_input_type[OF n] b
    add_type[of h l] final_composed output_composed
  show ?thesis unfolding yields_def by blast
qed

lemma yields_sequential_imp:
  assumes computation: "computes_number(R,n,m)" and D: "D \<in> machine"
    and result: "yields(sequential_machine(R,D),numeral_input(n),b)"
  shows "yields(D,numeral_input(m),b)"
proof -
  from computation obtain k where R: "R \<in> machine" and n: "n \<in> nat"
    and m: "m \<in> nat" and k: "k \<in> nat"
    and out: "config_eq(steps(R,initial_config(numeral_input(n)),k),
      \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>)"
    unfolding computes_number_def by auto
  from result obtain l where b: "b \<in> symbol" and l: "l \<in> nat"
    and final: "fst(steps(sequential_machine(R,D),initial_config(numeral_input(n)),l)) = final_state"
    and output_b: "scan(snd(steps(sequential_machine(R,D),initial_config(numeral_input(n)),l))) = b"
    unfolding yields_def by auto
  let ?c = "initial_config(numeral_input(n))"
  let ?d = "\<langle>initial_state,snd(steps(R,?c,k))\<rangle>"
  have c: "?c \<in> configuration" by (rule initial_config_type[OF numeral_input_type[OF n]])
  have bound: "fst(?c) \<in> control_bound(R)"
    using initial_state_below_control[OF R] by simp
  from out have final_R: "fst(steps(R,?c,k)) = final_state"
    unfolding config_eq_def by auto
  from steps_sequential_handoff[OF R D c bound _ k final_R]
  obtain h where bounded: "h \<in> succ(k)"
    and handoff: "steps(sequential_machine(R,D),?c,h) = shift_configuration(control_bound(R),?d)"
    by auto
  from bounded k have h: "h \<in> nat" by (blast intro: Ord_trans Ord_nat)
  from R have offset: "control_bound(R) \<in> nat" by typecheck
  from handoff offset have nonfinal:
    "fst(steps(sequential_machine(R,D),?c,h)) \<noteq> final_state" by simp
  have not_before: "\<not> l \<le> h"
  proof
    assume "l \<le> h"
    from steps_final_mono[OF sequential_machine_type[OF R D] c l h this final] nonfinal
    show False by contradiction
  qed
  from not_le_iff_lt[OF nat_into_Ord[OF l] nat_into_Ord[OF h]] not_before
  have ordered: "h \<le> l" by (auto intro: leI)
  let ?r = "l #- h"
  have r: "?r \<in> nat" by typecheck
  from add_diff_inverse[OF ordered l] have split: "h #+ ?r = l" .
  from computation_restart_eq[OF out] have restart:
    "config_eq(?d,initial_config(numeral_input(m)))" .
  from restart have d: "?d \<in> configuration" unfolding config_eq_def by auto
  from steps_sequential_after_handoff[OF R D d h r handoff] have sim:
    "steps(sequential_machine(R,D),?c,h #+ ?r) =
      shift_configuration(control_bound(R),steps(D,?d,?r))" .
  from shift_configuration_final_iff[OF offset steps_type[OF D d r]] sim split final
  have final_d: "fst(steps(D,?d,?r)) = final_state" by simp
  from sim split output_b have output_d: "scan(snd(steps(D,?d,?r))) = b" by simp
  from steps_config_eq[OF D restart r] final_d output_d
  have final_D: "fst(steps(D,initial_config(numeral_input(m)),?r)) = final_state"
    and output_D: "scan(snd(steps(D,initial_config(numeral_input(m)),?r))) = b"
    by (auto dest: config_eq_observe)
  from D numeral_input_type[OF m] b r final_D output_D
  show ?thesis unfolding yields_def by blast
qed

theorem computes_number_then_yields_iff:
  assumes computation: "computes_number(R,n,m)"
    and machine_D: "D \<in> machine"
  shows "yields(sequential_machine(R,D),numeral_input(n),b) \<longleftrightarrow>
    yields(D,numeral_input(m),b)"
proof
  assume "yields(sequential_machine(R,D),numeral_input(n),b)"
  then show "yields(D,numeral_input(m),b)"
    by (rule yields_sequential_imp[OF computation machine_D])
next
  assume "yields(D,numeral_input(m),b)"
  then show "yields(sequential_machine(R,D),numeral_input(n),b)"
    by (rule computes_number_then_yields[OF computation])
qed

theorem accepts_number_sequential_iff:
  assumes computation: "computes_number(R,n,m)"
    and machine_D: "D \<in> machine"
  shows "accepts_number(sequential_machine(R,D),n) \<longleftrightarrow>
    accepts_number(D,m)"
  unfolding accepts_number_def
  by (rule computes_number_then_yields_iff[OF computation machine_D])

theorem rejects_number_sequential_iff:
  assumes computation: "computes_number(R,n,m)"
    and machine_D: "D \<in> machine"
  shows "rejects_number(sequential_machine(R,D),n) \<longleftrightarrow>
    rejects_number(D,m)"
  unfolding rejects_number_def
  by (rule computes_number_then_yields_iff[OF computation machine_D])

subsection \<open>Many-One Reduction\<close>

definition tm_reduces :: "[i,i,i] \<Rightarrow> o" where
  "tm_reduces(R,A,B) \<equiv>
    R \<in> machine \<and>
    A \<subseteq> nat \<and>
    B \<subseteq> nat \<and>
    (\<forall>n\<in>nat. \<exists>m\<in>nat.
      computes_number(R,n,m) \<and>
      (n \<in> A \<longleftrightarrow> m \<in> B))"

definition tm_many_one_reducible :: "[i,i] \<Rightarrow> o" where
  "tm_many_one_reducible(A,B) \<equiv>
    \<exists>R. tm_reduces(R,A,B)"

lemma tm_reduces_machine:
  assumes reduction: "tm_reduces(R,A,B)"
  shows "R \<in> machine"
  using reduction unfolding tm_reduces_def by auto

theorem tm_many_one_decidable:
  assumes reduction: "tm_many_one_reducible(A,B)"
    and decidable: "tm_decidable(B)"
  shows "tm_decidable(A)"
proof -
  from reduction obtain R where reduction_R: "tm_reduces(R,A,B)"
    unfolding tm_many_one_reducible_def by auto
  from reduction_R have subset_A: "A \<subseteq> nat"
    and reduces:
      "\<forall>n\<in>nat. \<exists>m\<in>nat.
        computes_number(R,n,m) \<and>
        (n \<in> A \<longleftrightarrow> m \<in> B)"
    unfolding tm_reduces_def by auto
  from reduction_R have machine_R: "R \<in> machine"
    by (rule tm_reduces_machine)
  from decidable obtain D where decision_D: "decides(D,B)"
    unfolding tm_decidable_def by auto
  from decision_D have machine_D: "D \<in> machine"
    by (rule decides_machine)
  have decision: "decides(sequential_machine(R,D),A)"
  proof (unfold decides_def, intro conjI)
    show "sequential_machine(R,D) \<in> machine"
      by (rule sequential_machine_type[OF machine_R machine_D])
    show "A \<subseteq> nat" by (rule subset_A)
    show "\<forall>n\<in>nat.
      (accepts_number(sequential_machine(R,D),n) \<longleftrightarrow> n \<in> A) \<and>
      (rejects_number(sequential_machine(R,D),n) \<longleftrightarrow> n \<notin> A)"
    proof (intro ballI)
      fix n
      assume natural_n: "n \<in> nat"
      from reduces natural_n obtain m where natural_m: "m \<in> nat"
        and computation: "computes_number(R,n,m)"
        and membership: "n \<in> A \<longleftrightarrow> m \<in> B"
        by auto
      from decides_accepts_iff[OF decision_D natural_m] have accepts_D:
        "accepts_number(D,m) \<longleftrightarrow> m \<in> B" .
      from decides_rejects_iff[OF decision_D natural_m] have rejects_D:
        "rejects_number(D,m) \<longleftrightarrow> m \<notin> B" .
      from accepts_number_sequential_iff[OF computation machine_D]
        accepts_D membership
      have accepts:
        "accepts_number(sequential_machine(R,D),n) \<longleftrightarrow> n \<in> A"
        by blast
      from membership have nonmembership:
        "n \<notin> A \<longleftrightarrow> m \<notin> B"
        by blast
      from rejects_number_sequential_iff[OF computation machine_D]
        rejects_D nonmembership
      have rejects:
        "rejects_number(sequential_machine(R,D),n) \<longleftrightarrow> n \<notin> A"
        by blast
      from accepts rejects show
        "(accepts_number(sequential_machine(R,D),n) \<longleftrightarrow> n \<in> A) \<and>
         (rejects_number(sequential_machine(R,D),n) \<longleftrightarrow> n \<notin> A)"
        by blast
    qed
  qed
  show ?thesis unfolding tm_decidable_def using decision by blast
qed

corollary tm_many_one_undecidable:
  assumes reduction: "tm_many_one_reducible(A,B)"
    and undecidable: "\<not> tm_decidable(A)"
  shows "\<not> tm_decidable(B)"
proof
  assume "tm_decidable(B)"
  from tm_many_one_decidable[OF reduction this] undecidable
  show False by contradiction
qed

end
