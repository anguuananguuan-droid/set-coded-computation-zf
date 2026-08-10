(*  Title:      Turing_Reduction.thy
    Author:     Tang Ziyi
*)

section \<open>Machine Reductions\<close>

theory Turing_Reduction
  imports Turing_Composition
begin

subsection \<open>Numerical Computation\<close>

definition computes_number :: "[i,i,i] \<Rightarrow> o" where
  "computes_number(M,n,m) \<equiv>
    M \<in> machine \<and>
    n \<in> nat \<and>
    m \<in> nat \<and>
    (\<exists>k\<in>nat.
      steps(M,initial_config(numeral_input(n)),k) =
        \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>)"

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

lemma computes_number_unique:
  assumes first: "computes_number(M,n,m)"
    and second: "computes_number(M,n,k)"
  shows "m = k"
proof -
  from first obtain p where machine_M: "M \<in> machine"
    and natural_n: "n \<in> nat"
    and natural_m: "m \<in> nat"
    and time_p: "p \<in> nat"
    and result_m:
      "steps(M,initial_config(numeral_input(n)),p) =
        \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>"
    unfolding computes_number_def by auto
  from second obtain q where natural_k: "k \<in> nat"
    and time_q: "q \<in> nat"
    and result_k:
      "steps(M,initial_config(numeral_input(n)),q) =
        \<langle>final_state,\<langle>[],numeral_input(k)\<rangle>\<rangle>"
    unfolding computes_number_def by auto
  from numeral_input_type[OF natural_n] have input:
    "numeral_input(n) \<in> list(symbol)" .
  from initial_config_type[OF input] have configuration:
    "initial_config(numeral_input(n)) \<in> configuration" .
  have terminal_equal:
    "steps(M,initial_config(numeral_input(n)),p) =
      steps(M,initial_config(numeral_input(n)),q)"
  proof (rule Ord_linear_le[
      OF nat_into_Ord[OF time_p] nat_into_Ord[OF time_q]])
    assume ordered: "p \<le> q"
    from result_m have final:
      "fst(steps(M,initial_config(numeral_input(n)),p)) = final_state"
      by simp
    from steps_final_absorb[
      OF machine_M configuration time_p time_q ordered final]
    show ?thesis by simp
  next
    assume ordered: "q \<le> p"
    from result_k have final:
      "fst(steps(M,initial_config(numeral_input(n)),q)) = final_state"
      by simp
    from steps_final_absorb[
      OF machine_M configuration time_q time_p ordered final]
    show ?thesis by simp
  qed
  from terminal_equal result_m result_k have
    "numeral_input(m) = numeral_input(k)"
    by simp
  then show ?thesis
    by (rule numeral_input_injective[OF natural_m natural_k])
qed

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

lemma computes_number_then_yields:
  assumes computation: "computes_number(R,n,m)"
    and result: "yields(D,numeral_input(m),b)"
  shows "yields(sequential_machine(R,D),numeral_input(n),b)"
proof -
  from computation obtain k where machine_R: "R \<in> machine"
    and natural_n: "n \<in> nat"
    and natural_m: "m \<in> nat"
    and time_k: "k \<in> nat"
    and computed:
      "steps(R,initial_config(numeral_input(n)),k) =
        \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>"
    unfolding computes_number_def by auto
  from result obtain l where machine_D: "D \<in> machine"
    and symbol_b: "b \<in> symbol"
    and time_l: "l \<in> nat"
    and final_D:
      "fst(steps(D,initial_config(numeral_input(m)),l)) = final_state"
    and output_D:
      "scan(snd(steps(D,initial_config(numeral_input(m)),l))) = b"
    unfolding yields_def by auto
  from numeral_input_type[OF natural_n] have input_n:
    "numeral_input(n) \<in> list(symbol)" .
  from initial_config_type[OF input_n] have configuration:
    "initial_config(numeral_input(n)) \<in> configuration" .
  from initial_state_below_control[OF machine_R] have initial_below:
    "fst(initial_config(numeral_input(n))) \<in> control_bound(R)"
    by simp
  have initial_nonfinal:
    "fst(initial_config(numeral_input(n))) \<noteq> final_state"
    by simp
  from computed have final_R:
    "fst(steps(R,initial_config(numeral_input(n)),k)) = final_state"
    by simp
  from steps_sequential_after_halting[
      OF machine_R machine_D configuration initial_below initial_nonfinal
        time_k final_R time_l]
  obtain h where time_h: "h \<in> nat"
    and composed:
      "steps(sequential_machine(R,D),
        initial_config(numeral_input(n)),h #+ l) =
        shift_configuration(control_bound(R),
          steps(D,
            \<langle>initial_state,
              snd(steps(R,initial_config(numeral_input(n)),k))\<rangle>,l))"
    by auto
  from computed have handoff_input:
    "\<langle>initial_state,
      snd(steps(R,initial_config(numeral_input(n)),k))\<rangle> =
      initial_config(numeral_input(m))"
    by simp
  from time_h time_l have total_time: "h #+ l \<in> nat"
    by typecheck
  from machine_R have offset: "control_bound(R) \<in> nat"
    by typecheck
  from numeral_input_type[OF natural_m] have input_m:
    "numeral_input(m) \<in> list(symbol)" .
  from initial_config_type[OF input_m] time_l machine_D have terminal_D:
    "steps(D,initial_config(numeral_input(m)),l) \<in> configuration"
    by typecheck
  from shift_configuration_final_iff[OF offset terminal_D]
    composed handoff_input final_D
  have final_composed:
    "fst(steps(sequential_machine(R,D),
      initial_config(numeral_input(n)),h #+ l)) = final_state"
    by simp
  from composed handoff_input output_D have output_composed:
    "scan(snd(steps(sequential_machine(R,D),
      initial_config(numeral_input(n)),h #+ l))) = b"
    by simp
  from sequential_machine_type[OF machine_R machine_D] input_n symbol_b
    total_time final_composed output_composed
  show ?thesis unfolding yields_def by blast
qed

lemma yields_sequential_imp:
  assumes computation: "computes_number(R,n,m)"
    and machine_D: "D \<in> machine"
    and result:
      "yields(sequential_machine(R,D),numeral_input(n),b)"
  shows "yields(D,numeral_input(m),b)"
proof -
  from computation obtain k where machine_R: "R \<in> machine"
    and natural_n: "n \<in> nat"
    and natural_m: "m \<in> nat"
    and time_k: "k \<in> nat"
    and computed:
      "steps(R,initial_config(numeral_input(n)),k) =
        \<langle>final_state,\<langle>[],numeral_input(m)\<rangle>\<rangle>"
    unfolding computes_number_def by auto
  from result obtain l where symbol_b: "b \<in> symbol"
    and time_l: "l \<in> nat"
    and final_composed:
      "fst(steps(sequential_machine(R,D),
        initial_config(numeral_input(n)),l)) = final_state"
    and output_composed:
      "scan(snd(steps(sequential_machine(R,D),
        initial_config(numeral_input(n)),l))) = b"
    unfolding yields_def by auto
  from numeral_input_type[OF natural_n] have input_n:
    "numeral_input(n) \<in> list(symbol)" .
  from initial_config_type[OF input_n] have configuration:
    "initial_config(numeral_input(n)) \<in> configuration" .
  from initial_state_below_control[OF machine_R] have initial_below:
    "fst(initial_config(numeral_input(n))) \<in> control_bound(R)"
    by simp
  have initial_nonfinal:
    "fst(initial_config(numeral_input(n))) \<noteq> final_state"
    by simp
  from computed have final_R:
    "fst(steps(R,initial_config(numeral_input(n)),k)) = final_state"
    by simp
  from steps_sequential_handoff[
      OF machine_R machine_D configuration initial_below initial_nonfinal
        time_k final_R]
  obtain h where bounded: "h \<in> succ(k)"
    and handoff:
      "steps(sequential_machine(R,D),
        initial_config(numeral_input(n)),h) =
        shift_configuration(control_bound(R),
          \<langle>initial_state,
            snd(steps(R,initial_config(numeral_input(n)),k))\<rangle>)"
    by auto
  from bounded time_k have time_h: "h \<in> nat"
    by (blast intro: Ord_trans Ord_nat)
  from computed have handoff_input:
    "\<langle>initial_state,
      snd(steps(R,initial_config(numeral_input(n)),k))\<rangle> =
      initial_config(numeral_input(m))"
    by simp
  from machine_R have offset: "control_bound(R) \<in> nat"
    by typecheck
  from handoff handoff_input offset have handoff_nonfinal:
    "fst(steps(sequential_machine(R,D),
      initial_config(numeral_input(n)),h)) \<noteq> final_state"
    by simp
  from sequential_machine_type[OF machine_R machine_D] have machine_composed:
    "sequential_machine(R,D) \<in> machine" .
  have not_before: "\<not> l \<le> h"
  proof
    assume before: "l \<le> h"
    from steps_final_mono[
      OF machine_composed configuration time_l time_h before final_composed]
    handoff_nonfinal show False by contradiction
  qed
  from not_le_iff_lt[
      OF nat_into_Ord[OF time_l] nat_into_Ord[OF time_h]] not_before
  have after_handoff: "h < l"
    by (rule iffD1)
  then have ordered: "h \<le> l" by (rule leI)
  let ?d = "l #- h"
  have continuation_time: "?d \<in> nat" by typecheck
  from add_diff_inverse[OF ordered time_l] have decomposition:
    "h #+ ?d = l" .
  from numeral_input_type[OF natural_m] have input_m:
    "numeral_input(m) \<in> list(symbol)" .
  from initial_config_type[OF input_m] have next_configuration:
    "initial_config(numeral_input(m)) \<in> configuration" .
  from handoff handoff_input have handoff_D:
    "steps(sequential_machine(R,D),
      initial_config(numeral_input(n)),h) =
      shift_configuration(control_bound(R),
        initial_config(numeral_input(m)))"
    by simp
  from steps_sequential_after_handoff[
      OF machine_R machine_D next_configuration time_h
        continuation_time handoff_D]
  have simulation:
    "steps(sequential_machine(R,D),
      initial_config(numeral_input(n)),h #+ ?d) =
      shift_configuration(control_bound(R),
        steps(D,initial_config(numeral_input(m)),?d))" .
  from steps_type[OF machine_D next_configuration continuation_time]
  have terminal_D:
    "steps(D,initial_config(numeral_input(m)),?d) \<in> configuration" .
  from shift_configuration_final_iff[OF offset terminal_D]
    simulation decomposition final_composed
  have final_D:
    "fst(steps(D,initial_config(numeral_input(m)),?d)) = final_state"
    by simp
  from simulation decomposition output_composed have output_D:
    "scan(snd(steps(D,initial_config(numeral_input(m)),?d))) = b"
    by simp
  from machine_D input_m symbol_b continuation_time final_D output_D
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
