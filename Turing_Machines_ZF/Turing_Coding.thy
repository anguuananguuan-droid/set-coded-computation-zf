(*  Title:      Turing_Coding.thy
    Author:     Tang Ziyi
*)

section \<open>Machine Coding\<close>

theory Turing_Coding
  imports Turing_Machine
begin

subsection \<open>Instruction Streams\<close>

consts machine_code_list :: "i \<Rightarrow> i"

primrec
  "machine_code_list([]) = []"
  "machine_code_list(Cons(a,M)) =
    Cons(fst(a),Cons(snd(a),machine_code_list(M)))"

lemma action_in_nat [TC]:
  "action \<in> nat"
  unfolding action_def by typecheck

lemma action_subset_nat:
  "action \<subseteq> nat"
  using action_in_nat Ord_nat by (blast dest: OrdmemD)

lemma machine_code_list_type [TC]:
  assumes machine_M: "M \<in> machine"
  shows "machine_code_list(M) \<in> list(nat)"
  using machine_M unfolding machine_def instruction_def
proof (induct M rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons a M)
  then have action_field: "fst(a) \<in> action"
    and state_field: "snd(a) \<in> nat"
    and tail_code: "machine_code_list(M) \<in> list(nat)"
    by typecheck+
  from action_field action_subset_nat have "fst(a) \<in> nat"
    by blast
  with state_field tail_code show ?case by simp
qed

lemma machine_code_list_injective:
  assumes machine_M: "M \<in> machine"
    and machine_N: "N \<in> machine"
    and codes: "machine_code_list(M) = machine_code_list(N)"
  shows "M = N"
  using machine_M machine_N codes unfolding machine_def
proof (induct M arbitrary: N rule: list.induct)
  case Nil
  then show ?case
    by (cases rule: list.cases) simp_all
next
  case (Cons a M)
  note induction_hyps = Cons.hyps
  note induction_prems = Cons.prems
  from induction_hyps(1) have instruction_a: "a \<in> instruction" .
  from induction_prems(1) show ?case
  proof (cases rule: list.cases)
    case Nil
    with induction_prems show ?thesis by simp
  next
    case (Cons b N)
    have instruction_b: "b \<in> instruction" by fact
    have tail_b: "N \<in> list(instruction)" by fact
    from induction_prems(2) Cons have action_eq: "fst(a) = fst(b)"
      by simp
    from induction_prems(2) Cons have state_eq: "snd(a) = snd(b)"
      by simp
    from induction_prems(2) Cons have tails:
      "machine_code_list(M) = machine_code_list(N)"
      by simp
    from instruction_a have pair_a: "\<langle>fst(a),snd(a)\<rangle> = a"
      unfolding instruction_def by (rule Pair_fst_snd_eq)
    from instruction_b have pair_b: "\<langle>fst(b),snd(b)\<rangle> = b"
      unfolding instruction_def by (rule Pair_fst_snd_eq)
    from action_eq state_eq have pair_eq:
      "\<langle>fst(a),snd(a)\<rangle> = \<langle>fst(b),snd(b)\<rangle>"
      by (simp only: action_eq state_eq)
    have instruction_eq: "a = b"
    proof -
      from pair_a have "a = \<langle>fst(a),snd(a)\<rangle>"
        by (rule sym)
      also from pair_eq have
        "... = \<langle>fst(b),snd(b)\<rangle>" .
      also from pair_b have "... = b" .
      finally show ?thesis .
    qed
    from induction_hyps(3)[OF tail_b tails] have tail_eq: "M = N" .
    from instruction_eq tail_eq Cons show ?thesis by simp
  qed
qed

theorem machine_code_list_inj:
  "(\<lambda>M\<in>machine. machine_code_list(M))
    \<in> inj(machine,list(nat))"
  unfolding inj_def
  using machine_code_list_type machine_code_list_injective
  by auto

end
