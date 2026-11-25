(*  Title:      Arithmetic_Translation.thy
    Author:     Tang Ziyi
*)

section \<open>Translation of Arithmetic into Set Theory\<close>

theory Arithmetic_Translation
  imports Turing_Arithmetic_Truth
begin

subsection \<open>Relational arithmetic\<close>

text \<open>The source language uses relations for zero, successor, addition
and multiplication, with equality and order. For example, addition has
three variable indices, with the third naming the result. The indices are
de Bruijn indices into a list of natural numbers. Universal quantification
adds a new value at the front of that list. NAND and universal quantification
suffice to express the other Boolean connectives and the existential quantifier.
Nested arithmetic terms can be represented relationally by naming their
intermediate values.\<close>

consts arith_formula :: i
datatype
  "arith_formula" =
    Arith_Zero ("i \<in> nat")
  | Arith_Succ ("i \<in> nat", "j \<in> nat")
  | Arith_Eq ("i \<in> nat", "j \<in> nat")
  | Arith_Less ("i \<in> nat", "j \<in> nat")
  | Arith_Add ("i \<in> nat", "j \<in> nat", "k \<in> nat")
  | Arith_Mult ("i \<in> nat", "j \<in> nat", "k \<in> nat")
  | Arith_Nand ("p \<in> arith_formula", "q \<in> arith_formula")
  | Arith_All ("p \<in> arith_formula")

declare arith_formula.intros [TC]

consts arith_arity :: "i \<Rightarrow> i"
primrec
  "arith_arity(Arith_Zero(i)) = succ(i)"
  "arith_arity(Arith_Succ(i,j)) = succ(i) \<union> succ(j)"
  "arith_arity(Arith_Eq(i,j)) = succ(i) \<union> succ(j)"
  "arith_arity(Arith_Less(i,j)) = succ(i) \<union> succ(j)"
  "arith_arity(Arith_Add(i,j,k)) = succ(i) \<union> succ(j) \<union> succ(k)"
  "arith_arity(Arith_Mult(i,j,k)) = succ(i) \<union> succ(j) \<union> succ(k)"
  "arith_arity(Arith_Nand(p,q)) = arith_arity(p) \<union> arith_arity(q)"
  "arith_arity(Arith_All(p)) = Arith.pred(arith_arity(p))"

lemma arith_arity_type [TC]:
  "p \<in> arith_formula \<Longrightarrow> arith_arity(p) \<in> nat"
  by (induct set: arith_formula) (simp_all add: arith_arity.simps Un_nat_type)

text \<open>The semantics is defined independently of the translation. It
collects the natural number environments satisfying each source formula.
An environment supplies all free variables when its length is at least
the arity.\<close>

consts arith_true_envs :: "i \<Rightarrow> i"
primrec
  "arith_true_envs(Arith_Zero(i)) =
    {env \<in> list(nat). nth(i,env) = 0}"
  "arith_true_envs(Arith_Succ(i,j)) =
    {env \<in> list(nat). nth(j,env) = succ(nth(i,env))}"
  "arith_true_envs(Arith_Eq(i,j)) =
    {env \<in> list(nat). nth(i,env) = nth(j,env)}"
  "arith_true_envs(Arith_Less(i,j)) =
    {env \<in> list(nat). nth(i,env) < nth(j,env)}"
  "arith_true_envs(Arith_Add(i,j,k)) =
    {env \<in> list(nat). nth(k,env) = nth(i,env) #+ nth(j,env)}"
  "arith_true_envs(Arith_Mult(i,j,k)) =
    {env \<in> list(nat). nth(k,env) = nth(i,env) #* nth(j,env)}"
  "arith_true_envs(Arith_Nand(p,q)) =
    {env \<in> list(nat). \<not> (env \<in> arith_true_envs(p) \<and> env \<in> arith_true_envs(q))}"
  "arith_true_envs(Arith_All(p)) =
    {env \<in> list(nat). \<forall>n\<in>nat. Cons(n,env) \<in> arith_true_envs(p)}"

definition arith_sentence :: "i \<Rightarrow> o" where
  "arith_sentence(p) \<equiv> p \<in> arith_formula \<and> arith_arity(p) = 0"

subsection \<open>Translation and free variables\<close>

consts arith_translate :: "i \<Rightarrow> i"
primrec
  "arith_translate(Arith_Zero(i)) = empty_fm(i)"
  "arith_translate(Arith_Succ(i,j)) = succ_fm(i,j)"
  "arith_translate(Arith_Eq(i,j)) = Equal(i,j)"
  "arith_translate(Arith_Less(i,j)) = Member(i,j)"
  "arith_translate(Arith_Add(i,j,k)) = is_cadd_fm(i,j,k)"
  "arith_translate(Arith_Mult(i,j,k)) = is_cmult_fm(i,j,k)"
  "arith_translate(Arith_Nand(p,q)) = Nand(arith_translate(p),arith_translate(q))"
  "arith_translate(Arith_All(p)) = arith_forall_fm(arith_translate(p))"

lemma arith_translate_type [TC]:
  "p \<in> arith_formula \<Longrightarrow> arith_translate(p) \<in> formula"
  by (induct set: arith_formula) (simp_all add: arith_translate.simps arith_forall_fm_type)

lemma nat_domain_guard_arity:
  "arity(nat_member_fm(0)) = 1"
  by (simp add: nat_member_fm_def arity_omega_fm arity pred_Un_distrib)

lemma arith_forall_fm_arity:
  assumes "p \<in> formula"
  shows "arity(arith_forall_fm(p)) = Arith.pred(arity(p))"
  unfolding arith_forall_fm_def
  using assms by (simp add: arity nat_domain_guard_arity pred_Un_distrib)

theorem arith_translate_arity:
  "p \<in> arith_formula \<Longrightarrow> arity(arith_translate(p)) = arith_arity(p)"
  by (induct set: arith_formula)
    (simp_all add: arity arity_empty_fm arity_succ_fm arity_is_cadd_fm
      arity_is_cmult_fm Un_assoc Un_left_commute Un_commute arith_forall_fm_arity)

subsection \<open>Truth preservation\<close>

lemma arith_bound_union_iff:
  assumes "a \<in> nat" "b \<in> nat" "k \<in> nat"
  shows "a \<union> b \<le> k \<longleftrightarrow> a \<le> k \<and> b \<le> k"
  using assms by (simp add: le_subset_iff Un_subset_iff)

lemma arith_bound_under_binder:
  assumes a: "a \<in> nat" and k: "k \<in> nat" and bound: "Arith.pred(a) \<le> k"
  shows "a \<le> succ(k)"
proof -
  from a consider "a = 0" | n where "n \<in> nat" "a = succ(n)"
    by (blast elim: natE)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using k by simp
  next
    case 2
    then show ?thesis using bound by simp
  qed
qed

theorem sats_arith_translate_iff:
  assumes model: "transitive_zf_model(A)" and p: "p \<in> arith_formula"
    and env: "env \<in> list(nat)" and bound: "arith_arity(p) \<le> length(env)"
  shows "sats(A,arith_translate(p),env) \<longleftrightarrow> env \<in> arith_true_envs(p)"
proof -
  interpret A: M_trivial "##A"
    by (rule transitive_zf_M_trivial[OF model])
  have subset: "nat \<subseteq> A" using A.nat_into_M by auto
  have model_env: "\<And>vs. vs \<in> list(nat) \<Longrightarrow> vs \<in> list(A)"
    by (rule list_mono[OF subset, THEN subsetD])
  from p env bound show ?thesis
  proof (induct arbitrary: env set: arith_formula)
    case (Arith_Zero i)
    then show ?case using model_env sats_arith_zero[OF model] by simp
  next
    case (Arith_Succ i j)
    then show ?case using model_env sats_arith_successor[OF model]
      by (simp add: arith_bound_union_iff)
  next
    case (Arith_Eq i j)
    then show ?case using model_env by simp
  next
    case (Arith_Less i j)
    then show ?case using model_env sats_arith_less
      by (simp add: arith_bound_union_iff nth_type)
  next
    case (Arith_Add i j k)
    then show ?case using model_env sats_arith_add[OF model]
      by (simp add: arith_bound_union_iff nth_type)
  next
    case (Arith_Mult i j k)
    then show ?case using model_env sats_arith_multiply[OF model]
      by (simp add: arith_bound_union_iff nth_type)
  next
    case (Arith_Nand p q)
    then show ?case using model_env by (simp add: arith_bound_union_iff)
  next
    case (Arith_All p)
    have body_bound: "arith_arity(p) \<le> succ(length(env))"
      using Arith_All by (simp add: arith_bound_under_binder)
    have body_equiv: "\<And>n. n \<in> nat \<Longrightarrow>
        sats(A,arith_translate(p),Cons(n,env)) \<longleftrightarrow>
        Cons(n,env) \<in> arith_true_envs(p)"
      using Arith_All body_bound by simp
    show ?case
      using Arith_All.hyps(1) Arith_All.prems(1) body_equiv model_env
      by (simp add: sats_arith_forall_fm[OF model])
  qed
qed

theorem arith_translate_sentence:
  assumes "arith_sentence(p)"
  shows "arith_translate(p) \<in> formula" "arity(arith_translate(p)) = 0"
  using assms by (auto simp add: arith_sentence_def arith_translate_arity)

theorem sats_arith_sentence_iff:
  assumes model: "transitive_zf_model(A)" and p: "arith_sentence(p)"
  shows "sats(A,arith_translate(p),[]) \<longleftrightarrow> [] \<in> arith_true_envs(p)"
  using p by (simp add: arith_sentence_def sats_arith_translate_iff[OF model])

end
