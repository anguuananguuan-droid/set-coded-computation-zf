(*  Title:      Turing_Primrec_Reduction.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Reductions\<close>

theory Turing_Primrec_Reduction
  imports
    Turing_Reduction
    Turing_Transformations_Primrec
begin

subsection \<open>Primitive-Recursive Many-One Reduction\<close>

definition pr_reduces :: "[i,i,i] \<Rightarrow> o" where
  "pr_reduces(f,A,B) \<equiv>
    f \<in> prim_rec \<and>
    A \<subseteq> nat \<and>
    B \<subseteq> nat \<and>
    (\<forall>n\<in>nat. n \<in> A \<longleftrightarrow> f`[n] \<in> B)"

definition pr_many_one_reducible :: "[i,i] \<Rightarrow> o" where
  "pr_many_one_reducible(A,B) \<equiv>
    \<exists>f. pr_reduces(f,A,B)"

lemma realised_pr_reduction:
  assumes realisation: "tm_realises_unary(M,f)"
    and reduction: "pr_reduces(f,A,B)"
  shows "tm_reduces(M,A,B)"
proof -
  from realisation have machine_M: "M \<in> machine"
    and computes: "\<forall>n\<in>nat. computes_number(M,n,f`[n])"
    unfolding tm_realises_unary_def by auto
  from reduction have primitive: "f \<in> prim_rec"
    and subset_A: "A \<subseteq> nat"
    and subset_B: "B \<subseteq> nat"
    and reduces: "\<forall>n\<in>nat. n \<in> A \<longleftrightarrow> f`[n] \<in> B"
    unfolding pr_reduces_def by auto
  show ?thesis
    unfolding tm_reduces_def
  proof (intro conjI ballI)
    show "M \<in> machine" by (rule machine_M)
    show "A \<subseteq> nat" by (rule subset_A)
    show "B \<subseteq> nat" by (rule subset_B)
    fix n
    assume natural: "n \<in> nat"
    from primitive natural have value: "f`[n] \<in> nat"
      by typecheck
    from computes natural have computation:
      "computes_number(M,n,f`[n])"
      by auto
    from reduces natural have membership:
      "n \<in> A \<longleftrightarrow> f`[n] \<in> B"
      by auto
    from value computation membership show
      "\<exists>m\<in>nat.
        computes_number(M,n,m) \<and> (n \<in> A \<longleftrightarrow> m \<in> B)"
      by blast
  qed
qed

theorem pr_many_one_reducible_imp_tm_many_one_reducible:
  assumes reduction: "pr_many_one_reducible(A,B)"
    and realisation:
      "\<And>f. f \<in> prim_rec \<Longrightarrow> \<exists>M. tm_realises_unary(M,f)"
  shows "tm_many_one_reducible(A,B)"
proof -
  from reduction obtain f where reduction_f: "pr_reduces(f,A,B)"
    unfolding pr_many_one_reducible_def by auto
  from reduction_f have primitive: "f \<in> prim_rec"
    unfolding pr_reduces_def by auto
  from realisation[OF primitive] obtain M where realised:
    "tm_realises_unary(M,f)"
    by auto
  from realised_pr_reduction[OF realised reduction_f] have
    "tm_reduces(M,A,B)" .
  then show ?thesis
    unfolding tm_many_one_reducible_def by blast
qed

lemma self_hardwire_pr_reduces:
  "pr_reduces(pr_self_hardwire_code,self_halting,blank_halting)"
proof -
  show ?thesis
    unfolding pr_reduces_def
  proof (intro conjI ballI)
    show "pr_self_hardwire_code \<in> prim_rec"
      by typecheck
    show "self_halting \<subseteq> nat"
      by (rule self_halting_subset_nat)
    show "blank_halting \<subseteq> nat"
      by (rule blank_halting_subset_nat)
    fix e
    assume natural: "e \<in> nat"
    from self_hardwire_reduction[OF natural]
      pr_self_hardwire_code_singleton[OF natural]
    show "e \<in> self_halting \<longleftrightarrow>
      pr_self_hardwire_code`[e] \<in> blank_halting"
      by simp
  qed
qed

theorem self_halting_pr_many_one_reducible_blank_halting:
  "pr_many_one_reducible(self_halting,blank_halting)"
  unfolding pr_many_one_reducible_def
  using self_hardwire_pr_reduces by blast

theorem self_hardwire_realiser_imp_blank_halting_undecidable:
  assumes realisation:
    "tm_realises_unary(R,pr_self_hardwire_code)"
  shows "\<not> tm_decidable(blank_halting)"
proof -
  from realised_pr_reduction[OF realisation self_hardwire_pr_reduces]
  have "tm_reduces(R,self_halting,blank_halting)" .
  then have machine_reduction:
    "tm_many_one_reducible(self_halting,blank_halting)"
    unfolding tm_many_one_reducible_def by blast
  from tm_many_one_undecidable[
      OF machine_reduction self_halting_not_tm_decidable]
  show ?thesis .
qed

corollary prim_rec_realisation_imp_blank_halting_undecidable:
  assumes realisation:
    "\<And>f. f \<in> prim_rec \<Longrightarrow> \<exists>M. tm_realises_unary(M,f)"
  shows "\<not> tm_decidable(blank_halting)"
proof -
  from realisation[OF pr_self_hardwire_code_in_prim_rec]
  obtain R where "tm_realises_unary(R,pr_self_hardwire_code)"
    by auto
  then show ?thesis
    by (rule self_hardwire_realiser_imp_blank_halting_undecidable)
qed

end
