(*  Title:      Turing_Primrec_Reductions.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Reductions\<close>

theory Turing_Primrec_Reductions
  imports "Set_Coded_Turing_Machines.Turing_Primrec"
begin

text \<open>Members of \<open>prim_rec\<close> act on finite lists of natural numbers.
A unary reduction evaluates its function on the singleton list \<open>[n]\<close>.
The source and target sets are subsets of \<open>nat\<close>. Composition preserves
this convention by supplying the first output as the second singleton input.\<close>

definition pr_reduces :: "[i,i,i] \<Rightarrow> o" where
  "pr_reduces(f,A,B) \<equiv>
    f \<in> prim_rec \<and>
    A \<subseteq> nat \<and>
    B \<subseteq> nat \<and>
    (\<forall>n\<in>nat. n \<in> A \<longleftrightarrow> f`[n] \<in> B)"

definition pr_many_one_reducible :: "[i,i] \<Rightarrow> o" where
  "pr_many_one_reducible(A,B) \<equiv> \<exists>f. pr_reduces(f,A,B)"

lemma pr_reduces_output_type:
  assumes "pr_reduces(f,A,B)" "n \<in> nat"
  shows "f`[n] \<in> nat"
proof -
  from assms(1) have "f \<in> prim_rec" unfolding pr_reduces_def by blast
  with assms(2) show ?thesis by typecheck
qed

lemma pr_reduces_refl:
  assumes "A \<subseteq> nat"
  shows "pr_reduces(PROJ(0),A,A)"
  using assms unfolding pr_reduces_def by (simp add: PROJ_0)

lemma pr_reduces_comp:
  assumes f: "pr_reduces(f,A,B)" and g: "pr_reduces(g,B,C)"
  shows "pr_reduces(COMP(g,[f]),A,C)"
proof -
  from f g have fg: "f \<in> prim_rec" "g \<in> prim_rec"
    and sets: "A \<subseteq> nat" "C \<subseteq> nat"
    unfolding pr_reduces_def by blast+
  from fg have "COMP(g,[f]) \<in> prim_rec" by typecheck
  moreover have "\<forall>n\<in>nat. n \<in> A \<longleftrightarrow> COMP(g,[f])`[n] \<in> C"
  proof (intro ballI)
    fix n assume n: "n \<in> nat"
    have value_nat: "f`[n] \<in> nat" by (rule pr_reduces_output_type[OF f n])
    from f g n value_nat show "n \<in> A \<longleftrightarrow> COMP(g,[f])`[n] \<in> C"
      unfolding pr_reduces_def by (simp add: COMP_1)
  qed
  ultimately show ?thesis using sets unfolding pr_reduces_def by blast
qed

lemma pr_many_one_reducible_refl:
  "A \<subseteq> nat \<Longrightarrow> pr_many_one_reducible(A,A)"
  unfolding pr_many_one_reducible_def using pr_reduces_refl by blast

lemma pr_many_one_reducible_trans:
  "\<lbrakk>pr_many_one_reducible(A,B); pr_many_one_reducible(B,C)\<rbrakk>
    \<Longrightarrow> pr_many_one_reducible(A,C)"
  unfolding pr_many_one_reducible_def using pr_reduces_comp by blast

end
