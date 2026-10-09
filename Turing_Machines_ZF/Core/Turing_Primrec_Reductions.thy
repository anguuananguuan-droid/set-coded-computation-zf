(*  Title:      Turing_Primrec_Reductions.thy
    Author:     Tang Ziyi
*)

section \<open>Primitive-Recursive Reductions\<close>

theory Turing_Primrec_Reductions
  imports Turing_Primrec
begin

definition pr_reduces :: "[i,i,i] \<Rightarrow> o" where
  "pr_reduces(f,A,B) \<equiv>
    f \<in> prim_rec \<and>
    A \<subseteq> nat \<and>
    B \<subseteq> nat \<and>
    (\<forall>n\<in>nat. n \<in> A \<longleftrightarrow> f`[n] \<in> B)"

definition pr_many_one_reducible :: "[i,i] \<Rightarrow> o" where
  "pr_many_one_reducible(A,B) \<equiv> \<exists>f. pr_reduces(f,A,B)"

end
