(*  Title:      Nat_Membership.thy
    Author:     Tang Ziyi
*)

section \<open>Natural Membership in Transitive Models\<close>

theory Nat_Membership
  imports "Turing_Model_Witnesses"
begin

text \<open>The formula expresses membership in the standard natural
numbers. Transitivity identifies the model's natural numbers with the
external set \<open>nat\<close>.\<close>

definition nat_member_fm :: "i \<Rightarrow> i" where
  "nat_member_fm(i) \<equiv> Exists(And(omega_fm(0),Member(succ(i),0)))"

text \<open>The existentially bound set at index 0 is the model's omega.
The original variable at index \<open>i\<close> shifts to
\<open>succ(i)\<close>, and membership in that set expresses membership in
the external natural numbers.\<close>

lemma nat_member_fm_type [TC]:
  "i \<in> nat \<Longrightarrow> nat_member_fm(i) \<in> formula"
  unfolding nat_member_fm_def by typecheck

theorem sats_nat_member_fm:
  assumes model: "M_ZF1_trans(A)" and env: "env \<in> list(A)"
    and i: "i \<in> nat"
  shows "sats(A,nat_member_fm(i),env) \<longleftrightarrow> nth(i,env) \<in> nat"
proof -
  interpret A: M_ZF1_trans A by (rule model)
  have natA: "nat \<in> A" using A.M_nat by simp
  show ?thesis unfolding nat_member_fm_def
    using env i natA by auto
qed

end
