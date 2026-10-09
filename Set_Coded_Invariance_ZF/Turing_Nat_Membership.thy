(*  Title:      Turing_Nat_Membership.thy
    Author:     Tang Ziyi
*)

section \<open>Natural Membership in Transitive Models\<close>

theory Turing_Nat_Membership
  imports Turing_Model_Witnesses
begin

definition nat_member_fm :: "i \<Rightarrow> i" where
  "nat_member_fm(i) \<equiv> Exists(And(omega_fm(0),Member(succ(i),0)))"

lemma nat_member_fm_type [TC]:
  "i \<in> nat \<Longrightarrow> nat_member_fm(i) \<in> formula"
  unfolding nat_member_fm_def by typecheck

theorem sats_nat_member_fm:
  assumes model: "transitive_zfc_model(A)" and env: "env \<in> list(A)"
    and i: "i \<in> nat"
  shows "sats(A,nat_member_fm(i),env) \<longleftrightarrow> nth(i,env) \<in> nat"
proof -
  interpret A: M_trancl "##A" by (rule transitive_zfc_M_trancl[OF model])
  have natA: "nat \<in> A" using A.M_nat by simp
  show ?thesis unfolding nat_member_fm_def
    using env i natA by auto
qed

end
