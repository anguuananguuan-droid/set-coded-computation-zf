(*  Title:      Turing_Arithmetic_Truth.thy
    Author:     Tang Ziyi
*)

section \<open>First Arithmetic Formulas in Transitive Models\<close>

theory Turing_Arithmetic_Truth
  imports "Set_Coded_Invariance_ZF.Turing_Nat_Membership"
begin

text \<open>This begins a direct route from arithmetic truth to model invariance.
Quantifiers over arithmetic variables must range over the standard naturals;
the following formula makes that domain explicit.\<close>

theorem sats_arith_zero:
  assumes model: "transitive_zfc_model(A)" and env: "env \<in> list(A)"
    and i: "i \<in> nat"
  shows "sats(A,empty_fm(i),env) \<longleftrightarrow> nth(i,env) = 0"
proof -
  from model have trans: "Transset(A)" unfolding transitive_zfc_model_def by simp
  show ?thesis by (rule Transset_sats_empty_fm_eq_0[OF i env trans])
qed

theorem sats_arith_successor:
  assumes model: "transitive_zfc_model(A)" and env: "env \<in> list(A)"
    and i: "i \<in> nat" and j: "j \<in> nat"
    and ib: "i < length(env)" and jb: "j < length(env)"
  shows "sats(A,succ_fm(i,j),env) \<longleftrightarrow>
    nth(j,env) = succ(nth(i,env))"
proof -
  interpret A: M_trivial "##A" by (rule transitive_zfc_M_trivial[OF model])
  have x: "nth(i,env) \<in> A" using env i ib by typecheck
  have y: "nth(j,env) \<in> A" using env j jb by typecheck
  show ?thesis using env i j x y by simp
qed

theorem sats_arith_less:
  assumes env: "env \<in> list(A)" and i: "i \<in> nat" and j: "j \<in> nat"
    and x: "nth(i,env) \<in> nat" and y: "nth(j,env) \<in> nat"
  shows "sats(A,Member(i,j),env) \<longleftrightarrow> nth(i,env) < nth(j,env)"
  using env i j x y by (simp add: lt_def)

theorem sats_arith_add:
  assumes model: "transitive_zfc_model(A)" and env: "env \<in> list(A)"
    and i: "i \<in> nat" and j: "j \<in> nat" and k: "k \<in> nat"
    and x: "nth(i,env) \<in> nat" and y: "nth(j,env) \<in> nat"
    and z: "nth(k,env) \<in> nat"
  shows "sats(A,is_cadd_fm(i,j,k),env) \<longleftrightarrow>
    nth(k,env) = nth(i,env) #+ nth(j,env)"
proof -
  interpret A: M_ZF2_trans A by (rule transitive_zfc_M_ZF2_trans[OF model])
  have xm: "nth(i,env) \<in> A" using A.nat_into_M[OF x] by simp
  have ym: "nth(j,env) \<in> A" using A.nat_into_M[OF y] by simp
  have zm: "nth(k,env) \<in> A" using A.nat_into_M[OF z] by simp
  have zeroA: "0 \<in> A" by (rule A.zero_in_M)
  show ?thesis using env i j k x y xm ym zm zeroA
    by (simp add: sats_is_cadd_fm A.is_cadd_iff A.nat_cadd_rel_eq_add)
qed

theorem sats_arith_multiply:
  assumes model: "transitive_zfc_model(A)" and env: "env \<in> list(A)"
    and i: "i \<in> nat" and j: "j \<in> nat" and k: "k \<in> nat"
    and x: "nth(i,env) \<in> nat" and y: "nth(j,env) \<in> nat"
    and z: "nth(k,env) \<in> nat"
  shows "sats(A,is_cmult_fm(i,j,k),env) \<longleftrightarrow>
    nth(k,env) = nth(i,env) #* nth(j,env)"
proof -
  interpret A: M_ZF2_trans A by (rule transitive_zfc_M_ZF2_trans[OF model])
  have xm: "nth(i,env) \<in> A" using A.nat_into_M[OF x] by simp
  have ym: "nth(j,env) \<in> A" using A.nat_into_M[OF y] by simp
  have zm: "nth(k,env) \<in> A" using A.nat_into_M[OF z] by simp
  have zeroA: "0 \<in> A" by (rule A.zero_in_M)
  show ?thesis using env i j k x y xm ym zm zeroA
    by (simp add: sats_is_cmult_fm A.is_cmult_iff A.nat_cmult_rel_eq_mult)
qed

definition arith_exists_fm :: "i \<Rightarrow> i" where
  "arith_exists_fm(p) \<equiv> Exists(And(nat_member_fm(0),p))"

definition arith_forall_fm :: "i \<Rightarrow> i" where
  "arith_forall_fm(p) \<equiv> Forall(Implies(nat_member_fm(0),p))"

lemma arith_exists_fm_type [TC]:
  "p \<in> formula \<Longrightarrow> arith_exists_fm(p) \<in> formula"
  unfolding arith_exists_fm_def by typecheck

lemma arith_forall_fm_type [TC]:
  "p \<in> formula \<Longrightarrow> arith_forall_fm(p) \<in> formula"
  unfolding arith_forall_fm_def by typecheck

theorem sats_arith_exists_fm:
  assumes model: "transitive_zfc_model(A)" and env: "env \<in> list(A)"
    and p: "p \<in> formula"
  shows "sats(A,arith_exists_fm(p),env) \<longleftrightarrow>
    (\<exists>n\<in>nat. sats(A,p,Cons(n,env)))"
proof -
  interpret A: M_trivial "##A" by (rule transitive_zfc_M_trivial[OF model])
  have nat_in_A: "\<And>n. n \<in> nat \<Longrightarrow> n \<in> A"
  proof -
    fix n assume n: "n \<in> nat"
    from A.nat_into_M[OF n] show "n \<in> A" by simp
  qed
  show ?thesis unfolding arith_exists_fm_def
    using env p nat_in_A sats_nat_member_fm[OF model] by auto
qed

theorem sats_arith_forall_fm:
  assumes model: "transitive_zfc_model(A)" and env: "env \<in> list(A)"
    and p: "p \<in> formula"
  shows "sats(A,arith_forall_fm(p),env) \<longleftrightarrow>
    (\<forall>n\<in>nat. sats(A,p,Cons(n,env)))"
proof -
  interpret A: M_trivial "##A" by (rule transitive_zfc_M_trivial[OF model])
  have nat_in_A: "\<And>n. n \<in> nat \<Longrightarrow> n \<in> A"
  proof -
    fix n assume n: "n \<in> nat"
    from A.nat_into_M[OF n] show "n \<in> A" by simp
  qed
  show ?thesis unfolding arith_forall_fm_def
    using env p nat_in_A sats_nat_member_fm[OF model] by auto
qed

end
