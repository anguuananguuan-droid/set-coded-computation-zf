(*  Title:      Turing_Context.thy
    Author:     Tang Ziyi
*)

section \<open>The Boundary of Standalone Numerical Contracts\<close>

theory Turing_Context
  imports Turing_Realisation
begin

text \<open>A numerical realiser is specified on an otherwise blank tape.
This does not give a frame rule for executing it beside saved nonblank data.
The following identity program moves left, erases that cell, and returns.
It satisfies the standalone numerical contract but destroys a saved stroke.
General COMP and PREC compilation must provide its own workspace discipline
or an explicit simulation that protects the surrounding storage.\<close>

definition scratch_identity_machine :: i where
  "scratch_identity_machine \<equiv>
   [\<langle>move_left,2\<rangle>,\<langle>move_left,2\<rangle>,
    \<langle>write_blank,succ(2)\<rangle>,\<langle>write_blank,succ(2)\<rangle>,
    \<langle>move_right,final_state\<rangle>,\<langle>move_right,final_state\<rangle>]"

lemma scratch_identity_machine_type [TC]: "scratch_identity_machine \<in> machine"
  unfolding scratch_identity_machine_def machine_def instruction_def by typecheck

lemma scratch_identity_computes:
  assumes n: "n \<in> nat"
  shows "computes_number(scratch_identity_machine,n,n)"
proof -
  have run: "steps(scratch_identity_machine,initial_config(numeral_input(n)),succ(2)) =
    \<langle>final_state,\<langle>[blank_symbol],numeral_input(n)\<rangle>\<rangle>"
    using n by (induct n rule: nat_induct)
      (simp_all add: scratch_identity_machine_def fetch_def slot_def)
  have eq: "config_eq(\<langle>final_state,\<langle>[blank_symbol],numeral_input(n)\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[],numeral_input(n)\<rangle>\<rangle>)"
    using numeral_input_type[OF n]
    unfolding config_eq_def tape_eq_def configuration_def tape_def by auto
  from run eq n scratch_identity_machine_type
  show ?thesis unfolding computes_number_def by (auto intro!: bexI[of _ "succ(2)"])
qed

lemma scratch_identity_realises_projection:
  "tm_realises_unary(scratch_identity_machine,PROJ(0))"
proof -
  have f: "PROJ(0) \<in> list(nat) \<rightarrow> nat" by typecheck
  from scratch_identity_computes scratch_identity_machine_type f
  show ?thesis unfolding tm_realises_unary_def by (auto simp add: PROJ_def)
qed

lemma scratch_identity_erases_saved_cell:
  "steps(scratch_identity_machine,\<langle>initial_state,\<langle>[one_symbol],[]\<rangle>\<rangle>,succ(2)) =
    \<langle>final_state,\<langle>[blank_symbol],[]\<rangle>\<rangle>"
  by (simp add: scratch_identity_machine_def fetch_def slot_def)

theorem numerical_realisation_does_not_imply_frame:
  "tm_realises_unary(scratch_identity_machine,PROJ(0)) \<and>
   \<not> config_eq(steps(scratch_identity_machine,\<langle>initial_state,\<langle>[one_symbol],[]\<rangle>\<rangle>,succ(2)),
     \<langle>final_state,\<langle>[one_symbol],[]\<rangle>\<rangle>)"
proof -
  have not_equal: "\<not> half_tape_eq([blank_symbol],[one_symbol])"
  proof
    assume eq: "half_tape_eq([blank_symbol],[one_symbol])"
    have left: "[blank_symbol] \<in> list(symbol)" by typecheck
    have right: "[one_symbol] \<in> list(symbol)" by typecheck
    from half_tape_eq_hd[OF eq left right] show False by simp
  qed
  have different: "\<not> config_eq(\<langle>final_state,\<langle>[blank_symbol],[]\<rangle>\<rangle>,
    \<langle>final_state,\<langle>[one_symbol],[]\<rangle>\<rangle>)"
    using not_equal unfolding config_eq_def tape_eq_def by auto
  show ?thesis by (simp only: scratch_identity_realises_projection
    scratch_identity_erases_saved_cell different; simp)
qed

end
