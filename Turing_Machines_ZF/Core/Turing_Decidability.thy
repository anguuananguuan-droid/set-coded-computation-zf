(*  Title:      Turing_Decidability.thy
    Author:     Tang Ziyi
*)

section \<open>Decision Problems\<close>

theory Turing_Decidability
  imports Turing_Coding
begin

subsection \<open>Numeral Inputs\<close>

definition numeral_input :: "i \<Rightarrow> i" where
  "numeral_input(n) \<equiv> repeat(one_symbol,n)"

lemma numeral_input_type [TC]:
  assumes natural: "n \<in> nat"
  shows "numeral_input(n) \<in> list(symbol)"
  using natural unfolding numeral_input_def by typecheck

lemma length_numeral_input [simp]:
  assumes natural: "n \<in> nat"
  shows "length(numeral_input(n)) = n"
  using natural unfolding numeral_input_def by (rule length_repeat)

lemma numeral_input_injective:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
    and equal: "numeral_input(m) = numeral_input(n)"
  shows "m = n"
proof -
  from equal have "length(numeral_input(m)) = length(numeral_input(n))"
    by simp
  with first second show ?thesis by simp
qed

subsection \<open>Halting and Output\<close>

text \<open>Output is the symbol scanned when the machine reaches the final
state. Scanning 1 means acceptance and scanning 0 means rejection. This
convention differs from output specifications that require a canonical
literal tape or a numeral remaining on the tape.\<close>

definition yields :: "[i,i,i] \<Rightarrow> o" where
  "yields(M,x,b) \<equiv>
    M \<in> machine \<and>
    x \<in> list(symbol) \<and>
    b \<in> symbol \<and>
    (\<exists>n\<in>nat.
      fst(steps(M,initial_config(x),n)) = final_state \<and>
      scan(snd(steps(M,initial_config(x),n))) = b)"

lemma yields_imp_halts_on:
  assumes result: "yields(M,x,b)"
  shows "halts_on(M,x)"
  using result unfolding yields_def halts_on_def by auto

definition accepts_number :: "[i,i] \<Rightarrow> o" where
  "accepts_number(M,n) \<equiv>
    yields(M,numeral_input(n),one_symbol)"

definition rejects_number :: "[i,i] \<Rightarrow> o" where
  "rejects_number(M,n) \<equiv>
    yields(M,numeral_input(n),blank_symbol)"

lemma accepts_number_imp_halts_on:
  assumes accepts: "accepts_number(M,n)"
  shows "halts_on(M,numeral_input(n))"
  using accepts unfolding accepts_number_def by (rule yields_imp_halts_on)

lemma rejects_number_imp_halts_on:
  assumes rejects: "rejects_number(M,n)"
  shows "halts_on(M,numeral_input(n))"
  using rejects unfolding rejects_number_def by (rule yields_imp_halts_on)

lemma yields_unique:
  assumes first: "yields(M,x,b)"
    and second: "yields(M,x,d)"
  shows "b = d"
proof -
  from first obtain m where machine_M: "M \<in> machine"
    and input: "x \<in> list(symbol)"
    and time_m: "m \<in> nat"
    and final_m:
      "fst(steps(M,initial_config(x),m)) = final_state"
    and output_b:
      "scan(snd(steps(M,initial_config(x),m))) = b"
    unfolding yields_def by auto
  from second obtain n where time_n: "n \<in> nat"
    and final_n:
      "fst(steps(M,initial_config(x),n)) = final_state"
    and output_d:
      "scan(snd(steps(M,initial_config(x),n))) = d"
    unfolding yields_def by auto
  from initial_config_type[OF input] have configuration:
    "initial_config(x) \<in> configuration" .
  show ?thesis
  proof (rule Ord_linear_le[
      OF nat_into_Ord[OF time_m] nat_into_Ord[OF time_n]])
    assume ordered: "m \<le> n"
    from steps_final_absorb[
      OF machine_M configuration time_m time_n ordered final_m]
    output_b output_d show ?thesis by simp
  next
    assume ordered: "n \<le> m"
    from steps_final_absorb[
      OF machine_M configuration time_n time_m ordered final_n]
    output_b output_d show ?thesis by simp
  qed
qed

lemma accepts_rejects_exclusive:
  assumes accepts: "accepts_number(M,n)"
    and rejects: "rejects_number(M,n)"
  shows False
proof -
  from accepts have first:
    "yields(M,numeral_input(n),one_symbol)"
    unfolding accepts_number_def .
  from rejects have second:
    "yields(M,numeral_input(n),blank_symbol)"
    unfolding rejects_number_def .
  from yields_unique[OF first second]
  show False by simp
qed

subsection \<open>Decision Semantics\<close>

definition decides :: "[i,i] \<Rightarrow> o" where
  "decides(M,A) \<equiv>
    M \<in> machine \<and>
    A \<subseteq> nat \<and>
    (\<forall>n\<in>nat.
      (accepts_number(M,n) \<longleftrightarrow> n \<in> A) \<and>
      (rejects_number(M,n) \<longleftrightarrow> n \<notin> A))"

definition tm_decidable :: "i \<Rightarrow> o" where
  "tm_decidable(A) \<equiv> \<exists>M. decides(M,A)"

lemma decides_machine:
  assumes decision: "decides(M,A)"
  shows "M \<in> machine"
  using decision unfolding decides_def by auto

lemma decides_accepts_iff:
  assumes decision: "decides(M,A)"
    and natural: "n \<in> nat"
  shows "accepts_number(M,n) \<longleftrightarrow> n \<in> A"
  using decision natural unfolding decides_def by auto

lemma decides_rejects_iff:
  assumes decision: "decides(M,A)"
    and natural: "n \<in> nat"
  shows "rejects_number(M,n) \<longleftrightarrow> n \<notin> A"
  using decision natural unfolding decides_def by auto

lemma decides_halts_on:
  assumes decision: "decides(M,A)"
    and natural: "n \<in> nat"
  shows "halts_on(M,numeral_input(n))"
proof (cases "n \<in> A")
  case True
  from decides_accepts_iff[OF decision natural] True
  have "accepts_number(M,n)" by (rule iffD2)
  then show ?thesis by (rule accepts_number_imp_halts_on)
next
  case False
  from decides_rejects_iff[OF decision natural] False
  have "rejects_number(M,n)" by (rule iffD2)
  then show ?thesis by (rule rejects_number_imp_halts_on)
qed

subsection \<open>Diagonal Rejection\<close>

definition diagonal_rejection :: i where
  "diagonal_rejection \<equiv>
    {e\<in>nat. rejects_number(decode_machine(e),e)}"

lemma diagonal_rejection_subset_nat:
  "diagonal_rejection \<subseteq> nat"
  unfolding diagonal_rejection_def by blast

lemma diagonal_rejection_iff:
  assumes natural: "e \<in> nat"
  shows "e \<in> diagonal_rejection \<longleftrightarrow>
    rejects_number(decode_machine(e),e)"
  using natural unfolding diagonal_rejection_def by simp

theorem diagonal_rejection_not_tm_decidable:
  "\<not> tm_decidable(diagonal_rejection)"
proof
  assume decidable: "tm_decidable(diagonal_rejection)"
  then obtain D where decision: "decides(D,diagonal_rejection)"
    unfolding tm_decidable_def by auto
  from decision have machine_D: "D \<in> machine"
    by (rule decides_machine)
  let ?d = "encode_machine(D)"
  from encode_machine_type[OF machine_D] have code_d:
    "?d \<in> machine_code" .
  from machine_code_subset_nat code_d have natural_d: "?d \<in> nat"
    by (rule subsetD)
  from decode_encode_machine[OF machine_D] have decoded_d:
    "decode_machine(?d) = D" .
  have diagonal:
    "?d \<in> diagonal_rejection \<longleftrightarrow>
      rejects_number(D,?d)"
    using diagonal_rejection_iff[OF natural_d] decoded_d by simp
  have rejection:
    "rejects_number(D,?d) \<longleftrightarrow>
      ?d \<notin> diagonal_rejection"
    by (rule decides_rejects_iff[OF decision natural_d])
  from diagonal rejection have paradox:
    "?d \<in> diagonal_rejection \<longleftrightarrow>
      ?d \<notin> diagonal_rejection"
    by simp
  then show False by blast
qed

subsection \<open>Blank-Input Halting\<close>

definition blank_halting :: i where
  "blank_halting \<equiv>
    {e\<in>nat. halts_blank(decode_machine(e))}"

lemma blank_halting_subset_nat:
  "blank_halting \<subseteq> nat"
  unfolding blank_halting_def by blast

lemma blank_halting_iff:
  assumes natural: "e \<in> nat"
  shows "e \<in> blank_halting \<longleftrightarrow>
    halts_blank(decode_machine(e))"
  using natural unfolding blank_halting_def by simp

subsection \<open>Self-Halting\<close>

text \<open>The self-halting set uses the total machine decoder and the
unary input for its own code. The locale halting_diagonal separates the
diagonal argument from the construction of a machine that halts exactly
when another machine rejects. Turing_Rejection supplies that machine.\<close>

definition self_halting :: i where
  "self_halting \<equiv>
    {e\<in>nat. halts_on(decode_machine(e),numeral_input(e))}"

lemma self_halting_subset_nat:
  "self_halting \<subseteq> nat"
  unfolding self_halting_def by blast

lemma self_halting_iff:
  assumes natural: "e \<in> nat"
  shows "e \<in> self_halting \<longleftrightarrow>
    halts_on(decode_machine(e),numeral_input(e))"
  using natural unfolding self_halting_def by simp

locale halting_diagonal =
  fixes rejection_transform :: "i \<Rightarrow> i"
  assumes rejection_transform_type:
      "D \<in> machine \<Longrightarrow> rejection_transform(D) \<in> machine"
    and rejection_transform_halts_iff:
      "\<lbrakk>D \<in> machine; n \<in> nat\<rbrakk> \<Longrightarrow>
        halts_on(rejection_transform(D),numeral_input(n)) \<longleftrightarrow>
        rejects_number(D,n)"
begin

theorem self_halting_not_tm_decidable:
  "\<not> tm_decidable(self_halting)"
proof
  assume decidable: "tm_decidable(self_halting)"
  then obtain D where decision: "decides(D,self_halting)"
    unfolding tm_decidable_def by auto
  from decision have machine_D: "D \<in> machine"
    by (rule decides_machine)
  let ?Q = "rejection_transform(D)"
  from rejection_transform_type[OF machine_D] have machine_Q:
    "?Q \<in> machine" .
  let ?q = "encode_machine(?Q)"
  from encode_machine_type[OF machine_Q] have code_q:
    "?q \<in> machine_code" .
  from machine_code_subset_nat code_q have natural_q: "?q \<in> nat"
    by (rule subsetD)
  from decode_encode_machine[OF machine_Q] have decoded_q:
    "decode_machine(?q) = ?Q" .
  have self:
    "?q \<in> self_halting \<longleftrightarrow>
      halts_on(?Q,numeral_input(?q))"
    using self_halting_iff[OF natural_q] decoded_q by simp
  have transformed:
    "halts_on(?Q,numeral_input(?q)) \<longleftrightarrow>
      rejects_number(D,?q)"
    by (rule rejection_transform_halts_iff[OF machine_D natural_q])
  have rejection:
    "rejects_number(D,?q) \<longleftrightarrow> ?q \<notin> self_halting"
    by (rule decides_rejects_iff[OF decision natural_q])
  from self transformed rejection have paradox:
    "?q \<in> self_halting \<longleftrightarrow> ?q \<notin> self_halting"
    by simp
  show False
  proof (cases "?q \<in> self_halting")
    case True
    from paradox True have "?q \<notin> self_halting"
      by (rule iffD1)
    with True show False by contradiction
  next
    case False
    from paradox False have "?q \<in> self_halting"
      by (rule iffD2)
    with False show False by contradiction
  qed
qed

end

end
