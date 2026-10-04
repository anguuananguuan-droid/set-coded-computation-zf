(*  Title:      Turing_Workspace.thy
    Author:     Tang Ziyi
*)

section \<open>Finite Workspaces and Protected Contexts\<close>

theory Turing_Workspace
  imports Turing_Tape
begin

text \<open>A frame appends saved data beyond both ends of a finite workspace.
The left lists are stored nearest to the head first. The frame is ordinary
binary tape data, not a new machine operation.\<close>

definition frame_config :: "[i,i,i] \<Rightarrow> i" where
  "frame_config(c,L,R) \<equiv> \<langle>fst(c),\<langle>fst(snd(c)) @ L,snd(snd(c)) @ R\<rangle>\<rangle>"

lemma frame_config_pair [simp]:
  "frame_config(\<langle>q,\<langle>l,r\<rangle>\<rangle>,L,R) = \<langle>q,\<langle>l @ L,r @ R\<rangle>\<rangle>"
  unfolding frame_config_def by simp

lemma frame_config_type [TC]:
  "\<lbrakk>c \<in> configuration; L \<in> list(symbol); R \<in> list(symbol)\<rbrakk> \<Longrightarrow>
    frame_config(c,L,R) \<in> configuration"
  unfolding frame_config_def configuration_def tape_def by auto

lemma frame_config_state [simp]: "fst(frame_config(c,L,R)) = fst(c)"
  unfolding frame_config_def by simp

lemma update_frame_interior:
  assumes l: "l \<in> list(symbol)" and r: "r \<in> list(symbol)"
    and left: "l \<noteq> []" and right: "r \<noteq> []"
  shows "update(a,\<langle>l @ L,r @ R\<rangle>) =
    \<langle>fst(update(a,\<langle>l,r\<rangle>)) @ L,snd(update(a,\<langle>l,r\<rangle>)) @ R\<rangle>"
  using l r left right
  by (erule_tac a=l in list.cases; erule_tac a=r in list.cases; auto simp add: update_def)

lemma step_frame_interior:
  assumes c: "c \<in> configuration"
    and left: "fst(snd(c)) \<noteq> []" and right: "snd(snd(c)) \<noteq> []"
  shows "step(M,frame_config(c,L,R)) = frame_config(step(M,c),L,R)"
proof -
  from c obtain q l r where rep: "c = \<langle>q,\<langle>l,r\<rangle>\<rangle>"
    and l: "l \<in> list(symbol)" and r: "r \<in> list(symbol)"
    unfolding configuration_def tape_def by auto
  from rep left right have nonempty: "l \<noteq> []" "r \<noteq> []" by simp_all
  from r nonempty(2) have head: "hd(r @ R) = hd(r)" by (cases rule: list.cases) auto
  from update_frame_interior[OF l r nonempty] rep head
  show ?thesis by (simp add: frame_config_def)
qed

definition workspace_margin :: "[i,i] \<Rightarrow> o" where
  "workspace_margin(c,n) \<equiv> n \<le> length(fst(snd(c))) \<and> n \<le> length(snd(snd(c)))"

lemma margin_nonempty:
  "workspace_margin(c,succ(n)) \<Longrightarrow> fst(snd(c)) \<noteq> [] \<and> snd(snd(c)) \<noteq> []"
  unfolding workspace_margin_def by auto

lemma update_margin:
  assumes l: "l \<in> list(symbol)" and r: "r \<in> list(symbol)"
    and n: "n \<in> nat" and left: "succ(n) \<le> length(l)" and right: "succ(n) \<le> length(r)"
  shows "n \<le> length(fst(update(a,\<langle>l,r\<rangle>))) \<and>
    n \<le> length(snd(update(a,\<langle>l,r\<rangle>)))"
  using l r n left right
  by (erule_tac a=l in list.cases; erule_tac a=r in list.cases;
      auto simp add: update_def intro: le_trans leI)

lemma step_margin:
  assumes c: "c \<in> configuration" and n: "n \<in> nat"
    and margin: "workspace_margin(c,succ(n))"
  shows "workspace_margin(step(M,c),n)"
proof -
  from c obtain q l r where rep: "c = \<langle>q,\<langle>l,r\<rangle>\<rangle>"
    and l: "l \<in> list(symbol)" and r: "r \<in> list(symbol)"
    unfolding configuration_def tape_def by auto
  from margin rep have bounds: "succ(n) \<le> length(l)" "succ(n) \<le> length(r)"
    unfolding workspace_margin_def by simp_all
  from update_margin[OF l r n bounds] rep
  show ?thesis unfolding workspace_margin_def by simp
qed

lemma steps_succ_first:
  "n \<in> nat \<Longrightarrow> steps(M,c,succ(n)) = steps(M,step(M,c),n)"
  using steps_add[OF nat_1I, of n M c] by simp

text \<open>In n steps the head can consume at most n cells on either side.
With those cells present, the two saved lists are left untouched. The result
is literal configuration equality, including the final head position.\<close>

theorem steps_preserve_frame:
  assumes M: "M \<in> machine" and c: "c \<in> configuration" and n: "n \<in> nat"
    and margin: "workspace_margin(c,n)"
  shows "steps(M,frame_config(c,L,R),n) = frame_config(steps(M,c,n),L,R)"
  using n c margin
proof (induct n arbitrary: c rule: nat_induct)
  case 0 show ?case by simp
next
  case (succ n)
  from margin_nonempty[OF succ.prems(2)]
  have interior: "fst(snd(c)) \<noteq> []" "snd(snd(c)) \<noteq> []" by auto
  have first: "step(M,frame_config(c,L,R)) = frame_config(step(M,c),L,R)"
    by (rule step_frame_interior[OF succ.prems(1) interior])
  have next_c: "step(M,c) \<in> configuration" by (rule step_type[OF M succ.prems(1)])
  have next_margin: "workspace_margin(step(M,c),n)"
    by (rule step_margin[OF succ.prems(1) succ.hyps(1) succ.prems(2)])
  from succ.hyps(2)[OF next_c next_margin] first
  show ?case by (simp only: steps_succ_first[OF succ.hyps(1)])
qed

definition pad_config :: "[i,i] \<Rightarrow> i" where
  "pad_config(c,n) \<equiv> frame_config(c,repeat(blank_symbol,n),repeat(blank_symbol,n))"

lemma pad_config_type [TC]:
  "\<lbrakk>c \<in> configuration; n \<in> nat\<rbrakk> \<Longrightarrow> pad_config(c,n) \<in> configuration"
  unfolding pad_config_def by typecheck

lemma half_tape_eq_blank_padding:
  assumes xs: "xs \<in> list(symbol)" and n: "n \<in> nat"
  shows "half_tape_eq(xs @ repeat(blank_symbol,n),xs)"
  using half_tape_eq_append[OF xs half_tape_eq_blank_repeat[OF n]] xs by simp

lemma pad_config_eq:
  assumes c: "c \<in> configuration" and n: "n \<in> nat"
  shows "config_eq(pad_config(c,n),c)"
proof -
  from c obtain q l r where rep: "c = \<langle>q,\<langle>l,r\<rangle>\<rangle>"
    and l: "l \<in> list(symbol)" and r: "r \<in> list(symbol)"
    unfolding configuration_def tape_def by auto
  from c pad_config_type[OF c n] half_tape_eq_blank_padding[OF l n]
    half_tape_eq_blank_padding[OF r n] rep
  show ?thesis unfolding config_eq_def tape_eq_def pad_config_def frame_config_def configuration_def tape_def by auto
qed

lemma pad_config_margin:
  assumes c: "c \<in> configuration" and n: "n \<in> nat"
  shows "workspace_margin(pad_config(c,n),n)"
proof -
  from c have l: "fst(snd(c)) \<in> list(symbol)" and r: "snd(snd(c)) \<in> list(symbol)"
    unfolding configuration_def tape_def by auto
  have bound: "\<And>k. k \<in> nat \<Longrightarrow> n \<le> k #+ n"
  proof -
    fix k assume "k \<in> nat"
    then show "n \<le> k #+ n" by (induct k rule: nat_induct) (auto simp add: n le_succ_iff)
  qed
  show ?thesis unfolding workspace_margin_def pad_config_def frame_config_def
    using l r n by (simp add: length_repeat bound)
qed

theorem bounded_workspace_simulation:
  assumes M: "M \<in> machine" and c: "c \<in> configuration" and n: "n \<in> nat"
  shows "steps(M,frame_config(pad_config(c,n),L,R),n) =
    frame_config(steps(M,pad_config(c,n),n),L,R)"
    and "config_eq(steps(M,pad_config(c,n),n),steps(M,c,n))"
  by (rule steps_preserve_frame[OF M pad_config_type[OF c n] n pad_config_margin[OF c n]],
      rule steps_config_eq[OF M pad_config_eq[OF c n] n])

corollary bounded_workspace_history:
  assumes M: "M \<in> machine" and c: "c \<in> configuration"
    and n: "n \<in> nat" and k: "k \<in> nat" and bound: "k \<le> n"
  shows "steps(M,frame_config(pad_config(c,n),L,R),k) =
    frame_config(steps(M,pad_config(c,n),k),L,R)"
    and "config_eq(steps(M,pad_config(c,n),k),steps(M,c,k))"
proof -
  have margin: "workspace_margin(pad_config(c,n),k)"
    using pad_config_margin[OF c n] bound unfolding workspace_margin_def
    by (blast intro: le_trans)
  show "steps(M,frame_config(pad_config(c,n),L,R),k) =
    frame_config(steps(M,pad_config(c,n),k),L,R)"
    by (rule steps_preserve_frame[OF M pad_config_type[OF c n] k margin])
  show "config_eq(steps(M,pad_config(c,n),k),steps(M,c,k))"
    by (rule steps_config_eq[OF M pad_config_eq[OF c n] k])
qed

text \<open>The buffer size is a supplied time bound. This theorem gives a
protected finite simulation; it does not provide a computable time bound for
an arbitrary terminating program or a general primitive-recursive compiler.\<close>

end
