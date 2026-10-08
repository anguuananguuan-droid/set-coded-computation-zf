(*  Title:      Turing_Tape.thy
    Author:     Tang Ziyi
*)

section \<open>Observable Tape Contents\<close>

theory Turing_Tape
  imports Turing_Machine
begin

text \<open>A finite list represents an infinite blank-ended half-tape. The
Isabelle/ZF function nth returns 0 beyond the end of the list, matching the
blank symbol. Equality of represented contents must therefore ignore trailing
blanks. No instruction
is added to the machine: this relation is used only to observe its output.\<close>

definition half_tape_eq :: "[i,i] \<Rightarrow> o" where
  "half_tape_eq(xs,ys) \<equiv> \<forall>n\<in>nat. nth(n,xs) = nth(n,ys)"

lemma half_tape_eq_refl [simp]: "half_tape_eq(xs,xs)"
  unfolding half_tape_eq_def by simp

lemma half_tape_eq_sym: "half_tape_eq(xs,ys) \<Longrightarrow> half_tape_eq(ys,xs)"
  unfolding half_tape_eq_def by auto

lemma half_tape_eq_trans:
  "\<lbrakk>half_tape_eq(xs,ys); half_tape_eq(ys,zs)\<rbrakk> \<Longrightarrow> half_tape_eq(xs,zs)"
  unfolding half_tape_eq_def by auto

lemma nth_zero_hd:
  "xs \<in> list(A) \<Longrightarrow> nth(0,xs) = hd(xs)"
  by (erule list.cases) auto

lemma nth_succ_tl:
  "\<lbrakk>xs \<in> list(A); n \<in> nat\<rbrakk> \<Longrightarrow> nth(succ(n),xs) = nth(n,tl(xs))"
  by (erule list.cases) auto

lemma half_tape_eq_hd:
  "\<lbrakk>half_tape_eq(xs,ys); xs \<in> list(A); ys \<in> list(B)\<rbrakk> \<Longrightarrow> hd(xs) = hd(ys)"
  unfolding half_tape_eq_def
  by (drule_tac x=0 in bspec) (auto simp add: nth_zero_hd)

lemma half_tape_eq_tl:
  assumes eq: "half_tape_eq(xs,ys)"
    and xs: "xs \<in> list(A)" and ys: "ys \<in> list(B)"
  shows "half_tape_eq(tl(xs),tl(ys))"
  unfolding half_tape_eq_def
proof (intro ballI)
  fix n assume n: "n \<in> nat"
  from eq n have "nth(succ(n),xs) = nth(succ(n),ys)"
    unfolding half_tape_eq_def by auto
  with xs ys n show "nth(n,tl(xs)) = nth(n,tl(ys))"
    by (simp add: nth_succ_tl)
qed

lemma half_tape_eq_Cons:
  assumes eq: "half_tape_eq(xs,ys)"
  shows "half_tape_eq(Cons(a,xs),Cons(a,ys))"
  unfolding half_tape_eq_def
proof (intro ballI)
  fix n assume "n \<in> nat"
  then show "nth(n,Cons(a,xs)) = nth(n,Cons(a,ys))"
  proof (induct n rule: nat_induct)
    case 0 then show ?case by simp
  next
    case (succ n)
    with eq show ?case unfolding half_tape_eq_def by auto
  qed
qed

lemma half_tape_eq_blank [simp]: "half_tape_eq([blank_symbol],[])"
  unfolding half_tape_eq_def
  by (auto elim: natE)

definition tape_eq :: "[i,i] \<Rightarrow> o" where
  "tape_eq(t,u) \<equiv> t \<in> tape \<and> u \<in> tape \<and>
    half_tape_eq(fst(t),fst(u)) \<and> half_tape_eq(snd(t),snd(u))"

lemma tape_eq_refl: "t \<in> tape \<Longrightarrow> tape_eq(t,t)"
  unfolding tape_eq_def by simp

lemma tape_eq_sym: "tape_eq(t,u) \<Longrightarrow> tape_eq(u,t)"
  unfolding tape_eq_def using half_tape_eq_sym by blast

lemma tape_eq_trans:
  "\<lbrakk>tape_eq(t,u); tape_eq(u,v)\<rbrakk> \<Longrightarrow> tape_eq(t,v)"
  unfolding tape_eq_def using half_tape_eq_trans by blast

lemma tape_eq_scan: "tape_eq(t,u) \<Longrightarrow> scan(t) = scan(u)"
  unfolding tape_eq_def scan_def
  by (blast intro: half_tape_eq_hd dest: tapeD)

lemma tape_eq_update:
  assumes eq: "tape_eq(t,u)"
  shows "tape_eq(tm_update(a,t),tm_update(a,u))"
proof -
  from eq have t: "t \<in> tape" and u: "u \<in> tape"
    and left: "half_tape_eq(fst(t),fst(u))"
    and right: "half_tape_eq(snd(t),snd(u))"
    unfolding tape_eq_def by auto
  from tapeD[OF t] tapeD[OF u] left right
  have heads: "hd(fst(t)) = hd(fst(u))" "hd(snd(t)) = hd(snd(u))"
    and tails: "half_tape_eq(tl(fst(t)),tl(fst(u)))"
      "half_tape_eq(tl(snd(t)),tl(snd(u)))"
    by (auto intro: half_tape_eq_hd half_tape_eq_tl)
  from tm_update_type[OF t] tm_update_type[OF u]
  show ?thesis
    unfolding tape_eq_def
    using left right heads tails
    by (auto simp add: tm_update_def intro: half_tape_eq_Cons)
qed

definition config_eq :: "[i,i] \<Rightarrow> o" where
  "config_eq(c,d) \<equiv> c \<in> configuration \<and> d \<in> configuration \<and>
    fst(c) = fst(d) \<and> tape_eq(snd(c),snd(d))"

lemma config_eq_refl: "c \<in> configuration \<Longrightarrow> config_eq(c,c)"
  unfolding config_eq_def configuration_def
  by (auto intro: tape_eq_refl)

lemma config_eq_sym: "config_eq(c,d) \<Longrightarrow> config_eq(d,c)"
  unfolding config_eq_def tape_eq_def half_tape_eq_def by auto

lemma config_eq_trans:
  "\<lbrakk>config_eq(c,d); config_eq(d,e)\<rbrakk> \<Longrightarrow> config_eq(c,e)"
  unfolding config_eq_def tape_eq_def half_tape_eq_def by auto

lemma config_eq_pair:
  "\<lbrakk>q \<in> nat; tape_eq(t,u)\<rbrakk> \<Longrightarrow> config_eq(\<langle>q,t\<rangle>,\<langle>q,u\<rangle>)"
  unfolding config_eq_def tape_eq_def configuration_def by auto

lemma config_eq_observe:
  "config_eq(c,d) \<Longrightarrow> fst(c) = fst(d)"
  "config_eq(c,d) \<Longrightarrow> scan(snd(c)) = scan(snd(d))"
  unfolding config_eq_def by (auto intro: tape_eq_scan)

lemma step_config_eq:
  assumes M: "M \<in> machine" and eq: "config_eq(c,d)"
  shows "config_eq(step(M,c),step(M,d))"
proof -
  from eq have c: "c \<in> configuration" and d: "d \<in> configuration"
    and state: "fst(c) = fst(d)" and tapes: "tape_eq(snd(c),snd(d))"
    unfolding config_eq_def by auto
  from tape_eq_scan[OF tapes] state have fetch:
    "fetch(M,fst(c),scan(snd(c))) = fetch(M,fst(d),scan(snd(d)))" by simp
  from step_type[OF M c] step_type[OF M d] tape_eq_update[OF tapes] fetch
  show ?thesis unfolding config_eq_def step_def Let_def by simp
qed

theorem steps_config_eq:
  assumes M: "M \<in> machine" and eq: "config_eq(c,d)" and n: "n \<in> nat"
  shows "config_eq(steps(M,c,n),steps(M,d,n))"
  using n by (induct n rule: nat_induct) (auto intro: eq step_config_eq[OF M])

subsection \<open>Tape Span and Trailing Blanks\<close>

definition tape_span :: "i \<Rightarrow> i" where
  "tape_span(t) \<equiv> length(fst(t)) #+ length(snd(t))"

lemma update_span_mono:
  assumes t: "t \<in> tape"
  shows "tape_span(t) \<le> tape_span(tm_update(a,t))"
proof -
  from tapeD[OF t] have l: "fst(t) \<in> list(symbol)" and r: "snd(t) \<in> list(symbol)" .
  from l r show ?thesis
    unfolding tape_span_def tm_update_def
    by (erule_tac a="fst(t)" in list.cases;
        erule_tac a="snd(t)" in list.cases;
        auto simp add: add_commute)
qed

lemma step_span_mono:
  "c \<in> configuration \<Longrightarrow> tape_span(snd(c)) \<le> tape_span(snd(step(M,c)))"
  unfolding step_def Let_def
  by (auto intro: update_span_mono simp add: configuration_def)

lemma steps_span_mono:
  assumes M: "M \<in> machine" and c: "c \<in> configuration" and n: "n \<in> nat"
  shows "tape_span(snd(c)) \<le> tape_span(snd(steps(M,c,n)))"
  using n
proof (induct n rule: nat_induct)
  case 0
  with tapeD c show ?case unfolding tape_span_def configuration_def by auto
next
  case (succ n)
  from step_span_mono[OF steps_type[OF M c succ.hyps(1)]] succ.hyps(2)
  show ?case by (auto intro: le_trans)
qed

lemma half_tape_eq_blank_repeat:
  assumes n: "n \<in> nat"
  shows "half_tape_eq(repeat(blank_symbol,n),[])"
  using n
proof (induct n rule: nat_induct)
  case 0 then show ?case by simp
next
  case (succ n)
  from half_tape_eq_Cons[OF succ.hyps(2), of blank_symbol]
    half_tape_eq_blank
  show ?case by (auto intro: half_tape_eq_trans)
qed


lemma half_tape_eq_append:
  "\<lbrakk>xs \<in> list(symbol); half_tape_eq(ys,zs)\<rbrakk> \<Longrightarrow> half_tape_eq(xs @ ys,xs @ zs)"
  by (induct xs rule: list.induct) (auto intro: half_tape_eq_Cons)

lemma half_tape_eq_trailing_blank:
  "xs \<in> list(symbol) \<Longrightarrow> half_tape_eq(xs @ [blank_symbol],xs)"
  using half_tape_eq_append[OF _ half_tape_eq_blank] by auto


end
