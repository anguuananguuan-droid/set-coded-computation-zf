(*  Title:      Turing_Arguments.thy
    Author:     Tang Ziyi
*)

section \<open>Unambiguous Argument Lists\<close>

theory Turing_Arguments
  imports Turing_Programs
begin

text \<open>Each argument n occupies n+1 strokes followed by a blank. Positive
block lengths distinguish zero from a missing argument even when trailing
blanks are ignored. The original unary numerical interface is unchanged.\<close>

consts arguments :: "i \<Rightarrow> i"
primrec
  "arguments([]) = []"
  "arguments(Cons(n,ns)) = numeral_input(succ(n)) @ Cons(blank_symbol,arguments(ns))"

lemma arguments_type [TC]:
  "ns \<in> list(nat) \<Longrightarrow> arguments(ns) \<in> list(symbol)"
  by (induct ns rule: list.induct) (auto intro: app_type numeral_input_type)

lemma arguments_Cons [simp]:
  "arguments(Cons(n,ns)) = Cons(one_symbol,numeral_input(n) @ Cons(blank_symbol,arguments(ns)))"
  by simp

consts leading_ones :: "i \<Rightarrow> i"
primrec
  "leading_ones([]) = 0"
  "leading_ones(Cons(b,bs)) = (if b = one_symbol then succ(leading_ones(bs)) else 0)"

lemma leading_ones_numeral_blank:
  assumes n: "n \<in> nat"
  shows "leading_ones(numeral_input(n) @ Cons(blank_symbol,r)) = n"
  using n by (induct n rule: nat_induct) auto

lemma leading_ones_arguments [simp]:
  "n \<in> nat \<Longrightarrow> leading_ones(arguments(Cons(n,ns))) = succ(n)"
  by (simp add: leading_ones_numeral_blank)

lemma leading_ones_eq:
  assumes xs: "xs \<in> list(symbol)" and ys: "ys \<in> list(symbol)"
    and eq: "half_tape_eq(xs,ys)"
  shows "leading_ones(xs) = leading_ones(ys)"
  using xs ys eq
proof (induct xs arbitrary: ys rule: list.induct)
  case Nil
  from Nil.prems(1) show ?case
  proof (cases rule: list.cases)
    case Nil then show ?thesis by simp
  next
    case (Cons b bs)
    from half_tape_eq_hd[OF Nil.prems(2) list.intros(1) Nil.prems(1)] Cons
    have "b = blank_symbol" by simp
    with Cons show ?thesis by simp
  qed
next
  case (Cons a as)
  from Cons.prems(1) show ?case
  proof (cases rule: list.cases)
    case Nil
    from half_tape_eq_hd[OF Cons.prems(2) _ Cons.prems(1)] Cons.hyps Nil
    have "a = blank_symbol" by auto
    with Nil show ?thesis by simp
  next
    case (Cons b bs)
    have left: "Cons(a,as) \<in> list(symbol)" using \<open>a \<in> symbol\<close> \<open>as \<in> list(symbol)\<close> by typecheck
    from half_tape_eq_hd[OF \<open>half_tape_eq(Cons(a,as),ys)\<close> left \<open>ys \<in> list(symbol)\<close>] Cons
    have heads: "a = b" by simp
    from half_tape_eq_tl[OF \<open>half_tape_eq(Cons(a,as),ys)\<close> left \<open>ys \<in> list(symbol)\<close>] Cons
    have tails: "half_tape_eq(as,bs)" by simp
    from \<open>\<And>ys. \<lbrakk>ys \<in> list(symbol); half_tape_eq(as,ys)\<rbrakk> \<Longrightarrow> leading_ones(as) = leading_ones(ys)\<close>[OF \<open>bs \<in> list(symbol)\<close> tails]
      heads Cons
    show ?thesis by simp
  qed
qed

lemma half_tape_eq_drop:
  assumes n: "n \<in> nat" and xs: "xs \<in> list(symbol)" and ys: "ys \<in> list(symbol)"
    and eq: "half_tape_eq(xs,ys)"
  shows "half_tape_eq(drop(n,xs),drop(n,ys))"
  using eq xs ys n
  unfolding half_tape_eq_def
  by (auto simp add: nth_drop)

lemma drop_numeral_blank [simp]:
  "n \<in> nat \<Longrightarrow> drop(succ(n),numeral_input(n) @ Cons(blank_symbol,r)) = r"
  by (induct n rule: nat_induct) simp_all

lemma drop_argument:
  assumes n: "n \<in> nat"
  shows "drop(succ(succ(n)),arguments(Cons(n,ns))) = arguments(ns)"
  using n
  by (induct n rule: nat_induct) (simp_all)

theorem arguments_eq_imp_equal:
  assumes ns: "ns \<in> list(nat)" and ms: "ms \<in> list(nat)"
    and eq: "half_tape_eq(arguments(ns),arguments(ms))"
  shows "ns = ms"
  using ns ms eq
proof (induct ns arbitrary: ms rule: list.induct)
  case Nil
  from Nil.prems(1) show ?case
  proof (cases rule: list.cases)
    case Nil then show ?thesis by simp
  next
    case (Cons b bs)
    from leading_ones_eq[OF arguments_type[OF list.intros(1)] arguments_type[OF Nil.prems(1)] Nil.prems(2)] Cons
    show ?thesis by simp
  qed
next
  case (Cons a as)
  from Cons.prems(1) show ?case
  proof (cases rule: list.cases)
    case Nil
    from leading_ones_eq[OF arguments_type[OF _] arguments_type[OF Cons.prems(1)] Cons.prems(2)] Cons.hyps Nil
    show ?thesis by auto
  next
    case (Cons b bs)
    have ns: "Cons(a,as) \<in> list(nat)" using \<open>a \<in> nat\<close> \<open>as \<in> list(nat)\<close> by typecheck
    from leading_ones_eq[OF arguments_type[OF ns] arguments_type[OF \<open>ms \<in> list(nat)\<close>] \<open>half_tape_eq(arguments(Cons(a,as)),arguments(ms))\<close>]
      Cons \<open>a \<in> nat\<close>
    have heads: "a = b" by (simp add: leading_ones_numeral_blank)
    from half_tape_eq_drop[OF nat_succI[OF nat_succI[OF \<open>a \<in> nat\<close>]]
        arguments_type[OF ns] arguments_type[OF \<open>ms \<in> list(nat)\<close>]
        \<open>half_tape_eq(arguments(Cons(a,as)),arguments(ms))\<close>]
      heads Cons \<open>a \<in> nat\<close>
    have tails: "half_tape_eq(arguments(as),arguments(bs))"
      by (simp add: drop_argument)
    from \<open>\<And>ms. \<lbrakk>ms \<in> list(nat); half_tape_eq(arguments(as),arguments(ms))\<rbrakk> \<Longrightarrow> as = ms\<close>[OF \<open>bs \<in> list(nat)\<close> tails]
      heads Cons
    show ?thesis by simp
  qed
qed

lemma arguments_singleton:
  "n \<in> nat \<Longrightarrow> half_tape_eq(arguments([n]),numeral_input(succ(n)))"
  using half_tape_eq_trailing_blank[OF numeral_input_type[OF nat_succI]] by simp

end
