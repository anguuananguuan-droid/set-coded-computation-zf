(*  Title:      Turing_Code_Operations.thy
    Author:     Tang Ziyi
*)

section \<open>Operations on Machine and List Codes\<close>

theory Turing_Code_Operations
  imports Turing_Coding
begin

text \<open>The operations below act directly on natural-number codes.
Their correctness lemmas relate them to pairing and list operations after
decoding. The arithmetic definitions are also used by the
primitive-recursive certificates.\<close>

consts pair_diagonal :: "i \<Rightarrow> i"

primrec
  "pair_diagonal(0) = 0"
  "pair_diagonal(succ(n)) =
    (if n = triangle(pair_diagonal(n)) #+ pair_diagonal(n) then
      succ(pair_diagonal(n))
    else
      pair_diagonal(n))"

lemma pair_diagonal_type [TC]:
  assumes natural: "n \<in> nat"
  shows "pair_diagonal(n) \<in> nat"
  using natural by (induct n rule: nat_induct) simp_all

lemma pair_diagonal_decode:
  assumes natural: "n \<in> nat"
  shows "pair_diagonal(n) =
    fst(pair_decode(n)) #+ snd(pair_decode(n))"
  using natural
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ n)
  from succ.hyps(1) have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have first: "fst(pair_decode(n)) \<in> nat"
    and second: "snd(pair_decode(n)) \<in> nat"
    by typecheck+
  from pair_code_decode[OF succ.hyps(1)] have code:
    "pair_code(fst(pair_decode(n)),snd(pair_decode(n))) = n" .
  from first show ?case
  proof (cases rule: natE)
    case 0
    from code 0 second have end_of_diagonal:
      "n = triangle(snd(pair_decode(n))) #+ snd(pair_decode(n))"
      unfolding pair_code_def by simp
    from succ.hyps(2) 0 second have diagonal:
      "pair_diagonal(n) = snd(pair_decode(n))"
      by simp
    from end_of_diagonal diagonal have at_end:
      "n = triangle(pair_diagonal(n)) #+ pair_diagonal(n)"
      by simp
    from 0 have next_pair:
      "pair_decode(succ(n)) =
        \<langle>succ(snd(pair_decode(n))),0\<rangle>"
      by (simp add: pair_step_def)
    from at_end have next_diagonal:
      "pair_diagonal(succ(n)) = succ(pair_diagonal(n))"
      by simp
    from diagonal next_pair next_diagonal second show ?thesis
      by simp
  next
    case (succ m)
    let ?s = "fst(pair_decode(n)) #+ snd(pair_decode(n))"
    have sum_natural: "?s \<in> nat"
      using first second by typecheck
    have not_end:
      "n \<noteq> triangle(?s) #+ ?s"
    proof
      assume at_end: "n = triangle(?s) #+ ?s"
      from code have
        "triangle(?s) #+ snd(pair_decode(n)) = n"
        unfolding pair_code_def .
      also from at_end have "... = triangle(?s) #+ ?s" .
      finally have equal:
        "snd(pair_decode(n)) = ?s"
        using second sum_natural
        by (rule add_left_cancel[OF refl])
      from equal succ second show False
        by (simp add: add_ac)
    qed
    from succ.hyps(2) have diagonal:
      "pair_diagonal(n) = ?s" .
    from not_end diagonal have not_at_end:
      "n \<noteq> triangle(pair_diagonal(n)) #+ pair_diagonal(n)"
      by simp
    from succ have next_pair:
      "pair_decode(succ(n)) =
        \<langle>m,succ(snd(pair_decode(n)))\<rangle>"
      by (simp add: pair_step_def)
    from not_at_end have next_diagonal:
      "pair_diagonal(succ(n)) = pair_diagonal(n)"
      by simp
    from diagonal next_pair next_diagonal succ second show ?thesis
      by (simp add: add_ac)
  qed
qed


definition pair_right_code :: "i \<Rightarrow> i" where
  "pair_right_code(n) \<equiv>
    n #- triangle(pair_diagonal(n))"

definition pair_left_code :: "i \<Rightarrow> i" where
  "pair_left_code(n) \<equiv>
    pair_diagonal(n) #- pair_right_code(n)"

lemma pair_right_code_type [TC]:
  "pair_right_code(n) \<in> nat"
  unfolding pair_right_code_def by typecheck

lemma pair_left_code_type [TC]:
  "pair_left_code(n) \<in> nat"
  unfolding pair_left_code_def by typecheck

theorem pair_right_code_decode:
  assumes natural: "n \<in> nat"
  shows "pair_right_code(n) = snd(pair_decode(n))"
proof -
  from natural have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have first: "fst(pair_decode(n)) \<in> nat"
    and second: "snd(pair_decode(n)) \<in> nat"
    by typecheck+
  from pair_code_decode[OF natural] have code:
    "n = triangle(fst(pair_decode(n)) #+ snd(pair_decode(n))) #+
      snd(pair_decode(n))"
    unfolding pair_code_def by (rule sym)
  have "pair_right_code(n) =
      (triangle(fst(pair_decode(n)) #+ snd(pair_decode(n))) #+
        snd(pair_decode(n))) #-
      triangle(fst(pair_decode(n)) #+ snd(pair_decode(n)))"
    unfolding pair_right_code_def
    using code pair_diagonal_decode[OF natural] by simp
  also from second have "... = snd(pair_decode(n))"
    by (simp add: diff_add_inverse)
  finally show ?thesis .
qed

theorem pair_left_code_decode:
  assumes natural: "n \<in> nat"
  shows "pair_left_code(n) = fst(pair_decode(n))"
proof -
  from natural have decoded: "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  from decoded have first: "fst(pair_decode(n)) \<in> nat"
    and second: "snd(pair_decode(n)) \<in> nat"
    by typecheck+
  show ?thesis
    unfolding pair_left_code_def
    using pair_diagonal_decode[OF natural]
      pair_right_code_decode[OF natural] first second
    by (simp add: diff_add_inverse2 add_ac)
qed

lemma pair_right_code_pair_code:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
  shows "pair_right_code(pair_code(m,n)) = n"
  using pair_right_code_decode[OF pair_code_type[OF first second]]
    pair_decode_code[OF first second]
  by simp

lemma pair_left_code_pair_code:
  assumes first: "m \<in> nat"
    and second: "n \<in> nat"
  shows "pair_left_code(pair_code(m,n)) = m"
  using pair_left_code_decode[OF pair_code_type[OF first second]]
    pair_decode_code[OF first second]
  by simp


definition code_cons :: "[i,i] \<Rightarrow> i" where
  "code_cons(a,c) \<equiv> succ(pair_code(a,c))"

definition code_head :: "i \<Rightarrow> i" where
  "code_head(c) \<equiv>
    if c = 0 then 0 else fst(pair_decode(pred(c)))"

definition code_tail :: "i \<Rightarrow> i" where
  "code_tail(c) \<equiv>
    if c = 0 then 0 else snd(pair_decode(pred(c)))"

lemma code_cons_type [TC]:
  assumes element: "a \<in> nat"
    and tail: "c \<in> nat"
  shows "code_cons(a,c) \<in> nat"
  using element tail unfolding code_cons_def by typecheck

lemma code_head_type [TC]:
  assumes natural: "c \<in> nat"
  shows "code_head(c) \<in> nat"
  using natural
proof (cases rule: natE)
  case 0
  then show ?thesis unfolding code_head_def by simp
next
  case (succ n)
  from succ(1) have "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  with succ natural show ?thesis unfolding code_head_def by typecheck
qed

lemma code_tail_type [TC]:
  assumes natural: "c \<in> nat"
  shows "code_tail(c) \<in> nat"
  using natural
proof (cases rule: natE)
  case 0
  then show ?thesis unfolding code_tail_def by simp
next
  case (succ n)
  from succ(1) have "pair_decode(n) \<in> nat \<times> nat"
    by (rule pair_decode_type)
  with succ natural show ?thesis unfolding code_tail_def by typecheck
qed

lemma code_cons_encode [simp]:
  "code_cons(a,nat_list_encode(l)) =
    nat_list_encode(Cons(a,l))"
  unfolding code_cons_def by simp

lemma code_head_encode:
  assumes list: "l \<in> list(nat)"
  shows "code_head(nat_list_encode(l)) = hd(l)"
  using list
proof (induct l rule: list.induct)
  case Nil
  then show ?case unfolding code_head_def by simp
next
  case (Cons a l)
  from Cons.hyps(2) have tail_code: "nat_list_encode(l) \<in> nat"
    by (rule nat_list_encode_type)
  from Cons tail_code show ?case
    unfolding code_head_def by (simp add: pair_decode_code)
qed

lemma code_tail_encode:
  assumes list: "l \<in> list(nat)"
  shows "code_tail(nat_list_encode(l)) = nat_list_encode(tl(l))"
  using list
proof (induct l rule: list.induct)
  case Nil
  then show ?case unfolding code_tail_def by simp
next
  case (Cons a l)
  from Cons.hyps(2) have tail_code: "nat_list_encode(l) \<in> nat"
    by (rule nat_list_encode_type)
  from Cons tail_code show ?case
    unfolding code_tail_def by (simp add: pair_decode_code)
qed


consts code_drop :: "[i,i] \<Rightarrow> i"

primrec
  "code_drop(0,c) = c"
  "code_drop(succ(k),c) = code_tail(code_drop(k,c))"

lemma code_drop_type [TC]:
  assumes count: "k \<in> nat"
    and code: "c \<in> nat"
  shows "code_drop(k,c) \<in> nat"
  using count code
  by (induct k rule: nat_induct) (simp_all add: code_tail_type)


lemma code_drop_encode:
  assumes count: "k \<in> nat"
    and list: "l \<in> list(nat)"
  shows "code_drop(k,nat_list_encode(l)) =
    nat_list_encode(drop(k,l))"
  using count
proof (induct k rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (succ k)
  from succ.hyps(1) list have dropped: "drop(k,l) \<in> list(nat)"
    by typecheck
  from succ list dropped show ?case
    by (simp add: code_tail_encode drop_succ)
qed

definition code_nth :: "[i,i] \<Rightarrow> i" where
  "code_nth(k,c) \<equiv> code_head(code_drop(k,c))"

lemma code_nth_type [TC]:
  assumes count: "k \<in> nat"
    and code: "c \<in> nat"
  shows "code_nth(k,c) \<in> nat"
  using count code unfolding code_nth_def by typecheck


lemma hd_eq_nth_zero:
  assumes list: "l \<in> list(A)"
  shows "hd(l) = nth(0,l)"
  using list by (cases rule: list.cases) simp_all

lemma code_nth_encode:
  assumes count: "k \<in> nat"
    and list: "l \<in> list(nat)"
  shows "code_nth(k,nat_list_encode(l)) = nth(k,l)"
proof -
  from count list have dropped: "drop(k,l) \<in> list(nat)"
    by typecheck
  from nth_drop[OF count] list have nth:
    "nth(0,drop(k,l)) = nth(k,l)"
    using count by simp
  show ?thesis
    unfolding code_nth_def
    using code_drop_encode[OF count list]
      code_head_encode[OF dropped] hd_eq_nth_zero[OF dropped] nth
    by simp
qed


definition code_has_index :: "[i,i] \<Rightarrow> i" where
  "code_has_index(k,c) \<equiv>
    if code_drop(k,c) = 0 then 0 else 1"

lemma code_has_index_type [TC]:
  "code_has_index(k,c) \<in> nat"
  unfolding code_has_index_def by typecheck


lemma nat_list_encode_zero_iff:
  assumes list: "l \<in> list(nat)"
  shows "nat_list_encode(l) = 0 \<longleftrightarrow> l = []"
  using list by (cases rule: list.cases) simp_all

lemma drop_eq_Nil_iff:
  assumes count: "k \<in> nat"
    and list: "l \<in> list(A)"
  shows "drop(k,l) = [] \<longleftrightarrow> length(l) \<le> k"
proof
  assume empty: "drop(k,l) = []"
  from length_drop[OF count, rule_format, OF list] empty
  have "length(l) #- k = 0" by simp
  with count list show "length(l) \<le> k"
    by (simp add: diff_is_0_lemma)
next
  assume "length(l) \<le> k"
  with count list show "drop(k,l) = []"
    by (rule drop_all)
qed

lemma code_has_index_encode:
  assumes count: "k \<in> nat"
    and list: "l \<in> list(nat)"
  shows "code_has_index(k,nat_list_encode(l)) =
    (if k < length(l) then 1 else 0)"
proof -
  from list have length: "length(l) \<in> nat"
    by typecheck
  from count length have not_le:
    "\<not> length(l) \<le> k \<longleftrightarrow> k < length(l)"
    using not_le_iff_lt[OF nat_into_Ord nat_into_Ord] by simp
  show ?thesis
    unfolding code_has_index_def
    using code_drop_encode[OF count list]
      nat_list_encode_zero_iff[OF drop_type[OF count list]]
      drop_eq_Nil_iff[OF count list] not_le
    by auto
qed

end
