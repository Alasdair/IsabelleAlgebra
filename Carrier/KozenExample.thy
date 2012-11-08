theory KozenExample
  imports Ranked_Alphabet List
begin

(* Kozen and Angus's example *)

(* Defining the alphabet *)

definition biconditional ::
  "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat" (infixl "iff" 65)
where
  "x iff y = !((x + y) \<cdot> !(x \<cdot> y))"

declare biconditional_def [skat_simp]

definition concat_map where "concat_map f = concat \<circ> map f"

declare concat_map_def [simp]

fun linsert :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "linsert 0 x ys = x#ys"
| "linsert (Suc n) x (y#ys) = y # linsert n x ys"

fun permute_step :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "permute_step x [] = [[x]]"
| "permute_step x (y#ys) = (x#y#ys) # (map (op # y) (permute_step x ys))"

fun permute :: "'a list \<Rightarrow> 'a list list" where
  "permute [] = [[]]"
| "permute (x#xs) = concat_map (permute_step x) (permute xs)"

datatype kzp = f_kzp | g_kzp | P_kzp | bot_kzp | x_kzp

lemma kzp_UNIV: "UNIV = {P_kzp,f_kzp,g_kzp,bot_kzp,x_kzp}"
  by (auto, metis kzp.exhaust)

instantiation kzp :: ranked_alphabet
begin

  fun arity_kzp :: "kzp \<Rightarrow> nat" where
    "arity_kzp f_kzp = 1"
  | "arity_kzp g_kzp = 2"
  | "arity_kzp P_kzp = 1"
  | "arity_kzp bot_kzp = 0"
  | "arity_kzp x_kzp = 0"

  definition funs_kzp :: "kzp set" where "funs_kzp \<equiv> {f_kzp, g_kzp, bot_kzp, x_kzp}"

  definition rels_kzp :: "kzp set" where "rels_kzp \<equiv> {P_kzp}"

  definition NULL_kzp :: "kzp" where "NULL_kzp \<equiv> bot_kzp"

  declare funs_kzp_def [skat_alphabet]
    and rels_kzp_def [skat_alphabet]
    and NULL_kzp_def [skat_alphabet]

  definition output_vars_kzp :: "kzp itself \<Rightarrow> nat set" where "output_vars_kzp x \<equiv> {0}"

  instance proof
    show "finite (UNIV::kzp set)" by (simp add: kzp_UNIV)

    show "(funs :: kzp set) \<inter> rels = {}"
      by (simp add: funs_kzp_def rels_kzp_def)

    show "(funs :: kzp set) \<union> rels = UNIV"
      by (simp add: funs_kzp_def rels_kzp_def kzp_UNIV)

    show "(funs :: kzp set) \<noteq> {}"
      by (simp add: funs_kzp_def)

    show "(rels :: kzp set) \<noteq> {}"
      by (simp add: rels_kzp_def)

    show "NULL \<in> (funs :: kzp set)"
      by (simp add: NULL_kzp_def funs_kzp_def)

    show "arity (NULL::kzp) = 0"
      by (simp add: NULL_kzp_def)
  qed
end

definition f :: "kzp wf_trm \<Rightarrow> kzp wf_trm" where
  "f x \<equiv> Abs_wf_trm (App f_kzp [Rep_wf_trm x])"

definition g :: "kzp wf_trm \<Rightarrow> kzp wf_trm \<Rightarrow> kzp wf_trm" where
  "g x y \<equiv> Abs_wf_trm (App g_kzp [Rep_wf_trm x, Rep_wf_trm y])"

definition P :: "kzp wf_trm \<Rightarrow> kzp skat" where
  "P x \<equiv> pred (Abs_wf_pred (Pred P_kzp [x]))"

definition vx :: "kzp wf_trm " where
  "vx \<equiv> Abs_wf_trm (App x_kzp [])"

definition bot :: "kzp wf_trm" where
  "bot \<equiv> Abs_wf_trm (App bot_kzp [])"

declare f_def [skat_simp]
  and g_def [skat_simp]
  and bot_def [skat_simp]
  and P_def [skat_simp]
  and vx_def [skat_simp]

(* Sequences *)

definition seq :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "seq xs = foldr op \<cdot> xs \<one>"

declare seq_def [skat_simp]

lemmas oner = skd.mult_oner[simplified]

declare oner [skat_simp]

lemma seq_singleton: "seq [v] = v"
  by (simp add: seq_def, metis skd.mult_oner)

lemma seq_mult: "seq (xs @ ys) = seq xs \<cdot> seq ys"
  apply (induct xs)
  apply (simp add: seq_def)
  apply (metis skd.mult_onel)
  apply (simp add: seq_def)
  by (metis skd.mult_assoc)

lemma list_td_split: "take n xs @ drop n xs = xs"
  by (induct xs, simp_all)

lemma seq_split:
  assumes seq_take: "seq (take n xs) = seq (take n ys)"
  and seq_drop: "seq (drop n xs) = seq (drop n ys)"
  shows "seq xs = seq ys"
proof -
  have "seq (take n xs @ drop n xs) = seq (take n ys @ drop n ys)"
    by (simp only: seq_mult, metis seq_drop seq_take)
  thus ?thesis
    by simp
qed

definition take_rev :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take_rev n xs = rev (take n (rev xs))"

declare take_rev_def [simp]

definition drop_rev :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "drop_rev n xs = rev (drop n (rev xs))"

declare drop_rev_def [simp]

lemma take_drop_rev_id [simp]: "drop_rev n xs @ take_rev n xs = xs"
  by (metis append_take_drop_id drop_rev_def rev_append rev_rev_ident take_rev_def)

lemma seq_split_rev:
  assumes seq_take: "seq (take_rev n xs) = seq (take_rev n ys)"
  and seq_drop: "seq (drop_rev n xs) = seq (drop_rev n ys)"
  shows "seq xs = seq ys"
proof -
  have "seq (drop_rev n xs @ take_rev n xs) = seq (drop_rev n ys @ take_rev n ys)"
    by (simp only: seq_mult, metis seq_drop seq_take)
  thus ?thesis
    by (simp only: take_drop_rev_id)
qed

lemma seq_append:
  "seq (take n xs) \<cdot> seq (drop n xs) = seq (take m ys) \<cdot> seq (drop m ys) \<Longrightarrow> seq xs = seq ys"
  by (simp add: seq_mult[symmetric])

abbreviation loop where "loop v \<equiv> skat_star (seq v)"

(* Useful lemmas *)

(* Sliding *)

lemma seq_slide:
  assumes xs_def: "xs = drop n ys"
  shows "seq xs\<cdot>(seq ys)\<^sup>\<star> = (seq (xs @ take n ys))\<^sup>\<star>\<cdot>seq xs"
proof -
  have "seq xs \<cdot> (seq (take n ys) \<cdot> seq xs)\<^sup>\<star> = (seq xs \<cdot> seq (take n ys))\<^sup>\<star> \<cdot> seq xs"
    by (simp add: ska.star_slide[simplified,symmetric])
  thus ?thesis
    by (metis append_take_drop_id assms seq_mult)
qed

(* Denesting *)

definition APPEND :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "APPEND \<alpha> \<beta> = \<alpha> @ \<beta>"

lemma seq_denest_break: "x\<^sup>\<star>\<cdot>loop ys = x\<^sup>\<star>\<cdot>loop (APPEND (drop_rev n ys) (take_rev n ys))"
  by (simp only: APPEND_def take_drop_rev_id)

lemma seq_denest: "x\<^sup>\<star>\<cdot>loop (ys @ [x\<^sup>\<star>]) = (x + seq ys)\<^sup>\<star>"
  by (metis seq_mult seq_singleton ska.star_denest_1 ska.star_denest_2 skat_order_def skd.add_comm)

lemma seq_match: "\<lbrakk>x = y; seq xs = seq ys\<rbrakk> \<Longrightarrow> seq (x # xs) = seq (y # ys)"
  by (metis (lifting) drop_1_Cons seq_split take_1_Cons)

lemma seq_cut: "seq xs = seq (take n xs) \<cdot> seq (drop n xs)"
  by (metis append_take_drop_id seq_mult)

lemma seq_cut_app: "seq xs = seq (APPEND (take n xs) (drop n xs))"
  by (simp add: APPEND_def)

lemma seq_cut_app_rev: "seq xs = seq (APPEND (drop_rev n xs) (take_rev n xs))"
  by (simp only: APPEND_def take_drop_rev_id)

lemma seq_cut_rev: "seq xs = seq (drop_rev n xs) \<cdot> seq (take_rev n xs)"
  by (metis seq_mult take_drop_rev_id)

lemma seq_push: "y\<cdot>z = z\<cdot>y \<Longrightarrow> seq xs \<cdot> y \<cdot> seq (z#zs) = seq (xs @ [z]) \<cdot> y \<cdot> seq zs"
proof -
  assume yz_comm: "y \<cdot> z = z \<cdot> y"
  have "seq xs \<cdot> y \<cdot> seq (z#zs) = seq xs \<cdot> (y \<cdot> z) \<cdot> seq zs"
    by (metis append_Cons append_Nil seq_mult seq_singleton skd.mult_assoc)
  also have "... = seq xs \<cdot> (z \<cdot> y) \<cdot> seq zs"
    by (metis yz_comm)
  also have "... = seq (xs @ [z]) \<cdot> y \<cdot> seq zs"
    by (metis seq_mult seq_singleton skd.mult_assoc)
  finally show ?thesis .
qed

lemma seq_head_comm: "x\<cdot>y = y\<cdot>x \<Longrightarrow> seq (x#y#xs) = seq (y#x#xs)"
  by (metis (hide_lams, no_types) append_Cons append_Nil seq_mult seq_singleton)

lemma seq_empty: "x = seq [] \<cdot> x"
  by (simp add: seq_def skd.mult_onel)

lemma seq_snoc: "seq xs \<cdot> x = seq (xs @ [x])"
  by (metis seq_mult seq_singleton)

lemma seq_cons: "x \<cdot> seq xs = seq (x#xs)"
  by (metis append_Cons append_Nil seq_mult seq_singleton)

lemma plus_indiv: "\<lbrakk>x1 = x2; y1 = y2\<rbrakk> \<Longrightarrow> (x1::kzp skat) + y1 = x2 + y2"
  by auto

lemma seq_plus_head_r: "seq xs = seq ys + seq zs \<Longrightarrow> seq (x#xs) = seq (x#ys) + seq (x#zs)"
  by (metis append_Cons eq_Nil_appendI seq_mult skd.distl)

lemma seq_plus_elim:
  assumes pc: "p \<in> carrier tests"
  shows "seq ((!p)#xs) + seq (p#xs) = seq xs"
proof -
  have "seq (!p#xs) + seq (p#xs) = !p \<cdot> seq xs + p \<cdot> seq xs"
    by (simp add: seq_cons)
  also have "... = (!p + p) \<cdot> seq xs"
    by (metis skd.distr)
  also have "... = \<one> \<cdot> seq xs"
    sorry
  also have "... = seq xs"
    by (metis skd.mult_onel)
  finally show ?thesis .
qed

lemma seq_permute: "\<lbrakk>xs \<in> set (permute ys); \<And>x y. \<lbrakk>x\<in>set xs; y \<in> set ys\<rbrakk> \<Longrightarrow> x\<cdot>y = y\<cdot>x\<rbrakk> \<Longrightarrow> seq xs = seq ys"
  sorry

lemma seq_zero: "last xs = !y \<Longrightarrow> seq xs \<cdot> seq(y#ys) = \<zero>"
  sorry

lemma seq_zero_var: "last xs \<cdot> y = \<zero> \<Longrightarrow> seq xs \<cdot> seq (y#ys) = \<zero>"
  sorry

lemma seq_shunt: "(\<forall>y\<in>set xs. x\<cdot>y = y\<cdot>x) \<Longrightarrow> seq (x#xs) = seq (xs@[x])"
  sorry

lemma seq_12: "seq (x#y#xs) = seq (x\<cdot>y#xs)"
  sorry

(* Shorthand notation *)

definition a :: "nat \<Rightarrow> kzp skat" where
  "a i \<equiv> P (var i)"

abbreviation a1 where "a1 \<equiv> a 1"
abbreviation a2 where "a2 \<equiv> a 2"
abbreviation a3 where "a3 \<equiv> a 3"
abbreviation a4 where "a4 \<equiv> a 4"

declare a_def [skat_simp]

lemma a_test: "a n \<in> carrier tests"
  by (simp add: a_def P_def, rule pred_closed)

lemma a_comm: "a n \<cdot> a m = a m \<cdot> a n" by skat_comm

lemma a_assign: "n \<noteq> m \<Longrightarrow> a n \<cdot> m := x = m := x \<cdot> a n"
  by (skat_comm, auto)

definition b :: "nat \<Rightarrow> kzp skat" where
  "b i \<equiv> P (f (var i))"

declare b_def [skat_simp]

definition c :: "nat \<Rightarrow> kzp skat" where
  "c i \<equiv> P (f (f (var i)))"

declare c_def [skat_simp]

definition p :: "nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "p i j \<equiv> i := f (var j)"

declare p_def [skat_simp]

abbreviation p41 where "p41 \<equiv> p 4 1"
abbreviation p11 where "p11 \<equiv> p 1 1"
abbreviation p13 where "p13 \<equiv> p 1 3"
abbreviation p22 where "p22 \<equiv> p 2 2"

definition q :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "q i j k \<equiv> i := g (var j) (var k)"

abbreviation q214 where "q214 \<equiv> q 2 1 4"
abbreviation q311 where "q311 \<equiv> q 3 1 1"
abbreviation q211 where "q211 \<equiv> q 2 1 1"

declare q_def [skat_simp]

definition r :: "nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "r i j \<equiv> i := f (f (var j))"

abbreviation x1 where "x1 \<equiv> 1 := vx"

definition s :: "nat \<Rightarrow> kzp skat" where
  "s i \<equiv> i := f vx"

definition t :: "nat \<Rightarrow> kzp skat" where
  "t i \<equiv> i := g (f vx) (f vx)"

definition u :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "u i j k \<equiv> i := g (f (f (var j))) (f (f (var k)))"

definition z :: "nat \<Rightarrow> kzp skat" where
  "z i \<equiv> 0 := var i"

declare z_def [skat_simp]

abbreviation z2 where "z2 \<equiv> z 2"

definition y :: "nat \<Rightarrow> kzp skat" where
  "y i \<equiv> i := bot"

no_notation
  one_class.one ("1") and
  dioid.one ("1\<index>") and
  dioid.zero ("0\<index>") and
  zero_class.zero ("0") and
  plus_class.plus (infixl "+" 65)

definition scheme1 :: "kzp skat list" where "scheme1 \<equiv>
  [ 1 := vx
  , 4 := f (var 1)
  , 1 := f (var 1)
  , 2 := g (var 1) (var 4)
  , 3 := g (var 1) (var 1)
  , loop
    [ !(P (var 1))
    , 1 := f (var 1)
    , 2 := g (var 1) (var 4)
    , 3 := g (var 1) (var 1)
    ]
  , P (var 1)
  , 1 := f (var 3)
  , loop
    [ !(P (var 4)) + seq
      [ P (var 4)
      , (!(P (var 2)) \<cdot> 2 := f (var 2))\<^sup>\<star>
      , P (var 2)
      , ! (P (var 3))
      , 4 := f (var 1)
      , 1 := f (var 1)
      ]
    , 2 := g (var 1) (var 4)
    , 3 := g (var 1) (var 1)
    , loop
      [ !(P (var 1))
      , 1 := f (var 1)
      , 2 := g (var 1) (var 4)
      , 3 := g (var 1) (var 1)
      ]
    , P (var 1)
    , 1 := f (var 3)
    ]
  , P (var 4)
  , (!(P (var 2)) \<cdot> 2 := f (var 2))\<^sup>\<star>
  , P (var 2)
  , P (var 3)
  , 0 := var 2
  , halt
  ]"

definition scheme2 where "scheme2 \<equiv>
  [ 2 := f vx
  , P (var 2)
  , 2 := g (var 2) (var 2)
  , skat_star (seq
    [ !(P (var 2))
    , 2 := f (f (var 2))
    , P (var 2)
    , 2 := g (var 2) (var 2)
    ])
  , P (var 2)
  , 0 := var 2
  , halt
  ]"

declare Nat.One_nat_def [simp del]
declare foldr.simps[skat_simp]
declare o_def[skat_simp]
declare id_def[skat_simp]

lemma kozen1: "p41\<cdot>p11 = p41\<cdot>p11\<cdot>(a1 iff a4)"
  sorry

lemma kozen2: "p41\<cdot>p11\<cdot>q214 = p41\<cdot>p11\<cdot>q211"
  sorry

theorem kozen_scheme_equivalence: "seq scheme1 = seq scheme2"
proof -
  have "seq scheme1 = seq
    [x1,p41,p11,q214,q311,loop [!a1,p11,q214,q311]
    ,loop [a1,p13,!a4 + seq [a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11],q214,q311,loop [!a1,p11,q214,q311]]
    ,a1,p13,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,a3,z2,halt]"
    apply (simp add: scheme1_def p_def[symmetric] q_def[symmetric] a_def[symmetric] z_def[symmetric])
    apply (rule seq_split[of 6], simp_all)
    apply (rule seq_split[of 3], simp_all)
    apply (rule seq_append[of 2 _ 1], simp)
    apply (simp only: seq_singleton)
    apply (rule HOL.trans)
    by (rule seq_slide[of _ 4], simp_all)

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [!a1,p11,q214,q311] + seq [a1,p13,!a4 + seq [a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11],q214,q311])\<^sup>\<star>
    ,a1,p13,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,a3,z2,halt]"
    apply (rule seq_split[of 5])
    apply simp_all
    apply (rule seq_split_rev[of 8])
    apply simp_all
    apply (subst seq_def, simp)
    apply (subst skd.mult_oner[simplified])
    apply (subst seq_denest_break[of _ _ 1])
    apply simp
    apply (simp only: APPEND_def)
    apply (subst seq_denest)
    by (simp only: seq_singleton)

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [!a1,p11,q214,q311] + seq [a1,p13,!a4,q214,q311] + seq [a1,p13,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q214,q311])\<^sup>\<star>
    ,a1,p13,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,a3,z2,halt]"
    apply (rule seq_split[of 5], simp_all)
    apply (rule seq_split_rev[of 8], simp_all)
    apply (simp add: seq_singleton)
    apply (subst skd.add_assoc[simplified])
    apply (rule_tac f = "\<lambda>x. (?v + x)\<^sup>\<star>" in arg_cong)
    apply (simp add: seq_def skd.mult_oner)
    apply (subst skd.distr[simplified])
    apply (simp add: skd.mult_assoc[symmetric, simplified])
    apply (subst skd.distl[simplified])
    by (simp add: skd.mult_assoc[simplified])

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [!a1,!a4,p11,q214,q311] + seq [!a1,a4,p11,q214,q311] + seq [a1,!a4,p13,q214,q311]
    + seq [a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q214,q311])\<^sup>\<star>
    ,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    apply (rule seq_split[of 5], simp_all)
    apply (rule seq_match)
    apply (rule arg_cong) back
    apply (rule plus_indiv)+
    apply (rule seq_plus_head_r)
    apply (subst seq_plus_elim)
    apply (rule a_test, simp)
    apply (rule seq_split[of 1], simp_all)
    apply (rule seq_split_rev[of 2], simp_all)
    apply (simp add: seq_def skd.mult_oner)
    apply skat_comm
    apply (rule seq_split[of 1], simp_all)
    apply (rule seq_split_rev[of 7], simp_all)
    apply (simp add: seq_def)
    apply skat_comm
    apply (subst seq_head_comm) back
    apply skat_comm
    apply (subst seq_split[of 1], simp_all)
    apply (subgoal_tac "halt = p13 \<cdot> halt")
    apply (erule ssubst) back
    apply (subst seq_cut[of _ 1], simp_all)
    apply (subst seq_def, simp add: skd.mult_oner[simplified])
    apply (subst seq_empty)
    apply (subst seq_push, skat_comm)+
    apply (subst skd.mult_assoc[simplified])
    apply (subst seq_snoc)
    apply (simp add: seq_singleton)
    apply (subst seq_split_rev[of 2], simp_all)
    apply (subst seq_head_comm, skat_comm, subst seq_split[of 1], simp_all)+
    apply (subst skat_halt[of 1]) back
    apply (simp add: output_vars_kzp_def)
    apply (simp add: p_def)
    apply (subst skd.mult_assoc[symmetric,simplified])
    apply (subst skat_null_zero)
    apply (subst skat_halt[symmetric])
    apply (simp add: output_vars_kzp_def)
    by simp

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [!a1,a4,p11,q214,q311]
    + seq [a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q214,q311])\<^sup>\<star>
    ,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    apply (subst seq_split[of 5], simp_all)
    apply (subst seq_cons[symmetric])
    apply (subst seq_cons[symmetric]) back back back back back
    apply (subst skd.add_assoc[simplified])
    apply (subst skd.add_comm[simplified]) back
    apply (subst skd.add_assoc[symmetric,simplified])
    apply (subst skd.add_assoc[simplified]) back
    apply (rule ska.kozen_skat_lemma[simplified])
    apply (subgoal_tac "seq [!a1,!a4,p11,q214,q311] = seq [!a1,p11,q214,q311,!a4]")
    apply (erule ssubst)
    apply (subgoal_tac "seq [a1,!a4,p13,q214,q311] = seq [a1,p13,q214,q311,!a4]")
    apply (erule ssubst)
    apply (subst seq_head_comm) back back
    apply skat_comm
    apply (subst seq_head_comm) back back back
    apply skat_comm
    apply (simp add: skd.distr[simplified] skd.distl[simplified])
    apply (subst seq_zero, simp)+
    apply (simp add: skd.add_zerol)
    prefer 3
    apply (subgoal_tac "seq [(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt] = seq [a4,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]")
    apply (erule ssubst)
    apply (subgoal_tac "seq [!a1,!a4,p11,q214,q311] = seq [!a1,p11,q214,q311,!a4]")
    apply (erule ssubst)
    apply (subgoal_tac "seq [a1,!a4,p13,q214,q311] = seq [a1,p13,q214,q311,!a4]")
    apply (erule ssubst)
    apply (simp add: skd.distr[simplified])
    apply (subst seq_zero,simp)+
    apply (simp add: skd.add_zerol)
    prefer 3
    apply (subst seq_head_comm) back
    apply skat_comm
    apply (subst seq_split[of 1], simp_all)
    apply (subst seq_split_rev[of 2], simp_all)
    apply (rule seq_permute)
    apply simp
    apply (simp, safe)
    apply skat_comm+
    apply (subst seq_split[of 1], simp_all)
    apply (subst seq_shunt, simp, safe, skat_comm+, simp)
    apply (subst seq_split[of 1], simp_all)
    by (subst seq_shunt, simp, safe, skat_comm+, simp)

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q214,q311])\<^sup>\<star>
    ,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    apply (subst seq_split_rev[of 7], simp_all)
    apply (subst seq_def)
    apply (subst seq_def) back back
    apply (simp add: skd.mult_assoc[symmetric,simplified] skd.mult_oner[simplified])
    apply (rule ska.kozen_skat_lemma_dual[simplified])
    defer
    apply (subst skd.mult_assoc[simplified])
    apply (subst kozen1)
    apply (simp add: skd.mult_assoc[symmetric,simplified])
    apply (subst seq_empty)
    apply (subst seq_snoc)+
    apply (subst seq_snoc[symmetric])
    apply simp
    apply (subst seq_cut[of _ 3], simp)
    apply (subst seq_shunt) back
    apply (simp, safe)
    apply skat_comm+
    apply simp
    apply (subst seq_12) back back
    apply (subst skd.mult_assoc[simplified])
    apply (subst seq_zero_var)
    apply (simp add: biconditional_def)
    defer
    apply (metis skd.mult_zeror)
    apply (subst seq_cut[of _ 6], simp)
    apply (subst seq_cut[of _ 2]) back apply simp
    apply (subst seq_def) back
    apply (simp add: skd.mult_oner[simplified])
    apply (subst kozen1)
    apply (subst skd.mult_assoc[simplified]) back
    apply (subst seq_cons)
    apply (simp add: skd.mult_assoc[simplified])
    apply (subst seq_shunt) back
    apply (simp, safe)
    apply skat_comm+
    apply simp
    apply (subst seq_12) back back
    apply (subst seq_zero_var)
    apply simp
    prefer 2
    apply (simp add: skd.mult_zeror[simplified])
    apply (simp add: biconditional_def)
    sorry

  also have "... = seq
    [x1,p41,p11,q211,q311
    ,(seq [a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q211,q311])\<^sup>\<star>
    ,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    apply (simp add: seq_def)
    apply (simp add: skd.mult_assoc[symmetric,simplified] skd.mult_oner[simplified])
    by (smt kozen2 skd.mult_assoc)
    

  also have "... = seq scheme2"
    sorry

  finally show ?thesis .
qed

end
