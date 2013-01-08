theory KozenExample
  imports SKAT_Tactics List
begin

(* Kozen and Angus's example *)

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

  declare funs_kzp_def [alphabet]
    and rels_kzp_def [alphabet]
    and NULL_kzp_def [alphabet]

  definition output_vars_kzp :: "kzp itself \<Rightarrow> nat set" where "output_vars_kzp x \<equiv> {0}"

  declare output_vars_kzp_def [alphabet]

  instance proof
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

    show "\<exists>x. x \<in> output_vars TYPE(kzp)"
      by (metis (mono_tags) insertI1 output_vars_kzp_def)

    show "finite (output_vars TYPE(kzp))"
      by (metis (hide_lams, mono_tags) atLeastLessThan0 finite_atLeastLessThan finite_insert output_vars_kzp_def)
  qed
end

definition f :: "kzp trm \<Rightarrow> kzp trm" where
  "f x \<equiv> App f_kzp [x]"

definition g :: "kzp trm \<Rightarrow> kzp trm \<Rightarrow> kzp trm" where
  "g x y \<equiv> App g_kzp [x, y]"

definition P :: "kzp trm \<Rightarrow> kzp skat" where
  "P x \<equiv> pred (Pred P_kzp [x])"

definition vx :: "kzp trm " where
  "vx \<equiv> App x_kzp []"

definition bot :: "kzp trm" where
  "bot \<equiv> App bot_kzp []"

declare f_def [skat_simp]
  and g_def [skat_simp]
  and bot_def [skat_simp]
  and P_def [skat_simp]
  and vx_def [skat_simp]

(* Sequences *)

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

(* Shorthand notation *)

definition a :: "nat \<Rightarrow> kzp skat" where
  "a i \<equiv> P (Var i)"

abbreviation a1 where "a1 \<equiv> a 1"
abbreviation a2 where "a2 \<equiv> a 2"
abbreviation a3 where "a3 \<equiv> a 3"
abbreviation a4 where "a4 \<equiv> a 4"

declare a_def [skat_simp]

lemma a_test [intro]: "a n \<in> carrier tests"
  by (simp add: a_def P_def, rule pred_closed)

lemma a_comm: "a n \<cdot> a m = a m \<cdot> a n"
  by skat_comm

lemma a_assign: "n \<noteq> m \<Longrightarrow> a n \<cdot> m := x = m := x \<cdot> a n"
  by skat_comm

definition b :: "nat \<Rightarrow> kzp skat" where
  "b i \<equiv> P (f (Var i))"

declare b_def [skat_simp]

definition c :: "nat \<Rightarrow> kzp skat" where
  "c i \<equiv> P (f (f (Var i)))"

abbreviation c2 where "c2 \<equiv> c 2"

declare c_def [skat_simp]

definition p :: "nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "p i j \<equiv> i := f (Var j)"

declare p_def [skat_simp]

abbreviation p41 where "p41 \<equiv> p 4 1"
abbreviation p11 where "p11 \<equiv> p 1 1"
abbreviation p13 where "p13 \<equiv> p 1 3"
abbreviation p22 where "p22 \<equiv> p 2 2"

definition q :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "q i j k \<equiv> i := g (Var j) (Var k)"

abbreviation q214 where "q214 \<equiv> q 2 1 4"
abbreviation q311 where "q311 \<equiv> q 3 1 1"
abbreviation q211 where "q211 \<equiv> q 2 1 1"
abbreviation q222 where "q222 \<equiv> q 2 2 2"

declare q_def [skat_simp]

definition r :: "nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "r i j \<equiv> i := f (f (Var j))"

abbreviation r13 where "r13 \<equiv> r 1 3"
abbreviation r12 where "r12 \<equiv> r 1 2"
abbreviation r22 where "r22 \<equiv> r 2 2"

declare r_def [skat_simp]

lemma p_to_r: "p n n \<cdot>p n n = r n n"
  by skat_simp (simp add: skat_assign3)

abbreviation x1 where "x1 \<equiv> 1 := vx"

definition s :: "nat \<Rightarrow> kzp skat" where
  "s i \<equiv> i := f vx"

abbreviation s1 where "s1 \<equiv> s 1"

abbreviation s2 where "s2 \<equiv> s 2"

declare s_def [skat_simp]

definition t :: "nat \<Rightarrow> kzp skat" where
  "t i \<equiv> i := g (f vx) (f vx)"

abbreviation t2 where "t2 \<equiv> t 2"

declare t_def [skat_simp]

definition u :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "u i j k \<equiv> i := g (f (f (Var j))) (f (f (Var k)))"

abbreviation "u222" where "u222 \<equiv> u 2 2 2"

declare u_def [skat_simp]

definition z :: "nat \<Rightarrow> kzp skat" where
  "z i \<equiv> 0 := Var i"

declare z_def [skat_simp]

abbreviation z2 where "z2 \<equiv> z 2"

definition y :: "nat \<Rightarrow> kzp skat" where
  "y i \<equiv> i := null"

declare y_def [skat_simp]

definition d :: "kzp skat" where
  "d \<equiv> P (f vx)"

declare d_def [skat_simp]

no_notation
  one_class.one ("1") and
  dioid.one ("1\<index>") and
  dioid.zero ("0\<index>") and
  zero_class.zero ("0") and
  plus_class.plus (infixl "+" 65)

abbreviation halt where "halt \<equiv> SKAT.halt [1,2,3,4]"

definition scheme1 :: "kzp skat list" where "scheme1 \<equiv>
  [ 1 := vx
  , 4 := f (Var 1)
  , 1 := f (Var 1)
  , 2 := g (Var 1) (Var 4)
  , 3 := g (Var 1) (Var 1)
  , loop
    [ !(P (Var 1))
    , 1 := f (Var 1)
    , 2 := g (Var 1) (Var 4)
    , 3 := g (Var 1) (Var 1)
    ]
  , P (Var 1)
  , 1 := f (Var 3)
  , loop
    [ !(P (Var 4)) + seq
      [ P (Var 4)
      , (!(P (Var 2)) \<cdot> 2 := f (Var 2))\<^sup>\<star>
      , P (Var 2)
      , ! (P (Var 3))
      , 4 := f (Var 1)
      , 1 := f (Var 1)
      ]
    , 2 := g (Var 1) (Var 4)
    , 3 := g (Var 1) (Var 1)
    , loop
      [ !(P (Var 1))
      , 1 := f (Var 1)
      , 2 := g (Var 1) (Var 4)
      , 3 := g (Var 1) (Var 1)
      ]
    , P (Var 1)
    , 1 := f (Var 3)
    ]
  , P (Var 4)
  , (!(P (Var 2)) \<cdot> 2 := f (Var 2))\<^sup>\<star>
  , P (Var 2)
  , P (Var 3)
  , 0 := Var 2
  , halt
  ]"

definition scheme2 where "scheme2 \<equiv>
  [ 2 := f vx
  , P (Var 2)
  , 2 := g (Var 2) (Var 2)
  , skat_star (seq
    [ !(P (Var 2))
    , 2 := f (f (Var 2))
    , P (Var 2)
    , 2 := g (Var 2) (Var 2)
    ])
  , P (Var 2)
  , 0 := Var 2
  , halt
  ]"

declare Nat.One_nat_def [simp del]
declare foldr.simps[skat_simp]
declare o_def[skat_simp]
declare id_def[skat_simp]
declare halt.simps(1) [simp del]

lemma seq_merge: "seq (Vx#Vy#Vxs) = seq (Vx\<cdot>Vy#Vxs)"
  by (metis seq_cons skd.mult_assoc)

lemma kozen1: "p41\<cdot>p11 = p41\<cdot>p11\<cdot>(a1 iff a4)"
  by (subst bicon_comm) (auto simp add: pred_closed p_def a_def P_def f_def intro: eq_pred)

lemma kozen1_seq: "seq [p41,p11] = seq [p41,p11,(a1 iff a4)]"
  by (metis kozen1 seq_merge)

lemma kozen2: "p41\<cdot>p11\<cdot>q214 = p41\<cdot>p11\<cdot>q211"
proof -
  have "p41\<cdot>p11\<cdot>q214 = 4 := f (Var 1); 1 := f (Var 1); 2 := g (Var 1) (Var 4)"
    by (simp add: p_def q_def)
  also have "... = 1 := f (Var 1); 4 := Var 1; 2 := g (Var 1) (Var 4)"
    by (subst skat_assign1_var[symmetric]) (auto simp add: f_def)
  also have "... = 1 := f (Var 1); 4 := Var 1; 2 := g (Var 1) (Var 1)"
    by (simp add: g_def f_def skd.mult_assoc, subst skat_assign2_var, auto)
  also have "... = 4 := f (Var 1); 1 := f (Var 1); 2 := g (Var 1) (Var 1)"
    by (subst skat_assign1_var) (auto simp add: f_def)
  also have "... = p41\<cdot>p11\<cdot>q211"
    by (simp add: p_def q_def)
  finally show ?thesis .
qed

lemma kozen3: "p41\<cdot>p11\<cdot>q211\<cdot>q311\<cdot>a1\<cdot>a4 = p41\<cdot>p11\<cdot>q211\<cdot>q311\<cdot>a1"
proof -
  have "p41\<cdot>p11\<cdot>q211\<cdot>q311\<cdot>a1 = p41\<cdot>p11\<cdot>(a1 iff a4)\<cdot>q211\<cdot>q311\<cdot>a1"
    by (metis kozen1)
  also have "... = p41\<cdot>p11\<cdot>q211\<cdot>q311\<cdot>(a1 iff a4)\<cdot>a1"
    apply (subgoal_tac "(a1 iff a4)\<cdot>q211 = q211\<cdot>(a1 iff a4)" "(a1 iff a4)\<cdot>q311 = q311\<cdot>(a1 iff a4)")
    apply (smt skd.mult_assoc)
    by (skat_comm, auto)+
  also have "... = p41\<cdot>p11\<cdot>q211\<cdot>q311\<cdot>a1\<cdot>a4"
    apply (subgoal_tac "a1 iff a4 ; a1 = a1\<cdot>a4")
    apply (smt skd.mult_assoc)
    apply (subst bicon_comm)
    apply auto
    apply (subst bicon_conj1)
    apply auto
    by (rule a_comm)
  finally show ?thesis ..
qed

lemma kozen3_seq: "seq [p41,p11,q211,q311,a1,a4] = seq [p41,p11,q211,q311,a1]"
  by (simp add: seq_def skd.mult_onel kozen3)

lemma kozen4_seq: "seq [q211,q311,r13] = seq [q211,q311,r12]"
proof -
  have "q211\<cdot>q311\<cdot>r13 = 2 := g (Var 1) (Var 1); 3 := g (Var 1) (Var 1); 1 := f (f (Var 3))"
    by (simp add: q_def r_def)
  also have "... = 2 := g (Var 1) (Var 1); 3 := Var 2; 1 := f (f (Var 3))"
    by (subst skat_assign2_var[symmetric]) (auto simp add: g_def)
  also have "... = 2 := g (Var 1) (Var 1); 3 := Var 2; 1 := f (f (Var 2))"
    by (simp add: f_def g_def skd.mult_assoc, subst skat_assign2_var, auto)
  also have "... = 2 := g (Var 1) (Var 1); 3 := g (Var 1) (Var 1); 1 := f (f (Var 2))"
    by (subst skat_assign2_var) (auto simp add: g_def)
  finally show ?thesis
    by (simp add: q_def r_def seq_def skd.mult_onel)
qed

lemma kozen5': "q211\<cdot>q311 = q211\<cdot>q311\<cdot>(a2 iff a3)"
  by (auto simp add: pred_closed q_def a_def P_def g_def intro: eq_pred)

lemma kozen5_seq1: "seq [q211,q311,a3] = seq [q211,q311,a2]"
proof -
  have "q211\<cdot>q311\<cdot>a3 = q211\<cdot>q311\<cdot>(a2 iff a3)\<cdot>a3"
    by (metis kozen5')
  also have "... = q211\<cdot>q311\<cdot>a2\<cdot>a3"
    by (subgoal_tac "(a2 iff a3)\<cdot>a3 = a2\<cdot>a3") (auto simp add: skd.mult_assoc intro: bicon_conj1)
  also have "... = q211\<cdot>q311\<cdot>a3\<cdot>a2"
    by (metis skd.mult_assoc a_comm)
  also have "... = q211\<cdot>q311\<cdot>(a3 iff a2)\<cdot>a2"
    by (subgoal_tac "(a3 iff a2)\<cdot>a2 = a3\<cdot>a2") (auto simp add: skd.mult_assoc intro: bicon_conj1)
  also have "... = q211\<cdot>q311\<cdot>(a2 iff a3)\<cdot>a2"
    by (subst bicon_comm, auto)
  also have "... = q211\<cdot>q311\<cdot>a2"
    by (smt kozen5')
  finally show ?thesis
    by (simp add: seq_def skd.mult_onel)
qed

lemma kozen5_seq2: "seq [q211,q311,!a3] = seq [q211,q311,!a2]"
proof -
  have "q211\<cdot>q311\<cdot>!a3 = q211\<cdot>q311\<cdot>(!a2 iff !a3)\<cdot>!a3"
    by (subst kozen5', subst bicon_not, auto)
  also have "... = q211\<cdot>q311\<cdot>!a2\<cdot>!a3"
    by (subgoal_tac "(!a2 iff !a3)\<cdot>!a3 = !a2\<cdot>!a3") (auto simp add: skd.mult_assoc intro: bicon_conj1 not_closed)
  also have "... = q211\<cdot>q311\<cdot>!a3\<cdot>!a2"
    by (subgoal_tac "!a3\<cdot>!a2 = !a2\<cdot>!a3", smt skd.mult_assoc, skat_comm)
  also have "... = q211\<cdot>q311\<cdot>(!a3 iff !a2)\<cdot>!a2"
    by (subgoal_tac "(!a3 iff !a2)\<cdot>!a2 = !a3\<cdot>!a2") (auto simp add: skd.mult_assoc intro: bicon_conj1 not_closed)
  also have "... = q211\<cdot>q311\<cdot>(!a2 iff !a3)\<cdot>!a2"
    by (subst bicon_comm) (auto intro: not_closed)
  also have "... = q211\<cdot>q311\<cdot>!a2"
    by (subst bicon_not[symmetric], auto, smt kozen5')
  finally show ?thesis
    by (simp add: seq_def skd.mult_onel)
qed

lemma plus_indiv: "\<lbrakk>vx1 = x2; y1 = y2\<rbrakk> \<Longrightarrow> (vx1::kzp skat) + y1 = x2 + y2"
  by auto

lemma lemma41: "r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>!a2 = \<zero>"
proof -
  have "r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>!a2 \<sqsubseteq> r12\<cdot>a1\<cdot>p22\<cdot>(a2 + !a2)\<cdot>p22\<cdot>!a2"
    by (smt skat_order_def skd.add_assoc skd.add_comm skd.add_idem skd.distl skd.distr)
  also have "... = r12\<cdot>a1\<cdot>p22\<cdot>p22\<cdot>!a2"
    by (subst complement_one) (auto simp add: mult_oner)
  also have "... = r12\<cdot>a1\<cdot>r22\<cdot>!a2"
    by (metis p_to_r skd.mult_assoc)
  also have "... = r12\<cdot>r22\<cdot>a1\<cdot>!a2"
    by (subgoal_tac "a1\<cdot>r22 = r22\<cdot>a1", metis skd.mult_assoc, skat_comm)
  also have "... = r12\<cdot>r22\<cdot>(a1 iff a2)\<cdot>a1\<cdot>!a2"
    by (subgoal_tac "r12\<cdot>r22 = r12\<cdot>r22\<cdot>(a1 iff a2)") (auto simp add: r_def a_def P_def f_def intro: eq_pred)
  also have "... = \<zero>"
    apply (subgoal_tac "a1 iff a2; a1; !a2 = \<zero>")
    apply (metis skd.mult_assoc skd.mult_zeror)
    apply (subst bicon_comm)
    apply auto
    apply (subst bicon_conj1)
    apply auto
    apply (subgoal_tac "a2\<cdot>!a2 = \<zero>")
    apply (metis a_comm skd.mult_assoc skd.mult_zeror)
    apply (subst complement_zero)
    by auto
  finally show ?thesis
    by (metis skd.nat_antisym skd.zero_min)
qed

theorem kozen_scheme_equivalence: "seq scheme1 = seq scheme2"
proof -
  have "seq scheme1 = seq
    [x1,p41,p11,q214,q311,loop [!a1,p11,q214,q311],a1,p13
    ,loop [!a4 + seq [a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11],q214,q311,loop [!a1,p11,q214,q311],a1,p13]
    ,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,a3,z2,halt]"
    by (simp add: scheme1_def p_def[symmetric] q_def[symmetric] a_def[symmetric] z_def[symmetric])

  also have "... = seq
    [x1,p41,p11,q214,q311,loop [!a1,p11,q214,q311]
    ,loop [a1,p13,!a4 + seq [a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11],q214,q311,loop [!a1,p11,q214,q311]]
    ,a1,p13,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,a3,z2,halt]"
    by (cong, cut 1 2, cut 6 1, simp, cut 2 4, cut 3 2, simp only: ska.star_slide[simplified])

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [!a1,p11,q214,q311] + seq [a1,p13,!a4 + seq [a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11],q214,q311])\<^sup>\<star>
    ,a1,p13,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,a3,z2,halt]"
    by (cong, cut 1 1, cut 2 5, simp add: ska.star_denest[symmetric,simplified])

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [!a1,p11,q214,q311] + seq [a1,p13,!a4,q214,q311] + seq [a1,p13,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q214,q311])\<^sup>\<star>
    ,a1,p13,a4,(!a2\<cdot>p22)\<^sup>\<star>,a2,a3,z2,halt]"
    apply (cong, simp, subst skd.add_assoc[simplified])
    apply (rule_tac f = "\<lambda>x. (?v + x)\<^sup>\<star>" in arg_cong)
    apply (simp add: seq_foldr skd.mult_oner)
    by (smt skd.distl skd.distr skd.mult_assoc)

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [!a1,!a4,p11,q214,q311] + seq [!a1,a4,p11,q214,q311] + seq [a1,!a4,p13,q214,q311]
    + seq [a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q214,q311])\<^sup>\<star>
    ,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    apply congl
    apply (rule seq_head_eq)
    apply (rule arg_cong) back
    apply (rule plus_indiv)+
    apply (auto simp add: seq_head_elim_var[OF a_test])
    apply cong
    apply skat_comm
    apply cong
    apply skat_comm
    apply (commr1 1 2)
    apply (comml1 1 3)
    apply congl
    apply (comml1 2 3)
    apply congl
    apply (auto simp add: seq_foldr mult_oner p_def output_vars_kzp_def)
    by (metis (lifting) halt_first skat_null_zero skd.mult_assoc)

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [!a1,a4,p11,q214,q311]
    + seq [a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q214,q311])\<^sup>\<star>
    ,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    apply congl
    apply (cut 1 1, simp, cut 6 1, simp)
    apply (subst skd.add_assoc[simplified])
    apply (subst skd.add_comm[simplified]) back
    apply (subst skd.add_assoc[symmetric,simplified])
    apply (subst skd.add_assoc[simplified]) back
    apply (rule ska.kozen_skat_lemma[simplified])
    apply (subgoal_tac "seq [!a1,!a4,p11,q214,q311] = seq [!a1,p11,q214,q311,!a4]")
    apply (erule ssubst)
    apply (subgoal_tac "seq [a1,!a4,p13,q214,q311] = seq [a1,p13,q214,q311,!a4]")
    apply (erule ssubst)
    apply (commr1 3 1)
    apply (commr1 4 1)
    apply (simp add: skd.distr[simplified] skd.distl[simplified])
    apply (zero, auto simp add: skd.add_zerol)+
    prefer 3
    apply (subgoal_tac "seq [(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt] = seq [a4,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]")
    apply (erule ssubst)
    apply (subgoal_tac "seq [!a1,!a4,p11,q214,q311] = seq [!a1,p11,q214,q311,!a4]")
    apply (erule ssubst)
    apply (subgoal_tac "seq [a1,!a4,p13,q214,q311] = seq [a1,p13,q214,q311,!a4]")
    apply (erule ssubst)
    apply (simp add: skd.distr[simplified])
    apply (comml1 2 5)
    apply (comml1 4 5)
    apply (zero, auto simp add: skd.add_zerol)+
    apply seq_comm
    apply seq_comm
    apply (comml1 2 2, cong)
    by seq_comm

  also have "... = seq
    [x1,p41,p11,q214,q311
    ,(seq [a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q214,q311])\<^sup>\<star>
    ,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    apply congr
    apply (subst seq_foldr)
    apply (subst seq_foldr) back back
    apply (simp add: skd.mult_assoc[symmetric,simplified] skd.mult_oner[simplified])
    apply (rule ska.kozen_skat_lemma_dual[simplified])
    apply (cut 1 6, cut 2 2, seq_select 2, subst kozen1_seq, seq_deselect)
    apply (subst seq_mult[symmetric], subst seq_mult[symmetric], simp)
    apply (subst zippify, simp)
    apply (subst zip_right)
    apply (subst zip_right)
    apply (comml1 1 4)
    apply (comml1 1 4)
    apply (subst seq_merge)
    apply (rule zip_zero)
    apply (metis (lifting) a_test bicon_zero)
    apply (subst skd.mult_assoc[simplified])
    apply (subst kozen1)
    apply (simp add: skd.mult_assoc[symmetric,simplified])
    apply (subst seq_singleton[symmetric])
    apply seq_rev
    apply (subst qes_snoc[symmetric])+
    apply (subst qes_snoc)
    apply (subst zip_right, subst zip_right)
    apply (comml1 1 4)
    apply (comml1 1 4)
    apply (subst seq_merge, rule zip_zero)
    by (metis (lifting) a_test bicon_zero)

  also have "... = seq
    [x1,p41,p11,q211,q311
    ,(seq [a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3,p41,p11,q211,q311])\<^sup>\<star>
    ,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    by (simp add: seq_def skd.mult_onel[simplified], smt kozen2 skd.mult_assoc)

  also have "... = seq
    [x1,(seq [p41,p11,q211,q311,a1,a4,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3])\<^sup>\<star>
    ,p41,p11,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,a4,z2,halt]"
    by (cong, cut 1 4, cut 3 6, cut 6 4, cut 5 1, simp add: ska.star_slide)

  also have "... = seq
    [x1,(seq [p41,p11,q211,q311,a1,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3])\<^sup>\<star>
    ,p41,p11,q211,q311,a1,(!a2\<cdot>p22)\<^sup>\<star>,a2,a3,z2,halt]"
    apply (cut 2 6, zip 1 7, subst zip_comm, skat_comm)
    apply (zip 3 3)
    apply (subst zip_comm, skat_comm, subst zip_right)+
    apply (unzip+, cut 1 2, cut 4 6)
    apply (simp add: kozen3_seq)
    by (subst seq_mult[symmetric], simp)+

  also have "... = seq
    [x1,(seq [p41,p11,q211,q311,a1,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3])\<^sup>\<star>
    ,p41,p11,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]"
    by (congr, zip 3 7, subst zip_comm, skat_comm, unzip, seq_deselect)

  also have "... = seq
    [x1,(seq [p11,q211,q311,a1,p13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3])\<^sup>\<star>
    ,p11,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]"
    by (eliminate_variable 4)

  also have "... = seq
    [x1,p11,(seq [q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,!a3,p13,p11])\<^sup>\<star>
    ,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]"
    by (commr1 2 5, commr1 2 4 1, simp add: seq_def mult_onel, smt ska.star_slide skd.mult_assoc)

  also have "... = seq
    [s1,(seq [q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,!a3,r13])\<^sup>\<star>
    ,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]"
  proof -
    have "x1\<cdot>p11 = s1"
      by (simp add: vx_def f_def p_def s_def, subst skat_assign3, auto)
    moreover have "p13\<cdot>p11 = r13"
      by (simp add: f_def p_def r_def, subst skat_assign3, auto)
    ultimately show ?thesis
      by (simp add: seq_def skd.mult_onel) (smt skd.mult_assoc)
  qed

  also have "... = seq
    [s1,(seq [a1,q211,q311,r13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3])\<^sup>\<star>
    ,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]"
    by (comml1 2 4, comml1 2 7)

  also have "... = seq
    [s1,(seq [a1,q211,q311,!a2,r12,(!a2\<cdot>p22)\<^sup>\<star>,a2])\<^sup>\<star>
    ,q211,q311,a2,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,z2,halt]"
    apply (cut 2 1)
    apply (cut 3 3)
    apply (simp only: kozen4_seq seq_mult[symmetric] append.simps)
    apply (comml1 2 7, comml1 1 8, cut 1 2, cut 3 3, cut 2 1, cut 3 3)
    apply (simp add: kozen5_seq1 kozen5_seq2)
    by (simp add: seq_def mult_onel skd.mult_assoc[simplified])

  also have "... = seq
    [s1,(seq [a1,q211,!a2,r12,(!a2\<cdot>p22)\<^sup>\<star>,a2])\<^sup>\<star>
    ,q211,a2,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,z2,halt]"
    by (eliminate_variable 3)

  also have "... = seq
    [s1,(seq [a1,q211,r12,!a2,p22,(!a2\<cdot>p22)\<^sup>\<star>,a2])\<^sup>\<star>
    ,q211,a1,a2,z2,halt]"
  proof -
    have "!a2\<cdot>(!a2\<cdot>p22)\<^sup>\<star>\<cdot>a2 = !a2\<cdot>a2 + !a2\<cdot>!a2\<cdot>p22\<cdot>(!a2\<cdot>p22)\<^sup>\<star>\<cdot>a2"
      by (smt mult_oner ska.star_unfoldl_eq skd.distl skd.distr skd.mult_assoc)
    also have "... = !a2\<cdot>p22\<cdot>(!a2\<cdot>p22)\<^sup>\<star>\<cdot>a2"
      by (smt skd.add_zerol a_test not_closed skt.test_meet_idem complement_zero not_closed skt.test_mult_comm)
    finally have a: "!a2\<cdot>(!a2\<cdot>p22)\<^sup>\<star>\<cdot>a2 = !a2\<cdot>p22\<cdot>(!a2\<cdot>p22)\<^sup>\<star>\<cdot>a2" .

    have "a2\<cdot>(!a2\<cdot>p22)\<^sup>\<star>\<cdot>a2 = a2\<cdot>a2 + a2\<cdot>!a2\<cdot>p22\<cdot>(!a2\<cdot>p22)\<^sup>\<star>\<cdot>a2"
      by (smt mult_oner ska.star_unfoldl_eq skd.distl skd.distr skd.mult_assoc)
    also have "... = a2"
      by (metis skd.add_zeror skd.mult_zerol a_test complement_zero skt.test_meet_idem)
    finally have b: "a2\<cdot>(!a2\<cdot>p22)\<^sup>\<star>\<cdot>a2 = a2" .

    from a b show ?thesis
      by (comml1 2 4 1, simp add: seq_def mult_onel, smt a_comm skd.mult_assoc)
  qed

  also have "... = seq
    [s1,a1,q211,(seq [r12,!a2,p22,(!a2\<cdot>p22)\<^sup>\<star>,a2,a1,q211])\<^sup>\<star>,a2,z2,halt]"
    apply (comml1 1 4 1)
    apply (cut 1 1)
    apply (cut 2 3)
    apply (cut 3 2)
    apply (cut 2 1)
    apply (simp add: seq_singleton)
    apply (subst ska.star_slide[simplified])
    by (simp add: seq_def mult_onel skd.mult_assoc)

  also have "... = seq
    [s1,a1,q211,(seq [!a2,r12,p22,(!a2\<cdot>p22)\<^sup>\<star>,a2,a1,q211])\<^sup>\<star>,a2,z2,halt]"
    by (comml1 2 2)

  also have "... = seq
    [s1,a1,q211,(seq [!a2,r12,a1,p22,a2,q211] + seq [!a2,r12,a1,p22,!a2,p22,a2,q211])\<^sup>\<star>
    ,a2,z2, halt]"
  proof -
    have "r12\<cdot>a1\<cdot>p22\<cdot>(!a2\<cdot>p22)\<^sup>\<star> = r12\<cdot>a1\<cdot>p22\<cdot>(\<one> + !a2\<cdot>p22 + !a2\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>(!a2\<cdot>p22)\<^sup>\<star>)"
      apply (subst ska.star_unfoldl_eq[simplified])
      apply (subst ska.star_unfoldl_eq[simplified])
      by (smt skd.add_assoc skd.distl skd.mult_assoc skd.mult_oner)
    also have "... = r12\<cdot>a1\<cdot>p22 + r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22 + r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>(!a2\<cdot>p22)\<^sup>\<star>"
      by (smt skd.mult_oner skd.distl skd.mult_assoc)
    also have "... = r12\<cdot>a1\<cdot>p22 + r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22"
      by (smt lemma41 skd.add_zeror skd.mult_zerol)
    finally have "r12\<cdot>a1\<cdot>p22\<cdot>(!a2\<cdot>p22)\<^sup>\<star> = r12\<cdot>a1\<cdot>p22 + r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22" .

    thus ?thesis
      apply (cong, simp)
      apply (comml1 1 6)
      apply (simp add: seq_def skd.mult_onel)
      by (smt skd.distl skd.distr skd.mult_assoc)
  qed

  also have "... = seq
    [s1,a1,q211,(seq [!a2,r12,a1,p22,a2,q211] + seq [!a2,r12,a1,p22,!a2,p22,q211])\<^sup>\<star>
    ,a2,z2, halt]"
  proof -
    have "r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22 = r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>\<one>"
      by (metis skd.mult_oner)
    also have "... = r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>(a2 + !a2)"
      by (subst complement_one) auto
    also have "... = r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>a2 + r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>!a2"
      by (metis skd.distl)
    also have "... = r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>a2"
      by (smt lemma41 skd.add_zeror)
    finally have "r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22 = r12\<cdot>a1\<cdot>p22\<cdot>!a2\<cdot>p22\<cdot>a2" .

    thus ?thesis
      apply cong
      apply (rule arg_cong) back back back back
      apply (simp add: seq_def skd.mult_onel)
      by (smt skd.mult_assoc)
  qed

  also have "... = seq
    [s1,a1,q211,(seq [!a2,r12,a1,p22,a2,q211] + seq [!a2,r12,a1,p22,!a2,q211])\<^sup>\<star>
    ,a2,z2, halt]"
  proof -
    have "p22\<cdot>q211 = q211"
      by (simp add: p_def q_def g_def f_def skat_assign3)
    thus ?thesis
      by (simp add: seq_def skd.mult_onel) (smt skd.mult_assoc)
  qed

  also have "... = seq [s1,a1,q211,(seq [!a2,r12,a1,p22,(a2 + !a2),q211])\<^sup>\<star>,a2,z2, halt]"
    apply cong
    apply (rule arg_cong) back back back
    by (smt seq_cons skd.distl skd.distr)

  also have "... = seq [s1,a1,q211,(seq [!a2,r12,a1,p22,q211])\<^sup>\<star>,a2,z2, halt]"
    by (subst complement_one, auto simp add: seq_def skd.mult_onel skd.mult_oner)

  also have "... = seq [s1,a1,q211,(seq [!a2,r12,a1,q211])\<^sup>\<star>,a2,z2, halt]"
  proof -
    have "p22\<cdot>q211 = q211"
      by (simp add: p_def q_def g_def f_def skat_assign3)
    thus ?thesis
      by (simp add: seq_def skd.mult_onel) (smt skd.mult_assoc)
  qed

  also have "... = seq [d,s1,t2,(seq [!a2,c2,r12,u222])\<^sup>\<star>,a2,z2,halt]"
  proof -
    {
      have "s1\<cdot>a1\<cdot>q211 = d\<cdot>s1\<cdot>q211"
        by (simp add: s_def a_def f_def P_def d_def skat_assign4_var[symmetric])
      also have "... = d\<cdot>s1\<cdot>t2"
        apply (simp add: t_def s_def d_def f_def P_def q_def g_def vx_def skd.mult_assoc)
        apply (rule arg_cong) back
        apply (rule skat_assign2_var)
        by auto
      finally have "s1\<cdot>a1\<cdot>q211 = d\<cdot>s1\<cdot>t2" .
    }
    moreover
    {
      have "r12\<cdot>a1\<cdot>q211 = c2\<cdot>r12\<cdot>q211"
        by (simp add: r_def a_def f_def P_def c_def skat_assign4_var[symmetric])
      also have "... = c2\<cdot>r12\<cdot>u222"
        apply (simp add: c_def r_def u_def f_def P_def q_def g_def vx_def skd.mult_assoc)
        apply (rule arg_cong) back
        apply (rule skat_assign2_var)
        by auto
      finally have "r12\<cdot>a1\<cdot>q211 = c2\<cdot>r12\<cdot>u222" .
    }
    ultimately show ?thesis
      by (simp add: seq_def skd.mult_onel) (smt skd.mult_assoc)
  qed

  also have "... = seq [d,t2,(seq [!a2,c2,u222])\<^sup>\<star>,a2,z2,halt]"
    by (eliminate_variable 1)

  also have "... = seq [s2,a2,q222,(seq [!a2,r22,a2,q222])\<^sup>\<star>,a2,z2,halt]"
  proof -
    {
      have "d\<cdot>t2 = d\<cdot>s2\<cdot>q222"
        by (simp add: g_def d_def t_def s_def q_def skd.mult_assoc, subst skat_assign3, auto)
      also have "... = s2\<cdot>a2\<cdot>q222"
        by (simp add: d_def s_def a_def f_def P_def skat_assign4_var[symmetric])
      finally have "d\<cdot>t2 = s2\<cdot>a2\<cdot>q222" .
    }
    moreover
    {
      have "c2\<cdot>u222 = c2\<cdot>r22\<cdot>q222"
        by (simp add: g_def c_def u_def r_def q_def skd.mult_assoc, subst skat_assign3, auto)
      also have "... = r22\<cdot>a2\<cdot>q222"
        by (simp add: f_def P_def a_def r_def c_def skat_assign4_var[symmetric])
      finally have "c2\<cdot>u222 = r22\<cdot>a2\<cdot>q222" .
    }
    ultimately show "?thesis"
      by (simp add: seq_def skd.mult_onel) (smt skd.mult_assoc)
  qed

  also have "... = seq scheme2"
    by (simp add: scheme2_def) skat_simp

  finally show ?thesis .
qed

end
