theory KozenExample
  imports Ranked_Alphabet List
begin

(* Kozen and Angus's example *)

lemma zip_elim_var: "x\<cdot>y = y \<Longrightarrow> qes (x#xs) \<cdot> seq (y#ys) = qes xs \<cdot> seq (y#ys)"
  by (metis (lifting) seq_cons skd.mult_assoc zip_left)

lemma test_under_one: "p \<in> carrier tests \<Longrightarrow> p \<sqsubseteq> \<one>"
  by (metis skt.test_under_one)

lemma test_double_compl: "p \<in> carrier tests \<Longrightarrow> p = !(!p)"
  by (metis kat_comp_simp not_closed skt.test_double_compl)

lemma de_morgan1: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> !p \<cdot> !q = !(p + q)"
  by (smt kat_comp_simp skt.de_morgan1 test_plus_closed)

lemma test_meet_def: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p \<cdot> q = !(!p + !q)"
  by (metis (lifting) de_morgan1 not_closed test_double_compl)

lemma de_morgan2: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> !p + !q = !(p \<cdot> q)"
  by (smt not_closed test_double_compl test_meet_def test_plus_closed)

lemma test_compl_anti: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p \<sqsubseteq> q \<longleftrightarrow> !q \<sqsubseteq> !p"
  by (metis kat_comp_simp skt.test_compl_anti)

lemma test_join_def: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p + q = !(!p \<cdot> !q)"
  by (metis (lifting) de_morgan2 not_closed test_double_compl)

lemma ba_3: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p = (p \<cdot> q) + (p \<cdot> !q)"
  by (metis Ranked_Alphabet.mult_oner complement_one skd.distl)

lemma ba_5: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> (p + q) \<cdot> !p = q \<cdot> !p"
  by (metis (lifting) complement_zero skd.add_zerol skd.distr)

lemma compl_1: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> !p = !(p + q) + !(p + !q)"
  by (metis (lifting) ba_3 de_morgan1 not_closed)

lemma ba_1: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests; r \<in> carrier tests\<rbrakk> \<Longrightarrow> p + q + !q = r + !r"
  by (metis Ranked_Alphabet.mult_oner complement_one ska.star_unfoldl_eq skd.add_assoc skd.add_comm skt.test_star)

lemma ba_2: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p + p = p + !(q + !q)"
  by (metis complement_one kat_comp_simp skd.add_idem skd.add_zeror skt.test_not_one test_one_closed)

lemma ba_4: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p = (p + !q) \<cdot> (p + q)"
  by (metis complement_zero not_closed skd.add_zeror skt.test_dist2 skt.test_mult_comm)

lemma shunting:
  assumes pc: "p \<in> carrier tests" and qc: "q \<in> carrier tests" and rc: "r \<in> carrier tests"
  shows "p \<cdot> q \<sqsubseteq> r \<longleftrightarrow> q \<sqsubseteq> !p + r"
  by (metis kat_comp_simp pc qc rc skt.shunting)

fun break' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)" where
  "break' ac 0 xs = (rev ac, xs)"
| "break' ac (Suc n) [] = (rev ac, [])"
| "break' ac (Suc n) (x#xs) = break' (x#ac) n xs"

abbreviation break :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)" where
  "break \<equiv> break' []"

inductive comms :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat list \<Rightarrow> bool" where
  comms_nil: "comms x []"
| comms_cons: "\<lbrakk>x\<cdot>y = y\<cdot>x; comms x ys\<rbrakk> \<Longrightarrow> comms x (y#ys)"

lemma comm_step:
  assumes "\<exists>i. nth ys i = x \<and> comms x (fst (break i ys)) \<and> seq xs = seq (fst (break i ys) @ tl (snd (break i ys)))"
  shows "seq (x#xs) = seq ys"
  sorry

(* Defining the alphabet *)

definition biconditional ::
  "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat" (infixl "iff" 65)
where
  "x iff y = !x\<cdot>!y + x\<cdot>y"

declare biconditional_def [skat_simp]

lemma bicon_conj1: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> (x iff y)\<cdot>y = x\<cdot>y"
  apply (simp add: biconditional_def skd.distr[simplified])
  by (smt complement_zero de_morgan1 not_closed skd.add_comm skd.add_idem skd.add_zeror skd.mult_assoc test_double_compl)

lemma bicon_conj2: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> y\<cdot>(x iff y) = x\<cdot>y"
  by (smt biconditional_def complement_zero de_morgan1 de_morgan2 not_closed skd.add_zerol skd.distl skd.mult_assoc skt.test_meet_idem skt.test_mult_comm)

lemma bicon_zero: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> (x iff y)\<cdot>(!x\<cdot>y) = \<zero>"
  by (smt bicon_conj1 complement_zero not_closed skd.mult_assoc skd.mult_zeror skt.test_mult_comm)

lemma bicon_comm: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> x iff y = y iff x"
  by (metis (lifting) biconditional_def not_closed skt.test_mult_comm)

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
(*

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

lemma seq_zero_var: "\<lbrakk>xs \<noteq> []; last xs \<cdot> y = \<zero>\<rbrakk> \<Longrightarrow> seq xs \<cdot> seq (y#ys) = \<zero>"
  apply (subst seq_cut_rev[of _ 1])
  apply (subgoal_tac "take_rev 1 xs = [last xs]")
  apply (rotate_tac 2)
  apply (erule ssubst)
  apply (simp add: seq_singleton)
  apply (subst seq_cons[symmetric])
  apply (subst skd.mult_assoc[simplified])
  apply (subst skd.mult_assoc[symmetric,simplified]) back
  apply (erule ssubst)
  apply (simp add: skd.mult_zeror[simplified] skd.mult_zerol[simplified])
  apply (induct xs)
  apply auto
  by (smt length_greater_0_conv)

lemma seq_zero: "\<lbrakk>y \<in> carrier tests; xs \<noteq> []; last xs = !y\<rbrakk> \<Longrightarrow> seq xs \<cdot> seq(y#ys) = \<zero>"
  apply (rule seq_zero_var)
  apply auto
  by (metis complement_zero not_closed skt.test_mult_comm)

lemma seq_shunt: "(\<forall>y\<in>set xs. x\<cdot>y = y\<cdot>x) \<Longrightarrow> seq (x#xs) = seq (xs@[x])"
  by (induct xs, simp, auto, metis seq_cons seq_head_comm)

lemma seq_12: "seq (x#y#xs) = seq (x\<cdot>y#xs)"
  by (metis seq_cons seq_def skd.mult_assoc)
*)

(* Shorthand notation *)

definition a :: "nat \<Rightarrow> kzp skat" where
  "a i \<equiv> P (var i)"

abbreviation a1 where "a1 \<equiv> a 1"
abbreviation a2 where "a2 \<equiv> a 2"
abbreviation a3 where "a3 \<equiv> a 3"
abbreviation a4 where "a4 \<equiv> a 4"

declare a_def [skat_simp]

lemma a_test [intro]: "a n \<in> carrier tests"
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

abbreviation r13 where "r13 \<equiv> r 1 3"
abbreviation r12 where "r12 \<equiv> r 1 2"

declare r_def [skat_simp]

abbreviation x1 where "x1 \<equiv> 1 := vx"

definition s :: "nat \<Rightarrow> kzp skat" where
  "s i \<equiv> i := f vx"

abbreviation s1 where "s1 \<equiv> s 1"

declare s_def [skat_simp]

definition t :: "nat \<Rightarrow> kzp skat" where
  "t i \<equiv> i := g (f vx) (f vx)"

definition u :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "u i j k \<equiv> i := g (f (f (var j))) (f (f (var k)))"

definition z :: "nat \<Rightarrow> kzp skat" where
  "z i \<equiv> 0 := var i"

declare z_def [skat_simp]

abbreviation z2 where "z2 \<equiv> z 2"

definition y :: "nat \<Rightarrow> kzp skat" where
  "y i \<equiv> i := null"

declare y_def [skat_simp]

ML {*
fun NTIMES 0 _ = all_tac
  | NTIMES n tac = tac THEN (NTIMES (n - 1) tac)

fun commr_tac s c m = Subgoal.FOCUS (fn {context, ...} =>
  let
    val move_right_tac = EVERY
      [ EqSubst.eqsubst_tac context [0] @{thms zip_comm} 1
      , skat_comm_tac context 1
      , EqSubst.eqsubst_tac context [0] @{thms zip_left} 1
      ]
  in
    DETERM (zip_tac s c context 1)
    THEN (if m = 0
          then (CHANGED (REPEAT move_right_tac))
          else (NTIMES m move_right_tac))
    THEN unzip_tac context 1
    THEN seq_deselect_tac 1
  end)
*}

method_setup commr1 = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat -- Scan.lift (Scan.optional Parse.nat 0) >>
  (fn ((s, c), m) => fn ctxt => SIMPLE_METHOD' (commr_tac s c m ctxt))
*}

method_setup comml1 = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat -- Scan.lift (Scan.optional Parse.nat 0) >>
  (fn ((s, c), m) => fn ctxt =>
    let
      val move_left_tac = EVERY
        [ EqSubst.eqsubst_tac ctxt [0] @{thms zip_comm} 1
        , skat_comm_tac ctxt 1
        , EqSubst.eqsubst_tac ctxt [0] @{thms zip_right} 1
        ]
    in
      DETERM (zip_tac s (c - 1) ctxt 1)
      THEN (if m = 0
            then (CHANGED (REPEAT move_left_tac))
            else (NTIMES m move_left_tac))
      THEN unzip_tac ctxt 1
      THEN seq_deselect_tac 1
      |> SIMPLE_METHOD
    end)
*}

ML_val {* Subgoal.FOCUS *}

ML {*
fun seq_comm_step_tac ctxt n =
  rtac @{thm conjI} n THEN simp_tac (simpset_of ctxt) n
  THEN rtac @{thm conjI} n THEN simp_tac (simpset_of ctxt) n
  THEN REPEAT (rtac @{thm comms_cons} n THEN skat_comm_tac ctxt n)
  THEN rtac @{thm comms_nil} n
  THEN simp_tac (simpset_of ctxt) n

fun destroy [] = (fn x => x)
  | destroy (f::fs) = f o Thm.dest_comb #> destroy fs

fun safe_dest_comb ctrm = SOME (Thm.dest_comb ctrm)
  handle CTERM _ => NONE

fun safe_destroy [] ctrm = SOME ctrm
  | safe_destroy (f::fs) ctrm =
    case (safe_dest_comb ctrm) of
      NONE => NONE
    | SOME x => safe_destroy fs (f x);

fun ml_list ctrm =
  case (safe_destroy [fst, snd] ctrm) of
    NONE => []
  | SOME x => x :: ml_list (destroy [snd] ctrm);

fun find_index _ [] = 0
  | find_index x (y::ys) =
    (if x aconvc y then 0 else 1 + find_index x ys)

fun seq_comm_get_index concl =
  let
    val ys = concl |> destroy [snd, snd, snd] |> ml_list
    val xs = concl |> destroy [snd, fst, snd, snd] |> ml_list
  in
    find_index (hd xs) ys
  end

val seq_comm1_tac = Subgoal.FOCUS (fn {concl, context, ...} =>
  let
    val index = nat_cterm (seq_comm_get_index concl)
    val exI_index = Drule.instantiate' [SOME @{ctyp "nat"}] [NONE, SOME index] @{thm exI}
  in
    EVERY [rtac @{thm comm_step} 1, rtac exI_index 1, seq_comm_step_tac context 1]
    ORELSE commr_tac 1 1 0 context 1
  end
  handle CTERM _ => no_tac)

val seq_comm_tac = Subgoal.FOCUS (fn {context, ...} =>
  REPEAT1 (seq_comm1_tac context 1))
*}

method_setup seq_comm = {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (seq_comm_tac ctxt)) *}

lemma null_simp [simp]: "X ::= exp \<cdot> X ::= null = X ::= null"
  by (metis FV_null Int_empty_right no_FV skat_set_assign3)

lemma elim_inst: "halt = seq [x := null, halt]"
  sorry

lemma elim_subst: "X = Y \<Longrightarrow> X ::= x \<cdot> Y ::= null = Y ::= null"
  sorry

lemma elim_null: "qes (x := null#xs) \<cdot> seq [halt] = qes xs \<cdot> seq [halt]"
  sorry

ML {*
fun zip_var_elim_tac ctxt n = DETERM (
  EqSubst.eqsubst_tac ctxt [0] @{thms zip_elim_var} n
  THEN SOLVED' (fn n =>
    asm_full_simp_tac (simpset_of ctxt addsimps SkatSimpRules.get ctxt) n
    THEN TRY (touch_simp_tac ctxt n)
    THEN TRY (rtac @{thm elim_subst} n)
    THEN TRY (simp_tac (simpset_of ctxt) n)) n)

fun zip_comml_tac ctxt n = DETERM (
  EqSubst.eqsubst_tac ctxt [0] @{thms zip_comm} n
  THEN skat_comm_tac' skat_ni_commuter ctxt n
  THEN EqSubst.eqsubst_tac ctxt [0] @{thms zip_right} n)

fun zip_commr_tac ctxt n = DETERM (
  EqSubst.eqsubst_tac ctxt [0] @{thms zip_comm} n
  THEN skat_comm_tac ctxt n
  THEN EqSubst.eqsubst_tac ctxt [0] @{thms zip_left} n)

fun var_elim_tac v ctxt n =
  let
    val v_ctrm = nat_cterm v
  in
    seq_select_tac 1 ctxt n
    THEN simp_tac (HOL_basic_ss addsimps @{thms seq_to_qes rev.simps append.simps}) n
    THEN EqSubst.eqsubst_tac ctxt [0] @{thms qes_snoc} n
    THEN EqSubst.eqsubst_tac ctxt [0] [Drule.instantiate' [] [SOME v_ctrm] @{thm elim_inst}] n
    THEN REPEAT (zip_var_elim_tac ctxt n ORELSE zip_comml_tac ctxt n ORELSE manual_elim_tac)
    THEN EqSubst.eqsubst_tac ctxt [0] @{thms zip_left} n
    THEN REPEAT (zip_commr_tac ctxt n)
    THEN EqSubst.eqsubst_tac ctxt [0] @{thms elim_null} n
    THEN unzip_tac ctxt n
    THEN seq_deselect_tac n
  end
*}

lemma "seq [q311,q 2 3 1,q311,halt] = seq [halt]"
  apply (tactic {* var_elim_tac 3 @{context} 1 *})
  ML_prf {* Goal.init @{cprop "False"} *}
  defer

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

lemma seq_merge: "seq (Vx#Vy#Vxs) = seq (Vx\<cdot>Vy#Vxs)"
  sorry

lemma vhalt [intro]: "vy \<notin> output_vars TYPE(kzp) \<Longrightarrow> vy := vs \<cdot> halt = halt"
  sorry

lemma vhalt2 [intro]: "vy \<notin> output_vars TYPE(kzp) \<Longrightarrow> halt = vy := vs \<cdot> halt"
  by (metis vhalt)

declare output_vars_kzp_def [simp]

lemma kozen1: "p41\<cdot>p11 = p41\<cdot>p11\<cdot>(a1 iff a4)"
  sorry

lemma kozen1_seq: "seq [p41,p11] = seq [p41,p11,(a1 iff a4)]"
  sorry

lemma kozen2: "p41\<cdot>p11\<cdot>q214 = p41\<cdot>p11\<cdot>q211"
  sorry

lemma kozen3: "p41\<cdot>p11\<cdot>q211\<cdot>q311\<cdot>a1\<cdot>a4 = p41\<cdot>p11\<cdot>q211\<cdot>q311\<cdot>a1"
  sorry

lemma kozen3_seq: "seq [p41,p11,q211,q311,a1,a4] = seq [p41,p11,q211,q311,a1]"
  by (simp add: seq_def skd.mult_onel kozen3)

lemma kozen4_seq: "seq [q211,q311,r13] = seq [q211,q311,r12]"
  sorry

lemma kozen5_seq1: "seq [q211,q311,a3] = seq [q211,q311,a2]"
  sorry

lemma kozen5_seq2: "seq [q211,q311,!a3] = seq [q211,q311,!a2]"
  sorry

lemma [simp]: "X ::= v \<cdot> X ::= null = X ::= null"
  by (metis FV_null inf_bot_right no_FV skat_set_assign3)

lemma plus_indiv: "\<lbrakk>vx1 = x2; y1 = y2\<rbrakk> \<Longrightarrow> (vx1::kzp skat) + y1 = x2 + y2"
  by auto

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
    apply seq_comm+
    by (auto simp add: seq_foldr mult_oner p_def)

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
    apply (commr 3 1)
    apply (commr 4 1)
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
    apply (zero, auto simp add: skd.add_zerol)+
    by seq_comm+

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
    apply (commr 1 9) apply (subst seq_merge) back
    apply (subst zippify, simp, rule zip_zero)
    apply (metis (lifting) a_test bicon_zero)
    apply (subst skd.mult_assoc[simplified])
    apply (subst kozen1)
    apply (simp add: skd.mult_assoc[symmetric,simplified])
    apply (subst seq_singleton[symmetric])
    apply seq_rev
    apply (subst qes_snoc[symmetric])+
    apply (subst qes_snoc)
    apply qes_rev
    apply (commr 1 4)
    apply (subst seq_merge) back
    apply (subst zippify, simp, rule zip_zero)
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
    apply (cut 1 11)
    apply (subgoal_tac "halt = seq[y 4, halt]", erule ssubst) back back
    apply (simp add: seq_singleton seq_mult[symmetric])
    apply (zip 1 11)
    apply (subst zip_comm, skat_comm, subst zip_right)+
    apply (unzip, seq_deselect)
    apply (subst seq_cons) back
    apply (zip 1 2)
    apply (subst seq_cons, subst qes_snoc)
    apply (subst skd.mult_assoc[symmetric,simplified])
    apply (subst skd.mult_assoc[simplified])
    apply (seq_deselect)
    apply (subst ska.star_elim[symmetric,simplified])
    apply (metis (lifting) skat_null_zero y_def)
    apply skat_comm+
    apply (metis (lifting) p_def skat_null_zero y_def)
    apply (simp add: qes_singleton skd.mult_assoc[simplified])
    apply (subst seq_cons[symmetric])+
    apply (zip 1 3)
    apply (subst zip_comm, skat_comm)
    apply (subst qes_snoc, subst seq_cons)
    apply (subst skd.mult_assoc[simplified,symmetric])
    apply (subst skd.mult_assoc[simplified])
    apply (subgoal_tac "p41 \<cdot> y 4 = y 4", erule ssubst)
    apply (subst qes_snoc[symmetric])
    apply (subst zip_comm, skat_comm, subst zip_left)+
    apply (unzip, seq_deselect)
    apply (seq_rev)
    apply (subst qes_snoc, subst qes_snoc)
    apply (subst skd.mult_assoc[simplified])
    apply (subgoal_tac "y 4 \<cdot> halt = halt", erule ssubst)
    apply (subst qes_snoc[symmetric])
    apply (simp add: qes_def)
    apply (simp add: y_def)
    apply (insert output_vars_kzp_def[of "TYPE(kzp)"])
    apply (smt singletonE vhalt)
    apply (metis (lifting) p_def skat_null_zero y_def)
    by (smt seq_cons seq_singleton singleton_iff vhalt2 y_def)

  also have "... = seq
    [x1,p11,(seq [q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,!a3,p13,p11])\<^sup>\<star>
    ,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]"
    by (commr 2 5, commr1 2 4 1, simp add: seq_def mult_onel, smt ska.star_slide skd.mult_assoc)

  also have "... = seq
    [s1,(seq [q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,!a3,r13])\<^sup>\<star>
    ,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]"
    sorry

  also have "... = seq
    [s1,(seq [a1,q211,q311,r13,(!a2\<cdot>p22)\<^sup>\<star>,a2,!a3])\<^sup>\<star>
    ,q211,q311,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,a3,z2,halt]"
    by (comml 2 4, comml 2 7)

  also have "... = seq
    [s1,(seq [a1,q211,q311,!a2,r12,(!a2\<cdot>p22)\<^sup>\<star>,a2])\<^sup>\<star>
    ,q211,q311,a2,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,z2,halt]"
    apply (cut 2 1)
    apply (cut 3 3)
    apply (simp only: kozen4_seq seq_mult[symmetric] append.simps)
    apply (comml 2 7, comml 1 8, cut 1 2, cut 3 3, cut 2 1, cut 3 3)
    apply (simp add: kozen5_seq1 kozen5_seq2)
    by (simp add: seq_def mult_onel skd.mult_assoc[simplified])

  also have "... = seq
    [s1,(seq [a1,q211,!a2,(!a2\<cdot>p22)\<^sup>\<star>,a2])\<^sup>\<star>
    ,q211,a2,(!a2\<cdot>p22)\<^sup>\<star>,a1,a2,z2,halt]"
    apply (tactic {* var_elim_tac 3 @{context} 1 *})
    apply (subgoal_tac "halt = y 3 \<cdot> halt", erule ssubst) back back
    apply (seq_rev, subst qes_snoc)
    apply (subst skd.mult_assoc[symmetric,simplified])
    apply (subst qes_snoc[symmetric])+
    apply (qes_rev)
    apply (comml1 1 10 5)
    apply (zip 1 4)
    

  also have "... = seq scheme2"
    sorry

  finally show ?thesis .
qed

end
