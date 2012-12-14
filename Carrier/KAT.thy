theory KAT
  imports Kleene_Algebra Galois_Connection Boolean_Algebra_Extras
begin

record 'a test_algebra = "'a kleene_algebra" +
  test :: "'a ord"

abbreviation tests :: "('a, 'b) test_algebra_scheme \<Rightarrow> 'a set" where
    "tests A \<equiv> carrier (test A)"

locale kat' =
  fixes A :: "('a, 'b) test_algebra_scheme" (structure)
  assumes kat_ka: "kleene_algebra A"
  and test_subset: "tests A \<subseteq> carrier A"
  and test_le [simp]: "le (test A) = dioid.nat_order A"
  and test_ba: "boolean_algebra (test A)"

sublocale kat' \<subseteq> kleene_algebra using kat_ka .

locale kat = kat' +
  assumes test_one: "bounded_lattice.top (test A) = 1"
  and test_zero: "bounded_lattice.bot (test A) = 0"
  and test_join: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> order.join (test A) x y = x + y"
  and test_meet: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> order.meet (test A) x y = x \<cdot> y"

sublocale kat \<subseteq> test: boolean_algebra "test A"
  where "bounded_lattice.top (test A) = 1"
  and "bounded_lattice.bot (test A) = 0"
  and "x \<sqsubseteq>\<^bsub>test A\<^esub> y \<longleftrightarrow> x \<sqsubseteq> y"
  by (simp_all add: test_ba test_one test_zero test_join test_meet test_join)

context kat
begin

  lemma rem_tj: "\<lbrakk>P (x \<sqinter>\<^bsub>test A\<^esub> y); x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> P (x \<cdot> y)"
    by (metis test_meet)

  lemma test_le_var: "x \<sqsubseteq>\<^bsub>test A\<^esub> y \<longleftrightarrow> x \<sqsubseteq> y"
    by (metis (full_types) test_le)

  lemma test_subset_var: "p \<in> tests A \<Longrightarrow> p \<in> carrier A"
    by (metis insert_absorb insert_subset test_subset)

  lemma test_ord: "order (test A)"
    apply (insert test_ba)
    by (simp add: boolean_algebra_def distributive_lattice_def lattice_def join_semilattice_def)

  lemma test_bl: "bounded_lattice (test A)"
    by (insert test_ba, simp add: boolean_algebra_def complemented_lattice_def)

  lemma test_js: "join_semilattice (test A)"
    by (insert test_bl, simp add: bounded_lattice_def lattice_def)

  lemma test_ms: "meet_semilattice (test A)"
    by (insert test_bl, simp add: bounded_lattice_def lattice_def)

  lemma test_lattice: "lattice (test A)"
    by (insert test_bl, simp add: bounded_lattice_def)

  lemma test_distributive: "distributive_lattice (test A)"
    by (insert test_ba, simp add: boolean_algebra_def)

  lemma test_complemented: "complemented_lattice (test A)"
    by (insert test_ba, simp add: boolean_algebra_def)

  lemma test_plus_closed [simp]: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x + y \<in> tests A"
    by (metis test.join_closed test_join)

  lemma test_mult_closed [simp]: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> tests A"
    by (metis meet_closed test_meet)

  declare test_join [simp]
  declare test_meet [simp]
  declare test_le_var[simp]
  declare test_one[simp]
  declare test_zero[simp]

  lemma test_dist1:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A\<rbrakk> \<Longrightarrow> x \<cdot> (y + z) = (x \<cdot> y) + (x \<cdot> z)"
    by (insert distributive_lattice.dist1[OF test_distributive], simp)

  lemma test_dist2:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A\<rbrakk> \<Longrightarrow> x + y \<cdot> z = (x + y) \<cdot> (x + z)"
    by (insert distributive_lattice.dist2[OF test_distributive], simp)

  lemma test_join_closed: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x + y \<in> tests A"
    by (insert join_semilattice.join_closed[OF test_js], simp)

  lemma test_meet_closed: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> tests A"
    by (insert meet_semilattice.meet_closed[OF test_ms], simp)

  lemma test_absorb1: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x + x \<cdot> y = x"
    by (insert lattice.absorb1[OF test_lattice], simp)

  lemma test_absorb2: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x \<cdot> (x + y) = x"
    by (insert lattice.absorb2[OF test_lattice], simp)

  lemma test_join_assoc:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A\<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
    by (insert join_semilattice.join_assoc[OF test_js], simp)

  lemma test_meet_assoc:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    by (insert meet_semilattice.meet_assoc[OF test_ms], simp)

  lemma test_join_idem: "x \<in> tests A \<Longrightarrow> x + x = x"
    by (insert join_semilattice.join_idem[OF test_js], simp)

  lemma test_meet_idem: "x \<in> tests A \<Longrightarrow> x \<cdot> x = x"
    by (insert meet_semilattice.meet_idem[OF test_ms], simp)

  lemma test_leq_def:
        "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) = (x + y = y)"
    by (insert join_semilattice.leq_def[OF test_js], simp)

  lemma test_leq_meet_def:
        "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) = (x \<cdot> y = x)"
    by (insert meet_semilattice.leq_meet_def[OF test_ms], simp)

  lemma test_refl: "x \<in> tests A \<Longrightarrow> x \<sqsubseteq> x"
    by (insert order.order_refl[OF test_ord], simp)

  lemma test_trans:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A; x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
    by (insert order.order_trans[OF test_ord,simplified,of x y z], auto)

  lemma test_antisym: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x = y"
    by (insert order.order_antisym[OF test_ord], simp)

  lemma test_compl:
    "x \<in> tests A \<Longrightarrow> \<exists>y. y \<in> tests A \<and> x + y = 1 \<and> x \<cdot> y = 0"
    apply (insert complemented_lattice.compl[OF test_complemented], simp)
    by (metis test_join test_meet)

  lemma test_compl_uniq:
    "x \<in> tests A \<Longrightarrow> \<exists>!y. y \<in> tests A \<and> x + y = 1 \<and> x \<cdot> y = 0"
    apply (insert boolean_algebra.compl_uniq[OF test_ba], simp)
    by (metis test_join test_meet)

  lemmas test_one_closed = bounded_lattice.top_closed[OF test_bl, simplified]
    and test_zero_closed = bounded_lattice.bot_closed[OF test_bl, simplified]

  declare test_join_closed [simp del]
  declare test_meet_closed [simp del]
  declare test_join [simp del]
  declare test_meet [simp del]
  declare test_le_var [simp del]
  declare test_one [simp del]
  declare test_zero [simp del]

  definition complement :: "'a \<Rightarrow> 'a" ("!") where
    "complement x = (THE y. y \<in> tests A \<and> x + y = 1 \<and> x \<cdot> y = 0)"

  lemma complement_closed: assumes xc: "x \<in> tests A" shows "!x \<in> tests A"
    by (simp add: complement_def, rule the1I2, rule test_compl_uniq[OF xc], auto)

  lemma complement1: "p \<in> tests A \<Longrightarrow> p + !p = 1"
    by (simp add: complement_def, rule the1I2, rule test_compl_uniq[OF assms], auto+)

  lemma complement2: "p \<in> tests A \<Longrightarrow> p \<cdot> !p = 0"
    by (simp add: complement_def, rule the1I2, rule test_compl_uniq[OF assms], auto+)

  lemma test_under_one: "p \<in> tests A \<Longrightarrow> p \<sqsubseteq> 1"
    by (metis mult_oner test_leq_meet_def test_one_closed test_subset_var)

  lemma test_star: "p \<in> tests A \<Longrightarrow> p\<^sup>\<star> = 1"
    by (smt set_rev_mp star_subid test_subset test_under_one)

  lemma test_not_one: "!1 = 0"
    by (metis (lifting) complement2 complement_closed mult_onel test_one_closed test_subset_var)

  lemma test_not_zero: "!0 = 1"
    by (metis add_zerol complement1 complement_closed test_subset_var test_zero_closed)

  lemma test_mult_comm: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p\<cdot>q = q\<cdot>p"
    by (metis (lifting) meet_semilattice.meet_comm test_meet test_ms)

  lemma test_double_compl: "p \<in> tests A \<Longrightarrow> p = !(!p)"
    apply (simp add: complement_def)
    apply (rule the1I2)
    apply (simp_all add: complement_def[symmetric])
    apply (rule test_compl_uniq)
    apply (rule complement_closed[OF assms])
    apply auto
    by (smt add_comm complement1 complement2 complement_closed test_compl_uniq test_mult_comm test_subset_var)

  lemma de_morgan1: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> !p \<cdot> !q = !(p + q)"
    apply (subgoal_tac "p + q + !p\<cdot>!q = 1" "(p + q) \<cdot> (!p\<cdot>!q) = 0")
    apply (smt complement1 complement2 complement_closed test_compl_uniq test_join_closed test_meet_closed)
    apply (smt complement2 complement_closed mult_zeror test_dist1 test_join_closed test_meet_assoc test_meet_closed test_mult_comm test_subset_var)
    by (smt add_comm complement1 complement_closed nat_order_def test_absorb2 test_dist2 test_join_assoc test_join_closed test_subset_var test_under_one)

  lemma test_meet_def: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p \<cdot> q = !(!p + !q)"
    by (metis complement_closed de_morgan1 test_double_compl)

  lemma de_morgan2: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> !p + !q = !(p \<cdot> q)"
    by (smt complement_closed test_double_compl test_join_closed test_meet_def)

  lemma test_compl_anti: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p \<sqsubseteq> q \<longleftrightarrow> !q \<sqsubseteq> !p"
    by (metis add_idem de_morgan2 nat_order_def test_leq_meet_def test_meet_def test_mult_comm test_subset_var)

  lemma test_join_def: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p + q = !(!p \<cdot> !q)"
    by (metis de_morgan1 test_double_compl test_join_closed)

  lemma ba_3: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p = (p \<cdot> q) + (p \<cdot> !q)"
    by (metis (lifting) complement1 complement_closed mult_oner test_dist1 test_subset_var)

  lemma ba_5: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> (p + q) \<cdot> !p = q \<cdot> !p"
    by (metis (lifting) complement2 complement_closed dioid.add_zerol distr ka_dioid mult_closed test_subset_var)

  lemma compl_1: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> !p = !(p + q) + !(p + !q)"
    by (metis (lifting) ba_3 complement_closed de_morgan1)

  lemma ba_1: "\<lbrakk>p \<in> tests A; q \<in> tests A; r \<in> tests A\<rbrakk> \<Longrightarrow> p + q + !q = r + !r"
    by (metis (lifting) complement1 complement_closed nat_order_def test_join_assoc test_under_one)

  lemma ba_2: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p + p = p + !(q + !q)"
    by (metis (lifting) add_zeror complement1 test_join_idem test_not_one test_subset_var)

  lemma ba_4: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p = (p + !q) \<cdot> (p + q)"
    by (metis complement2 complement_closed dioid.add_zeror ka_dioid test_dist2 test_mult_comm test_subset_var)

  lemma shunting:
    assumes pc: "p \<in> tests A" and qc: "q \<in> tests A" and rc: "r \<in> tests A"
    shows "p \<cdot> q \<sqsubseteq> r \<longleftrightarrow> q \<sqsubseteq> !p + r"
    apply default
    apply (smt complement1 complement_closed distl mult_assoc mult_oner pc qc rc test_absorb2 test_double_compl test_join_closed test_leq_meet_def test_meet_closed test_mult_comm test_subset_var)
    by (smt ba_5 complement_closed pc qc rc test_double_compl test_join_closed test_leq_meet_def test_meet_assoc test_meet_def test_mult_comm)

  lemma shunting_galois:
    assumes pc: "p \<in> tests A"
    shows "galois_connection (test A) (test A) (\<lambda>x. p \<cdot> x) (\<lambda>x. !p + x)"
  proof (simp add: galois_connection_def test_le_var, intro conjI, safe del: iffI)
    from test_ord show "order (test A)" .

    show "(\<lambda>x. p \<cdot> x) \<in> tests A \<rightarrow> tests A"
      by (smt ftype_pred pc test_meet_closed)

    show "(\<lambda>x. !p + x) \<in> tests A \<rightarrow> tests A"
      by (smt ftype_pred pc test_join_closed complement_closed)

    fix q r assume qc: "q \<in> tests A" and rc: "r \<in> tests A"
    show "p \<cdot> q \<sqsubseteq> r \<longleftrightarrow> q \<sqsubseteq> !p + r"
      by (rule shunting[OF pc qc rc])
  qed

  text {* We can now import a few theorems based on the shunting
  Galois connection *}

  declare test_join [simp]
  declare test_meet [simp]
  declare test_le_var[simp]
  declare test_one[simp]
  declare test_zero[simp]
  declare o_def[simp]

  lemmas test_max = galois_max[OF shunting_galois, simplified]
    and test_min = galois_min[OF shunting_galois, simplified]
    and test_semi_inverse1 = semi_inverse1[OF _ shunting_galois, simplified]
    and test_semi_inverse2 = semi_inverse2[OF _ shunting_galois, simplified]
    and test_fg_iso = fg_iso[OF shunting_galois, simplified]
    and test_gf_iso = gf_iso[OF shunting_galois, simplified]
    and test_lower_iso = galois_connection.lower_iso[OF shunting_galois, simplified]
    and test_upper_iso = galois_connection.upper_iso[OF shunting_galois, simplified]
    and test_idem1 = galois_connection.adjoint_idem1[OF shunting_galois, simplified]
    and test_idem2 = galois_connection.adjoint_idem2[OF shunting_galois, simplified]

  declare test_join [simp del]
  declare test_meet [simp del]
  declare test_le_var[simp del]
  declare test_one[simp del]
  declare test_zero[simp del]
  declare o_def[simp del]

end

primrec (in kat) kat_bexpr_unfold :: "'a bexpr \<Rightarrow> 'a" where
  "kat_bexpr_unfold (BLeaf x) = x"
| "kat_bexpr_unfold (BOr x y) = kat_bexpr_unfold x + kat_bexpr_unfold y"
| "kat_bexpr_unfold (BAnd x y) = kat_bexpr_unfold x \<cdot> kat_bexpr_unfold y"
| "kat_bexpr_unfold BOne = 1"
| "kat_bexpr_unfold BZero = 0"
| "kat_bexpr_unfold (BNot x) = !(kat_bexpr_unfold x)"

lemma (in kat) kat_bexpr_fold_leaf: "x \<in> tests A \<Longrightarrow> x = kat_bexpr_unfold (BLeaf x)"
  by (rule kat_bexpr_unfold.simps(1)[symmetric])

lemma (in kat) kat_bexpr_test: "bexpr_leaves \<alpha> \<subseteq> tests A \<Longrightarrow> kat_bexpr_unfold \<alpha> \<in> tests A"
  apply (induct \<alpha>, simp_all)
  by (metis test_join_closed test_meet_closed test_one_closed test_zero_closed complement_closed)+

ML {*

fun test_fold_tac leaves = Subgoal.FOCUS (fn {context, prems, ...} =>
  let
    val witnesses = Locale.get_witnesses context
    val subst_thm = hd (witnesses RL @{thms kat.kat_bexpr_fold_leaf})
    val subst_thms = prems RL [subst_thm]
    val unfolds = witnesses RL @{thms kat.kat_bexpr_unfold.simps[symmetric]}
    val to_leaves_thm = hd (witnesses RL @{thms kat.kat_bexpr_test})
  in
    Method.insert_tac subst_thms 1
    THEN REPEAT (etac @{thm ssubst} 1)
    THEN asm_full_simp_tac (HOL_basic_ss addsimps unfolds) 1
    THEN (if leaves then rtac to_leaves_thm 1 else all_tac)
  end)

*}

method_setup test_closure = {*
Scan.succeed (fn ctxt =>
  METHOD (fn _ => test_fold_tac true ctxt 1 THEN asm_full_simp_tac @{simpset} 1))
*}

lemma (in kat) test_closure_example: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> 1\<cdot>y\<cdot>!(y + 0 + !x) \<in> tests A"
  by test_closure

datatype 'a kat_expr = KATLeaf 'a
                     | KATPlus "'a kat_expr" "'a kat_expr"
                     | KATTimes "'a kat_expr" "'a kat_expr"
                     | KATStar "'a kat_expr"
                     | KATBool "'a bexpr"

no_notation
  Groups.plus_class.plus (infixl "+" 65) and
  Groups.one_class.one ("1") and
  Groups.zero_class.zero ("0")

primrec (in kat) kat_expr_unfold :: "'a kat_expr \<Rightarrow> 'a" where
  "kat_expr_unfold (KATLeaf x) = x"
| "kat_expr_unfold (KATPlus x y) = kat_expr_unfold x + kat_expr_unfold y"
| "kat_expr_unfold (KATTimes x y) = kat_expr_unfold x \<cdot> kat_expr_unfold y"
| "kat_expr_unfold (KATStar x) = (kat_expr_unfold x)\<^sup>\<star>"
| "kat_expr_unfold (KATBool x) = kat_bexpr_unfold x"

lemma (in kat) kat_expr_fold_leaf: "x \<in> carrier A \<Longrightarrow> x = kat_expr_unfold (KATLeaf x)"
  by (rule kat_expr_unfold.simps(1)[symmetric])

primrec kat_expr_leaves :: "'a kat_expr \<Rightarrow> 'a set" where
  "kat_expr_leaves (KATLeaf x) = {x}"
| "kat_expr_leaves (KATPlus x y) = kat_expr_leaves x \<union> kat_expr_leaves y"
| "kat_expr_leaves (KATTimes x y) = kat_expr_leaves x \<union> kat_expr_leaves y"
| "kat_expr_leaves (KATStar x) = kat_expr_leaves x"
| "kat_expr_leaves (KATBool x) = {}"

primrec kat_expr_bexpr_leaves :: "'a kat_expr \<Rightarrow> 'a set" where
  "kat_expr_bexpr_leaves (KATLeaf x) = {}"
| "kat_expr_bexpr_leaves (KATPlus x y) = kat_expr_bexpr_leaves x \<union> kat_expr_bexpr_leaves y"
| "kat_expr_bexpr_leaves (KATTimes x y) = kat_expr_bexpr_leaves x \<union> kat_expr_bexpr_leaves y"
| "kat_expr_bexpr_leaves (KATStar x) = kat_expr_bexpr_leaves x"
| "kat_expr_bexpr_leaves (KATBool x) = bexpr_leaves x"

lemma (in kat) kat_expr_closed:
  "\<lbrakk>kat_expr_leaves \<alpha> \<subseteq> carrier A; kat_expr_bexpr_leaves \<alpha> \<subseteq> tests A\<rbrakk> \<Longrightarrow> kat_expr_unfold \<alpha> \<in> carrier A"
  apply (induct \<alpha>, simp_all)
  by (metis add_closed mult_closed star_closed kat_bexpr_test test_subset_var)+

lemma (in kat) bexpr_to_kat_expr: "kat_bexpr_unfold \<alpha> = kat_expr_unfold (KATBool \<alpha>)" by simp

ML {*

fun inst_thm thm ctrm = SOME (Drule.instantiate' [] [SOME ctrm] thm)
  handle _ => NONE

fun inst_thms thm ctrms = List.mapPartial (inst_thm thm) ctrms

fun delete_alpha_eq y (x::xs) =
    if y aconvc x
    then delete_alpha_eq y xs
    else x :: (delete_alpha_eq y xs)
  | delete_alpha_eq _ [] = []

fun rem_alpha_eq (x::xs) = x :: rem_alpha_eq (delete_alpha_eq x xs)
  | rem_alpha_eq [] = []

fun kat_fold_tac leaves = Subgoal.FOCUS (fn {context, prems, ...} =>
  let
    val witnesses = Locale.get_witnesses context
    val subst_thm = hd (witnesses RL @{thms kat.kat_expr_fold_leaf})
    val subst_thms = prems RL [subst_thm]
    val to_kat_expr_thm = hd (witnesses RL @{thms kat.bexpr_to_kat_expr})
    val folds = witnesses RL @{thms kat.kat_expr_unfold.simps[symmetric]}
    val to_leaves_thm = hd (witnesses RL @{thms kat.kat_expr_closed})
  in
    DETERM
      (TRY (simp_tac (HOL_basic_ss addsimps [to_kat_expr_thm]) 1)
      THEN Method.insert_tac subst_thms 1
      THEN REPEAT (etac @{thm ssubst} 1)
      THEN asm_full_simp_tac (HOL_basic_ss addsimps folds) 1)
    THEN (if leaves then rtac to_leaves_thm 1 else all_tac)
  end)

fun safe_dest_fun ct = SOME (Thm.dest_fun ct)
  handle CTERM _ => NONE

fun safe_dest_arg ct = SOME (Thm.dest_arg ct)
  handle CTERM _ => NONE

fun safe_dest_funarg ct = SOME (Thm.dest_fun ct, Thm.dest_arg ct)
  handle CTERM _ => NONE

fun safe_dest_funargs ct acc =
  case safe_dest_funarg ct of
    SOME (ct_f, ct_x) => safe_dest_funargs ct_f (ct_x :: acc)
  | NONE => (ct, acc)

datatype apptree = App of cterm * apptree list

fun mk_apptree ct =
  case safe_dest_funargs ct [] of
    (f, xs) => App (f, map mk_apptree xs)

fun get_kat_expr_unfolds ct =
  case safe_dest_funargs ct [] of
    (f, xs) =>
      if f aconvc @{cterm "kat.kat_expr_unfold"}
      then [ct]
      else List.concat (map get_kat_expr_unfolds xs)

val get_kat_exprs_ct = map Thm.dest_arg o get_kat_expr_unfolds

datatype kat_expr = KLeaf of cterm
                  | KPlus of kat_expr * kat_expr
                  | KTimes of kat_expr * kat_expr
                  | KStar of kat_expr
                  | KBool of cterm;

fun mk_kat_expr ct =
  case safe_dest_funargs ct [] of
    (f, [x]) =>
      if f aconvc @{cterm KATLeaf}
      then KLeaf x
      else
        if f aconvc @{cterm KATBool}
        then KBool x
        else KStar (mk_kat_expr x)
  | (f, [x, y]) =>
      if f aconvc @{cterm KATPlus}
      then KPlus (mk_kat_expr x, mk_kat_expr y)
      else KTimes (mk_kat_expr x, mk_kat_expr y)

val get_kat_exprs = map mk_kat_expr o get_kat_exprs_ct

fun kat_expr_explode kat_expr =
  case kat_expr of
    (KPlus (k1, k2)) => kat_expr :: (kat_expr_explode k1 @ kat_expr_explode k2)
  | (KTimes (k1, k2)) => kat_expr :: (kat_expr_explode k1 @ kat_expr_explode k2)
  | (KStar k) => kat_expr :: kat_expr_explode k
  | _ => [kat_expr]

fun kat_expr_ct (KLeaf ct) = Thm.apply @{cterm KATLeaf} ct
  | kat_expr_ct (KPlus (k1, k2)) =
      Thm.apply (Thm.apply @{cterm KATPlus} (kat_expr_ct k1)) (kat_expr_ct k2)
  | kat_expr_ct (KTimes (k1, k2)) =
      Thm.apply (Thm.apply @{cterm KATTimes} (kat_expr_ct k1)) (kat_expr_ct k2)
  | kat_expr_ct (KStar k) = Thm.apply @{cterm KATStar} (kat_expr_ct k)
  | kat_expr_ct (KBool ct) = Thm.apply @{cterm KATBool} ct

fun get_explosions context ct =
  get_kat_exprs ct
  |> map kat_expr_explode
  |> List.concat
  |> map kat_expr_ct
  |> rem_alpha_eq
  |> map (Thm.apply @{cterm "\<lambda>x. kat.kat_expr_unfold A x \<in> carrier A"})

fun my_subgoal_tac ct i =
  case inst_thm @{thm mp[rule_format]} ct of
    SOME thm => rtac thm i
  | NONE => no_tac

val explode_tac = Subgoal.FOCUS (fn {context, concl, ...} =>
  EVERY (get_explosions context concl |> map (fn cc => my_subgoal_tac cc 1)))

fun kat_closure_tac ctxt i =
  let
    val witnesses = Locale.get_witnesses ctxt
    val unfolds1 = witnesses RL @{thms kat.kat_expr_unfold.simps}
    val unfolds2 = witnesses RL @{thms kat.kat_bexpr_unfold.simps}
  in
    test_fold_tac false ctxt i
    THEN DETERM (kat_fold_tac true ctxt i)
    THEN asm_full_simp_tac @{simpset} i
    THEN asm_full_simp_tac (@{simpset} addsimps unfolds1 @ unfolds2) i
  end

*}

method_setup kat_closure = {*
Scan.succeed (fn ctxt => SIMPLE_METHOD (kat_closure_tac ctxt 1))
*}

method_setup kat_explode = {*
Scan.succeed (fn ctxt =>
  let
    val witnesses = Locale.get_witnesses ctxt
    val unfolds1 = witnesses RL @{thms kat.kat_expr_unfold.simps}
    val unfolds2 = witnesses RL @{thms kat.kat_bexpr_unfold.simps}
  in
    test_fold_tac false ctxt 1
    THEN kat_fold_tac false ctxt 1
    THEN explode_tac ctxt 1
    THEN defer_tac 1
    THEN ALLGOALS (asm_full_simp_tac (@{simpset} addsimps unfolds1 @ unfolds2))
    THEN REPEAT1 (kat_closure_tac ctxt 1)
    |> SIMPLE_METHOD
  end)
*}

lemma (in kat) test1: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> 1 + x\<cdot>x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  by (kat_explode, metis mult_assoc star_trans_eq star_unfoldl)

lemma (in kat) test2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (x + (x + y + x)) + x = (x + x) + (y + (x + x))"
  by (kat_explode, metis add_assoc)

context kat
begin

  definition if_then_else :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("IF _ THEN _ ELSE _ ENDIF" [64,64,64] 63) where
    "IF b THEN p ELSE q ENDIF \<equiv> b\<cdot>p + (!b)\<cdot>q"

  definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("WHILE _ DO _ WEND" [64,64] 63) where
    "WHILE b DO p WEND = (b\<cdot>p)\<^sup>\<star>\<cdot>!b"

(*
  definition hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lbrace> _ \<rbrace> _" [54,54,54] 53) where
    "b \<lbrace> p \<rbrace> c \<equiv> b \<in> tests A \<and> c \<in> tests A \<and> p \<in> carrier A \<and> b\<cdot>p\<cdot>(!c) = 0"

  lemma hoare_triple_var: "b \<lbrace> p \<rbrace> c \<longleftrightarrow> b \<in> tests A \<and> c \<in> tests A \<and> p \<in> carrier A \<and> b\<cdot>p = b\<cdot>p\<cdot>c"
    apply (auto simp add: hoare_triple_def)
    apply (smt add_zerol complement2 complement_closed de_morgan2 distl mult_closed mult_oner test_double_compl test_not_zero test_subset_var)
    by (metis (lifting) complement2 complement_closed mult_assoc mult_closed mult_zeror test_subset_var)

  lemma mult4_assoc: "\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A; d \<in> carrier A\<rbrakk> \<Longrightarrow> a\<cdot>(b\<cdot>c\<cdot>d) = (a\<cdot>b\<cdot>c)\<cdot>d"
    by (metis (lifting) mult_assoc mult_closed)

  lemma hoare_composition: "\<lbrakk>b \<lbrace> p \<rbrace> c; c \<lbrace> q \<rbrace> d\<rbrakk> \<Longrightarrow> b \<lbrace> p \<cdot> q \<rbrace> d"
    apply (simp add: hoare_triple_var, safe, metis mult_closed)
    by (metis (hide_lams, no_types) mult_assoc mult_closed test_subset_var)

  lemma hoare_weakening: "\<lbrakk>b' \<in> tests A; c' \<in> tests A; b' \<sqsubseteq> b; b \<lbrace> p \<rbrace> c; c \<sqsubseteq> c'\<rbrakk> \<Longrightarrow> b' \<lbrace> p \<rbrace> c'"
    apply (simp add: hoare_triple_var, safe)
    by (smt mult4_assoc mult_assoc test_leq_meet_def test_subset_var)

  lemma hoare_if:
    assumes bt: "b \<in> tests A" and ct: "c \<in> tests A"
    and then_branch: "b\<cdot>c \<lbrace> p \<rbrace> d"
    and else_branch: "!b\<cdot>c \<lbrace> q \<rbrace> d"
    shows "c \<lbrace> IF b THEN p ELSE q ENDIF \<rbrace> d"
    apply (insert then_branch else_branch)
    apply (simp add: hoare_triple_var if_then_else_def ct bt, safe)
    apply (metis add_closed bt complement_closed dioid.mult_closed ka_dioid test_subset_var)
    by (smt bt complement_closed ct distl distr mult_assoc mult_closed test_mult_comm test_subset_var)

  lemma hoare_while:
    assumes bt: "b \<in> tests A" and ct: "c \<in> tests A" and pc: "p \<in> carrier A"
    shows "b\<cdot>c \<lbrace>p\<rbrace> c \<Longrightarrow> c \<lbrace> WHILE b DO p WEND \<rbrace> !b \<cdot> c"
    apply (simp add: hoare_triple_var while_def, safe)
    apply (metis bt complement_closed test_meet_closed)
    apply (metis bt complement_closed mult_closed star_closed test_subset_var)
  proof -
    assume "b\<cdot>c \<in> tests A" and "c \<in> tests A" and "p \<in> carrier A" and asm: "b \<cdot> c \<cdot> p = b \<cdot> c \<cdot> p \<cdot> c"
    hence "c\<cdot>b\<cdot>p \<sqsubseteq> c\<cdot>b\<cdot>p\<cdot>c"
      by (metis (lifting) bt mult_closed nat_refl test_mult_comm test_subset_var)
    hence "c\<cdot>(b\<cdot>p)\<^sup>\<star> \<sqsubseteq> (c\<cdot>b\<cdot>p)\<^sup>\<star>\<cdot>c"
      by (metis (lifting) bt ct mult_assoc mult_closed pc star_sim2 test_subset_var)
    hence "c\<cdot>(b\<cdot>p)\<^sup>\<star> \<sqsubseteq> c\<cdot>(b\<cdot>p)\<^sup>\<star>\<cdot>c"
      by (smt asm bt ct mult_assoc mult_closed pc star_closed star_sim test_meet_idem test_mult_comm test_subset_var)
    thus "c\<cdot>((b\<cdot>p)\<^sup>\<star>\<cdot>!b) = c\<cdot>((b\<cdot>p)\<^sup>\<star>\<cdot>!b)\<cdot>(!b\<cdot>c)"
      by (smt bt complement_closed ct mult_double_iso mult_assoc mult_closed mult_oner nat_antisym nat_refl one_closed pc star_closed test_meet_idem test_mult_comm test_subset_var test_under_one)
  qed

  lemma hoare_skip: "b \<in> tests A \<Longrightarrow> b \<lbrace> SKIP \<rbrace> b"
    by (metis (lifting) complement2 hoare_triple_def mult_oner one_closed test_subset_var)

*)
end

notation
  Groups.plus_class.plus (infixl "+" 65) and
  Groups.one_class.one ("1") and
  Groups.zero_class.zero ("0")

end

