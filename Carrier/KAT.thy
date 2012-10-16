theory KAT
  imports Kleene_Algebra Galois_Connection
begin

record 'a test = "'a kleene_algebra" +
  test :: "'a ord"

abbreviation tests :: "('a, 'b) test_scheme \<Rightarrow> 'a set" where
    "tests A \<equiv> carrier (test A)"

locale kat' =
  fixes A :: "('a, 'b) test_scheme" (structure)
  assumes kat_ka: "kleene_algebra A"
  and test_subset: "tests A \<subseteq> carrier A"
  and test_le [simp]: "le (test A) = dioid.nat_order A"
  and test_ba: "boolean_algebra (test A)"

sublocale kat' \<subseteq> kleene_algebra using kat_ka .

locale kat = kat' +
  assumes test_one: "bounded_lattice.top (test A) = 1"
  and test_zero: "bounded_lattice.bot (test A) = 0"
  and test_join: "order.join (test A) x y = x + y"
  and test_meet: "order.meet (test A) x y = x \<cdot> y"

begin

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

  declare test_join [simp]
  declare test_meet [simp]
  declare test_le_var[simp]
  declare test_one[simp]
  declare test_zero[simp]

  lemmas test_dist1 = distributive_lattice.dist1[OF test_distributive, simplified]
    and test_dist2 = distributive_lattice.dist2[OF test_distributive, simplified]
    and test_join_closed = join_semilattice.join_closed[OF test_js, simplified]
    and test_meet_closed = meet_semilattice.meet_closed[OF test_ms, simplified]
    and test_absorb1 = lattice.absorb1[OF test_lattice, simplified]
    and test_absorb2 = lattice.absorb2[OF test_lattice, simplified]
    and test_join_assoc = join_semilattice.join_assoc[OF test_js, simplified]
    and test_meet_assoc = meet_semilattice.meet_assoc[OF test_ms, simplified]
    and test_join_idem = join_semilattice.join_idem[OF test_js, simplified]
    and test_meet_idem = meet_semilattice.meet_idem[OF test_ms, simplified]
    and test_leq_def = join_semilattice.leq_def[OF test_js, simplified]
    and test_leq_meet_def = meet_semilattice.leq_meet_def[OF test_ms, simplified]
    and test_refl = order.order_refl[OF test_ord, simplified]
    and test_trans = order.order_trans[OF test_ord, simplified]
    and test_antisym = order.order_antisym[OF test_ord, simplified]
    and test_one_closed = bounded_lattice.top_closed[OF test_bl, simplified]
    and test_zero_closed = bounded_lattice.bot_closed[OF test_bl, simplified]
    and test_compl = complemented_lattice.compl[OF test_complemented, simplified]
    and test_compl_uniq = boolean_algebra.compl_uniq[OF test_ba, simplified]

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

  definition if_then_else :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("IF _ THEN _ ELSE _ ENDIF" [64,64,64] 63) where
    "IF b THEN p ELSE q ENDIF \<equiv> b\<cdot>p + (!b)\<cdot>q"

  definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("WHILE _ DO _ WEND" [64,64] 63) where
    "WHILE b DO p WEND = (b\<cdot>p)\<^sup>\<star>\<cdot>!b"

  abbreviation SKIP :: "'a" where "SKIP \<equiv> 1"

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
    assume "b\<cdot>c \<in> tests A" and "c \<in> tests A" and "p \<in> carrier A" and "b \<cdot> c \<cdot> p = b \<cdot> c \<cdot> p \<cdot> c"
    hence "c\<cdot>b\<cdot>p \<sqsubseteq> c\<cdot>b\<cdot>p\<cdot>c"
      by (metis (lifting) bt mult_closed nat_refl test_mult_comm test_subset_var)
    hence "c\<cdot>(b\<cdot>p)\<^sup>\<star> \<sqsubseteq> c\<cdot>(b\<cdot>p)\<^sup>\<star>\<cdot>c"
      by (smt add_idem bt ct star_closed meet_semilattice.meet_comm mult_assoc mult_closed nat_order_def pc test_meet test_meet_idem test_ms test_subset_var)
    thus "c\<cdot>((b\<cdot>p)\<^sup>\<star>\<cdot>!b) = c\<cdot>((b\<cdot>p)\<^sup>\<star>\<cdot>!b)\<cdot>(!b\<cdot>c)"
      by (smt bt complement_closed ct mult_double_iso mult_assoc mult_closed mult_oner nat_antisym nat_refl one_closed pc star_closed test_meet_idem test_mult_comm test_subset_var test_under_one)
  qed

  lemma hoare_skip: "b \<in> tests A \<Longrightarrow> b \<lbrace> SKIP \<rbrace> b"
    by (metis (lifting) complement2 hoare_triple_def mult_oner one_closed test_subset_var)

end

end
