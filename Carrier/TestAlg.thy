theory TestAlg
  imports KAT Quantale
begin

locale kat_module' =
  fixes K :: "'a test_algebra"
  and A :: "('b, 'c) ord_scheme"
  and mk :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes kat_subalg: "kat K"
  and cbl_subalg: "complete_boolean_lattice A"
  and mk_type: "mk : carrier K \<rightarrow> carrier A \<rightarrow> carrier A"

sublocale kat_module' \<subseteq> kat K using kat_subalg .
sublocale kat_module' \<subseteq> A: complete_boolean_lattice A using cbl_subalg .

no_notation
  Groups.plus_class.plus (infixl "+" 65) and
  Groups.one_class.one ("1") and
  Groups.zero_class.zero ("0") and
  Dioid.plus (infixl "+\<index>" 70) and
  Dioid.mult (infixl "\<cdot>\<index>" 80) and
  Dioid.one ("1\<index>") and
  Dioid.zero ("0") and
  Kleene_Algebra.star ("_\<^sup>\<star>\<index>" [101] 100) and
  KAT.kat.complement ("!")

context kat_module'
begin

  abbreviation plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 70) where
    "p + q \<equiv> dioid.plus K p q"

  abbreviation mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 80) where
     "p\<cdot>q \<equiv> dioid.mult K p q"

  abbreviation one :: "'a" ("1") where "1 \<equiv> Dioid.one K"

  abbreviation zero :: "'a" ("0") where "0 \<equiv> Dioid.zero K"

  abbreviation module :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<Colon>" 75) where
    "m \<Colon> p \<equiv> mk p m"

  abbreviation star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100) where
    "x\<^sup>\<star> \<equiv> Kleene_Algebra.star K x"

  notation
    nat_order (infixl "\<preceq>" 50)

  notation
    complement ("!")

end

locale kat_module = kat_module' +
  assumes mod_plus: "\<lbrakk>p \<in> carrier K; q \<in> carrier K; m \<in> carrier A\<rbrakk> \<Longrightarrow> m \<Colon> (p + q) = m \<Colon> p \<squnion> m \<Colon> q"
  and mod_mult: "\<lbrakk>p \<in> carrier K; q \<in> carrier K; m \<in> carrier A\<rbrakk> \<Longrightarrow> m \<Colon> (p\<cdot>q) = m \<Colon> p \<Colon> q"
  and mod_join: "\<lbrakk>p \<in> carrier K; P \<in> carrier A; Q \<in> carrier A\<rbrakk> \<Longrightarrow> P \<squnion> Q \<Colon> p = P \<Colon> p \<squnion> Q \<Colon> p"
  and mod_one: "m \<in> carrier A \<Longrightarrow> m \<Colon> 1 = m"
  and mod_zero: "m \<in> carrier A \<Longrightarrow> m \<Colon> 0 = \<bottom>"
  and mod_test: "\<lbrakk>a \<in> tests K; m \<in> carrier A\<rbrakk> \<Longrightarrow> m \<Colon> a = m \<sqinter> \<top> \<Colon> a"
  and mod_star: "\<lbrakk>m \<in> carrier A; n \<in> carrier A; p \<in> carrier K\<rbrakk> \<Longrightarrow> m \<squnion> n \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> n \<Longrightarrow> m \<Colon> p\<^sup>\<star> \<sqsubseteq>\<^bsub>A\<^esub> n"

begin

  lemma mb_boolean: "a \<in> tests K \<Longrightarrow> \<top> \<Colon> a = \<top> \<or> \<top> \<Colon> a = \<bottom>"
    by (metis (lifting) A.bot_closed A.top_closed bot_oner mod_join mod_mult mod_zero mult_zerol test_subset_var zero_closed)

  lemma "\<lbrakk>a \<in> tests K; m \<in> carrier A\<rbrakk> \<Longrightarrow> !(m \<Colon> a) = m \<Colon> !a"
    by (metis (lifting) A.bot_closed bot_oner cbl_subalg ccompl_top complete_boolean_lattice.ccompl_closed local.complement_closed mb_boolean mod_join mod_zero zero_closed)

  lemma mod_bot: "p \<in> carrier K \<Longrightarrow> \<bottom> \<Colon> p = \<bottom>"
  proof -
    assume pc: "p \<in> carrier K"
    have "\<bottom> \<Colon> p = \<bottom> \<Colon> 0 \<Colon> p"
      by (metis A.bot_closed mod_zero)
    also have "... = \<bottom> \<Colon> 0"
      by (metis A.bot_closed mod_mult mult_zerol pc zero_closed)
    also have "... = \<bottom>"
      by (metis A.bot_closed mod_zero)
    finally show ?thesis .
  qed

  lemma mod_star2: "\<lbrakk>m \<in> carrier A; p \<in> carrier K; q \<in> carrier K\<rbrakk> \<Longrightarrow> m \<Colon> (p + q) \<sqsubseteq>\<^bsub>A\<^esub> m \<Longrightarrow> m \<Colon> p\<^sup>\<star> \<sqsubseteq>\<^bsub>A\<^esub> m"
    by (metis (lifting) A.bot_closed bot_oner mod_bot mod_join mod_zero prop_bot star_closed zero_closed)

  lemma mod_closed : "\<lbrakk>p \<in> carrier K; P \<in> carrier A\<rbrakk> \<Longrightarrow> P \<Colon> p \<in> carrier A"
    by (metis mk_type typed_application)

  lemma mod_meet: "\<lbrakk>p \<in> carrier K; P \<in> carrier A; Q \<in> carrier A\<rbrakk> \<Longrightarrow> P \<sqinter> Q \<Colon> p = P \<Colon> p \<sqinter> Q \<Colon> p"
    by (metis bot_oner mod_closed mod_join mod_zero zero_closed)

  lemma mod_A_iso: "\<lbrakk>p \<in> carrier K; P \<in> carrier A; Q \<in> carrier A\<rbrakk> \<Longrightarrow> P \<sqsubseteq>\<^bsub>A\<^esub> Q \<Longrightarrow> P \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> Q \<Colon> p"
    by (metis bot_oner mod_closed mod_join mod_zero zero_closed)

  lemma mod_K_iso: "\<lbrakk>p \<in> carrier K; q \<in> carrier K; P \<in> carrier A\<rbrakk> \<Longrightarrow> p \<preceq> q \<Longrightarrow> P \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> P \<Colon> q"
    by (metis A.bot_closed A.order_refl bot_oner mod_bot mod_join mod_zero zero_closed)

  declare A.order_refl [intro]
  declare A.bot_closed [intro]

  lemma mod_zero_bot: "\<lbrakk>p \<in> carrier K; M \<in> carrier A; p \<preceq> 0\<rbrakk> \<Longrightarrow> M \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> \<bottom>"
    by (subgoal_tac "p = 0", auto simp add: mod_zero) (metis add_zeror nat_order_def)

  definition hoare_triple :: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" ("_ \<lbrace> _ \<rbrace> _" [54,54,54] 53) where
    "P \<lbrace> p \<rbrace> Q \<equiv> P \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> Q"

  lemma hoare_composition:
    assumes pc: "p \<in> carrier K" and qc: "q \<in> carrier K"
    and Pc: "P \<in> carrier A" and Qc: "Q \<in> carrier A" and Rc: "R \<in> carrier A"
    and p_triple: "P \<lbrace>p\<rbrace> Q" and q_triple: "Q \<lbrace>q\<rbrace> R"
    shows "P \<lbrace>p \<cdot> q\<rbrace> R"
    by (metis (lifting, full_types) A.top_closed Pc Rc bot_oner hoare_triple_def mod_closed mod_join mod_zero mult_closed pc prop_top qc zero_closed)

  lemma hoare_skip: shows "P \<in> carrier A \<Longrightarrow> P \<lbrace> 1 \<rbrace> P"
    by (metis A.order_refl hoare_triple_def mod_one)

  lemma hoare_weakening:
    assumes Pc: "P \<in> carrier A" and P'c: "P' \<in> carrier A" and Qc: "Q \<in> carrier A" and Q'c: "Q' \<in> carrier A"
    and pc: "p \<in> carrier K"
    shows "\<lbrakk>P \<lbrace> p \<rbrace> Q; P \<sqsubseteq>\<^bsub>A\<^esub> P'; Q \<sqsubseteq>\<^bsub>A\<^esub> Q'\<rbrakk> \<Longrightarrow> P' \<lbrace> p \<rbrace> Q'"
  proof -
    assume "Q \<sqsubseteq>\<^bsub>A\<^esub> Q'"
    hence a: "Q \<lbrace> 1 \<rbrace> Q'"
      by (metis Qc hoare_triple_def mod_one)
    assume "P \<lbrace> p \<rbrace> Q" and "P \<sqsubseteq>\<^bsub>A\<^esub> P'"
    hence b: "P' \<lbrace> p \<rbrace> Q"
      by (metis P'c Pc bot_oner mod_join mod_zero zero_closed)
    have "P' \<lbrace> p \<cdot> 1 \<rbrace> Q'"
      by (metis (lifting) P'c Q'c Qc a b hoare_composition one_closed pc)
    thus ?thesis
      by (metis mult_oner pc)
  qed

  lemma hoare_plus:
    assumes pc: "p \<in> carrier K" and qc: "q \<in> carrier K"
    and Pc: "P \<in> carrier A" and Qc: "Q \<in> carrier A"
    and then_branch: "P \<lbrace> p \<rbrace> Q"
    and else_branch: "P \<lbrace> q \<rbrace> Q"
    shows "P \<lbrace> p + q \<rbrace> Q"
    by (smt A.dist2 A.leq_def A.leq_meet_def Pc Qc add_closed else_branch hoare_triple_def mod_closed mod_plus pc qc then_branch)

  lemma hoare_if:
    assumes b_test: "b \<in> tests K"
    and pc: "p \<in> carrier K" and qc: "q \<in> carrier K"
    and Pc: "P \<in> carrier A" and Qc: "Q \<in> carrier A"
    and then_branch: "P \<sqinter> (\<top> \<Colon> b) \<lbrace> p \<rbrace> Q"
    and else_branch: "P \<sqinter> (\<top> \<Colon> !b) \<lbrace> q \<rbrace> Q"
    shows "P \<lbrace> b\<cdot>p + !b\<cdot>q \<rbrace> Q"
    apply (rule hoare_plus)
    apply (metis (lifting) b_test mult_closed pc test_subset_var)
    apply (metis b_test local.complement_closed mult_closed qc test_subset_var)
    apply (metis Pc)
    apply (metis Qc)
    apply (rule_tac Q = "P \<sqinter> (\<top> \<Colon> b)" in hoare_composition)
    apply (metis b_test test_subset_var)
    apply (metis pc)
    apply (metis Pc)
    apply (metis A.meet_closed A.top_closed Pc b_test mod_closed test_subset_var)
    apply (metis (lifting) Qc)
    apply (metis A.eq_refl Pc b_test hoare_triple_def mod_closed mod_test test_subset_var)
    apply (metis then_branch)
    apply (rule_tac Q = "P \<sqinter> \<top> \<Colon> !b" in hoare_composition)
    apply (metis b_test local.complement_closed test_subset_var)
    apply (metis (lifting) qc)
    apply (metis (lifting) Pc)
    apply (metis (lifting) A.meet_closed A.top_closed Pc b_test local.complement_closed mod_closed test_subset_var)
    apply (metis (lifting) Qc)
    apply (metis A.eq_refl Pc b_test hoare_triple_def kat.complement_closed kat_subalg mod_closed mod_test test_subset_var)
    by (metis (lifting) else_branch)

  lemma hoare_star:
    assumes pc: "p \<in> carrier K"
    and Pc: "P \<in> carrier A"
    and p_triple: "P \<lbrace> p \<rbrace> P"
    shows "P \<lbrace> p\<^sup>\<star> \<rbrace> P"
    by (metis (lifting) A.bin_lub_var A.order_refl Pc hoare_triple_def mod_closed mod_star p_triple pc)

  lemma hoare_while:
    assumes b_test: "b \<in> tests K" and pc: "p \<in> carrier K"
    and Pc: "P \<in> carrier A"
    and Q_def: "Q = P \<sqinter> (\<top> \<Colon> !b)"
    and loop_condition: "P \<sqinter> (\<top> \<Colon> b) \<lbrace>p\<rbrace> P"
    shows "P \<lbrace> (b\<cdot>p)\<^sup>\<star>\<cdot>!b \<rbrace> Q"
    apply (simp add: Q_def)
    apply (rule_tac Q = P in hoare_composition)
    apply (metis b_test mult_closed pc star_closed test_subset_var)
    apply (metis b_test local.complement_closed test_subset_var)
    apply (metis (lifting) Pc)
    apply (metis (lifting) Pc)
    apply (metis A.meet_closed A.top_closed Pc b_test local.complement_closed mod_closed test_subset_var)
    apply (rule hoare_star)
    apply (metis (lifting) b_test mult_closed pc test_subset_var)
    apply (metis (lifting) Pc)
    apply (rule_tac Q = "P \<sqinter> \<top> \<Colon> b" in hoare_composition)
    apply (metis (lifting) b_test test_subset_var)
    apply (metis (lifting) pc)
    apply (metis Pc)
    apply (metis Pc b_test mod_closed mod_test test_subset_var)
    apply (metis (lifting) Pc)
    apply (metis A.eq_refl Pc b_test hoare_triple_def mod_closed mod_test test_subset_var)
    apply (metis loop_condition)
    by (metis (lifting) A.order_refl Pc b_test hoare_triple_def kat.complement_closed kat.test_subset_var kat_subalg mod_closed mod_test)

end

no_notation
  Quantale.one ("1\<index>") and
  Quantale.mult (infixl "\<cdot>\<index>" 80)

hide_const unital_quantale.star

locale kat_q_module =
  fixes K :: "'a test_algebra"
  and A :: "'b mult_ord"
  and mk :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes kat_mod: "kat_module K A mk"
  and A_quantale [intro]: "unital_quantale A"
  and qmult_comm': "Quantale.mult A P Q = Quantale.mult A Q P"

sublocale kat_q_module \<subseteq> kat_module using kat_mod .

context kat_q_module
begin

  definition qmult :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<otimes>" 80) where
    "P \<otimes> Q = Quantale.mult A P Q"

  definition qone :: "'b" ("\<one>") where
    "\<one> \<equiv> Quantale.one A"

  lemma qone_closed: "\<one> \<in> carrier A"
    by (simp add: qone_def, rule unital_quantale.one_closed, auto)

  lemma qmult_comm: "\<lbrakk>P \<in> carrier A; Q \<in> carrier A\<rbrakk> \<Longrightarrow> P \<otimes> Q = Q \<otimes> P"
    by (metis qmult_comm' qmult_def)

  lemma qmult_assoc: "\<lbrakk>P \<in> carrier A; Q \<in> carrier A; R \<in> carrier A\<rbrakk> \<Longrightarrow> (P \<otimes> Q) \<otimes> R = P \<otimes> (Q \<otimes> R)"
    by (simp add: qmult_def, rule unital_quantale.mult_assoc, auto)

  lemma qmult_one: "\<lbrakk>P \<in> carrier A\<rbrakk> \<Longrightarrow> P \<otimes> \<one> = P"
    by (simp add: qmult_def qone_def, rule unital_quantale.mult_oner, auto)

  lemma qmult_closed: "\<lbrakk>P \<in> carrier A; Q \<in> carrier A\<rbrakk> \<Longrightarrow> P \<otimes> Q \<in> carrier A"
    by (simp add: qmult_def, rule unital_quantale.mult_closed, auto)

  lemma inf_distl: "\<lbrakk>P \<in> carrier A; X \<subseteq> carrier A\<rbrakk> \<Longrightarrow> P \<otimes> \<Sigma> X = \<Sigma> ((\<lambda>Q. P\<otimes>Q) ` X)"
    by (simp add: qmult_def, rule unital_quantale.inf_distl, auto)

  lemma inf_distr: "\<lbrakk>P \<in> carrier A; X \<subseteq> carrier A\<rbrakk> \<Longrightarrow> \<Sigma> X \<otimes> P = \<Sigma> ((\<lambda>Q. Q\<otimes>P) ` X)"
    by (simp add: qmult_def, rule unital_quantale.inf_distr, auto)

  definition magic_wand :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixr "\<rightharpoondown>" 60) where
    "P \<rightharpoondown> Q \<equiv> unital_quantale.preimp A P Q"

  lemma "P \<in> carrier A \<Longrightarrow> P \<otimes> (P \<rightharpoondown> \<one>) \<sqsubseteq>\<^bsub>A\<^esub> \<one>"
    sorry

  definition precise :: "'b \<Rightarrow> bool" where
    "precise P \<equiv> \<forall>X. P \<otimes> \<Pi> X = \<Pi> ((\<lambda>Q. P\<otimes>Q) ` X)"

  definition local_action :: "'a \<Rightarrow> bool" where
    "local_action p \<equiv> \<forall>P. \<Sigma> {(Q \<Colon> p) \<otimes> R |Q R. P = Q \<otimes> R \<and> Q \<in> carrier A \<and> R \<in> carrier A} = P \<Colon> p"

  lemma helper: "\<lbrakk>P \<in> carrier A; Q \<in> carrier A\<rbrakk> \<Longrightarrow>
    \<Sigma> {x \<otimes> y \<otimes> P|x y. x \<otimes> y = Q \<and> x \<in> carrier A \<and> y \<in> carrier A} = \<Sigma> {x \<otimes> y|x y. x \<otimes> y = Q \<otimes> P \<and> x \<in> carrier A \<and> y \<in> carrier A}"
    apply (rule arg_cong) back
    apply default
    apply auto
    apply (rule_tac x = Q in exI)
    apply (rule_tac x = \<one> in exI)
    by (auto simp add: qmult_one intro: qone_closed)

  lemma mod_qmult:
    assumes pc: "p \<in> carrier K" and Pc: "P \<in> carrier A" and Qc: "Q \<in> carrier A" and Rc: "R \<in> carrier A"
    and p_local: "local_action p"
    shows "(P \<Colon> p) \<otimes> R \<sqsubseteq>\<^bsub>A\<^esub> P \<otimes> R \<Colon> p"
  proof -
    have "(P \<Colon> p) \<otimes> R = \<Sigma> {(x \<Colon> p) \<otimes> y |x y. P = x \<otimes> y \<and> x \<in> carrier A \<and> y \<in> carrier A} \<otimes> R"
      by (insert p_local, simp add: local_action_def)
    moreover have "... = \<Sigma> {(x \<Colon> p) \<otimes> y \<otimes> R |x y. P = x \<otimes> y \<and> x \<in> carrier A \<and> y \<in> carrier A}"
      apply (subst inf_distr)
      apply (metis Rc)
      apply (auto simp add: image_def)
      apply (rule qmult_closed)
      apply (rule mod_closed)
      apply (metis pc)
      apply auto
      apply (rule arg_cong) back
      by auto
    moreover have "... \<sqsubseteq>\<^bsub>A\<^esub> \<Sigma> {(x \<Colon> p) \<otimes> y|x y. P \<otimes> R = x \<otimes> y \<and> x \<in> carrier A \<and> y \<in> carrier A}"
      apply (rule lub_subset_var)
      apply auto
      prefer 3
      apply (rule_tac x = xa in exI)
      apply (rule_tac x = "y \<otimes> R" in exI)
      apply auto
      apply (rule qmult_assoc)
      apply (rule mod_closed)
      apply (metis pc)
      apply auto
      apply (metis Rc)
      apply (rule qmult_assoc)
      apply auto
      apply (metis Rc)
      apply (metis (lifting) Rc qmult_closed)
      apply (rule qmult_closed)
      apply (rule qmult_closed)
      apply (rule mod_closed)
      apply auto
      apply (metis pc)
      apply (metis Rc)
      apply (rule qmult_closed)
      apply (rule mod_closed)
      apply (metis pc)
      by auto
    moreover have "... = P \<otimes> R \<Colon> p"
      by (insert p_local, simp add: local_action_def)
    ultimately show "(P \<Colon> p) \<otimes> R \<sqsubseteq>\<^bsub>A\<^esub> P \<otimes> R \<Colon> p"
      by auto
  qed

 lemma frame_rule:
    assumes pc: "p \<in> carrier K" and Pc: "P \<in> carrier A" and Qc: "Q \<in> carrier A" and Rc: "R \<in> carrier A"
    and p_local: "local_action p"
    and p_triple: "P \<lbrace> p \<rbrace> Q"
    shows "P \<otimes> R \<lbrace> p \<rbrace> Q \<otimes> R"
   

end


  
