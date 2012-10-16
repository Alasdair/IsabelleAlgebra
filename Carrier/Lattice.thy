theory Lattice
  imports Base
begin

subsection {* Partial orders *}

record 'a ord = "'a partial_object" +
  le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>\<index>" 50)

locale order = fixes A (structure)
  assumes order_refl [intro, simp]: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> x"
  and order_trans: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z; x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  and order_antisym: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = y"

subsubsection {* Order duality *}

definition ord_inv :: "('a, 'b) ord_scheme \<Rightarrow> ('a, 'b) ord_scheme" ("_\<sharp>" [1000] 100) where
  "ord_inv ordr \<equiv> \<lparr>carrier = carrier ordr, le = \<lambda>x y. le ordr y x, \<dots> = ord.more ordr\<rparr>"

lemma inv_carrier_id [simp]: "carrier (ord_inv A) = carrier A"
  by (metis ord_inv_def partial_object.simps(1))

lemma ord_to_inv: "order A \<Longrightarrow> order (ord_inv A)"
  by (default, simp_all add: ord_inv_def, (metis order.order_refl order.order_trans order.order_antisym)+)

lemma inv_inv_id: "ord_inv (A\<sharp>) = A"
  by (simp add: ord_inv_def)

lemma inv_to_ord: "order (A\<sharp>) \<Longrightarrow> order A"
  by (metis inv_inv_id ord_to_inv)

lemma ord_is_inv [simp]: "order (A\<sharp>) = order A"
  by (metis inv_to_ord ord_to_inv)

lemma inv_flip [simp]: "(x \<sqsubseteq>\<^bsub>A\<sharp>\<^esub> y) = (y \<sqsubseteq>\<^bsub>A\<^esub> x)"
  by (simp add: ord_inv_def)

lemma dual_carrier_subset: "X \<subseteq> carrier A \<longleftrightarrow> X \<subseteq> carrier (A\<sharp>)"
  by (metis inv_carrier_id)

subsubsection {* Isotone functions *}

definition isotone :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "isotone A B f \<equiv> order A \<and> order B \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y)"

lemma use_iso1: "\<lbrakk>isotone A A f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>A\<^esub> f y"
  by (simp add: isotone_def)

lemma use_iso2: "\<lbrakk>isotone A B f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y"
  by (simp add: isotone_def)

lemma iso_compose: "\<lbrakk>f \<in> carrier A \<rightarrow> carrier B; isotone A B f; g \<in> carrier B \<rightarrow> carrier C; isotone B C g\<rbrakk> \<Longrightarrow> isotone A C (g \<circ> f)"
  by (simp add: isotone_def, safe, metis (full_types) typed_application)

lemma inv_isotone [simp]: "isotone (A\<sharp>) (B\<sharp>) f = isotone A B f"
  by (simp add: isotone_def, auto)

definition idempotent :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "idempotent A f \<equiv> \<forall>x\<in>A. (f \<circ> f) x = f x"

context order
begin

  lemma eq_refl: "\<lbrakk>x \<in> carrier A; x = x\<rbrakk> \<Longrightarrow> x \<sqsubseteq> x" by (metis order_refl)

  subsection {* Least upper bounds *}

  definition is_ub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_ub x X \<equiv> (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x)"

  definition is_lub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lub x X \<equiv>  is_ub x X \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y)"

  lemma is_lub_simp: "is_lub x X = ((X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y))"
    by (simp add: is_lub_def is_ub_def)

  lemma is_lub_unique: "is_lub x X \<longrightarrow> is_lub y X \<longrightarrow> x = y"
    by (smt order_antisym is_lub_def is_ub_def)

  definition lub :: "'a set \<Rightarrow> 'a" ("\<Sigma>") where
    "\<Sigma> X = (THE x. is_lub x X)"

  lemma lub_simp: "\<Sigma> X = (THE x. (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y))"
    by (simp add: lub_def is_lub_simp)

  lemma the_lub_leq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<longrightarrow> z \<sqsubseteq> x\<rbrakk> \<Longrightarrow> \<Sigma> X \<sqsubseteq> x"
    by (metis is_lub_unique lub_def the_equality)

  lemma the_lub_geq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<Longrightarrow> x \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Sigma> X"
    by (metis is_lub_unique lub_def the_equality)

  lemma lub_is_lub [elim?]: "is_lub w X \<Longrightarrow> \<Sigma> X = w"
    by (metis is_lub_unique lub_def the_equality)

  lemma singleton_lub: "y \<in> carrier A \<Longrightarrow> \<Sigma> {y} = y"
    by (unfold lub_def, rule the_equality, simp_all add: is_lub_def is_ub_def, metis order_antisym order_refl)

  lemma surjective_lub: "\<forall>y\<in>carrier A. \<exists>X\<subseteq>carrier A. y = \<Sigma> X"
    by (metis bot_least insert_subset singleton_lub)

  lemma lub_subset: "\<lbrakk>X \<subseteq> Y; is_lub x X; is_lub y Y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
    by (metis (no_types) is_lub_def is_ub_def set_rev_mp)

  lemma lub_closed: "\<lbrakk>X \<subseteq> carrier A; \<exists>x. is_lub x X\<rbrakk> \<Longrightarrow> \<Sigma> X \<in> carrier A"
    by (rule_tac ?P = "\<lambda>x. is_lub x X" in the1I2, metis is_lub_unique, metis is_lub_def is_ub_def lub_is_lub)

  definition join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 70) where
    "x \<squnion> y = \<Sigma> {x,y}"

  subsection {* Greatest lower bounds *}

  definition is_lb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lb x X \<equiv> (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y)"

  definition is_glb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_glb x X \<longleftrightarrow> is_lb x X \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x)"

  lemma is_glb_simp: "is_glb x X = ((X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x))"
     by (simp add: is_glb_def is_lb_def)

  lemma is_glb_unique: "is_glb x X \<longrightarrow> is_glb y X \<longrightarrow> x = y"
    by (smt order_antisym is_glb_def is_lb_def)

  definition glb :: "'a set \<Rightarrow> 'a" ("\<Pi>") where
    "\<Pi> X = (THE x. is_glb x X)"

  lemma glb_simp: "\<Pi> X = (THE x. (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x))"
    by (simp add: glb_def is_glb_simp)

  lemma the_glb_geq: "\<lbrakk>\<exists>z. is_glb z X; \<And>z. is_glb z X \<longrightarrow> x \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Pi> X"
    by (metis glb_def is_glb_unique the_equality)

  lemma the_glb_leq: "\<lbrakk>\<exists>z. is_glb z X; \<And>z. is_glb z X \<longrightarrow> z \<sqsubseteq> x\<rbrakk> \<Longrightarrow> \<Pi> X \<sqsubseteq> x"
    by (metis glb_def is_glb_unique the_equality)

  lemma glb_is_glb [elim?]: "is_glb w X \<Longrightarrow> \<Pi> X = w"
    by (metis is_glb_unique glb_def the_equality)

  lemma singleton_glb: "y \<in> carrier A \<Longrightarrow> \<Pi> {y} = y"
    by (unfold glb_def, rule the_equality, simp_all add: is_glb_def is_lb_def, metis order_antisym order_refl)

  lemma surjective_glb: "\<forall>y\<in>carrier A. \<exists>X\<subseteq>carrier A. y = \<Pi> X"
    by (metis bot_least insert_subset singleton_glb)

  lemma glb_subset: "\<lbrakk>X \<subseteq> Y; is_glb x X; is_glb y Y\<rbrakk> \<Longrightarrow> y \<sqsubseteq> x"
    by (metis (no_types) in_mono is_glb_def is_lb_def)

  lemma glb_closed: "\<lbrakk>X \<subseteq> carrier A; \<exists>x. is_glb x X\<rbrakk> \<Longrightarrow> \<Pi> X \<in> carrier A"
    by (rule_tac ?P = "\<lambda>x. is_glb x X" in the1I2, metis is_glb_unique, metis is_glb_def is_lb_def glb_is_glb)

  definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70) where
    "x \<sqinter> y = \<Pi> {x,y}"

  definition less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
    "x \<sqsubset> y \<equiv> (x \<sqsubseteq> y \<and> x \<noteq> y)"

  lemma less_irrefl [iff]: "x \<in> carrier A \<Longrightarrow> \<not> x \<sqsubset> x"
    by (simp add: less_def)

  lemma less_imp_le: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
    by (simp add: less_def)

  lemma less_asym: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y; (\<not> P \<Longrightarrow> y \<sqsubset> x)\<rbrakk> \<Longrightarrow> P"
    by (metis order_antisym less_def)

  lemma less_trans: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A; x \<sqsubset> y; y \<sqsubset> z\<rbrakk> \<Longrightarrow> x \<sqsubset> z"
    by (metis less_asym less_def order_trans)

  lemma less_le_trans: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A; x \<sqsubset> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubset> z"
    by (metis less_def less_trans)

  lemma less_asym': "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y; y \<sqsubset> x\<rbrakk> \<Longrightarrow> P"
    by (metis less_asym)

  lemma le_imp_less_or_eq: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x \<sqsubset> y \<or> x = y"
    by (metis less_def)

  lemma less_imp_not_less: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y\<rbrakk> \<Longrightarrow> (\<not> y \<sqsubset> x) \<longleftrightarrow> True"
    by (metis less_asym)

  lemma less_imp_triv: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y\<rbrakk> \<Longrightarrow> (y \<sqsubset> x \<longrightarrow> P) \<longleftrightarrow> True"
    by (metis less_asym)

  definition coclosure :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "coclosure m \<equiv> (m \<in> carrier A \<rightarrow> carrier A) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. x \<sqsubseteq> y \<longrightarrow> m x \<sqsubseteq> m y)
                 \<and> (\<forall>x\<in>carrier A. m x \<sqsubseteq> x)
                 \<and> (\<forall>x\<in>carrier A. m x \<sqsubseteq> m (m x))"


  definition is_max :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_max x X \<equiv> x \<in> X \<and> (\<forall>y\<in>X. y \<sqsubseteq> x)"

  definition is_min :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_min x X \<equiv> x \<in> X \<and> (\<forall>y\<in>X. x \<sqsubseteq> y)"

  lemma is_max_equiv: "X \<subseteq> carrier A \<Longrightarrow> is_max x X = (x \<in> X \<and> is_lub x X)"
    by (simp add: is_lub_simp, safe, (metis is_max_def set_mp)+)

  lemma is_min_equiv: "X \<subseteq> carrier A \<Longrightarrow> is_min x X = (x \<in> X \<and> is_glb x X)"
    by (simp add: is_glb_simp, safe, (metis is_min_def set_mp)+)

  definition way_below :: "'a \<Rightarrow> 'a \<Rightarrow> prop" (infixl "\<guillemotleft>" 50) where
     "x \<guillemotleft> y \<equiv> (\<And>D. \<lbrakk>D \<subseteq> carrier A; \<forall>a\<in>D. \<forall>b\<in>D. \<exists>c\<in>D. a \<sqsubseteq> c \<and> b \<sqsubseteq> c; \<exists>z. is_lub z D; y \<sqsubseteq> \<Sigma> D\<rbrakk> \<Longrightarrow> \<exists>z\<in>D. x \<sqsubseteq> z)"

  lemma way_below_leq:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and x_below_y: "x \<guillemotleft> y"
    shows "x \<sqsubseteq> y"
  proof -
    have "\<And>D. \<lbrakk>D \<subseteq> carrier A; \<forall>a\<in>D. \<forall>b\<in>D. \<exists>c\<in>D. a \<sqsubseteq> c \<and> b \<sqsubseteq> c; \<exists>z. is_lub z D; y \<sqsubseteq> \<Sigma> D\<rbrakk> \<Longrightarrow> \<exists>z\<in>D. x \<sqsubseteq> z"
      by (insert x_below_y, simp add: way_below_def)
    hence "\<lbrakk>{y} \<subseteq> carrier A; \<forall>a\<in>{y}. \<forall>b\<in>{y}. \<exists>c\<in>{y}. a \<sqsubseteq> c \<and> b \<sqsubseteq> c; \<exists>z. is_lub z {y}; y \<sqsubseteq> \<Sigma> {y}\<rbrakk> \<Longrightarrow> \<exists>z\<in>{y}. x \<sqsubseteq> z"
      by auto
    moreover have "{y} \<subseteq> carrier A"
      by (metis empty_subsetI insert_subset yc)
    moreover have "\<forall>a\<in>{y}. \<forall>b\<in>{y}. \<exists>c\<in>{y}. a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
      by (metis order_refl singletonE yc)
    moreover have "\<exists>z. is_lub z {y}"
      by (rule_tac x = y in exI, simp add: is_lub_simp, metis order_refl yc)
    moreover have "y \<sqsubseteq> \<Sigma> {y}"
      by (metis eq_refl singleton_lub yc)
    ultimately show "x \<sqsubseteq> y"
      by (metis singleton_iff)
  qed

  definition compact :: "'a \<Rightarrow> prop" where
    "compact x \<equiv> x \<guillemotleft> x"

  definition covers_op :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "covers" 50) where
    "y covers x \<equiv> x \<sqsubset> y \<and> \<not> (\<exists>z. x \<sqsubset> z \<and> z \<sqsubset> y)"

end

definition pointwise_extension :: "'a ord \<Rightarrow> ('b \<Rightarrow> 'a) ord" ("\<up>") where
  "pointwise_extension ord = \<lparr>carrier = UNIV \<rightarrow> carrier ord, le = \<lambda>f g. \<forall>x. le ord (f x) (g x)\<rparr>"

lemma extend_ord: "order A \<Longrightarrow> order (\<up> A)"
  apply default
  apply (simp_all add: pointwise_extension_def)
  apply (metis UNIV_I ftype_pred order.order_refl)
  apply (metis UNIV_I ftype_pred order.order_trans)
  apply default
  by (metis UNIV_I ftype_pred order.order_antisym)

lemma extend_dual: "\<up> (A\<sharp>) = (\<up> A)\<sharp>"
  by (simp add: pointwise_extension_def ord_inv_def)

lemma dual_is_max: "order A \<Longrightarrow> order.is_max (A\<sharp>) x X = order.is_min A x X"
  by (simp add: order.is_max_def order.is_min_def)

lemma dual_is_min: "order A \<Longrightarrow> order.is_min (A\<sharp>) x X = order.is_max A x X"
  by (simp add: order.is_max_def order.is_min_def)

abbreviation less_ext :: "'a \<Rightarrow> ('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> bool" ("_\<sqsubset>\<^bsub>_\<^esub>_" [51,0,51] 50) where
  "x \<sqsubset>\<^bsub>A\<^esub> y \<equiv> order.less A x y"

abbreviation lub_ext :: "('a, 'b) ord_scheme \<Rightarrow> 'a set \<Rightarrow> 'a" ("\<Sigma>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "\<Sigma>\<^bsub>A\<^esub>X \<equiv> order.lub A X"

abbreviation glb_ext :: "('a, 'b) ord_scheme \<Rightarrow> 'a set \<Rightarrow> 'a" ("\<Pi>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "\<Pi>\<^bsub>A\<^esub>X \<equiv> order.glb A X"

abbreviation join_ext :: "'a \<Rightarrow> ('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<squnion>\<^bsub>_\<^esub> _" [71,0,70] 70) where
  "x \<squnion>\<^bsub>A\<^esub> y \<equiv> order.join A x y"

abbreviation meet_ext :: "'a \<Rightarrow> ('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<sqinter>\<^bsub>_\<^esub> _" [70,0,70] 70) where
  "x \<sqinter>\<^bsub>A\<^esub> y \<equiv> order.meet A x y"

subsection {* Join and meet preserving functions *}

definition ex_join_preserving :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "ex_join_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_lub A x X) \<longrightarrow> order.lub B (f ` X) = f (order.lub A X)))"

definition ex_meet_preserving :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "ex_meet_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_glb A x X) \<longrightarrow> order.glb B (f ` X) = f (order.glb A X)))"

definition join_preserving :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "join_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. order.lub B (f ` X) = f (order.lub A X))"

definition meet_preserving :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "meet_preserving A B g \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. order.glb B (g ` X) = g (order.glb A X))"

definition directed :: "('a, 'b) ord_scheme \<Rightarrow> bool" where
  "directed A \<equiv> order A \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. \<exists>z\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> z \<and> y \<sqsubseteq>\<^bsub>A\<^esub> z)"

definition scott_continuous :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "scott_continuous A B f \<equiv> (\<forall>D\<subseteq>carrier A. ((directed \<lparr>carrier = D, le = op \<sqsubseteq>\<^bsub>A\<^esub>\<rparr>) \<longrightarrow> order.lub B (f ` D) = f (order.lub A D)))"

definition scott_ne_continuous :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> prop" where
  "scott_ne_continuous A B f \<equiv> (\<And>D. \<lbrakk>D \<subseteq> carrier A; directed \<lparr>carrier = D, le = op \<sqsubseteq>\<^bsub>A\<^esub>, \<dots> = ord.more A\<rparr>; D \<noteq> {}\<rbrakk> \<Longrightarrow> \<Sigma>\<^bsub>B\<^esub>(f ` D) = f (\<Sigma>\<^bsub>A\<^esub>D))"

lemma dual_is_lub [simp]: "order A \<Longrightarrow> order.is_lub (A\<sharp>) x X = order.is_glb A x X"
  by (simp add: order.is_glb_simp order.is_lub_simp)

lemma dual_is_ub [simp]: "order A \<Longrightarrow> order.is_ub (A\<sharp>) x X = order.is_lb A x X"
  by (simp add: order.is_lb_def order.is_ub_def)

lemma dual_is_glb [simp]: "order A \<Longrightarrow> order.is_glb (A\<sharp>) x X = order.is_lub A x X"
  by (simp add: order.is_glb_simp order.is_lub_simp)

lemma dual_is_lb [simp]: "order A \<Longrightarrow> order.is_lb (A\<sharp>) x X = order.is_ub A x X"
  by (simp add: order.is_lb_def order.is_ub_def)

lemma dual_lub [simp]: "order A \<Longrightarrow> \<Sigma>\<^bsub>A\<sharp>\<^esub>X = \<Pi>\<^bsub>A\<^esub>X"
  by (simp add: order.glb_simp order.lub_simp)

lemma dual_glb [simp]: "order A \<Longrightarrow> \<Pi>\<^bsub>A\<sharp>\<^esub>X = \<Sigma>\<^bsub>A\<^esub>X"
  by (simp add: order.glb_simp order.lub_simp)

lemma common: "\<lbrakk>A \<Longrightarrow> P = Q\<rbrakk> \<Longrightarrow> (A \<and> P) = (A \<and> Q)" by metis

lemma dual_ex_join_preserving [simp]: "ex_join_preserving (A\<sharp>) (B\<sharp>) f = ex_meet_preserving A B f"
  by (simp add: ex_meet_preserving_def ex_join_preserving_def, (rule common)+, simp)

lemma dual_ex_meet_preserving [simp]: "ex_meet_preserving (A\<sharp>) (B\<sharp>) f = ex_join_preserving A B f"
  by (simp add: ex_meet_preserving_def ex_join_preserving_def, (rule common)+, simp)

lemma dual_join_preserving [simp]: "join_preserving (A\<sharp>) (B\<sharp>) f = meet_preserving A B f"
  by (simp add: meet_preserving_def join_preserving_def, (rule common)+, simp)

lemma dual_meet_preserving [simp]: "meet_preserving (A\<sharp>) (B\<sharp>) f = join_preserving A B f"
  by (simp add: meet_preserving_def join_preserving_def, (rule common)+, simp)

hide_fact common

(* +------------------------------------------------------------------------+ *)
subsection {* Total orders *}
(* +------------------------------------------------------------------------+ *)

locale total_order = order +
  assumes totality: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

lemma total_order_is_directed: "total_order A \<Longrightarrow> directed A"
  apply (simp add: directed_def, safe)
  apply (simp add: total_order_def)
  by (metis total_order.totality)

lemma dual_total_order: "total_order A \<longleftrightarrow> total_order (A\<sharp>)"
  by (simp add: total_order_def total_order_axioms_def, auto)

context total_order
begin

  lemma is_max_unique: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; X \<subseteq> carrier A; is_max x X; is_max y X\<rbrakk> \<Longrightarrow> x = y"
    by (metis is_max_def order_antisym)

  lemma is_min_unique: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; X \<subseteq> carrier A; is_min x X; is_min y X\<rbrakk> \<Longrightarrow> x = y"
    by (metis is_min_def order_antisym)

  lemma no_max_equiv: "X \<subseteq> carrier A \<Longrightarrow> (\<forall>x\<in>X. \<exists>y\<in>X. x \<sqsubset> y) \<longleftrightarrow> (\<forall>x\<in>carrier A. \<not> is_max x X)"
    by (smt in_mono is_max_def less_def order_antisym totality)

  lemma no_min_equiv: "X \<subseteq> carrier A \<Longrightarrow> (\<forall>x\<in>X. \<exists>y\<in>X. y \<sqsubset> x) \<longleftrightarrow> (\<forall>x\<in>carrier A. \<not> is_min x X)"
    by (smt is_min_def less_def order_antisym subsetD totality)

  lemma finite_max_var: "\<lbrakk>X \<subseteq> carrier A; finite X; y \<in> carrier A\<rbrakk> \<Longrightarrow> (\<exists>x\<in>(insert y X). is_max x (insert y X))"
    apply (rule finite_subset_induct_var[of X "carrier A"])
    apply (metis, metis)
    apply (rule_tac x = y in bexI)
    apply (simp add: is_max_def)
    apply (metis singleton_iff)
  proof -
    fix a F assume ac: "a \<in> carrier A" and F_subset: "F \<subseteq> carrier A" and yc: "y \<in> carrier A"
      and "\<exists>x\<in>insert y F. is_max x (insert y F)"
    then obtain x where f: "is_max x (insert y F)" by auto
    thus "\<exists>x\<in>insert y (insert a F). is_max x (insert y (insert a F))"
      apply (cases "x \<sqsubseteq> a")
      apply (rule_tac x = a in bexI)
      apply (smt ac F_subset yc insert_iff is_max_def order_refl order_trans set_rev_mp)
      apply (simp add: is_max_def)
      apply (rule_tac x = x in bexI)
      apply (smt ac F_subset yc insert_iff is_max_def set_rev_mp totality)
      by (simp add: is_max_def, auto)
  qed

  lemma finite_max: "\<lbrakk>X \<subseteq> carrier A; finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>x. is_max x X"
    by (metis finite_max_var insert_absorb2 insert_subset nonempty_iff)

  lemma finite_min:
    assumes subset: "X \<subseteq> carrier A" and finite: "finite X" and non_empty: "X \<noteq> {}"
    shows "\<exists>x. is_min x X"
  proof -
    have "total_order A"
      by unfold_locales
    hence "total_order (A\<sharp>)"
      by (metis (lifting) dual_total_order)
    hence "\<exists>x. order.is_max (A\<sharp>) x X"
      by (metis finite inv_carrier_id non_empty subset total_order.finite_max)
    thus "\<exists>x. is_min x X"
      by (metis `total_order (A\<sharp>)` directed_def dual_is_min inv_inv_id total_order_is_directed)
  qed

end

(* +------------------------------------------------------------------------+ *)
subsection {* Join semilattices *}
(* +------------------------------------------------------------------------+ *)

locale join_semilattice = order +
  assumes join_ex: "\<lbrakk>x \<in> carrier A; y\<in>carrier A\<rbrakk> \<Longrightarrow> \<exists>z\<in>carrier A. is_lub z {x,y}"

context join_semilattice
begin

  lemma leq_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) \<longleftrightarrow> (x \<squnion> y = y)"
    apply (simp add: join_def lub_def)
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and xy: "x \<sqsubseteq> y"
    show "(THE z. is_lub z {x,y}) = y"
      by (rule the_equality, simp_all add: is_lub_def is_ub_def, safe, (metis x_closed y_closed xy order_refl order_antisym)+)
  next
    assume "x \<in> carrier A" and "y \<in> carrier A" and "(THE z. is_lub z {x,y}) = y"
    thus "x \<sqsubseteq> y"
      by (metis insertCI is_lub_def is_ub_def join_ex lub_def lub_is_lub)
  qed

  lemma leq_def_right: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> (x \<squnion> y = y)"
    by (metis leq_def)

  lemma leq_def_left: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<squnion> y = y\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y)"
    by (metis leq_def)

  lemma join_idem: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> x = x" by (metis leq_def order_refl)

  lemma join_comm: "x \<squnion> y = y \<squnion> x" by (metis insert_commute join_def)

  lemma bin_lub_var: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    and join_le_z: "x \<squnion> y \<sqsubseteq> z"
    have "x \<sqsubseteq> z" using join_le_z
      apply (simp add: join_def lub_def)
      apply (rule_tac ?P = "\<lambda>z. is_lub z {x,y}" in the1I2)
      apply (metis join_ex lub_is_lub x_closed y_closed)
      by (smt insertI1 is_lub_def is_ub_def join_def join_le_z lub_is_lub order_trans x_closed z_closed)
    moreover have "y \<sqsubseteq> z" using join_le_z
      apply (simp add: join_def lub_def)
      apply (rule_tac ?P = "\<lambda>z. is_lub z {x,y}" in the1I2)
      apply (metis join_ex lub_is_lub x_closed y_closed)
      by (smt insert_iff is_lub_def is_ub_def join_def join_le_z lub_is_lub order_trans y_closed z_closed)
    ultimately show "x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by auto
  next
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    and xz_and_yz: "x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
    thus "x \<squnion> y \<sqsubseteq> z"
      by (smt emptyE lub_is_lub insertE is_lub_def is_ub_def join_ex join_def ord_le_eq_trans)
  qed

  lemma join_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> y \<in> carrier A"
    by (metis join_def join_ex lub_is_lub)

  lemma join_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  proof -
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    hence "(x \<squnion> y) \<squnion> z \<sqsubseteq> x \<squnion> (y \<squnion> z)"
      by (metis eq_refl bin_lub_var join_closed)
    thus ?thesis
      by (smt join_closed order_antisym bin_lub_var order_refl x_closed y_closed z_closed)
  qed

end

lemma ex_join_preserving_is_iso:
  assumes f_closed: "f \<in> carrier A \<rightarrow> carrier B"
  and js_A: "join_semilattice A" and js_B: "join_semilattice B"
  and join_pres: "ex_join_preserving A B f"
  shows "isotone A B f"
proof -

  have ord_A: "order A" and ord_B: "order B"
    by (metis ex_join_preserving_def join_pres)+

  have "\<forall>x y. x \<sqsubseteq>\<^bsub>A\<^esub> y \<and> x \<in> carrier A \<and> y \<in> carrier A \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y"
  proof clarify
    fix x y assume xy: "x \<sqsubseteq>\<^bsub>A\<^esub> y" and xc: "x \<in> carrier A" and yc: "y \<in> carrier A"

    have xyc: "{x,y} \<subseteq> carrier A"
      by (metis bot_least insert_subset xc yc)

    have ejp: "\<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_lub A x X) \<longrightarrow> \<Sigma>\<^bsub>B\<^esub>(f`X) = f (\<Sigma>\<^bsub>A\<^esub>X))"
      by (metis ex_join_preserving_def join_pres)

    have "\<exists>z\<in>carrier A. order.is_lub A z {x,y}"
      by (metis join_semilattice.join_ex js_A xc yc)

    hence xy_join_pres: "f (\<Sigma>\<^bsub>A\<^esub>{x,y}) = \<Sigma>\<^bsub>B\<^esub>{f x, f y}"
      by (metis ejp xyc image_empty image_insert)

    have "f (\<Sigma>\<^bsub>A\<^esub>{x,y}) = f y"
      by (rule_tac f = f in arg_cong, metis ord_A order.join_def join_semilattice.leq_def_right js_A xc xy yc)

    hence "\<Sigma>\<^bsub>B\<^esub>{f x, f y} = f y"
      by (metis xy_join_pres)

    thus "f x \<sqsubseteq>\<^bsub>B\<^esub> f y"
      by (smt join_semilattice.leq_def_left js_B typed_application f_closed xc yc ord_B order.join_def)
  qed

  thus ?thesis by (metis isotone_def ord_A ord_B)
qed

lemma helper: "\<lbrakk>\<And>x. P x \<and> Q x\<rbrakk> \<Longrightarrow> (\<forall>x. P x) \<and> (\<forall>x. Q x)" by fast

lemma extend_binlub:
  assumes js_A: "join_semilattice A"
  and fc: "f \<in> carrier (\<up> A)" and gc: "g \<in> carrier (\<up> A)"
  shows "order.is_lub (\<up> A) (\<lambda>x. f x \<squnion>\<^bsub>A\<^esub> g x) {f, g}"
proof -
  have ord_A_ex: "order (\<up> A)"
    by (insert js_A, simp add: join_semilattice_def, metis extend_ord)

  let ?L = "\<lambda>x. f x \<squnion>\<^bsub>A\<^esub> g x"
  have Lc: "?L \<in> carrier (\<up> A)"
    apply (simp add: pointwise_extension_def, rule typed_abstraction)
    by (smt UNIV_I assms fc gc join_semilattice.join_closed partial_object.simps(1) pointwise_extension_def typed_application)

  have "f \<sqsubseteq>\<^bsub>\<up> A\<^esub> ?L \<and> g \<sqsubseteq>\<^bsub>\<up> A\<^esub> ?L"
  proof (simp add: pointwise_extension_def, rule helper)
    fix x
    have fx: "f x \<in> carrier A" and gx: "g x \<in> carrier A"
      by (smt UNIV_I fc gc partial_object.simps(1) pointwise_extension_def typed_application)+
    hence Lx: "?L x \<in> carrier A"
      by (metis assms join_semilattice.join_closed)
    show "f x \<sqsubseteq>\<^bsub>A\<^esub> ?L x \<and> g x \<sqsubseteq>\<^bsub>A\<^esub> ?L x"
      apply (simp add: join_semilattice.leq_def[OF js_A fx Lx] join_semilattice.leq_def[OF js_A gx Lx])
      apply (intro conjI)
      by (smt assms fx gx join_semilattice.join_assoc join_semilattice.join_idem join_semilattice.join_comm)+
  qed

  moreover hence "\<forall>h\<in>carrier (\<up> A). f \<sqsubseteq>\<^bsub>\<up> A\<^esub> h \<and> g \<sqsubseteq>\<^bsub>\<up> A\<^esub> h \<longrightarrow> ?L \<sqsubseteq>\<^bsub>\<up> A\<^esub> h"
    apply (simp add: pointwise_extension_def)
    by (smt UNIV_I assms fc gc join_semilattice.bin_lub_var partial_object.simps(1) pointwise_extension_def typed_application)

  ultimately show ?thesis
    by (simp add: order.is_lub_simp[OF ord_A_ex], safe, (metis fc gc Lc)+)
qed

lemma extend_join:
  assumes js_A: "join_semilattice A"
  and fc: "f \<in> carrier (\<up> A)" and gc: "g \<in> carrier (\<up> A)"
  shows "f \<squnion>\<^bsub>\<up> A\<^esub> g = (\<lambda>x. f x \<squnion>\<^bsub>A\<^esub> g x)"
proof -
  have ord_A_ex: "order (\<up> A)"
    by (insert js_A, simp add: join_semilattice_def, metis extend_ord)

  show ?thesis
    apply (insert extend_binlub[OF js_A fc gc])
    by (simp add: order.join_def[OF ord_A_ex], metis ord_A_ex order.lub_is_lub)
qed

lemma extend_js:
  assumes js_A: "join_semilattice A"
  shows "join_semilattice (\<up> A)"
proof (simp add: join_semilattice_def join_semilattice_axioms_def, safe)
  show ord_A_ex: "order (\<up> A)"
    by (insert js_A, simp add: join_semilattice_def, metis extend_ord)

  fix f g :: "'b \<Rightarrow> 'a" assume fc: "f \<in> carrier (\<up> A)" and gc: "g \<in> carrier (\<up> A)"

  thus "\<exists>h\<in>carrier (\<up> A). order.is_lub (\<up> A) h {f, g}"
    by (smt assms extend_binlub ord_A_ex order.is_lub_simp)
qed

(* +------------------------------------------------------------------------+ *)
subsection {* Meet semilattices *}
(* +------------------------------------------------------------------------+ *)

locale meet_semilattice = order +
  assumes meet_ex: "\<lbrakk>x \<in> carrier A; y\<in>carrier A\<rbrakk> \<Longrightarrow> \<exists>z\<in>carrier A. is_glb z {x,y}"

context meet_semilattice
begin

  lemma leq_meet_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) \<longleftrightarrow> (x \<sqinter> y = x)"
    apply (simp add: meet_def glb_def)
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and xy: "x \<sqsubseteq> y"
    show "(THE z. is_glb z {x,y}) = x"
      by (rule the_equality, simp_all add: is_glb_def is_lb_def, safe, (metis x_closed y_closed xy order_refl order_antisym)+)
  next
    assume "x \<in> carrier A" and "y \<in> carrier A" and "(THE z. is_glb z {x,y}) = x"
    thus "x \<sqsubseteq> y"
      by (metis insertCI is_glb_def is_lb_def meet_ex glb_def glb_is_glb)
  qed

  lemma meet_idem: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> x = x" by (metis leq_meet_def order_refl)

  lemma meet_comm: "x \<sqinter> y = y \<sqinter> x" by (metis insert_commute meet_def)

  lemma bin_glb_var: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z \<sqsubseteq> x \<sqinter> y \<longleftrightarrow> z \<sqsubseteq> x \<and> z \<sqsubseteq> y"
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    and meet_le_z: "z \<sqsubseteq> x \<sqinter> y"
    have "z \<sqsubseteq> x" using meet_le_z
      apply (simp add: meet_def glb_def)
      apply (rule_tac ?P = "\<lambda>z. is_glb z {x,y}" in the1I2)
      apply (metis meet_ex glb_is_glb x_closed y_closed)
      by (smt insertI1 is_glb_def is_lb_def meet_def meet_le_z glb_is_glb order_trans x_closed z_closed)
    moreover have "z \<sqsubseteq> y" using meet_le_z
      apply (simp add: meet_def glb_def)
      apply (rule_tac ?P = "\<lambda>z. is_glb z {x,y}" in the1I2)
      apply (metis meet_ex glb_is_glb x_closed y_closed)
      by (smt insert_iff is_glb_def is_lb_def meet_def meet_le_z glb_is_glb order_trans y_closed z_closed)
    ultimately show "z \<sqsubseteq> x \<and> z \<sqsubseteq> y" by auto
  next
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    and xz_and_yz: "z \<sqsubseteq> x \<and> z \<sqsubseteq> y"
    thus "z \<sqsubseteq> x \<sqinter> y"
      by (smt emptyE glb_is_glb insertE is_glb_def is_lb_def meet_ex meet_def ord_le_eq_trans)
  qed

  lemma meet_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> y \<in> carrier A"
    by (metis meet_def meet_ex glb_is_glb)

  lemma meet_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  proof -
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    hence "(x \<sqinter> y) \<sqinter> z \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
      by (metis eq_refl bin_glb_var meet_closed)
    thus ?thesis
      by (smt meet_closed order_antisym bin_glb_var order_refl x_closed y_closed z_closed)
  qed

end

lemma inv_meet_semilattice_is_join [simp]: "meet_semilattice (A\<sharp>) = join_semilattice A"
  by (simp_all add: meet_semilattice_def join_semilattice_def meet_semilattice_axioms_def join_semilattice_axioms_def, safe, simp_all)

lemma inv_join_semilattice_is_meet [simp]: "join_semilattice (A\<sharp>) = meet_semilattice A"
  by (simp add: meet_semilattice_def join_semilattice_def meet_semilattice_axioms_def join_semilattice_axioms_def, safe, simp_all)

lemma ex_meet_preserving_is_iso:
  assumes f_closed: "f \<in> carrier A \<rightarrow> carrier B"
  and js_A: "meet_semilattice A" and js_B: "meet_semilattice B"
  and join_pres: "ex_meet_preserving A B f"
  shows "isotone A B f"
proof -
  have "isotone (A\<sharp>) (B\<sharp>) f"
    by (rule ex_join_preserving_is_iso, simp_all add: f_closed js_A js_B join_pres)
  thus "isotone A B f" by simp
qed

lemma extend_ms:
  assumes ms_A: "meet_semilattice A"
  shows "meet_semilattice (\<up> A)"
  by (metis (lifting) assms extend_dual extend_js inv_join_semilattice_is_meet)

lemma extend_binglb:
  assumes ms_A: "meet_semilattice A"
  and fc: "f \<in> carrier (\<up> A)" and gc: "g \<in> carrier (\<up> A)"
  shows "order.is_glb (\<up> A) (\<lambda>x. f x \<sqinter>\<^bsub>A\<^esub> g x) {f, g}"
proof -
  have ord_A: "order A"
    by (insert ms_A, simp add: meet_semilattice_def)
  hence ord_A_ex: "order (\<up> A)"
    by (metis extend_ord)
  have "order.is_lub (\<up> (A\<sharp>)) (\<lambda>x. f x \<squnion>\<^bsub>A\<sharp>\<^esub> g x) {f, g}"
    apply (rule extend_binlub)
    apply (metis assms(1) inv_join_semilattice_is_meet)
    apply (metis extend_dual fc inv_carrier_id)
    by (metis extend_dual gc inv_carrier_id)
  thus ?thesis using ord_A ord_A_ex
    by (simp add: extend_dual order.join_def order.meet_def dual_is_lub[OF ord_A_ex])
qed

lemma extend_meet:
  assumes ms_A: "meet_semilattice A"
  and fc: "f \<in> carrier (\<up> A)" and gc: "g \<in> carrier (\<up> A)"
  shows "f \<sqinter>\<^bsub>\<up> A\<^esub> g = (\<lambda>x. f x \<sqinter>\<^bsub>A\<^esub> g x)"
proof -
  have ord_A_ex: "order (\<up> A)"
    by (insert ms_A, simp add: meet_semilattice_def, metis extend_ord)
  thus ?thesis
    apply (insert extend_binglb[OF ms_A fc gc])
    apply (simp add: order.meet_def[OF ord_A_ex])
    by (metis ord_A_ex order.glb_is_glb)
qed

(* +------------------------------------------------------------------------+ *)
subsection {* Lattices *}
(* +------------------------------------------------------------------------+ *)

locale lattice = join_semilattice + meet_semilattice

begin

  lemma absorb1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> (x \<sqinter> y) = x"
    by (metis join_comm leq_def leq_meet_def meet_assoc meet_closed meet_comm meet_idem)

  lemma absorb2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> (x \<squnion> y) = x"
    by (metis join_assoc join_closed join_comm join_idem leq_def leq_meet_def)

  lemma order_change: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<sqinter>y = y \<longleftrightarrow> y\<squnion>x = x"
    by (metis leq_def leq_meet_def meet_comm)

  lemma bin_lub_insert:
    assumes xc: "x \<in> carrier A" and X_subset: "X \<subseteq> carrier A"
    and X_lub: "\<exists>y. is_lub y X"
    shows "\<exists>z. is_lub z (insert x X)"
  proof -
    obtain y where y_lub: "is_lub y X" and yc: "y \<in> carrier A" by (metis X_lub is_lub_simp)
    have "\<exists>z. is_lub z (insert x X)"
    proof (intro exI conjI)
      have "\<Sigma> {x, y} \<in> carrier A"
        by (metis join_closed join_def xc yc)
      thus "is_lub (\<Sigma> {x, y}) (insert x X)"
        apply (simp add: is_lub_simp, safe)
        apply (metis xc)
        apply (metis X_subset set_mp)
        apply (metis bin_lub_var join_def order_refl xc yc)
        apply (metis (full_types) absorb2 bin_glb_var is_lub_simp join_comm join_def set_mp xc y_lub yc)
        by (metis bin_lub_var is_lub_simp join_def xc y_lub)
    qed
    thus "\<exists>z. is_lub z (insert x X)"
      by metis
  qed

  lemma set_induct: "\<lbrakk>X \<subseteq> carrier A; finite X; P {}; \<And>y Y. \<lbrakk>finite Y; y \<notin> Y; y \<in> carrier A; P Y\<rbrakk> \<Longrightarrow> P (insert y Y)\<rbrakk> \<Longrightarrow> P X"
    by (metis (no_types) finite_subset_induct)

  lemma finite_lub_var: "\<lbrakk>(insert x X) \<subseteq> carrier A; finite (insert x X)\<rbrakk> \<Longrightarrow> \<exists>z. is_lub z (insert x X)"
    apply (rule_tac X = X and P = "\<lambda>X. \<exists>z. is_lub z (insert x X)" in set_induct)
    apply (metis insert_subset)
    apply (metis finite_insert)
    apply (metis insert_absorb2 insert_subset join_ex)
    apply (simp add: insert_commute)
    apply (rule bin_lub_insert)
    apply metis
    apply (metis is_lub_simp)
    by metis

  lemma finite_lub: "\<lbrakk>X \<subseteq> carrier A; finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>x. is_lub x X"
    by (metis finite.simps finite_lub_var)

end

lemma inv_lattice [simp]: "lattice (A\<sharp>) = lattice A"
  by (simp add: lattice_def, auto)

context lattice
begin

  lemma finite_glb:
    assumes "X \<subseteq> carrier A" and "finite X" and "X \<noteq> {}"
    shows "\<exists>x. is_glb x X"
  proof -
    have ord_Ash: "order (A\<sharp>)"
      by (simp, unfold_locales)

    have "\<exists>x. order.is_lub (A\<sharp>) x X"
      by (rule lattice.finite_lub, simp_all add: assms, unfold_locales)
    thus "\<exists>x. is_glb x X"
      by (insert ord_Ash, simp)
  qed

  lemma finite_lub_carrier:
    assumes A_finite: "finite (carrier A)"
    and A_non_empty: "carrier A \<noteq> {}"
    and X_subset: "X \<subseteq> carrier A"
    shows "\<exists>x. is_lub x X"
  proof (cases "X = {}")
    assume x_empty: "X = {}"
    show "\<exists>x. is_lub x X"
    proof (intro exI)
      show "is_lub (\<Pi> (carrier A)) X"
        by (metis (lifting) A_finite A_non_empty X_subset x_empty ex_in_conv finite_glb glb_is_glb is_glb_simp is_lub_def is_ub_def set_eq_subset)
    qed
  next
    assume "X \<noteq> {}"
    thus "\<exists>x. is_lub x X"
      by (metis A_finite X_subset finite_lub rev_finite_subset)
  qed

  lemma finite_glb_carrier:
    assumes A_finite: "finite (carrier A)"
    and A_non_empty: "carrier A \<noteq> {}"
    and X_subset: "X \<subseteq> carrier A"
    shows "\<exists>x. is_glb x X"
  proof -
    have ord_Ash: "order (A\<sharp>)"
      by (simp, unfold_locales)
    have "\<exists>x. order.is_lub (A\<sharp>) x X"
      by (rule lattice.finite_lub_carrier, simp_all add: assms, unfold_locales)
    thus ?thesis by (insert ord_Ash, simp)
  qed

end

lemma extend_lattice: "lattice A \<Longrightarrow> lattice (\<up> A)"
  by (simp add: lattice_def extend_js extend_ms)

(* +------------------------------------------------------------------------+ *)
subsection {* Distributive Lattices *}
(* +------------------------------------------------------------------------+ *)

locale distributive_lattice = lattice +
  assumes dist1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
  and dist2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"

lemma extend_distributive:
  assumes dl_A: "distributive_lattice A"
  shows "distributive_lattice (\<up> A)"
proof (simp add: distributive_lattice_def distributive_lattice_axioms_def, safe)
  have "lattice A"
    by (insert dl_A, simp add: distributive_lattice_def)
  thus "lattice (\<up> A)"
    by (metis extend_lattice)
  hence ord_A_ex: "order (\<up> A)"
    by (simp add: lattice_def join_semilattice_def, auto)
  from `lattice A` have js_A: "join_semilattice A" and ms_A: "meet_semilattice A"
    by (simp add: lattice_def)+

  fix x y z :: "'d \<Rightarrow> 'a"
  assume xc: "x \<in> carrier (\<up> A)" and yc: "y \<in> carrier (\<up> A)" and zc: "z \<in> carrier (\<up> A)"

  hence yzj: "y \<squnion>\<^bsub>\<up>A\<^esub> z \<in> carrier (\<up> A)"
    by (metis extend_js join_semilattice.join_closed js_A)
  have xym: "x \<sqinter>\<^bsub>\<up>A\<^esub> y \<in> carrier (\<up> A)"
    by (metis extend_ms meet_semilattice.meet_closed ms_A xc yc)
  have xzm: "x \<sqinter>\<^bsub>\<up>A\<^esub> z \<in> carrier (\<up> A)"
    by (metis extend_ms meet_semilattice.meet_closed ms_A xc zc)

  from xc yc zc yzj xym xzm
  show "x \<sqinter>\<^bsub>\<up> A\<^esub> (y \<squnion>\<^bsub>\<up> A\<^esub> z) = (x \<sqinter>\<^bsub>\<up> A\<^esub> y) \<squnion>\<^bsub>\<up> A\<^esub> (x \<sqinter>\<^bsub>\<up> A\<^esub> z)"
    apply (simp add: extend_join[OF js_A] extend_meet[OF ms_A])
    apply (simp add: pointwise_extension_def)
    by (metis (hide_lams, no_types) UNIV_I assms distributive_lattice.dist1 typed_application)

  hence yzm: "y \<sqinter>\<^bsub>\<up>A\<^esub> z \<in> carrier (\<up> A)"
    by (metis extend_ms meet_semilattice.meet_closed ms_A yc zc)
  have xyj: "x \<squnion>\<^bsub>\<up>A\<^esub> y \<in> carrier (\<up> A)"
    by (metis extend_js join_semilattice.join_closed js_A xc yc)
  have xzj: "x \<squnion>\<^bsub>\<up>A\<^esub> z \<in> carrier (\<up> A)"
    by (metis extend_js join_semilattice.join_closed js_A xc zc)

  from xc yc zc yzm xyj xzj
  show "x \<squnion>\<^bsub>\<up> A\<^esub> (y \<sqinter>\<^bsub>\<up> A\<^esub> z) = (x \<squnion>\<^bsub>\<up> A\<^esub> y) \<sqinter>\<^bsub>\<up> A\<^esub> (x \<squnion>\<^bsub>\<up> A\<^esub> z)"
    apply (simp add: extend_join[OF js_A] extend_meet[OF ms_A])
    apply (simp add: pointwise_extension_def)
    by (metis (hide_lams, no_types) UNIV_I assms distributive_lattice.dist2 typed_application)
qed

(* +------------------------------------------------------------------------+ *)
subsection {* Bounded Lattices *}
(* +------------------------------------------------------------------------+ *)

locale bounded_lattice = lattice +
  assumes bot_ex: "\<exists>b\<in>carrier A. \<forall>x\<in>carrier A. b \<squnion> x = x"
  and top_ex: "\<exists>t\<in>carrier A. \<forall>x\<in>carrier A. t \<sqinter> x = x"

context bounded_lattice
begin

  definition bot :: "'a" ("\<bottom>") where "\<bottom> \<equiv> THE x. x\<in>carrier A \<and> (\<forall>y\<in>carrier A. x \<sqsubseteq> y)"

  lemma bot_closed: "\<bottom> \<in> carrier A"
    apply (simp add: bot_def)
    apply (rule the1I2)
    apply (metis (no_types) bot_ex leq_def_left order_antisym)
    by auto

  definition top :: "'a" ("\<top>") where "\<top> \<equiv> THE x. x\<in>carrier A \<and> (\<forall>y\<in>carrier A. y \<sqsubseteq> x)"

  lemma top_closed: "\<top> \<in> carrier A"
    apply (simp add: top_def)
    apply (rule the1I2)
    apply (metis (hide_lams, no_types) leq_meet_def meet_comm top_ex)
    by auto

  lemma bot_least: "x \<in> carrier A \<Longrightarrow> \<bottom> \<sqsubseteq> x"
    apply (simp add: bot_def)
    apply (rule the1I2)
    apply (metis (no_types) bot_ex leq_def_left order_antisym)
    by auto

  lemma top_greatest: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> \<top>"
    apply (simp add: top_def)
    apply (rule the1I2)
    apply (metis (hide_lams, no_types) leq_meet_def meet_comm top_ex)
    by auto

  definition atom :: "'a \<Rightarrow> bool" where
    "atom x \<equiv> x covers \<bottom>"

  definition atoms :: "'a set" where
    "atoms \<equiv> {x. x covers \<bottom> \<and> x \<in> carrier A}"

end

(* +------------------------------------------------------------------------+ *)
subsection {* Complemented Lattices *}
(* +------------------------------------------------------------------------+ *)

locale complemented_lattice = bounded_lattice +
  assumes compl: "x \<in> carrier A \<Longrightarrow> \<exists>y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>"

(* +------------------------------------------------------------------------+ *)
subsection {* Boolean algebra *}
(* +------------------------------------------------------------------------+ *)

datatype 'a ba_expr = BNand "'a ba_expr" "'a ba_expr"
                    | BOne
                    | BZero
                    | BAtom 'a

primrec be_atoms :: "'a ba_expr \<Rightarrow> 'a set" where
  "be_atoms (BNand x y) = be_atoms x \<union> be_atoms y"
| "be_atoms BOne = {}"
| "be_atoms BZero = {}"
| "be_atoms (BAtom x) = {x}"

locale boolean_algebra = complemented_lattice + distributive_lattice

begin

  lemma compl_uniq:
    assumes xc: "x \<in> carrier A"
    shows "\<exists>!y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>"
    apply safe
    apply (metis assms compl)
    by (metis absorb2 assms dist1 join_comm meet_comm)

  definition complement :: "'a \<Rightarrow> 'a" ("!") where
    "complement x = (THE y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>)"

  lemma complement_closed: assumes xc: "x \<in> carrier A" shows "!x \<in> carrier A"
    by (simp add: complement_def, rule the1I2, rule compl_uniq[OF xc], auto)

  primrec be_unfold :: "'a ba_expr \<Rightarrow> 'a" where
    "be_unfold BOne = \<top>"
  | "be_unfold BZero = \<bottom>"
  | "be_unfold (BNand x y) = (! (be_unfold x \<squnion> be_unfold y))"
  | "be_unfold (BAtom x) = x"

  lemma atoms_closed: "atoms \<subseteq> carrier A"
    by (auto simp add: atoms_def)

  (*
  lemma complement1: "x \<in> carrier A \<Longrightarrow> x \<squnion> !x = \<top>" sorry

  lemma complement2: "x \<in> carrier A \<Longrightarrow> x \<sqinter> !x = \<bottom>" sorry

  lemma not_one: "!\<top> = \<bottom>" sorry

  lemma not_zero: "!\<bottom> = \<top>" sorry

  lemma double_compl: "x \<in> carrier A \<Longrightarrow> !(!x) = x" sorry

  lemma de_morgan1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !x \<sqinter> !y = !(x \<squnion> y)" sorry

  lemma ba_meet_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> y = !(!x \<squnion> !y)" sorry

  lemma de_morgan2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !x \<squnion> !y = !(x \<sqinter> y)" sorry

  lemma compl_anti: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longleftrightarrow> !y \<sqsubseteq> !x" sorry

  lemma ba_join_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> y = !(!x \<sqinter> !y)" sorry

  lemma ba_3: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = (x \<sqinter> y) \<squnion> (x \<sqinter> !y)" sorry
      *)

end

(* +------------------------------------------------------------------------+ *)
subsection {* Complete join semilattices *}
(* +------------------------------------------------------------------------+ *)

locale complete_join_semilattice = order +
  assumes lub_ex: "\<lbrakk>X \<subseteq> carrier A\<rbrakk> \<Longrightarrow> \<exists>x\<in>carrier A. is_lub x X"

sublocale complete_join_semilattice \<subseteq> join_semilattice
  by default (metis bot_least insert_subset lub_ex)

context complete_join_semilattice
begin

  lemma bot_ax: "\<exists>!b\<in>carrier A. \<forall>x\<in>carrier A. b \<sqsubseteq> x"
    by (metis (no_types) order_antisym bot_least equals0D is_lub_def lub_ex)

  definition bot :: "'a" ("\<bottom>") where "\<bottom> \<equiv> THE x. x\<in>carrier A \<and> (\<forall>y\<in>carrier A. x \<sqsubseteq> y)"

  lemma bot_closed: "\<bottom> \<in> carrier A" by (smt bot_def the1I2 bot_ax)

  lemma prop_bot: "\<forall>x\<in>carrier A. \<bottom> \<sqsubseteq> x"
    by (simp only: bot_def, rule the1I2, smt bot_ax, metis)

  lemma is_lub_lub [intro?]: "X \<subseteq> carrier A \<Longrightarrow> is_lub (\<Sigma> X) X"
    by (metis lub_ex lub_is_lub)

  lemma lub_ex_var: "X \<subseteq> carrier A \<Longrightarrow> \<exists>!x. is_lub x X"
    by (metis is_lub_lub lub_is_lub)

  lemma lub_ex_var2: "X \<subseteq> carrier A \<Longrightarrow> \<exists>x. is_lub x X"
    by (metis lub_ex)

  lemma lub_greatest [intro?]: "\<lbrakk>x \<in> carrier A; X \<subseteq> carrier A; \<forall>y\<in>X. y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> \<Sigma> X \<sqsubseteq> x"
    by (metis is_lub_def is_lub_lub)

  lemma lub_least [intro?]: "\<lbrakk>X \<subseteq> carrier A; x \<in> X\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Sigma> X"
    by (metis is_lub_def is_lub_lub is_ub_def)

  lemma empty_lub [simp]: "\<Sigma> {} = \<bottom>"
    by (metis bot_closed empty_iff empty_subsetI is_lub_def is_ub_def lub_is_lub prop_bot)

  lemma bot_oner [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> \<bottom> = x"
    by (metis join_comm bot_closed leq_def prop_bot)

  lemma bot_onel [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> \<bottom> \<squnion> x = x"
    by (metis join_comm bot_oner)

  lemma lub_union: "\<lbrakk>X \<subseteq> carrier A; Y \<subseteq> carrier A\<rbrakk> \<Longrightarrow> \<Sigma> (X \<union> Y) = \<Sigma> X \<squnion> \<Sigma> Y"
    apply (rule lub_is_lub)
    apply (simp add: join_def)
    apply (simp add: is_lub_simp, safe)
    prefer 4
    apply (metis UnCI bin_lub_var is_lub_simp join_def lub_ex lub_is_lub)
    apply (metis is_lub_lub is_lub_simp join_closed join_def)
    apply (rule the_lub_geq)
    apply (metis is_lub_lub is_lub_simp join_ex)
    apply (metis (hide_lams, no_types) insertI1 insert_absorb insert_subset is_lub_simp lub_least order_trans)
    apply (rule the_lub_geq)
    apply (metis is_lub_lub is_lub_simp join_ex)
    by (metis (hide_lams, no_types) insertI1 insertI2 insert_absorb insert_subset is_lub_simp lub_least order_trans)

  lemma lub_subset_var: "\<lbrakk>X \<subseteq> carrier A; Y \<subseteq> carrier A; X \<subseteq> Y\<rbrakk> \<Longrightarrow> \<Sigma> X \<sqsubseteq> \<Sigma> Y"
    by (metis is_lub_lub lub_subset)

  lemma lub_inf_idem_leq: assumes X_set: "X \<subseteq> Pow (carrier A)" shows "\<Sigma> (\<Sigma> ` X) \<sqsubseteq> \<Sigma> (\<Union> X)"
  proof -
    have "\<Sigma> ` X \<in> Pow (carrier A)"
      by (metis (lifting) PowD PowI X_set image_subsetI is_lub_lub is_lub_simp set_rev_mp)
    hence Sup_X_set: "\<Sigma> ` X \<subseteq> carrier A"
      by (metis Pow_iff)

    show ?thesis
      apply (rule the_lub_leq)
      apply (metis Sup_X_set lub_ex)
      apply safe
      apply (rule the_lub_geq)
      apply (metis Sup_subset_mono Union_Pow_eq X_set lub_ex)
      apply (simp add: is_lub_simp)
      apply safe
      by (metis Sup_le_iff lub_greatest)
  qed

end

abbreviation bot_ext :: "('a, 'b) ord_scheme \<Rightarrow> 'a" ("\<bottom>\<^bsub>_\<^esub>") where
  "\<bottom>\<^bsub>A\<^esub> \<equiv> complete_join_semilattice.bot A"

lemma extend_lub_closed:
  assumes cjs_A: "complete_join_semilattice A" and X_subset: "X \<subseteq> carrier (\<up> A)"
  shows "(\<lambda>x. \<Sigma>\<^bsub>A\<^esub>((\<lambda>f. f x) ` X)) \<in> carrier (\<up> A)"
proof -
  have ord_A: "order A"
    by (metis cjs_A complete_join_semilattice_def)

  have X_map: "\<forall>x. ((\<lambda>f. f x) ` X) \<subseteq> carrier A"
    apply (default, rule typed_mapping[of _ "carrier (\<up> A)"])
    apply (simp add: ftype_pred, simp add: pointwise_extension_def)
    by (metis UNIV_I typed_application, metis X_subset)

  show ?thesis
  proof (simp add: pointwise_extension_def, rule typed_abstraction, safe)
    fix x show "\<Sigma>\<^bsub>A\<^esub>((\<lambda>f. f x) ` X) \<in> carrier A"
      by (metis assms X_map complete_join_semilattice.lub_ex ord_A order.lub_closed)
  qed
qed

lemma extend_lub:
  assumes cjs_A: "complete_join_semilattice A" and X_subset: "X \<subseteq> carrier (\<up> A)"
  shows "order.is_lub (\<up> A) (\<lambda>x. \<Sigma>\<^bsub>A\<^esub>((\<lambda>f. f x) ` X)) X"
proof -
  have ord_A: "order A"
    by (metis cjs_A complete_join_semilattice_def)
  hence ord_A_ex: "order (\<up> A)" by (rule extend_ord)

  let ?L = "\<lambda>x. \<Sigma>\<^bsub>A\<^esub>((\<lambda>f. f x) ` X)"

  have X_map: "\<forall>x. ((\<lambda>f. f x) ` X) \<subseteq> carrier A"
    apply (default, rule typed_mapping[of _ "carrier (\<up> A)"])
    apply (simp add: ftype_pred, simp add: pointwise_extension_def)
    by (metis UNIV_I typed_application, metis X_subset)

  have Lc: "?L \<in> carrier (\<up> A)"
    by (metis X_subset cjs_A extend_lub_closed)

  have "\<forall>h\<in>X. h \<sqsubseteq>\<^bsub>\<up> A\<^esub> ?L"
    apply (simp add: pointwise_extension_def)
    apply (simp add: order.lub_def[OF ord_A])
    apply safe
    apply (rule the1I2)
    apply auto
    apply (rule complete_join_semilattice.lub_ex_var2[OF cjs_A])
    apply (metis X_map)
    apply (metis ord_A order.is_lub_unique)
    by (metis image_eqI ord_A order.is_lub_simp)

  thus "order.is_lub (\<up> A) ?L X"
    apply (simp add: order.is_lub_simp[OF ord_A_ex])
    apply safe
    apply (metis X_subset set_mp)
    apply (metis Lc)
    apply (simp add: pointwise_extension_def)
    by (smt UNIV_I X_map assms complete_join_semilattice.lub_greatest ftype_pred imageE)
qed

lemma extend_cjs:
  assumes cjs_A: "complete_join_semilattice A"
  shows "complete_join_semilattice (\<up> A)"
  apply (simp add: complete_join_semilattice_def complete_join_semilattice_axioms_def, safe)
  apply (subgoal_tac "order A")
  apply (rule extend_ord, auto)
  apply (metis cjs_A complete_join_semilattice_def)
  apply (rule_tac x = "\<lambda>x. \<Sigma>\<^bsub>A\<^esub>((\<lambda>f. f x) ` X)" in bexI)
  apply (metis assms extend_lub)
  by (metis assms extend_lub_closed)

(* +------------------------------------------------------------------------+ *)
subsection {* Complete meet semilattices *}
(* +------------------------------------------------------------------------+ *)

locale complete_meet_semilattice = order +
  assumes glb_ex: "\<lbrakk>X \<subseteq> carrier A\<rbrakk> \<Longrightarrow> \<exists>x\<in>carrier A. is_glb x X"

sublocale complete_meet_semilattice \<subseteq> meet_semilattice
  by default (metis bot_least insert_subset glb_ex)

context complete_meet_semilattice
begin

  lemma top_ax: "\<exists>!t\<in>carrier A. \<forall>x\<in>carrier A. x \<sqsubseteq> t"
    by (metis (no_types) order_antisym bot_least equals0D glb_ex is_glb_def)

  definition top :: "'a" ("\<top>") where "\<top> \<equiv> THE x. x\<in>carrier A \<and> (\<forall>y\<in>carrier A. y \<sqsubseteq> x)"

  lemma top_closed: "\<top> \<in> carrier A" by (smt top_def the1I2 top_ax)

  lemma prop_top: "\<forall>x\<in>carrier A. x \<sqsubseteq> \<top>"
    by (simp only: top_def, rule the1I2, smt top_ax, metis)

  lemma is_glb_glb [intro?]: "X \<subseteq> carrier A \<Longrightarrow> is_glb (\<Pi> X) X"
    by (metis glb_ex glb_is_glb)

  lemma glb_greatest [intro?]: "\<lbrakk>x \<in> carrier A; X \<subseteq> carrier A; \<forall>y\<in>X. x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Pi> X"
    by (metis is_glb_def is_glb_glb)

  lemma glb_least [intro?]: "\<lbrakk>X \<subseteq> carrier A; x \<in> X\<rbrakk> \<Longrightarrow> \<Pi> X \<sqsubseteq> x"
    by (metis is_glb_def is_glb_glb is_lb_def)

  lemma empty_glb [simp]: "\<Pi> {} = \<top>"
    by (metis order_antisym bot_least glb_closed glb_is_glb glb_subset insert_absorb2 is_glb_glb meet_def meet_ex prop_top singleton_glb subset_insertI top_closed)

  lemma top_oner [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> \<top> = x"
    by (metis meet_comm top_closed leq_meet_def prop_top)

  lemma top_onel [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> \<top> \<sqinter> x = x"
    by (metis meet_comm top_oner)

  lemma glb_inf_idem_leq: assumes X_set: "X \<subseteq> Pow (carrier A)" shows "\<Pi> (\<Pi> ` X) \<sqsubseteq> \<Pi> (\<Union> X)"
  proof -
    have "\<Pi> ` X \<in> Pow (carrier A)"
      by (metis (lifting) PowD PowI X_set image_subsetI is_glb_glb is_glb_simp set_rev_mp)
    hence Inf_X_set: "\<Pi> ` X \<subseteq> carrier A"
      by (metis Pow_iff)

    show ?thesis
      apply (rule the_glb_leq)
      apply (metis Inf_X_set glb_ex)
      apply safe
      apply (rule the_glb_geq)
      apply (metis Sup_subset_mono Union_Pow_eq X_set is_glb_glb)
      apply (simp add: is_glb_simp)
      apply safe
      by (smt Sup_le_iff glb_least imageI order_trans set_rev_mp)
  qed

end

lemma inv_cms_is_cjs [simp]: "complete_meet_semilattice (A\<sharp>) = complete_join_semilattice A"
  by (simp add: complete_meet_semilattice_def complete_join_semilattice_def complete_meet_semilattice_axioms_def complete_join_semilattice_axioms_def, safe, simp_all)

lemma inv_cjs_is_cms [simp]: "complete_join_semilattice (A\<sharp>) = complete_meet_semilattice A"
  by (simp add: complete_meet_semilattice_def complete_join_semilattice_def complete_meet_semilattice_axioms_def complete_join_semilattice_axioms_def, safe, simp_all)

abbreviation top_ext :: "('a, 'b) ord_scheme \<Rightarrow> 'a" ("\<top>\<^bsub>_\<^esub>") where
  "\<top>\<^bsub>A\<^esub> \<equiv> complete_meet_semilattice.top A"

lemma extend_cms: "complete_meet_semilattice A \<Longrightarrow> complete_meet_semilattice (\<up> A)"
  by (metis extend_cjs extend_dual inv_cms_is_cjs inv_inv_id)

lemma (in order) is_glb_from_is_lub:
  "\<lbrakk>x \<in> carrier A; X \<subseteq> carrier A; is_lub x {b. (\<forall>a\<in>X. b \<sqsubseteq> a) \<and> b \<in> carrier A}\<rbrakk> \<Longrightarrow> is_glb x X"
  by (auto simp add: is_glb_simp is_lub_simp)

lemma (in complete_join_semilattice) is_cms: "complete_meet_semilattice A"
proof
  fix X assume Xc: "X \<subseteq> carrier A"

  have "{b. (\<forall>a\<in>X. b \<sqsubseteq> a) \<and> b \<in> carrier A} \<subseteq> carrier A" by auto
  then obtain x where "is_lub x {b. (\<forall>a\<in>X. b \<sqsubseteq> a) \<and> b \<in> carrier A}" and "x \<in> carrier A"
    by (metis (lifting) lub_ex)
  hence "is_glb x X"
    by (metis (no_types) Xc is_glb_from_is_lub)
  thus "\<exists>x\<in>carrier A. is_glb x X"
    by (metis `x \<in> carrier A`)
qed

(* +------------------------------------------------------------------------+ *)
subsection {* Complete lattices *}
(* +------------------------------------------------------------------------+ *)

locale complete_lattice = complete_join_semilattice + complete_meet_semilattice

lemma cl_to_order: "complete_lattice A \<Longrightarrow> order A"
  by (simp add: complete_lattice_def complete_join_semilattice_def)

lemma cl_to_cjs: "complete_lattice A \<Longrightarrow> complete_join_semilattice A"
  by (simp add: complete_lattice_def)

lemma cl_to_cms: "complete_lattice A \<Longrightarrow> complete_meet_semilattice A"
  by (simp add: complete_lattice_def)

lemma inv_complete_lattice [simp]: "complete_lattice (A\<sharp>) = complete_lattice A"
  by (simp add: complete_lattice_def, auto)

sublocale complete_lattice \<subseteq> lattice
  by unfold_locales

lemma cl_to_lattice: "complete_lattice A \<Longrightarrow> lattice A"
  apply default
  apply (metis cl_to_order order.order_refl)
  apply (metis cl_to_order order.order_trans)
  apply (metis order.order_antisym cl_to_order)
  apply (metis cl_to_cjs complete_join_semilattice.lub_ex empty_subsetI insert_subset)
  by (metis cl_to_cms complete_meet_semilattice.glb_ex empty_subsetI insert_subset)

lemma cl_to_js: assumes cl: "complete_lattice A" shows "join_semilattice A"
proof -
  have "lattice A" by (metis cl cl_to_lattice)
  thus ?thesis by (simp add: lattice_def)
qed

lemma cl_to_ms: assumes cl: "complete_lattice A" shows "meet_semilattice A"
proof -
  have "lattice A" by (metis cl cl_to_lattice)
  thus ?thesis by (simp add: lattice_def)
qed

context complete_lattice
begin

  lemma univ_lub: "\<Sigma> (carrier A) = \<top>"
    by (metis is_lub_def is_lub_lub is_ub_def prop_top subset_refl top_ax top_closed)

  lemma univ_glb: "\<Pi> (carrier A) = \<bottom>"
    by (metis bot_ax bot_closed is_glb_def is_glb_glb is_lb_def prop_bot subset_refl)

  lemma lub_set_leq: "\<lbrakk>X \<subseteq> carrier A; Y \<subseteq> carrier A; \<forall>x\<in>X. \<exists>y\<in>Y. x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> \<Sigma> X \<sqsubseteq> \<Sigma> Y"
    apply (rule the_lub_leq)
    apply (metis lub_ex)
    apply safe
    apply (rule the_lub_geq)
    apply (metis lub_ex)
    apply (simp add: is_lub_simp)
    apply safe
    by (metis Un_iff le_iff_sup order_trans)

end

lemma lub_inf_idem_ext:
  assumes cl_A: "complete_lattice A"
  and X_set: "X \<subseteq> Pow (carrier A)"
  shows "\<Sigma>\<^bsub>A\<^esub>((order.lub A) ` X) = \<Sigma>\<^bsub>A\<^esub>(\<Union> X)"
proof -
  have ord_A: "order A"
    by (metis cl_A cl_to_order)

  have cl_Ash: "complete_lattice (A\<sharp>)"
    by (metis cl_A inv_complete_lattice)

  have right_closed: "\<Sigma>\<^bsub>A\<^esub>(\<Union> X) \<in> carrier A"
    by (metis Sup_subset_mono Union_Pow_eq X_set cl_A cl_to_cjs complete_join_semilattice.lub_ex ord_A order.lub_closed)
  have left_closed: "\<Sigma>\<^bsub>A\<^esub>((order.lub A) ` X) \<in> carrier A"
    by (metis (hide_lams, no_types) Sup_le_iff Union_Pow_eq Union_mono X_set cl_Ash cl_to_cms complete_join_semilattice.is_lub_lub image_subsetI inv_cms_is_cjs ord_A order.is_lub_simp)

  have dual: "\<Pi>\<^bsub>A\<sharp>\<^esub>(order.glb (A\<sharp>) ` X) \<sqsubseteq>\<^bsub>A\<sharp>\<^esub> \<Pi>\<^bsub>A\<sharp>\<^esub>(\<Union> X)"
    by (metis X_set cl_A cl_to_cjs complete_meet_semilattice.glb_inf_idem_leq inv_carrier_id inv_cms_is_cjs)
  have "\<Sigma>\<^bsub>A\<^esub>(\<Union> X) \<sqsubseteq>\<^bsub>A\<^esub> \<Sigma>\<^bsub>A\<^esub>((order.lub A) ` X)"
    by (insert ord_A dual, simp add: image_def)
  moreover have "\<Sigma>\<^bsub>A\<^esub>((order.lub A) ` X) \<sqsubseteq>\<^bsub>A\<^esub> \<Sigma>\<^bsub>A\<^esub>(\<Union> X)"
    by (metis X_set cl_A cl_to_cjs complete_join_semilattice.lub_inf_idem_leq)
  ultimately show ?thesis
    by (metis order.order_antisym left_closed ord_A right_closed)
qed

lemma (in complete_lattice) lub_inf_idem: "X \<subseteq> Pow (carrier A) \<Longrightarrow> \<Sigma> (\<Sigma> ` X) = \<Sigma> (\<Union> X)"
  by (rule lub_inf_idem_ext[of A], unfold_locales, simp)

hide_fact lub_inf_idem_ext

lemma glb_inf_idem_ext:
  assumes cl_A: "complete_lattice A"
  and X_set: "X \<subseteq> Pow (carrier A)"
  shows "\<Pi>\<^bsub>A\<^esub>((order.glb A) ` X) = \<Pi>\<^bsub>A\<^esub>(\<Union> X)"
proof -
  have ord_A: "order A"
    by (metis cl_A cl_to_order)

  have "\<Sigma>\<^bsub>A\<sharp>\<^esub>((order.lub (A\<sharp>)) ` X) = \<Sigma>\<^bsub>A\<sharp>\<^esub>(\<Union> X)"
    by (rule complete_lattice.lub_inf_idem, simp_all add: X_set cl_A)
  thus ?thesis using ord_A
    by (simp add: image_def)
qed

lemma (in complete_lattice) glb_inf_idem: "X \<subseteq> Pow (carrier A) \<Longrightarrow> \<Pi> (\<Pi> ` X) = \<Pi> (\<Union> X)"
  by (rule glb_inf_idem_ext[of A], unfold_locales, simp)

hide_fact glb_inf_idem_ext

definition cl_continuous :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "cl_continuous A B f = (\<forall>X\<subseteq>carrier A. complete_lattice \<lparr>carrier = X, le = op \<sqsubseteq>\<^bsub>A\<^esub>\<rparr> \<longrightarrow> order.lub B (f ` X) = f (order.lub A X))"

lemma glb_in:
  assumes ord_A: "order A" and X_glb: "\<exists>x. order.is_glb A x X"
  shows "\<exists>x\<in>carrier A. order.is_glb A x X"
proof -
  obtain x where "order.is_glb A x X" by (metis X_glb)
  hence "x \<in> carrier A"
    by (metis ord_A order.is_glb_simp)
  thus ?thesis
    by (metis `order.is_glb A x X`)
qed

lemma lub_in:
  assumes ord_A: "order A" and X_lub: "\<exists>x. order.is_lub A x X"
  shows "\<exists>x\<in>carrier A. order.is_lub A x X"
proof -
  obtain x where "order.is_lub A x X" by (metis X_lub)
  hence "x \<in> carrier A"
    by (metis ord_A order.is_lub_simp)
  thus ?thesis
    by (metis `order.is_lub A x X`)
qed

lemma finite_lattice_is_complete: "\<lbrakk>finite (carrier A); carrier A \<noteq> {}; lattice A\<rbrakk> \<Longrightarrow> complete_lattice A"
  apply (simp add: complete_lattice_def complete_meet_semilattice_def complete_join_semilattice_def)
  apply (simp add: complete_join_semilattice_axioms_def complete_meet_semilattice_axioms_def)
  apply safe
  prefer 3
  apply (simp add: lattice_def join_semilattice_def)
  apply (simp add: lattice_def join_semilattice_def)
  apply (rule lub_in)
  apply (simp add: lattice_def join_semilattice_def)
  apply (metis lattice.finite_lub_carrier)
  apply (rule glb_in)
  apply (simp add: lattice_def join_semilattice_def)
  by (metis lattice.finite_glb_carrier)

lemma extend_cl: "complete_lattice A \<Longrightarrow> complete_lattice (\<up> A)"
  by (simp add: complete_lattice_def extend_cjs extend_cms)

locale complete_boolean_lattice = complete_lattice + distributive_lattice +
  assumes ccompl_ex: "x \<in> carrier A \<Longrightarrow> \<exists>y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>"

begin

  lemma ccompl_uniq:
    assumes xc: "x \<in> carrier A"
    shows "\<exists>!y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>"
    apply safe
    apply (metis assms ccompl_ex)
    by (metis (lifting) assms dist1 meet_comm top_oner)

  definition ccompl :: "'a \<Rightarrow> 'a" ("!") where
    "! x = (THE y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>)"

  lemma ccompl_closed: "x \<in> carrier A \<Longrightarrow> ! x \<in> carrier A"
    by (simp add: ccompl_def, rule the1I2, (smt ccompl_uniq)+)

  lemma ccompl_top: "x \<in> carrier A \<Longrightarrow> x \<squnion> ! x = \<top>"
    apply (simp add: ccompl_def)
    apply (rule the1I2)
    apply (metis (lifting) ccompl_uniq)
    by auto

  lemma ccompl_bot: "x \<in> carrier A \<Longrightarrow> x \<sqinter> ! x = \<bottom>"
    apply (simp add: ccompl_def)
    apply (rule the1I2)
    apply (metis (lifting) ccompl_uniq)
    by auto

end

abbreviation ccompl_ext :: "('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> 'a" ("!\<^bsub>_\<^esub>") where
  "!\<^bsub>A\<^esub> x \<equiv> complete_boolean_lattice.ccompl A x"

lemma extend_cbl:
  assumes cbl_A: "complete_boolean_lattice A"
  shows "complete_boolean_lattice (\<up> A)"
proof (simp add: complete_boolean_lattice_def complete_boolean_lattice_axioms_def, safe)
  have "complete_lattice A"
    by (insert cbl_A, simp add: complete_boolean_lattice_def)
  thus "complete_lattice (\<up> A)"
    by (metis extend_cl)
  hence cms_A_ex: "complete_meet_semilattice (\<up> A)"
    by (metis cl_to_cms)
  from `complete_lattice (\<up> A)` have cjs_A_ex: "complete_join_semilattice (\<up> A)"
    by (metis cl_to_cjs)
  have "distributive_lattice A"
    by (insert cbl_A, simp add: complete_boolean_lattice_def)
  thus "distributive_lattice (\<up> A)"
    by (metis extend_distributive)
  have js_A: "join_semilattice A"
    by (metis `complete_lattice A` cl_to_js)
  have ms_A: "meet_semilattice A"
    by (metis `complete_lattice A` cl_to_ms)

  let ?INV = "(\<lambda>f x. !\<^bsub>A\<^esub> (f x))"

  fix f assume fc: "f \<in> carrier (\<up> A)"

  hence ifc: "?INV f \<in> carrier (\<up> A)"
    apply (simp add: pointwise_extension_def)
    by (smt assms complete_boolean_lattice.ccompl_closed ftype_pred)

  moreover have "f \<squnion>\<^bsub>\<up> A\<^esub> ?INV f = \<top>\<^bsub>\<up> A\<^esub>"
    apply (simp add: extend_join[OF js_A fc ifc])
    apply (rule sym)
    apply default
  proof -
    fix x :: 'c
    have fxc: "f x \<in> carrier A"
      apply (insert fc, simp add: pointwise_extension_def)
      by (metis UNIV_I ftype_pred)
    show "\<top>\<^bsub>\<up> A\<^esub> x = f x \<squnion>\<^bsub>A\<^esub> !\<^bsub>A\<^esub> (f x)"
      apply (simp add: complete_boolean_lattice.ccompl_top[OF cbl_A fxc])
      apply (simp add: complete_meet_semilattice.top_def[OF cms_A_ex])
      apply (rule_tac P = "\<lambda>x. x \<in> carrier (\<up> A) \<and> (\<forall>y\<in>carrier (\<up> A). y \<sqsubseteq>\<^bsub>\<up> A\<^esub> x)" in the1I2)
      apply (metis (no_types) cms_A_ex complete_meet_semilattice.top_ax)
    proof safe
      fix g :: "'c \<Rightarrow> 'a" assume gc: "g \<in> carrier (\<up> A)" and g_top: "\<forall>h\<in>carrier (\<up> A). h \<sqsubseteq>\<^bsub>\<up> A\<^esub> g"
      have "(\<lambda>x. \<top>\<^bsub>A\<^esub>) \<in> carrier (\<up> A)"
        apply (simp add: pointwise_extension_def)
        by (metis `complete_lattice A` cl_to_cms complete_meet_semilattice.top_closed ftype_pred)
      hence "(\<lambda>x. \<top>\<^bsub>A\<^esub>) \<sqsubseteq>\<^bsub>\<up> A\<^esub> g"
        by (metis g_top)
      hence "(\<lambda>x. \<top>\<^bsub>A\<^esub>) = g"
        apply (simp add: pointwise_extension_def)
        apply (rule sym)
        apply default
      proof -
        fix y assume "\<forall>x. \<top>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> g x"
        hence "\<top>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> g y"
          by metis
        moreover have "g y \<in> carrier A"
          apply (insert gc, simp add: pointwise_extension_def)
          by (metis UNIV_I ftype_pred)
        ultimately show "g y = \<top>\<^bsub>A\<^esub>"
          by (metis `complete_lattice A` cl_to_cms cl_to_order complete_meet_semilattice.prop_top complete_meet_semilattice.top_closed order.order_antisym)
      qed
      thus "g x = \<top>\<^bsub>A\<^esub>" by auto
    qed
  qed

  moreover have "f \<sqinter>\<^bsub>\<up> A\<^esub> ?INV f = \<bottom>\<^bsub>\<up> A\<^esub>"
    apply (simp add: extend_meet[OF ms_A fc ifc])
    apply (rule sym)
    apply default
  proof -
    fix x :: 'c
    have fxc: "f x \<in> carrier A"
      apply (insert fc, simp add: pointwise_extension_def)
      by (metis UNIV_I ftype_pred)
    show "\<bottom>\<^bsub>\<up> A\<^esub> x = f x \<sqinter>\<^bsub>A\<^esub> !\<^bsub>A\<^esub> (f x)"
      apply (simp add: complete_boolean_lattice.ccompl_bot[OF cbl_A fxc])
      apply (simp add: complete_join_semilattice.bot_def[OF cjs_A_ex])
      apply (rule_tac P = "\<lambda>x. x \<in> carrier (\<up> A) \<and> (\<forall>y\<in>carrier (\<up> A). x \<sqsubseteq>\<^bsub>\<up> A\<^esub> y)" in the1I2)
      apply (metis (no_types) cjs_A_ex complete_join_semilattice.bot_ax)
    proof safe
      fix g :: "'c \<Rightarrow> 'a" assume gc: "g \<in> carrier (\<up> A)" and g_bot: "\<forall>h\<in>carrier (\<up> A). g \<sqsubseteq>\<^bsub>\<up> A\<^esub> h"
      have "(\<lambda>x. \<bottom>\<^bsub>A\<^esub>) \<in> carrier (\<up> A)"
        apply (simp add: pointwise_extension_def)
        by (metis `complete_lattice A` cl_to_cjs complete_join_semilattice.bot_closed ftype_pred)
      hence "g \<sqsubseteq>\<^bsub>\<up> A\<^esub> (\<lambda>x. \<bottom>\<^bsub>A\<^esub>) "
        by (metis g_bot)
      hence "(\<lambda>x. \<bottom>\<^bsub>A\<^esub>) = g"
        apply (simp add: pointwise_extension_def)
        apply (rule sym)
        apply default
      proof -
        fix y assume "\<forall>x. g x \<sqsubseteq>\<^bsub>A\<^esub> \<bottom>\<^bsub>A\<^esub>"
        hence "g y \<sqsubseteq>\<^bsub>A\<^esub> \<bottom>\<^bsub>A\<^esub>"
          by metis
        moreover have "g y \<in> carrier A"
          apply (insert gc, simp add: pointwise_extension_def)
          by (metis UNIV_I ftype_pred)
        ultimately show "g y = \<bottom>\<^bsub>A\<^esub>"
          by (metis `complete_lattice A` cl_to_cjs cl_to_order complete_join_semilattice.prop_bot complete_join_semilattice.bot_closed order.order_antisym)
      qed
      thus "g x = \<bottom>\<^bsub>A\<^esub>" by auto
    qed
  qed

  ultimately show "\<exists>y. y \<in> carrier (\<up> A) \<and> f \<squnion>\<^bsub>\<up> A\<^esub> y = \<top>\<^bsub>\<up> A\<^esub> \<and> f \<sqinter>\<^bsub>\<up> A\<^esub> y = \<bottom>\<^bsub>\<up> A\<^esub>"
    by metis
qed


(* +------------------------------------------------------------------------+ *)
subsection {* Boolean algebra of booleans *}
(* +------------------------------------------------------------------------+ *)

definition BOOL :: "bool ord" where
  "BOOL = \<lparr>carrier = {True, False}, le = op \<longrightarrow>\<rparr>"

lemma bool_ord: "order BOOL"
  by (default, simp_all add: BOOL_def, auto)

lemma bool_js: "join_semilattice BOOL"
  apply (simp add: join_semilattice_def join_semilattice_axioms_def)
  apply safe
  apply (metis bool_ord)
  apply (simp add: order.is_lub_simp[OF bool_ord])
  apply (simp add: BOOL_def)
  by metis

lemma bool_ms: "meet_semilattice BOOL"
  apply (simp add: meet_semilattice_def meet_semilattice_axioms_def)
  apply safe
  apply (metis bool_ord)
  apply (simp add: order.is_glb_simp[OF bool_ord])
  apply (simp add: BOOL_def)
  by metis

lemma bool_lattice: "lattice BOOL"
  by (simp add: lattice_def bool_ms bool_js)

lemma bool_cl: "complete_lattice BOOL"
  apply (rule finite_lattice_is_complete)
  apply (metis finite_code)
  apply (simp add: BOOL_def)
  by (metis bool_lattice)

lemma bool_cjs: "complete_join_semilattice BOOL"
  by (metis bool_cl cl_to_cjs)

lemma bool_cms: "complete_meet_semilattice BOOL"
  by (metis bool_cl cl_to_cms)

lemma bool_meet: "x \<squnion>\<^bsub>BOOL\<^esub> y \<longleftrightarrow> x \<or> y"
  apply (simp add: order.join_def[OF bool_ord] order.lub_simp[OF bool_ord])
  apply (simp add: BOOL_def)
  by (smt the_equality)

lemma bool_join: "x \<sqinter>\<^bsub>BOOL\<^esub> y \<longleftrightarrow> x \<and> y"
  apply (simp add: order.meet_def[OF bool_ord] order.glb_simp[OF bool_ord])
  apply (simp add: BOOL_def)
  by (smt the_equality)

lemma bool_distributive: "distributive_lattice BOOL"
  apply (simp add: distributive_lattice_def distributive_lattice_axioms_def)
  apply safe
  apply (metis bool_lattice)
  apply (simp_all add: bool_join bool_meet)
  by auto+

lemma bool_total: "total_order BOOL"
  apply (simp add: total_order_def total_order_axioms_def)
  apply safe
  apply (metis bool_ord)
  by (simp add: BOOL_def)

lemma bool_top: "complete_meet_semilattice.top BOOL = True"
  apply (simp add: complete_meet_semilattice.top_def[OF bool_cms])
  apply (simp add: BOOL_def)
  apply (rule the1I2)
  by auto+

lemma bool_bot: "complete_join_semilattice.bot BOOL = False"
  apply (simp add: complete_join_semilattice.bot_def[OF bool_cjs])
  apply (simp add: BOOL_def)
  apply (rule the1I2)
  by auto+

lemma bool_cbl: "complete_boolean_lattice BOOL"
  apply (simp add: complete_boolean_lattice_def complete_boolean_lattice_axioms_def)
  apply safe
  apply (metis bool_cl)
  apply (metis bool_distributive)
  apply (simp add: bool_top bool_bot bool_join bool_meet)
  apply (simp add: BOOL_def)
  by auto

(* +------------------------------------------------------------------------+ *)
subsection {* Fixed points *}
(* +------------------------------------------------------------------------+ *)

definition is_pre_fp :: "('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_pre_fp A x f \<equiv> order A \<and> f \<in> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> f x \<sqsubseteq>\<^bsub>A\<^esub> x"

definition is_post_fp :: "('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_post_fp A x f \<equiv> order A \<and> f \<in> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> x \<sqsubseteq>\<^bsub>A\<^esub> f x"

lemma is_pre_fp_dual [simp]: "is_pre_fp (A\<sharp>) x f = is_post_fp A x f"
  by (simp add: is_pre_fp_def is_post_fp_def)

lemma is_post_fp_dual [simp]: "is_post_fp (A\<sharp>) x f = is_pre_fp A x f"
  by (simp add: is_pre_fp_def is_post_fp_def)

definition is_fp :: "('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_fp A x f \<equiv> order A \<and> f \<in> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> f x = x"

lemma is_fp_dual [simp]: "is_fp (A\<sharp>) x f = is_fp A x f"
  by (simp add: is_fp_def)

lemma is_fp_def_var: "is_fp A x f = (is_pre_fp A x f \<and> is_post_fp A x f)"
  by (simp add: is_fp_def is_pre_fp_def is_post_fp_def, metis order.order_antisym typed_application order.order_refl)

definition is_lpp :: "('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lpp A x f \<equiv> (is_pre_fp A x f) \<and> (\<forall>y\<in>carrier A. f y \<sqsubseteq>\<^bsub>A\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y)"

definition is_gpp :: "('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_gpp A x f \<equiv> (is_post_fp A x f) \<and> (\<forall>y\<in>carrier A. y \<sqsubseteq>\<^bsub>A\<^esub> f y \<longrightarrow> y \<sqsubseteq>\<^bsub>A\<^esub> x)"

lemma is_lpp_dual [simp]: "is_lpp (A\<sharp>) x f = is_gpp A x f"
  by (simp add: is_gpp_def is_lpp_def)

lemma is_gpp_dual [simp]: "is_gpp (A\<sharp>) x f = is_lpp A x f"
  by (simp add: is_lpp_def is_gpp_def)

definition is_lfp :: "('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lfp A x f \<equiv> is_fp A x f \<and> (\<forall>y\<in>carrier A. is_fp A y f \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y)"

lemma is_lfp_closed: "is_lfp A x f \<Longrightarrow> f \<in> carrier A \<rightarrow> carrier A"
  by (metis (no_types) is_fp_def is_lfp_def)

definition is_gfp :: "('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_gfp A x f \<equiv> is_fp A x f \<and> (\<forall>y\<in>carrier A. is_fp A y f \<longrightarrow> y \<sqsubseteq>\<^bsub>A\<^esub> x)"

lemma is_gfp_closed: "is_gfp A x f \<Longrightarrow> f \<in> carrier A \<rightarrow> carrier A"
  by (metis (no_types) is_fp_def is_gfp_def)

lemma is_lfp_dual [simp]: "is_lfp (A\<sharp>) x f = is_gfp A x f"
  by (simp add: is_lfp_def is_gfp_def)

lemma is_gfp_dual [simp]: "is_gfp (A\<sharp>) x f = is_lfp A x f"
  by (simp add: is_gfp_def is_lfp_def)

definition least_prefix_point :: "'a ord \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>\<^bsub>\<le>_\<^esub>_" [0,1000] 100) where
  "least_prefix_point A f \<equiv> THE x. is_lpp A x f"

definition greatest_postfix_point :: "'a ord \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>\<^bsub>\<le>_\<^esub>_" [0,1000] 100) where
  "greatest_postfix_point A f \<equiv> THE x. is_gpp A x f"

lemma least_prefix_point_dual [simp]: "\<mu>\<^bsub>\<le>(A\<sharp>)\<^esub>f = \<nu>\<^bsub>\<le>A\<^esub>f"
  by (simp add: least_prefix_point_def greatest_postfix_point_def)

lemma greatest_postfix_point_dual [simp]: "\<nu>\<^bsub>\<le>(A\<sharp>)\<^esub>f = \<mu>\<^bsub>\<le>A\<^esub>f"
  by (simp add: least_prefix_point_def greatest_postfix_point_def)

definition least_fixpoint :: "('a, 'b) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "least_fixpoint A f \<equiv> THE x. is_lfp A x f"

definition greatest_fixpoint :: "('a, 'b) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "greatest_fixpoint A f \<equiv> THE x. is_gfp A x f"

lemma least_fixpoint_dual [simp]: "\<mu>\<^bsub>(A\<sharp>)\<^esub>f = \<nu>\<^bsub>A\<^esub>f"
  by (simp add: least_fixpoint_def greatest_fixpoint_def)

lemma greatest_fixpoint_dual [simp]: "\<nu>\<^bsub>(A\<sharp>)\<^esub>f = \<mu>\<^bsub>A\<^esub>f"
  by (simp add: least_fixpoint_def greatest_fixpoint_def)

lemma lpp_unique: "\<lbrakk>is_lpp A x f; is_lpp A y f\<rbrakk> \<Longrightarrow> x = y"
  by (smt order.order_antisym is_lpp_def is_pre_fp_def)

lemma gpp_unique: "\<lbrakk>is_gpp A x f; is_gpp A y f\<rbrakk> \<Longrightarrow> x = y"
  by (smt order.order_antisym is_gpp_def is_post_fp_def)

lemma lpp_equality [intro?]: "is_lpp A x f \<Longrightarrow> \<mu>\<^bsub>\<le>A\<^esub> f = x"
  by (simp add: least_prefix_point_def, rule the_equality, auto, smt order.order_antisym is_lpp_def is_pre_fp_def)

lemma gpp_equality [intro?]: "is_gpp A x f \<Longrightarrow> \<nu>\<^bsub>\<le>A\<^esub> f = x"
  by (simp add: greatest_postfix_point_def, rule the_equality, auto, smt order.order_antisym is_gpp_def is_post_fp_def)

lemma lfp_equality: "is_lfp A x f \<Longrightarrow> \<mu>\<^bsub>A\<^esub> f = x"
  by (simp add: least_fixpoint_def, rule the_equality, auto, smt order.order_antisym is_fp_def is_lfp_def)

lemma lfp_equality_var [intro?]: "\<lbrakk>order A; f \<in> carrier A \<rightarrow> carrier A; x \<in> carrier A; f x = x; \<forall>y \<in> carrier A. f y = y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> x = \<mu>\<^bsub>A\<^esub> f"
  by (smt is_fp_def is_lfp_def lfp_equality)

lemma gfp_equality: "is_gfp A x f \<Longrightarrow> \<nu>\<^bsub>A\<^esub> f = x"
  by (simp add: greatest_fixpoint_def, rule the_equality, auto, smt order.order_antisym is_gfp_def is_fp_def)

lemma gfp_equality_var [intro?]: "\<lbrakk>order A; f \<in> carrier A \<rightarrow> carrier A; x \<in> carrier A; f x = x; \<forall>y \<in> carrier A. f y = y \<longrightarrow> y \<sqsubseteq>\<^bsub>A\<^esub> x\<rbrakk> \<Longrightarrow> x = \<nu>\<^bsub>A\<^esub> f"
  by (smt gfp_equality is_fp_def is_gfp_def)

lemma lpp_is_lfp: "\<lbrakk>isotone A A f; is_lpp A x f\<rbrakk> \<Longrightarrow> is_lfp A x f"
  by (simp add: isotone_def is_lpp_def is_pre_fp_def is_lfp_def is_fp_def, metis order.order_antisym order.order_refl typed_application)

lemma gpp_is_gfp: "\<lbrakk>isotone A A f; is_gpp A x f\<rbrakk> \<Longrightarrow> is_gfp A x f"
  by (simp add: isotone_def is_gpp_def is_post_fp_def is_gfp_def is_fp_def, smt order.order_antisym order.order_refl typed_application)

lemma least_fixpoint_set: "\<lbrakk>\<exists>x. is_lfp A x f\<rbrakk> \<Longrightarrow> \<mu>\<^bsub>A\<^esub> f \<in> carrier A"
  by (simp add: least_fixpoint_def, rule the1I2, metis lfp_equality, metis is_lfp_def is_fp_def)

lemma greatest_fixpoint_set: "\<lbrakk>\<exists>x. is_gfp A x f\<rbrakk> \<Longrightarrow> \<nu>\<^bsub>A\<^esub> f \<in> carrier A"
  by (unfold is_lfp_dual[symmetric] least_fixpoint_dual[symmetric], metis inv_carrier_id least_fixpoint_set)

(* +------------------------------------------------------------------------+ *)
subsection {* The Knaster-Tarski theorem *}
(* +------------------------------------------------------------------------+ *)

subsubsection {* For least fixed points *}

theorem knaster_tarski_lpp:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "\<exists>!x. is_lpp A x f"
proof
  let ?H = "{u. f u \<sqsubseteq>\<^bsub>A\<^esub> u \<and> u \<in> carrier A}"
  let ?a = "\<Pi>\<^bsub>A\<^esub>?H"

  have H_carrier: "?H \<subseteq> carrier A" by (metis (lifting) mem_Collect_eq subsetI)
  hence a_carrier: "?a \<in> carrier A"
    by (smt order.glb_closed complete_meet_semilattice.is_glb_glb cl_A cl_to_cms cl_to_order)

  have "is_pre_fp A ?a f"
  proof -
    have "\<forall>x\<in>?H. ?a \<sqsubseteq>\<^bsub>A\<^esub> x" by (smt H_carrier complete_meet_semilattice.glb_least cl_A cl_to_cms)
    hence "\<forall>x\<in>?H. f ?a \<sqsubseteq>\<^bsub>A\<^esub> f x" by (safe, rule_tac ?f = f in use_iso1, metis f_iso, metis a_carrier, auto)
    hence "\<forall>x\<in>?H. f ?a \<sqsubseteq>\<^bsub>A\<^esub> x" by (smt CollectD a_carrier cl_A cl_to_order typed_application f_closed order.order_trans)
    hence "f ?a \<sqsubseteq>\<^bsub>A\<^esub> ?a" by (smt complete_meet_semilattice.glb_greatest cl_A cl_to_cms a_carrier f_closed H_carrier typed_application)
    thus ?thesis by (smt a_carrier cl_A cl_to_order f_closed is_pre_fp_def)
  qed
  moreover show "\<And>x\<Colon>'a. is_lpp A x f \<Longrightarrow> x = ?a"
    by (smt H_carrier calculation cl_A cl_to_cms complete_meet_semilattice.glb_least is_lpp_def lpp_unique mem_Collect_eq)
  ultimately show "is_lpp A ?a f"
    by (smt H_carrier cl_A cl_to_cms complete_meet_semilattice.glb_least is_lpp_def mem_Collect_eq)
qed

corollary is_lpp_lpp [intro?]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> is_lpp A (\<mu>\<^bsub>\<le>A\<^esub> f) f"
  by (smt knaster_tarski_lpp lpp_equality)

theorem knaster_tarski:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> \<exists>!x. is_lfp A x f"
  by (metis knaster_tarski_lpp lfp_equality lpp_is_lfp)

corollary is_lfp_lfp [intro?]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> is_lfp A (\<mu>\<^bsub>A\<^esub> f) f"
  by (smt knaster_tarski lfp_equality)

subsubsection {* For greatest fixed points *}

theorem knaster_tarski_gpp:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "\<exists>!x. is_gpp A x f"
proof -
  have dual: "\<lbrakk>complete_lattice (A\<sharp>); f \<in> carrier (A\<sharp>) \<rightarrow> carrier (A\<sharp>); isotone (A\<sharp>) (A\<sharp>) f\<rbrakk> \<Longrightarrow> \<exists>!x. is_lpp (A\<sharp>) x f"
    by (smt knaster_tarski_lpp)
  thus ?thesis by (simp, metis cl_A f_closed f_iso)
qed

corollary is_gpp_gpp [intro?]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> is_gpp A (\<nu>\<^bsub>\<le>A\<^esub> f) f"
  by (smt knaster_tarski_gpp gpp_equality)

theorem knaster_tarski_greatest:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> \<exists>!x. is_gfp A x f"
  by (metis gfp_equality gpp_is_gfp knaster_tarski_gpp)

corollary is_gfp_gfp [intro?]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> is_gfp A (\<nu>\<^bsub>A\<^esub> f) f"
  by (smt knaster_tarski_greatest gfp_equality)

(* +------------------------------------------------------------------------+ *)
subsection {* Fixpoint computation *}
(* +------------------------------------------------------------------------+ *)

lemma prefix_point_computation [simp]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<mu>\<^bsub>\<le>A\<^esub> f) = \<mu>\<^bsub>\<le>A\<^esub> f"
  by (smt is_fp_def is_lfp_def is_lpp_lpp lpp_is_lfp)

lemma fixpoint_computation [simp]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<mu>\<^bsub>A\<^esub> f) = \<mu>\<^bsub>A\<^esub> f"
  by (metis is_fp_def is_lfp_def is_lfp_lfp)

lemma greatest_postfix_point_computation [simp]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<nu>\<^bsub>\<le>A\<^esub> f) = \<nu>\<^bsub>\<le>A\<^esub> f"
  by (smt is_gpp_gpp gpp_is_gfp is_gfp_def is_fp_def)

lemma greatest_fixpoint_computation [simp]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<nu>\<^bsub>A\<^esub> f) = \<nu>\<^bsub>A\<^esub> f"
  by (metis is_fp_def is_gfp_def is_gfp_gfp)

(* +------------------------------------------------------------------------+ *)
subsection {* Fixpoint induction *}
(* +------------------------------------------------------------------------+ *)

lemma prefix_point_induction [intro?]:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and x_carrier: "x \<in> carrier A" and f_iso: "isotone A A f"
  and pp: "f x \<sqsubseteq>\<^bsub>A\<^esub> x" shows "\<mu>\<^bsub>\<le>A\<^esub> f \<sqsubseteq>\<^bsub>A\<^esub> x"
  by (smt f_closed f_iso cl_A is_lpp_def is_lpp_lpp pp x_carrier)

lemma fixpoint_induction [intro?]:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and x_carrier: "x \<in> carrier A" and f_iso: "isotone A A f"
  and fp: "f x \<sqsubseteq>\<^bsub>A\<^esub> x" shows "\<mu>\<^bsub>A\<^esub> f \<sqsubseteq>\<^bsub>A\<^esub> x"
  by (metis cl_A f_closed f_iso fp is_lpp_def knaster_tarski_lpp lfp_equality lpp_is_lfp x_carrier)

lemma greatest_postfix_point_induction [intro?]:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and x_carrier: "x \<in> carrier A" and f_iso: "isotone A A f"
  and pp: "x \<sqsubseteq>\<^bsub>A\<^esub> f x" shows "x \<sqsubseteq>\<^bsub>A\<^esub> \<nu>\<^bsub>\<le>A\<^esub> f"
  by (smt f_closed f_iso is_gpp_def is_gpp_gpp pp x_carrier cl_A)

lemma greatest_fixpoint_induction [intro?]:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and x_carrier: "x \<in> carrier A" and f_iso: "isotone A A f"
  and fp: "x \<sqsubseteq>\<^bsub>A\<^esub> f x" shows "x \<sqsubseteq>\<^bsub>A\<^esub> \<nu>\<^bsub>A\<^esub> f"
  by (smt f_closed f_iso fp gfp_equality gpp_is_gfp is_gpp_def knaster_tarski_gpp x_carrier cl_A)

(* +------------------------------------------------------------------------+ *)
subsection {* Other simple fixpoint theorems *}
(* +------------------------------------------------------------------------+ *)

lemma fixpoint_compose:
  assumes f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and g_closed: "g \<in> carrier A \<rightarrow> carrier A"
  and k_closed: "k \<in> carrier A \<rightarrow> carrier A"
  and x_carrier: "x \<in> carrier A" and k_iso: "isotone A A k"
  and comp: "g\<circ>k = k\<circ>h" and fp: "is_fp A x h"
  shows "is_fp A (k x) g"
  using fp and comp by (simp add: is_fp_def o_def, safe, (metis g_closed k_closed typed_application)+)

lemma fixpoint_iso:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A" and g_closed: "g \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f" and g_iso: "isotone A A g"
  and fg: "\<forall>x\<in>carrier A. f x \<sqsubseteq>\<^bsub>A\<^esub> g x" shows "\<mu>\<^bsub>A\<^esub> f \<sqsubseteq>\<^bsub>A\<^esub> \<mu>\<^bsub>A\<^esub> g"
  by (smt f_closed f_iso fg fixpoint_computation g_closed g_iso is_lpp_def is_pre_fp_def knaster_tarski_lpp lfp_equality lpp_is_lfp cl_A)

lemma greatest_fixpoint_iso:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and g_closed: "g \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  and g_iso: "isotone A A g"
  and fg: "\<forall>x\<in>carrier A. f x \<sqsubseteq>\<^bsub>A\<^esub> g x" shows "\<nu>\<^bsub>A\<^esub> f \<sqsubseteq>\<^bsub>A\<^esub> \<nu>\<^bsub>A\<^esub> g"
  by (smt f_closed f_iso fg g_closed g_iso gfp_equality gpp_is_gfp greatest_fixpoint_computation is_gpp_def is_post_fp_def knaster_tarski_gpp cl_A)

(* +------------------------------------------------------------------------+ *)
subsection {* Iterated functions *}
(* +------------------------------------------------------------------------+ *)

primrec iter :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "iter 0 f x = x"
| "iter (Suc n) f x = f (iter n f x)"

lemma iter_closed: "f \<in> A \<rightarrow> A \<Longrightarrow> iter n f \<in> A \<rightarrow> A"
proof (induct n)
  case 0 show ?case
    by (metis (lifting) Lattice.iter.simps(1) ftype_pred)
  case (Suc m) show ?case
    by (metis (lifting, full_types) "0" Lattice.iter.simps(2) Suc.hyps ftype_pred)
qed

lemma iter_pointfree: "iter (Suc n) f = f \<circ> iter n f"
  by (simp add: o_def, metis Lattice.iter.simps(2))

lemma iter_iso:
  assumes f_type: "f \<in> carrier A \<rightarrow> carrier A" and f_iso: "isotone A A f"
  shows "isotone A A (iter n f)"
  apply (induct n)
  apply (metis (lifting) Lattice.iter.simps(1) isotone_def f_iso)
  apply (simp only: iter_pointfree)
  apply (rule_tac B = A in iso_compose)
  apply (metis f_type iter_closed)
  apply metis
  apply (metis f_type)
  by (metis f_iso)

lemma iter_inc:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "iter n f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter (Suc n) f \<bottom>\<^bsub>A\<^esub>"
proof (induct n)
  case 0 show ?case
    by (simp add: iter_def, metis cl_A cl_to_cjs complete_join_semilattice.bot_closed complete_join_semilattice.prop_bot f_closed ftype_pred)
  case (Suc m) fix n assume ind_hyp: "iter n f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter (Suc n) f \<bottom>\<^bsub>A\<^esub>"
  hence "f (iter n f \<bottom>\<^bsub>A\<^esub>) \<sqsubseteq>\<^bsub>A\<^esub> f (iter (Suc n) f \<bottom>\<^bsub>A\<^esub>)"
    by (metis (full_types) cl_A cl_to_cjs complete_join_semilattice.bot_closed f_closed f_iso ftype_pred isotone_def iter_closed)
  thus "iter (Suc n) f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter (Suc (Suc n)) f \<bottom>\<^bsub>A\<^esub>"
    by (metis Lattice.iter.simps(2))
qed

lemma iter_zero_pointfree [simp]: "iter 0 f = id"
  by (simp add: iter_def id_def)

lemma iter_add: "iter (n+m) f = iter n f \<circ> iter m f"
proof (induct n)
  case 0 show ?case by simp
next
  fix n assume ind_hyp: "iter (n + m) f = iter n f \<circ> iter m f"
  thus "iter (Suc n + m) f = iter (Suc n) f \<circ> iter m f"
    by (simp add: iter_pointfree ind_hyp o_assoc)
qed

lemma iter_add_point: "\<forall>x. iter (n+m) f x = iter n f (iter m f x)"
  by (metis iter_add o_apply)

lemma iter_chain:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  and nm: "n \<le> m" shows "iter n f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter m f \<bottom>\<^bsub>A\<^esub>"
proof -
  let ?k = "m - n"
  have "iter n f (iter 0 f \<bottom>\<^bsub>A\<^esub>) \<sqsubseteq>\<^bsub>A\<^esub> iter n f (iter ?k f \<bottom>\<^bsub>A\<^esub>)"
  proof (rule_tac f = "iter n f" in use_iso1)
    show "isotone A A (iter n f)"
      by (metis f_closed f_iso iter_iso)
    show "iter 0 f \<bottom>\<^bsub>A\<^esub> \<in> carrier A"
      by (metis Lattice.iter.simps(1) cl_A cl_to_cjs complete_join_semilattice.bot_closed)
    show "iter ?k f \<bottom>\<^bsub>A\<^esub> \<in> carrier A"
      by (metis Lattice.iter.simps(1) `iter 0 f \<bottom>\<^bsub>A\<^esub> \<in> carrier A` f_closed ftype_pred iter_closed)
    show "iter 0 f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter ?k f \<bottom>\<^bsub>A\<^esub>"
      by (metis Lattice.iter.simps(1) cl_A cl_to_cjs complete_join_semilattice.bot_closed complete_join_semilattice.prop_bot f_closed ftype_pred iter_closed)
  qed
  hence "iter (n+0) f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter (n+?k) f \<bottom>\<^bsub>A\<^esub>"
    by (metis iter_add_point)
  thus "iter n f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter m f \<bottom>\<^bsub>A\<^esub>" by (smt nm)
qed

lemma iter_unfold: "{x. (\<exists>i. x = iter i f z)} = {z} \<union> (f ` {x. (\<exists>i. x = iter i f z)})"
proof -
  have subset1: "{x. (\<exists>i. x = iter i f z)} \<subseteq> {z} \<union> {x. (\<exists>i. x = iter (Suc i) f z)}"
  proof
    fix x assume x_set: "x \<in> {x. \<exists>i. x = iter i f z}"
    show "x \<in> {z} \<union> {x. \<exists>i. x = iter (Suc i) f z}"
    proof (cases "x = z")
      assume "x = z"
      thus "x \<in> {z} \<union> {x. \<exists>i. x = iter (Suc i) f z}"
        by (metis insertI1 insert_is_Un)
    next
      assume x_not_bot: "x \<noteq> z"
      obtain j where x_eq: "x = iter j f z"
        by (smt CollectE x_set)
      hence "1 \<le> j"
        by (smt Lattice.iter.simps(1) x_not_bot)
      hence "\<exists>i. x = iter (Suc i) f z"
        by (metis One_nat_def Suc_le_D x_eq)
      thus "x \<in> {z} \<union> {x. \<exists>i. x = iter (Suc i) f z}"
        by (smt CollectI Un_def)
    qed
  qed
  have subset2: "{z} \<union> {x. (\<exists>i. x = iter (Suc i) f z)} \<subseteq> {x. (\<exists>i. x = iter i f z)}"
  proof
    fix x assume x_set: "x \<in> {z} \<union> {x. \<exists>i. x = iter (Suc i) f z}"
    hence "\<exists>i. x = iter i f z"
      by (smt Lattice.iter.simps(1) Un_iff empty_iff insert_iff mem_Collect_eq)
    thus "x \<in> {x. \<exists>i. x = iter i f z}"
      by (metis (lifting, full_types) mem_Collect_eq)
  qed
  have "(f ` {x. (\<exists>i. x = iter i f z)}) = {x. (\<exists>i. x = iter (Suc i) f z)}"
    by (simp add: image_def, smt Collect_cong)
  thus ?thesis
    by (metis (lifting) order_antisym subset1 subset2)
qed

lemma iter_fp: "f x = x \<Longrightarrow> iter n f x = x"
  by (induct n, simp_all)

(* +------------------------------------------------------------------------+ *)
subsection {* Kleene chains *}
(* +------------------------------------------------------------------------+ *)

definition kleene_chain :: "('a, 'b) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) ord_scheme" where
  "kleene_chain A f = \<lparr>carrier = {x. (\<exists>i. x = iter i f \<bottom>\<^bsub>A\<^esub>)}, le = op \<sqsubseteq>\<^bsub>A\<^esub>, \<dots> = ord.more A\<rparr>"

lemma kleene_chain_closed:
  "\<lbrakk>complete_join_semilattice A; f \<in> carrier A \<rightarrow> carrier A\<rbrakk> \<Longrightarrow> carrier (kleene_chain A f) \<subseteq> carrier A"
  apply (default, simp add: kleene_chain_def)
  by (metis complete_join_semilattice.bot_closed ftype_pred iter_closed)

lemma kleene_chain_order:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  shows "order (kleene_chain A f)"
  apply (simp add: kleene_chain_def)
  apply (default, simp_all)
  apply (metis (full_types) cl_A cl_to_cjs cl_to_order typed_application complete_join_semilattice.bot_closed f_closed iter_closed order.order_refl)
  apply safe
  apply simp_all
  apply (smt cl_A cl_to_cjs cl_to_order typed_application complete_join_semilattice.bot_closed f_closed iter_closed order.order_trans)
  by (metis order.order_antisym cl_A cl_to_cjs cl_to_order typed_application complete_join_semilattice.bot_closed f_closed iter_closed)

lemma kleene_chain_iso:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "isotone (kleene_chain A f) (kleene_chain A f) f"
  apply (simp add: isotone_def)
  apply safe
  apply (metis cl_A f_closed kleene_chain_order)
  using f_iso
  apply (simp add: isotone_def)
  apply (simp add: kleene_chain_def)
  by (metis cl_A cl_to_cjs typed_application complete_join_semilattice.bot_closed f_closed iter_closed)

lemma kleene_chain_total:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "total_order (kleene_chain A f)"
  apply (simp add: total_order_def total_order_axioms_def, rule conjI)
  apply (metis cl_A f_closed kleene_chain_order)
  apply (simp add: kleene_chain_def)
  apply clarsimp
proof -
  fix n m assume hyp: "\<not> iter m f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter n f \<bottom>\<^bsub>A\<^esub>"
  show "iter n f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter m f \<bottom>\<^bsub>A\<^esub>"
    apply (cases "n \<le> m")
    apply (metis cl_A f_closed f_iso iter_chain)
    by (smt cl_A f_closed f_iso hyp iter_chain)
qed

lemma kleene_chain_fun:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  shows "f \<in> carrier (kleene_chain A f) \<rightarrow> carrier (kleene_chain A f)"
  apply (simp add: kleene_chain_def ftype_pred)
  by (metis Lattice.iter.simps(2))

lemma kleene_chain_join_semilattice:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "join_semilattice (kleene_chain A f)"
proof (simp add: join_semilattice_def join_semilattice_axioms_def, safe)
  show order: "order (kleene_chain A f)"
    by (metis cl_A f_closed kleene_chain_order)
  fix x y assume xc: "x \<in> carrier (kleene_chain A f)" and yc: "y \<in> carrier (kleene_chain A f)"
  thus "\<exists>z\<in>carrier (kleene_chain A f). order.is_lub (kleene_chain A f) z {x, y}"
    using order apply (simp add: order.is_lub_simp)
    apply (simp add: kleene_chain_def)
    by (metis (lifting) cl_A f_closed f_iso kleene_chain_def kleene_chain_total ord.simps(1) total_order.totality xc yc)
qed

lemma kleene_chain_meet_semilattice:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "meet_semilattice (kleene_chain A f)"
proof (simp add: meet_semilattice_def meet_semilattice_axioms_def, safe)
  show order: "order (kleene_chain A f)"
    by (metis cl_A f_closed kleene_chain_order)
  fix x y assume xc: "x \<in> carrier (kleene_chain A f)" and yc: "y \<in> carrier (kleene_chain A f)"
  thus "\<exists>z\<in>carrier (kleene_chain A f). order.is_glb (kleene_chain A f) z {x, y}"
    using order apply (simp add: order.is_glb_simp)
    apply (simp add: kleene_chain_def)
    by (metis (lifting) cl_A f_closed f_iso kleene_chain_def kleene_chain_total ord.simps(1) total_order.totality xc yc)
qed

lemma kleene_chain_lattice:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "lattice (kleene_chain A f)"
  apply (simp add: lattice_def)
  apply (insert kleene_chain_meet_semilattice[of A f] kleene_chain_join_semilattice[of A f] cl_A f_closed f_iso)
  by simp

lemma kleene_chain_complete_lattice:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  and chain_finite: "finite (carrier (kleene_chain A f))"
  shows "complete_lattice (kleene_chain A f)"
  apply (rule finite_lattice_is_complete)
  apply (metis chain_finite)
  apply (simp add: kleene_chain_def)
  apply metis
  by (metis cl_A f_closed f_iso kleene_chain_lattice)

lemma kleene_chain_f_lub:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "\<Sigma>\<^bsub>A\<^esub>(f ` carrier (kleene_chain A f)) = \<Sigma>\<^bsub>A\<^esub>(carrier (kleene_chain A f))"
proof -
  let ?M = "carrier (kleene_chain A f)"

  have ord_A: "order A"
    by (metis cl_A cl_to_order)

  have "\<Sigma>\<^bsub>A\<^esub>(f ` ?M) = order.join A \<bottom>\<^bsub>A\<^esub> (\<Sigma>\<^bsub>A\<^esub>(f ` ?M))"
    apply (rule complete_join_semilattice.bot_onel[symmetric])
    apply (metis cl_A cl_to_cjs)
    by (smt cl_A cl_to_cjs complete_join_semilattice.is_lub_lub f_closed ftype_pred image_subsetI kleene_chain_closed ord_A order.is_lub_simp subsetD)
  also have "... = order.join A (\<Sigma>\<^bsub>A\<^esub>{\<bottom>\<^bsub>A\<^esub>}) (\<Sigma>\<^bsub>A\<^esub>(f ` ?M))"
    by (metis (lifting) cl_A cl_to_cjs complete_join_semilattice.bot_closed ord_A order.singleton_lub)
  also have "... = \<Sigma>\<^bsub>A\<^esub>({\<bottom>\<^bsub>A\<^esub>} \<union> (f ` ?M))"
    apply (rule complete_join_semilattice.lub_union[symmetric])
    apply (metis cl_A cl_to_cjs)
    apply (metis (lifting) bot_least cl_A cl_to_cjs complete_join_semilattice.bot_closed insert_subset)
    by (metis cl_A cl_to_cjs typed_application f_closed image_mono image_subsetI kleene_chain_closed subset_trans)
  also have "... = \<Sigma>\<^bsub>A\<^esub>?M"
    apply (simp only: kleene_chain_def partial_object.simps(1))
    apply (rule_tac f = "\<lambda>X. \<Sigma>\<^bsub>A\<^esub>X" in arg_cong)
    by (rule iter_unfold[symmetric])
  finally show ?thesis by metis
qed

lemma kleene_chain_iter_lub:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_jp: "join_preserving A A f"
  shows "\<Sigma>\<^bsub>A\<^esub>(iter n f ` carrier (kleene_chain A f)) = \<Sigma>\<^bsub>A\<^esub>(carrier (kleene_chain A f))"
proof (induct n, simp, simp only: kleene_chain_def partial_object.simps)
  let ?M = "{x. \<exists>i. x = iter i f \<bottom>\<^bsub>A\<^esub>}"

  fix n assume ind_hyp: "\<Sigma>\<^bsub>A\<^esub>(iter n f ` ?M) = \<Sigma>\<^bsub>A\<^esub>?M"

  have f_iso: "isotone A A f"
    apply (rule ex_join_preserving_is_iso)
    apply (metis f_closed)
    apply (metis cl_A cl_to_js)
    apply (metis cl_A cl_to_js)
    by (metis (mono_tags) ex_join_preserving_def f_jp join_preserving_def)

  have ord_A: "order A"
    by (metis cl_A cl_to_order)

  have M_subset: "?M \<subseteq> carrier A"
    by (metis (mono_tags) cl_A cl_to_cjs f_closed kleene_chain_closed kleene_chain_def partial_object.simps(1))

  moreover have "iter n f \<in> carrier A \<rightarrow> carrier A"
    by (metis f_closed iter_closed)

  ultimately have iter_M_subset: "(iter n f ` ?M) \<subseteq> carrier A"
    by (smt ftype_pred image_subsetI set_rev_mp)

  have "\<Sigma>\<^bsub>A\<^esub>(iter (Suc n) f ` ?M) = \<Sigma>\<^bsub>A\<^esub>(f ` iter n f ` ?M)"
    by (smt image_compose iter_pointfree)
  also have "... = f (\<Sigma>\<^bsub>A\<^esub>(iter n f ` ?M))"
    by (smt iter_M_subset f_jp join_preserving_def)
  also have "... = f (\<Sigma>\<^bsub>A\<^esub>?M)"
    by (metis ind_hyp)
  also have "... = \<Sigma>\<^bsub>A\<^esub>(f ` ?M)"
    by (smt M_subset f_jp join_preserving_def)
  also have "... = \<Sigma>\<^bsub>A\<^esub>?M"
    by (insert kleene_chain_f_lub[of A f] f_closed cl_A f_iso, simp add: kleene_chain_def)
  finally show "\<Sigma>\<^bsub>A\<^esub>(iter (Suc n) f ` {x. \<exists>i. x = iter i f \<bottom>\<^bsub>A\<^esub>}) = \<Sigma>\<^bsub>A\<^esub>{x. \<exists>i. x = iter i f \<bottom>\<^bsub>A\<^esub>}"
    by metis
qed

(* +------------------------------------------------------------------------+ *)
subsection {* Kleene's fixed point theorem *}
(* +------------------------------------------------------------------------+ *)

text {* Kleene's fixed point theorem states that for any
  scott-continuous function $f$ over a complete partial order, the
  least fixed point of $f$ is also the least upper bound of the
  ascending kleene chain of $f$ (denoted $C$).

  The chain $C$ is directed, and must therefore have a least upper
  bound $c$. It can then be shown that $c$ is a fixed point of $f$:

  \[
  f(c) = f\left(\sum C\right) = \sum f(C) = \sum C = c
  \]

  The last step is to show that $c$ is the least fixpoint of
  $f$. Given an arbitrary fixed point $a$ of $f$, it must be the case
  that $\bot \le a$. As $f^n$ is isotone, $f^n(\bot) \le f^n(a) \le
  a$, which implies that $\forall x \in C. x \le a$. This can be used
  to show that $\sum C \le \sum\{a\}$, and hence $c \le a$.

  Here we only prove this theorem for a complete lattice rather than a
  complete partial order, as we have not formalised complete partial
  orders. However, the proof could be easily adapted.
  *}

(* FIXME: Directed is incorrect, as a directed set cannot be empty! *)

theorem kleene_fixed_point:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  and f_scott_continuous:
    "\<And>D. \<lbrakk>D\<subseteq>carrier A; directed \<lparr>carrier = D, le = op \<sqsubseteq>\<^bsub>A\<^esub>, \<dots> = ord.more A\<rparr>; D \<noteq> {}\<rbrakk>
    \<Longrightarrow> f (\<Sigma>\<^bsub>A\<^esub>D) = \<Sigma>\<^bsub>A\<^esub>(f ` D)"
  shows "\<mu>\<^bsub>A\<^esub>f = \<Sigma>\<^bsub>A\<^esub>(carrier (kleene_chain A f))"
proof -
  let ?C = "carrier (kleene_chain A f)"

  have chain_nest [simp]:
    "\<lparr>carrier = carrier (kleene_chain A f), le = op \<sqsubseteq>\<^bsub>A\<^esub>, \<dots> = ord.more A\<rparr> = kleene_chain A f"
    by (simp add: kleene_chain_def)

  have "\<bottom>\<^bsub>A\<^esub> \<in> ?C"
    by (simp add: kleene_chain_def, metis Lattice.iter.simps(1))
  hence chain_non_empty: "?C \<noteq> {}"
    by (metis empty_iff)

  have chain_directed: "directed (kleene_chain A f)"
    by (metis cl_A f_closed f_iso kleene_chain_total total_order_is_directed)

  have ord_A: "order A"
    by (metis cl_A cl_to_order)

  have ord_kle: "order (kleene_chain A f)"
    by (metis cl_A f_closed kleene_chain_order)

  have "\<exists>c::'a. order.is_lub A c ?C"
    by (metis cl_A cl_to_cjs complete_join_semilattice.lub_ex f_closed kleene_chain_closed)
  then obtain c :: 'a where c_lub: "order.is_lub A c ?C" by metis
  have "f c = f (\<Sigma>\<^bsub>A\<^esub>?C)"
    by (metis c_lub ord_A order.lub_is_lub)
  also have "... = \<Sigma>\<^bsub>A\<^esub>(f ` ?C)"
    by (metis chain_directed chain_nest chain_non_empty cl_A cl_to_cjs f_closed f_scott_continuous kleene_chain_closed)
  also have "... = \<Sigma>\<^bsub>A\<^esub>?C"
    by (metis cl_A f_closed f_iso kleene_chain_f_lub)
  also have "... = c"
    by (metis c_lub ord_A order.lub_is_lub)
  finally have c_is_fixpoint: "f c = c" by auto

  have "\<forall>a\<in>carrier A. f a = a \<longrightarrow> c \<sqsubseteq>\<^bsub>A\<^esub> a"
  proof clarify
    fix a assume a_is_fixpoint: "f a = a" and ac: "a \<in> carrier A"
    have "\<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> a"
      by (metis ac cl_A cl_to_cjs complete_join_semilattice.prop_bot)
    hence "\<forall>n. iter n f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> iter n f a"
      by (metis (lifting) ac cl_A cl_to_cjs complete_join_semilattice.bot_closed f_closed f_iso iter_iso use_iso1)
    hence iter_leq_a: "\<forall>n. iter n f \<bottom>\<^bsub>A\<^esub> \<sqsubseteq>\<^bsub>A\<^esub> a"
      by (metis a_is_fixpoint iter_fp)
    have "\<Sigma>\<^bsub>A\<^esub>?C \<sqsubseteq>\<^bsub>A\<^esub> \<Sigma>\<^bsub>A\<^esub>{a}"
    proof (rule complete_lattice.lub_set_leq, simp_all add: cl_A ac)
      show "carrier (kleene_chain A f) \<subseteq> carrier A"
        by (metis c_lub ord_A order.is_lub_simp)
      show "\<forall>x\<in>carrier (kleene_chain A f). x \<sqsubseteq>\<^bsub>A\<^esub> a"
        by (simp add: kleene_chain_def, clarsimp, metis iter_leq_a)
    qed
    hence "\<Sigma>\<^bsub>A\<^esub>?C \<sqsubseteq>\<^bsub>A\<^esub> a"
      by (smt ac ord_A order.singleton_lub)
    thus "c \<sqsubseteq>\<^bsub>A\<^esub> a"
      by (metis `\<Sigma>\<^bsub>A\<^esub>?C = c`)
  qed
  thus ?thesis
    by (metis c_is_fixpoint c_lub f_closed lfp_equality_var lub_in ord_A order.lub_is_lub)
qed

end
