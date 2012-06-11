theory Lattice
  imports Main
begin

record 'a partial_object =
  carrier :: "'a set"

definition ftype :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<rightarrow>" 60) where
  "ftype A B \<equiv> {f. \<forall>x. x \<in> A \<longleftrightarrow> f x \<in> B}"

lemma ftype_pred: "(f \<in> A \<rightarrow> B) = (\<forall>x. x \<in> A \<longleftrightarrow> f x \<in> B)"
  by (simp add: ftype_def)

lemma closed_composition: "\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C\<rbrakk> \<Longrightarrow> g \<circ> f \<in> A \<rightarrow> C"
  by (simp add: ftype_def)

lemma closed_application: "\<lbrakk>x \<in> A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> f x \<in> B"
  by (simp add: ftype_def)

lemma id_poly: "id \<in> A \<rightarrow> A"
  by (simp add: ftype_def)

locale equivalence = fixes S (structure)
  assumes refl [simp, intro]: "x \<in> carrier S \<Longrightarrow> x = x"
  and sym [sym]: "\<lbrakk>x = y; x \<in> carrier S; y \<in> carrier S\<rbrakk> \<Longrightarrow> y = x"
  and trans [trans]: "\<lbrakk>x = y; y = z; x \<in> carrier S; y \<in> carrier S; z \<in> carrier S \<rbrakk> \<Longrightarrow> x = z"

record 'a ord = "'a partial_object" +
  le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>\<index>" 50)

locale order = equivalence A for A (structure) +
  assumes order_refl [intro, simp]: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> x"
  and order_trans: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z; x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  and antisym: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = y"

(* Inverse orders *)

definition ord_inv :: "'a ord \<Rightarrow> 'a ord" ("_\<sharp>" [1000] 100) where
  "ord_inv ordr \<equiv> \<lparr>carrier = carrier ordr, le = \<lambda>x y. le ordr y x\<rparr>"

lemma inv_carrier_id [simp]: "carrier (ord_inv A) = carrier A"
  by (metis ord_inv_def partial_object.simps(1))

lemma ord_to_inv: "order A \<Longrightarrow> order (ord_inv A)"
  by (default, simp_all add: ord_inv_def, (metis order.order_refl order.order_trans Lattice.order.antisym)+)

lemma inv_inv_id: "ord_inv (ord_inv A) = A"
  by (simp add: ord_inv_def)

lemma inv_to_ord: "order (ord_inv A) \<Longrightarrow> order A"
  by (metis inv_inv_id ord_to_inv)

lemma ord_is_inv [simp]: "order (ord_inv A) = order A"
  by (metis inv_to_ord ord_to_inv)

lemma inv_flip [simp]: "(x \<sqsubseteq>\<^bsub>ord_inv A\<^esub> y) = (y \<sqsubseteq>\<^bsub>A\<^esub> x)"
  by (simp add: ord_inv_def)

definition isotone :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "isotone A B f \<equiv> order A \<and> order B \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y)"

lemma use_iso1: "\<lbrakk>isotone A A f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>A\<^esub> f y"
  by (simp add: isotone_def)

lemma inv_isotone [simp]: "isotone (A\<sharp>) (B\<sharp>) f = isotone A B f"
  by (simp add: isotone_def, auto)

definition idempotent :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "idempotent A f \<equiv> \<forall>x\<in>A. (f \<circ> f) x = f x"

context order
begin

  lemma eq_refl: "\<lbrakk>x \<in> carrier A; x = x\<rbrakk> \<Longrightarrow> x \<sqsubseteq> x" by (metis order_refl)

  (* Least upper bounds *)

  definition is_ub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_ub x X \<equiv> (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x)"

  definition is_lub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lub x X \<equiv>  is_ub x X \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y)"

  lemma is_lub_simp: "is_lub x X = ((X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y))"
    by (simp add: is_lub_def is_ub_def)

  lemma is_lub_unique: "is_lub x X \<longrightarrow> is_lub y X \<longrightarrow> x = y"
    by (smt antisym is_lub_def is_ub_def)

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
    by (unfold lub_def, rule the_equality, simp_all add: is_lub_def is_ub_def, metis antisym order_refl)

  lemma surjective_lub: "\<forall>y\<in>carrier A. \<exists>X\<subseteq>carrier A. y = \<Sigma> X"
    by (metis bot_least insert_subset singleton_lub)

  lemma lub_subset: "\<lbrakk>X \<subseteq> Y; is_lub x X; is_lub y Y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
    by (metis (no_types) is_lub_def is_ub_def set_rev_mp)

  lemma lub_closed: "\<lbrakk>X \<subseteq> carrier A; \<exists>x. is_lub x X\<rbrakk> \<Longrightarrow> \<Sigma> X \<in> carrier A"
    by (rule_tac ?P = "\<lambda>x. is_lub x X" in the1I2, metis is_lub_unique, metis is_lub_def is_ub_def lub_is_lub)

  definition join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 70) where
    "x \<squnion> y = \<Sigma> {x,y}"

  (* Greatest lower bounds *)

  definition is_lb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lb x X \<equiv> (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y)"

  definition is_glb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_glb x X \<longleftrightarrow> is_lb x X \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x)"

  lemma is_glb_simp: "is_glb x X = ((X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x))"
     by (simp add: is_glb_def is_lb_def)

  lemma is_glb_unique: "is_glb x X \<longrightarrow> is_glb y X \<longrightarrow> x = y"
    by (smt antisym is_glb_def is_lb_def)

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
    by (unfold glb_def, rule the_equality, simp_all add: is_glb_def is_lb_def, metis antisym order_refl)

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
    by (metis antisym less_def)

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

end

abbreviation less_ext :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool" ("_\<sqsubset>\<^bsub>_\<^esub>_" [51,0,51] 50) where
  "x \<sqsubset>\<^bsub>A\<^esub> y \<equiv> order.less A x y"

abbreviation lub_ext :: "'a ord \<Rightarrow> 'a set \<Rightarrow> 'a" ("\<Sigma>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "\<Sigma>\<^bsub>A\<^esub>X \<equiv> order.lub A X"

abbreviation glb_ext :: "'a ord \<Rightarrow> 'a set \<Rightarrow> 'a" ("\<Pi>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "\<Pi>\<^bsub>A\<^esub>X \<equiv> order.glb A X"

definition ex_join_preserving :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "ex_join_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_lub A x X) \<longrightarrow> order.lub B (f ` X) = f (order.lub A X)))"

definition ex_meet_preserving :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "ex_meet_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_glb A x X) \<longrightarrow> order.glb B (f ` X) = f (order.glb A X)))"

definition join_preserving :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "join_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. order.lub B (f ` X) = f (order.lub A X))"

definition meet_preserving :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "meet_preserving A B g \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. order.glb B (g ` X) = g (order.glb A X))"

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

(* +------------------------------------------------------------------------+
   | Join semilattices                                                      |
   +------------------------------------------------------------------------+ *)

locale join_semilattice = order +
  assumes join_ex: "\<lbrakk>x \<in> carrier A; y\<in>carrier A\<rbrakk> \<Longrightarrow> \<exists>z\<in>carrier A. is_lub z {x,y}"

context join_semilattice
begin

  lemma leq_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) \<longleftrightarrow> (x \<squnion> y = y)"
    apply (simp add: join_def lub_def)
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and xy: "x \<sqsubseteq> y"
    show "(THE z. is_lub z {x,y}) = y"
      by (rule the_equality, simp_all add: is_lub_def is_ub_def, safe, (metis x_closed y_closed xy order_refl antisym)+)
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
      by (smt join_closed antisym bin_lub_var order_refl x_closed y_closed z_closed)
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
      by (smt join_semilattice.leq_def_left js_B closed_application f_closed xc yc ord_B order.join_def)
  qed

  thus ?thesis by (metis isotone_def ord_A ord_B)
qed

(* +------------------------------------------------------------------------+
   | Meet semilattices                                                      |
   +------------------------------------------------------------------------+ *)

locale meet_semilattice = order +
  assumes meet_ex: "\<lbrakk>x \<in> carrier A; y\<in>carrier A\<rbrakk> \<Longrightarrow> \<exists>z\<in>carrier A. is_glb z {x,y}"

context meet_semilattice
begin

  lemma leq_meet_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) \<longleftrightarrow> (x \<sqinter> y = x)"
    apply (simp add: meet_def glb_def)
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and xy: "x \<sqsubseteq> y"
    show "(THE z. is_glb z {x,y}) = x"
      by (rule the_equality, simp_all add: is_glb_def is_lb_def, safe, (metis x_closed y_closed xy order_refl antisym)+)
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
      by (smt meet_closed antisym bin_glb_var order_refl x_closed y_closed z_closed)
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

(* +------------------------------------------------------------------------+
   | Lattices                                                               |
   +------------------------------------------------------------------------+ *)

locale lattice = join_semilattice + meet_semilattice

begin

  lemma absorb1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> (x \<sqinter> y) = x"
    by (metis join_comm leq_def leq_meet_def meet_assoc meet_closed meet_comm meet_idem)

  lemma absorb2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> (x \<squnion> y) = x"
    by (metis join_assoc join_closed join_comm join_idem leq_def leq_meet_def)

  lemma order_change: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<sqinter>y = y \<longleftrightarrow> y\<squnion>x = x"
    by (metis leq_def leq_meet_def meet_comm)

end

lemma inv_lattice [simp]: "lattice (A\<sharp>) = lattice A"
  by (simp add: lattice_def, auto)

(* +------------------------------------------------------------------------+
   | Complete join semilattices                                             |
   +------------------------------------------------------------------------+ *)

locale complete_join_semilattice = order +
  assumes lub_ex: "\<lbrakk>X \<subseteq> carrier A\<rbrakk> \<Longrightarrow> \<exists>x\<in>carrier A. is_lub x X"

sublocale complete_join_semilattice \<subseteq> join_semilattice
  by default (metis bot_least insert_subset lub_ex)

context complete_join_semilattice
begin

  lemma bot_ax: "\<exists>!b\<in>carrier A. \<forall>x\<in>carrier A. b \<sqsubseteq> x"
    by (metis (no_types) antisym bot_least equals0D is_lub_def lub_ex)

  definition bot :: "'a" ("\<bottom>") where "\<bottom> \<equiv> THE x. x\<in>carrier A \<and> (\<forall>y\<in>carrier A. x \<sqsubseteq> y)"

  lemma bot_closed: "\<bottom> \<in> carrier A" by (smt bot_def the1I2 bot_ax)

  lemma prop_bot: "\<forall>x\<in>carrier A. \<bottom> \<sqsubseteq> x"
    by (simp only: bot_def, rule the1I2, smt bot_ax, metis)

  lemma is_lub_lub [intro?]: "X \<subseteq> carrier A \<Longrightarrow> is_lub (\<Sigma> X) X"
    by (metis lub_ex lub_is_lub)

  lemma lub_greatest [intro?]: "\<lbrakk>x \<in> carrier A; X \<subseteq> carrier A; \<forall>y\<in>X. y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> \<Sigma> X \<sqsubseteq> x"
    by (metis is_lub_def is_lub_lub)

  lemma lub_least [intro?]: "\<lbrakk>X \<subseteq> carrier A; x \<in> X\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Sigma> X"
    by (metis is_lub_def is_lub_lub is_ub_def)

  lemma empty_lub [simp]: "\<Sigma> {} = \<bottom>"
    by (metis antisym bot_closed bot_least lub_ex lub_is_lub lub_subset prop_bot surjective_lub)

  lemma bot_oner [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> \<bottom> = x"
    by (metis join_comm bot_closed leq_def prop_bot)

  lemma bot_onel [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> \<bottom> \<squnion> x = x"
    by (metis join_comm bot_oner)

end

(* +------------------------------------------------------------------------+
   | Complete meet semilattices                                             |
   +------------------------------------------------------------------------+ *)

locale complete_meet_semilattice = order +
  assumes glb_ex: "\<lbrakk>X \<subseteq> carrier A\<rbrakk> \<Longrightarrow> \<exists>x\<in>carrier A. is_glb x X"

sublocale complete_meet_semilattice \<subseteq> meet_semilattice
  by default (metis bot_least insert_subset glb_ex)

context complete_meet_semilattice
begin

  lemma top_ax: "\<exists>!t\<in>carrier A. \<forall>x\<in>carrier A. x \<sqsubseteq> t"
    by (metis (no_types) antisym bot_least equals0D glb_ex is_glb_def)

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
    by (metis antisym bot_least glb_closed glb_is_glb glb_subset insert_absorb2 is_glb_glb meet_def meet_ex prop_top singleton_glb subset_insertI top_closed)

  lemma top_oner [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> \<top> = x"
    by (metis meet_comm top_closed leq_meet_def prop_top)

  lemma top_onel [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> \<top> \<sqinter> x = x"
    by (metis meet_comm top_oner)

end

lemma inv_cms_is_cjs [simp]: "complete_meet_semilattice (A\<sharp>) = complete_join_semilattice A"
  by (simp add: complete_meet_semilattice_def complete_join_semilattice_def complete_meet_semilattice_axioms_def complete_join_semilattice_axioms_def, safe, simp_all)

lemma inv_cjs_is_cms [simp]: "complete_join_semilattice (A\<sharp>) = complete_meet_semilattice A"
  by (simp add: complete_meet_semilattice_def complete_join_semilattice_def complete_meet_semilattice_axioms_def complete_join_semilattice_axioms_def, safe, simp_all)

(* +------------------------------------------------------------------------+
   | Complete Lattices                                                      |
   +------------------------------------------------------------------------+ *)

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
  apply metis
  apply metis
  apply metis
  apply (metis cl_to_order order.order_refl)
  apply (metis cl_to_order order.order_trans)
  apply (metis Lattice.order.antisym cl_to_order)
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

end

definition is_pre_fp :: "'a ord \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_pre_fp A x f \<equiv> order A \<and> f \<in> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> f x \<sqsubseteq>\<^bsub>A\<^esub> x"

definition is_post_fp :: "'a ord \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_post_fp A x f \<equiv> order A \<and> f \<in> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> x \<sqsubseteq>\<^bsub>A\<^esub> f x"

lemma is_pre_fp_dual [simp]: "is_pre_fp (A\<sharp>) x f = is_post_fp A x f"
  by (simp add: is_pre_fp_def is_post_fp_def)

lemma is_post_fp_dual [simp]: "is_post_fp (A\<sharp>) x f = is_pre_fp A x f"
  by (simp add: is_pre_fp_def is_post_fp_def)

definition is_fp :: "'a ord \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_fp A x f \<equiv> order A \<and> f \<in> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> f x = x"

lemma is_fp_dual [simp]: "is_fp (A\<sharp>) x f = is_fp A x f"
  by (simp add: is_fp_def)

lemma is_fp_def_var: "is_fp A x f = (is_pre_fp A x f \<and> is_post_fp A x f)"
  by (simp add: is_fp_def is_pre_fp_def is_post_fp_def, metis Lattice.order.antisym closed_application order.order_refl)

definition is_lpp :: "'a ord \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lpp A x f \<equiv> (is_pre_fp A x f) \<and> (\<forall>y\<in>carrier A. f y \<sqsubseteq>\<^bsub>A\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y)"

definition is_gpp :: "'a ord \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_gpp A x f \<equiv> (is_post_fp A x f) \<and> (\<forall>y\<in>carrier A. y \<sqsubseteq>\<^bsub>A\<^esub> f y \<longrightarrow> y \<sqsubseteq>\<^bsub>A\<^esub> x)"

lemma is_lpp_dual [simp]: "is_lpp (A\<sharp>) x f = is_gpp A x f"
  by (simp add: is_gpp_def is_lpp_def)

lemma is_gpp_dual [simp]: "is_gpp (A\<sharp>) x f = is_lpp A x f"
  by (simp add: is_lpp_def is_gpp_def)

definition is_lfp :: "'a ord \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lfp A x f \<equiv> is_fp A x f \<and> (\<forall>y\<in>carrier A. is_fp A y f \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y)"

lemma is_lfp_closed: "is_lfp A x f \<Longrightarrow> f \<in> carrier A \<rightarrow> carrier A"
  by (metis (no_types) is_fp_def is_lfp_def)

definition is_gfp :: "'a ord \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
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

definition least_fixpoint :: "'a ord \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "least_fixpoint A f \<equiv> THE x. is_lfp A x f"

definition greatest_fixpoint :: "'a ord \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "greatest_fixpoint A f \<equiv> THE x. is_gfp A x f"

lemma least_fixpoint_dual [simp]: "\<mu>\<^bsub>(A\<sharp>)\<^esub>f = \<nu>\<^bsub>A\<^esub>f"
  by (simp add: least_fixpoint_def greatest_fixpoint_def)

lemma greatest_fixpoint_dual [simp]: "\<nu>\<^bsub>(A\<sharp>)\<^esub>f = \<mu>\<^bsub>A\<^esub>f"
  by (simp add: least_fixpoint_def greatest_fixpoint_def)

lemma lpp_unique: "\<lbrakk>is_lpp A x f; is_lpp A y f\<rbrakk> \<Longrightarrow> x = y"
  by (smt Lattice.order.antisym is_lpp_def is_pre_fp_def)

lemma gpp_unique: "\<lbrakk>is_gpp A x f; is_gpp A y f\<rbrakk> \<Longrightarrow> x = y"
  by (smt Lattice.order.antisym is_gpp_def is_post_fp_def)

lemma lpp_equality [intro?]: "is_lpp A x f \<Longrightarrow> \<mu>\<^bsub>\<le>A\<^esub> f = x"
  by (simp add: least_prefix_point_def, rule the_equality, auto, smt Lattice.order.antisym is_lpp_def is_pre_fp_def)

lemma gpp_equality [intro?]: "is_gpp A x f \<Longrightarrow> \<nu>\<^bsub>\<le>A\<^esub> f = x"
  by (simp add: greatest_postfix_point_def, rule the_equality, auto, smt Lattice.order.antisym is_gpp_def is_post_fp_def)

lemma lfp_equality: "is_lfp A x f \<Longrightarrow> \<mu>\<^bsub>A\<^esub> f = x"
  by (simp add: least_fixpoint_def, rule the_equality, auto, smt Lattice.order.antisym is_fp_def is_lfp_def)

lemma lfp_equality_var [intro?]: "\<lbrakk>order A; f \<in> carrier A \<rightarrow> carrier A; x \<in> carrier A; f x = x; \<forall>y \<in> carrier A. f y = y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> x = \<mu>\<^bsub>A\<^esub> f"
  by (smt is_fp_def is_lfp_def lfp_equality)

lemma gfp_equality: "is_gfp A x f \<Longrightarrow> \<nu>\<^bsub>A\<^esub> f = x"
  by (simp add: greatest_fixpoint_def, rule the_equality, auto, smt Lattice.order.antisym is_gfp_def is_fp_def)

lemma gfp_equality_var [intro?]: "\<lbrakk>order A; f \<in> carrier A \<rightarrow> carrier A; x \<in> carrier A; f x = x; \<forall>y \<in> carrier A. f y = y \<longrightarrow> y \<sqsubseteq>\<^bsub>A\<^esub> x\<rbrakk> \<Longrightarrow> x = \<nu>\<^bsub>A\<^esub> f"
  by (smt gfp_equality is_fp_def is_gfp_def)

lemma lpp_is_lfp: "\<lbrakk>isotone A A f; is_lpp A x f\<rbrakk> \<Longrightarrow> is_lfp A x f"
  by (simp add: isotone_def is_lpp_def is_pre_fp_def is_lfp_def is_fp_def, metis Lattice.order.antisym order.order_refl closed_application)

lemma gpp_is_gfp: "\<lbrakk>isotone A A f; is_gpp A x f\<rbrakk> \<Longrightarrow> is_gfp A x f"
  by (simp add: isotone_def is_gpp_def is_post_fp_def is_gfp_def is_fp_def, smt Lattice.order.antisym order.order_refl closed_application)

lemma least_fixpoint_set: "\<lbrakk>\<exists>x. is_lfp A x f\<rbrakk> \<Longrightarrow> \<mu>\<^bsub>A\<^esub> f \<in> carrier A"
  by (simp add: least_fixpoint_def, rule the1I2, metis lfp_equality, metis is_lfp_def is_fp_def)

lemma greatest_fixpoint_set: "\<lbrakk>\<exists>x. is_gfp A x f\<rbrakk> \<Longrightarrow> \<nu>\<^bsub>A\<^esub> f \<in> carrier A"
  by (unfold is_lfp_dual[symmetric] least_fixpoint_dual[symmetric], metis inv_carrier_id least_fixpoint_set)

(* +------------------------------------------------------------------------+
   | Knaster-Tarski for least fixed points                                  |
   +------------------------------------------------------------------------+ *)

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
    hence "\<forall>x\<in>?H. f ?a \<sqsubseteq>\<^bsub>A\<^esub> x" by (smt CollectD a_carrier cl_A cl_to_order closed_application f_closed order.order_trans)
    hence "f ?a \<sqsubseteq>\<^bsub>A\<^esub> ?a" by (smt complete_meet_semilattice.glb_greatest cl_A cl_to_cms a_carrier f_closed H_carrier closed_application)
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
  by (smt is_lpp_lpp lfp_equality lpp_is_lfp)

corollary is_lfp_lfp [intro?]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> is_lfp A (\<mu>\<^bsub>A\<^esub> f) f"
  by (smt knaster_tarski lfp_equality)

(* +------------------------------------------------------------------------+
   | Knaster-Tarski for greatest fixed points                               |
   +------------------------------------------------------------------------+ *)

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
  by (smt is_gpp_gpp gfp_equality gpp_is_gfp)

corollary is_gfp_gfp [intro?]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> is_gfp A (\<nu>\<^bsub>A\<^esub> f) f"
  by (smt knaster_tarski_greatest gfp_equality)

(* +------------------------------------------------------------------------+
   | Fixpoint Computation                                                   |
   +------------------------------------------------------------------------+ *)

lemma prefix_point_computation [simp]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<mu>\<^bsub>\<le>A\<^esub> f) = \<mu>\<^bsub>\<le>A\<^esub> f"
  by (smt is_fp_def is_lfp_def is_lpp_lpp lpp_is_lfp)

lemma fixpoint_computation [simp]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<mu>\<^bsub>A\<^esub> f) = \<mu>\<^bsub>A\<^esub> f"
  by (smt is_lpp_lpp lfp_equality lpp_is_lfp prefix_point_computation)

lemma greatest_postfix_point_computation [simp]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<nu>\<^bsub>\<le>A\<^esub> f) = \<nu>\<^bsub>\<le>A\<^esub> f"
  by (smt is_gpp_gpp gpp_is_gfp is_gfp_def is_fp_def)

lemma greatest_fixpoint_computation [simp]:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<nu>\<^bsub>A\<^esub> f) = \<nu>\<^bsub>A\<^esub> f"
  by (smt is_gpp_gpp gfp_equality gpp_is_gfp greatest_postfix_point_computation)

(* +------------------------------------------------------------------------+
   | Fixpoint Induction                                                     |
   +------------------------------------------------------------------------+ *)

lemma prefix_point_induction [intro?]:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and x_carrier: "x \<in> carrier A" and f_iso: "isotone A A f"
  and pp: "f x \<sqsubseteq>\<^bsub>A\<^esub> x" shows "\<mu>\<^bsub>\<le>A\<^esub> f \<sqsubseteq>\<^bsub>A\<^esub> x"
  by (smt f_closed f_iso cl_A is_lpp_def is_lpp_lpp pp x_carrier)

lemma fixpoint_induction [intro?]:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and x_carrier: "x \<in> carrier A" and f_iso: "isotone A A f"
  and fp: "f x \<sqsubseteq>\<^bsub>A\<^esub> x" shows "\<mu>\<^bsub>A\<^esub> f \<sqsubseteq>\<^bsub>A\<^esub> x"
  by (smt f_closed f_iso fp is_lpp_def is_lpp_lpp lfp_equality lpp_is_lfp x_carrier cl_A)

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

lemma fixpoint_compose:
  assumes f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and g_closed: "g \<in> carrier A \<rightarrow> carrier A"
  and k_closed: "k \<in> carrier A \<rightarrow> carrier A"
  and x_carrier: "x \<in> carrier A" and k_iso: "isotone A A k"
  and comp: "g\<circ>k = k\<circ>h" and fp: "is_fp A x h"
  shows "is_fp A (k x) g"
  using fp and comp by (simp add: is_fp_def o_def, safe, (metis g_closed k_closed closed_application)+)

lemma fixpoint_mono:
  assumes cl_A: "complete_lattice A"
  and f_closed: "f \<in> carrier A \<rightarrow> carrier A" and g_closed: "g \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f" and g_iso: "isotone A A g"
  and fg: "\<forall>x\<in>carrier A. f x \<sqsubseteq>\<^bsub>A\<^esub> g x" shows "\<mu>\<^bsub>A\<^esub> f \<sqsubseteq>\<^bsub>A\<^esub> \<mu>\<^bsub>A\<^esub> g"
  by (smt f_closed f_iso fg fixpoint_computation g_closed g_iso is_lpp_def is_pre_fp_def knaster_tarski_lpp lfp_equality lpp_is_lfp cl_A)

lemma greatest_fixpoint_mono:
  assumes cl_A: "complete_lattice A" and f_closed: "f \<in> carrier A \<rightarrow> carrier A"
  and g_closed: "g \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  and g_iso: "isotone A A g"
  and fg: "\<forall>x\<in>carrier A. f x \<sqsubseteq>\<^bsub>A\<^esub> g x" shows "\<nu>\<^bsub>A\<^esub> f \<sqsubseteq>\<^bsub>A\<^esub> \<nu>\<^bsub>A\<^esub> g"
  by (smt f_closed f_iso fg g_closed g_iso gfp_equality gpp_is_gfp greatest_fixpoint_computation is_gpp_def is_post_fp_def knaster_tarski_gpp cl_A)

end

