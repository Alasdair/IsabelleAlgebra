theory Lattice
  imports Main
begin

record 'a partial_object =
  carrier :: "'a set"

abbreviation closed :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("_\<Colon>_\<rightarrow>_") where
  "closed f A B \<equiv> (\<forall>x. x \<in> A \<longleftrightarrow> f x \<in> B)"

lemma closed_composition: "\<lbrakk>f \<Colon> A \<rightarrow> B; g \<Colon> B \<rightarrow> C\<rbrakk> \<Longrightarrow> g \<circ> f \<Colon> A \<rightarrow> C"
  by (metis o_apply)

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

definition isotone :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "isotone A B f \<equiv> order A \<and> order B \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y)"

definition idempotent :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) set" where
  "idempotent A f \<equiv> \<forall>x\<in>A. (f \<circ> f) x = f x"

context order
begin

  lemma eq_refl: "\<lbrakk>x \<in> carrier A; x = x\<rbrakk> \<Longrightarrow> x \<sqsubseteq> x" by (metis order_refl)

  (* Least upper bounds *)

  definition is_ub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_ub x X \<equiv> (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x)"

  definition is_lub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lub x X \<equiv>  is_ub x X \<and> (\<forall>y.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y)"

  lemma is_lub_unique: "is_lub x X \<longrightarrow> is_lub y X \<longrightarrow> x = y"
    by (smt antisym is_lub_def is_ub_def)

  definition lub :: "'a set \<Rightarrow> 'a" ("\<Sigma>") where
    "\<Sigma> X = (THE x. is_lub x X)"

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

  lemma lub_subset: "\<lbrakk>X \<subseteq> Y; is_lub x X; is_lub y Y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y" by (metis in_mono is_lub_def is_ub_def)

  lemma lub_closed: "\<lbrakk>X \<subseteq> carrier A; \<exists>x. is_lub x X\<rbrakk> \<Longrightarrow> \<Sigma> X \<in> carrier A"
    by (rule_tac ?P = "\<lambda>x. is_lub x X" in the1I2, metis is_lub_unique, metis is_lub_def is_ub_def lub_is_lub)

  definition join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 70) where
    "x \<squnion> y = \<Sigma> {x,y}"

  (* Greatest lower bounds *)

  definition is_lb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lb x X \<equiv> (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y)"

  definition is_glb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_glb x X \<longleftrightarrow> is_lb x X \<and> (\<forall>y.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x)"

  lemma is_glb_unique: "is_glb x X \<longrightarrow> is_glb y X \<longrightarrow> x = y"
    by (smt antisym is_glb_def is_lb_def)

  definition glb :: "'a set \<Rightarrow> 'a" ("\<Pi>") where
    "\<Pi> X = (THE x. is_glb x X)"

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

  lemma glb_subset: "\<lbrakk>X \<subseteq> Y; is_glb x X; is_glb y Y\<rbrakk> \<Longrightarrow> y \<sqsubseteq> x" by (metis in_mono is_glb_def is_lb_def)

  lemma glb_closed: "\<lbrakk>X \<subseteq> carrier A; \<exists>x. is_glb x X\<rbrakk> \<Longrightarrow> \<Pi> X \<in> carrier A"
    by (rule_tac ?P = "\<lambda>x. is_glb x X" in the1I2, metis is_glb_unique, metis is_glb_def is_lb_def glb_is_glb)

  definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70) where
    "x \<sqinter> y = \<Pi> {x,y}"

  (* Duality of lubs and glbs *)

  (*
  lemma is_glb_from_is_lub: "\<lbrakk>X \<subseteq> carrier A; x \<in> carrier A; is_lub x {b. \<forall>a\<in>X. b \<sqsubseteq> a}\<rbrakk> \<Longrightarrow> is_glb x X"

  lemma is_lub_from_is_glb: "\<lbrakk>is_glb x {b. \<forall>a\<in>A. a \<le> b}\<rbrakk> \<Longrightarrow> is_lub x A"
    by (smt Collect_def is_lub_def is_ub_def is_glb_equiv mem_def order_refl)
    *)

  (* Join and meet preserving functions *)

  definition join_preserving :: "('a \<Rightarrow> 'a) set" where
    "join_preserving f \<equiv> \<forall>X\<subseteq>carrier A. \<Sigma> (f ` X) = f (\<Sigma> X)"

  definition meet_preserving :: "('a \<Rightarrow> 'a) set" where
    "meet_preserving g \<equiv> \<forall>X\<subseteq>carrier A. \<Pi> (g ` X) = g (\<Pi> X)"

end

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

  lemma add_idem: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> x = x" by (metis leq_def order_refl)

  lemma add_comm: "x \<squnion> y = y \<squnion> x" by (metis insert_commute join_def)

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

  lemma add_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> y \<in> carrier A"
    by (metis join_def join_ex lub_is_lub)

  lemma add_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  proof -
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    hence "(x \<squnion> y) \<squnion> z \<sqsubseteq> x \<squnion> (y \<squnion> z)"
      by (metis eq_refl bin_lub_var add_closed)
    thus ?thesis
      by (smt add_closed antisym bin_lub_var order_refl x_closed y_closed z_closed)
  qed

end

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
    by (metis (full_types) antisym bot_least empty_iff is_lub_def lub_ex)

  definition bot :: "'a" ("\<bottom>") where "\<bottom> \<equiv> THE x. x\<in>carrier A \<and> (\<forall>y\<in>carrier A. x \<sqsubseteq> y)"

  lemma bot_closed: "\<bottom> \<in> carrier A" by (smt bot_def the1I2 bot_ax)

  lemma prop_bot: "\<forall>x\<in>carrier A. \<bottom> \<sqsubseteq> x"
    by (simp only: bot_def, rule the1I2, smt bot_ax, metis)

  lemma is_lub_lub [intro?]: "X \<subseteq> carrier A \<Longrightarrow> is_lub (\<Sigma> X) X"
    by (metis lub_ex lub_is_lub)

(*
  lemma lub_greatest [intro?]: "\<And>y. \<lbrakk>x \<in> carrier A; y \<in> carrier A; X \<subseteq> carrier A; y \<in> X; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> \<Sigma> X \<sqsubseteq> x"
    apply (rule the_lub_leq)
apply (metis lub_ex)
    nitpick
    by (metis is_lub_equiv is_lub_lub)
*)

  lemma lub_least [intro?]: "\<lbrakk>X \<subseteq> carrier A; x \<in> X\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Sigma> X"
    by (metis is_lub_def is_lub_lub is_ub_def)

  lemma empty_lub [simp]: "\<Sigma> {} = \<bottom>"
    by (metis antisym bot_closed bot_least lub_ex lub_is_lub lub_subset prop_bot surjective_lub)

  lemma bot_oner [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> \<bottom> = x"
    by (metis add_comm bot_closed leq_def prop_bot)

  lemma bot_onel [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> \<bottom> \<squnion> x = x"
    by (metis add_comm bot_oner)

end

(* +------------------------------------------------------------------------+
   | Lattices                                                               |
   +------------------------------------------------------------------------+ *)

locale lattice = join_semilattice + meet_semilattice

begin

  lemma absorb1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> (x \<sqinter> y) = x"
    by (metis add_comm leq_def leq_meet_def meet_assoc meet_closed meet_comm meet_idem)

  lemma absorb2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> (x \<squnion> y) = x"
    by (metis add_assoc add_closed add_comm add_idem leq_def leq_meet_def)

  lemma order_change: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<sqinter>y = y \<longleftrightarrow> y\<squnion>x = x"
    by (metis leq_def leq_meet_def meet_comm)

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

(*
  lemma glb_greatest [intro?]: "\<And>y. \<lbrakk>X \<subseteq> carrier A; y \<in> X; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Pi> X" nitpick
    apply (rule the_glb_leq)
    apply (metis glb_ex)
    nitpick
    by (metis is_glb_equiv is_glb_glb)
*)

  lemma glb_least [intro?]: "\<lbrakk>X \<subseteq> carrier A; x \<in> X\<rbrakk> \<Longrightarrow> \<Pi> X \<sqsubseteq> x"
    by (metis is_glb_def is_glb_glb is_lb_def)

  lemma empty_glb [simp]: "\<Pi> {} = \<top>"
    by (metis antisym bot_least glb_closed glb_is_glb glb_subset insert_absorb2 is_glb_glb meet_def meet_ex prop_top singleton_glb subset_insertI top_closed)

  lemma top_oner [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> \<top> = x"
    by (metis meet_comm top_closed leq_meet_def prop_top)

  lemma top_onel [simp]: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> \<top> \<sqinter> x = x"
    by (metis meet_comm top_oner)

end

(* +------------------------------------------------------------------------+
   | Complete Lattices                                                      |
   +------------------------------------------------------------------------+ *)

locale complete_lattice = complete_join_semilattice + complete_meet_semilattice

sublocale complete_lattice \<subseteq> lattice
  by unfold_locales

context complete_lattice
begin

  lemma univ_lub: "\<Sigma> (carrier A) = \<top>"
    by (metis is_lub_def is_lub_lub is_ub_def prop_top subset_refl top_ax top_closed)

  lemma univ_glb: "\<Pi> (carrier A) = \<bottom>"
    by (metis bot_ax bot_closed is_glb_def is_glb_glb is_lb_def prop_bot subset_refl)

  definition is_pre_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_pre_fp x f \<equiv> f \<Colon> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> f x \<sqsubseteq> x"

  definition is_post_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_post_fp x f \<equiv> f \<Colon> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> x \<sqsubseteq> f x"

  definition is_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_fp x f \<equiv> f \<Colon> carrier A \<rightarrow> carrier A \<and> x \<in> carrier A \<and> f x = x"

  lemma is_fp_def_var: "is_fp x f = (is_pre_fp x f \<and> is_post_fp x f)"
    by (simp add: is_fp_def is_pre_fp_def is_post_fp_def, metis antisym order_refl)

  definition is_lpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_lpp x f \<equiv> (is_pre_fp x f) \<and> (\<forall>y\<in>carrier A. f y \<sqsubseteq> y \<longrightarrow> x \<sqsubseteq> y)"

  definition is_gpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_gpp x f \<equiv> (is_post_fp x f) \<and> (\<forall>y\<in>carrier A. y \<sqsubseteq> f y \<longrightarrow> y \<sqsubseteq> x)"

  definition is_lfp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_lfp x f \<equiv> is_fp x f \<and> (\<forall>y\<in>carrier A. is_fp y f \<longrightarrow> x \<sqsubseteq> y)"

  definition is_gfp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_gfp x f \<equiv> is_fp x f \<and> (\<forall>y\<in>carrier A. is_fp y f \<longrightarrow> y \<sqsubseteq> x)"

  definition least_prefix_point :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>\<^sub>\<le>") where
    "least_prefix_point f \<equiv> THE x. is_lpp x f"

  definition greatest_postfix_point :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>\<^sub>\<le>") where
    "greatest_postfix_point f \<equiv> THE x. is_gpp x f"

  definition least_fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>") where
    "least_fixpoint f \<equiv> THE x. is_lfp x f"

  definition greatest_fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>") where
    "greatest_fixpoint f \<equiv> THE x. is_gfp x f"

  lemma lpp_unique: "\<lbrakk>is_lpp x f; is_lpp y f\<rbrakk> \<Longrightarrow> x = y"
    by (metis antisym is_lpp_def is_pre_fp_def)

  lemma gpp_unique: "\<lbrakk>is_gpp x f; is_gpp y f\<rbrakk> \<Longrightarrow> x = y"
    by (metis antisym is_gpp_def is_post_fp_def)

  lemma lpp_equality [intro?]: "is_lpp x f \<Longrightarrow> \<mu>\<^sub>\<le> f = x"
    by (simp add: least_prefix_point_def, rule the_equality, auto, metis antisym is_lpp_def is_pre_fp_def)

  lemma gpp_equality [intro?]: "is_gpp x f \<Longrightarrow> \<nu>\<^sub>\<le> f = x"
    by (simp add: greatest_postfix_point_def, rule the_equality, auto, metis antisym is_gpp_def is_post_fp_def)

  lemma lfp_equality: "is_lfp x f \<Longrightarrow> \<mu> f = x"
    by (simp add: least_fixpoint_def, rule the_equality, auto, metis antisym is_fp_def is_lfp_def)

  lemma lfp_equality_var [intro?]: "\<lbrakk>f \<Colon> carrier A \<rightarrow> carrier A; x \<in> carrier A; f x = x; \<forall>y\<in>carrier A. f y = y \<longrightarrow> x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x = \<mu> f"
    by (metis is_fp_def is_lfp_def lfp_equality)

  lemma gfp_equality: "is_gfp x f \<Longrightarrow> \<nu> f = x"
    by (simp add: greatest_fixpoint_def, rule the_equality, auto, metis antisym is_gfp_def is_fp_def)

  lemma gfp_equality_var [intro?]: "\<lbrakk>f \<Colon> carrier A \<rightarrow> carrier A; x \<in> carrier A; f x = x; \<forall>y\<in>carrier A. f y = y \<longrightarrow> y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = \<nu> f"
    by (metis gfp_equality is_fp_def is_gfp_def)

  lemma lpp_is_lfp: "\<lbrakk>isotone (truncate A) (truncate A) f; is_lpp x f\<rbrakk> \<Longrightarrow> is_lfp x f"
    by (simp add: isotone_def truncate_def order_def order_axioms_def is_lpp_def is_pre_fp_def is_lfp_def is_fp_def)

  lemma gpp_is_gfp: "\<lbrakk>isotone (truncate A) (truncate A) f; is_gpp x f\<rbrakk> \<Longrightarrow> is_gfp x f"
    by (simp add: isotone_def truncate_def order_def order_axioms_def is_gpp_def is_post_fp_def is_gfp_def is_fp_def)

  lemma use_iso: "\<lbrakk>isotone (truncate A) (truncate A) f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y"
    by (simp add: isotone_def truncate_def)

  theorem knaster_tarski_lpp:
    assumes f_closed: "f \<Colon> carrier A \<rightarrow> carrier A"
    and f_iso: "isotone (truncate A) (truncate A) f"
    obtains a where "is_lpp a f"
  proof
    let ?H = "{u. f u \<sqsubseteq> u \<and> u \<in> carrier A}"
    let ?a = "\<Pi> ?H"

    have H_carrier: "?H \<subseteq> carrier A" by (default, simp add: Collect_def mem_def)
    hence a_carrier: "?a \<in> carrier A" by (metis (no_types) is_glb_def is_glb_glb is_lb_def)

    have f_iso_var: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y" using f_iso
      by (simp add: isotone_def truncate_def)

    have "is_pre_fp ?a f"
    proof -
      have "\<forall>x\<in>?H. ?a \<sqsubseteq> x" by (smt H_carrier glb_least)
      hence "\<forall>x\<in>?H. f ?a \<sqsubseteq> f x" by (safe, rule_tac ?f = f in use_iso, metis f_iso, metis a_carrier, auto)
      hence "\<forall>x\<in>?H. f ?a \<sqsubseteq> x" by (smt Collect_def a_carrier f_closed mem_def order_trans)
      hence "f ?a \<sqsubseteq> \<Pi> ?H" 
      thus ?thesis by (metis is_pre_fp_def)
    qed
    moreover have "f y \<le> y \<Longrightarrow> ?a \<le> y"
      by (metis Collect_def glb_least mem_def)
    ultimately show "is_lpp ?a f"
      by (smt is_lpp_def Collect_def glb_least mem_def)
  qed

end
