header {* Boolean Algebras *}

theory Lattice
  imports Main Signatures
begin

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

context order
begin

definition is_ub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_ub x A \<longleftrightarrow> (\<forall>y\<in>A. y \<le> x)"

definition is_lub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_lub x A \<longleftrightarrow> is_ub x A \<and> (\<forall>y.(\<forall>z\<in>A. z \<le> y) \<longrightarrow> x \<le> y)"

lemma is_lub_equiv: "is_lub x A \<longleftrightarrow> (\<forall>z. (x \<le> z \<longleftrightarrow> (\<forall>y\<in>A. y \<le> z)))"
  by (metis is_lub_def is_ub_def order_refl order_trans)

lemma is_lub_unique: "is_lub x A \<longrightarrow> is_lub y A \<longrightarrow> x = y"
  by (metis antisym is_lub_def is_ub_def)

definition lub :: "'a set \<Rightarrow> 'a" ("\<Sigma>") where
  "\<Sigma> A = (THE x. is_lub x A)"

lemma the_lub_leq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<longrightarrow> z \<le> x\<rbrakk> \<Longrightarrow> \<Sigma> X \<le> x"
  by (metis is_lub_unique lub_def the_equality)

lemma singleton_lub: "\<Sigma> {y} = y"
  by (simp only: lub_def, rule the_equality, simp_all add: is_lub_def is_ub_def, metis eq_iff)

lemma surjective_lub: "surj \<Sigma>"
proof (simp only: surj_def, clarify)
  fix y
  show "\<exists>x. y = \<Sigma> x" by (metis singleton_lub)
qed

lemma lub_is_lub [elim?]: "is_lub w A \<Longrightarrow> \<Sigma> A = w"
  by (metis is_lub_unique lub_def the_equality)

definition is_lb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_lb x A \<longleftrightarrow> (\<forall>y\<in>A. x \<le> y)"

definition is_glb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_glb x A \<longleftrightarrow> is_lb x A \<and> (\<forall>y.(\<forall>z\<in>A. y \<le> z) \<longrightarrow> y \<le> x)"

lemma is_glb_equiv: "is_glb x A \<longleftrightarrow> (\<forall>z. (z \<le> x \<longleftrightarrow> (\<forall>y\<in>A. z \<le> y)))"
  by (metis is_glb_def is_lb_def order_refl order_trans)

lemma is_glb_unique: "is_glb x A \<longrightarrow> is_glb y A \<longrightarrow> x = y"
  by (metis antisym is_glb_def is_lb_def)

definition glb :: "'a set \<Rightarrow> 'a" ("\<Pi>") where
  "\<Pi> A = (THE x. is_glb x A)"

lemma the_glb_leq: "\<lbrakk>\<exists>z. is_glb z X; \<And>z. is_glb z X \<longrightarrow> x \<le> z\<rbrakk> \<Longrightarrow> x \<le> \<Pi> X"
  by (metis glb_def is_glb_unique the_equality)

lemma glb_is_glb [elim?]: "is_glb w A \<Longrightarrow> \<Pi> A = w"
by (metis is_glb_unique glb_def the_equality)

lemma is_glb_from_is_lub: "\<lbrakk>x \<in> A; is_lub x {b. \<forall>a\<in>A. b \<le> a}\<rbrakk> \<Longrightarrow> is_glb x A"
  by (simp add: is_lub_def is_ub_def is_glb_def is_lb_def)

end

definition ext_cup_junctive :: "('a::order \<Rightarrow> 'b::order) set" where
  "ext_cup_junctive f \<equiv> \<forall>X \<subseteq> UNIV. (\<exists>x. \<Sigma> X = x) \<longrightarrow> f (\<Sigma> X) = \<Sigma> (f ` X)"

class join_semilattice = order +
  assumes join_ex: "\<forall>x y. \<exists>z. is_lub z {x,y}"

class meet_semilattice = order +
  assumes meet_ex: "\<forall>x y. \<exists>z. is_glb z {x,y}"

class lattice = join_semilattice + meet_semilattice

class complete_join_semilattice = order +
  assumes  lub_ex: "\<exists>x. is_lub x A"
begin
  lemma bot_ax: "\<exists>!b. \<forall>x. b \<le> x" by (metis empty_iff eq_iff is_lub_def lub_ex)

  definition bot :: "'a" ("\<bottom>") where "\<bottom> \<equiv> THE x. \<forall> y. x \<le> y"

  lemma prop_bot: "\<forall>x. \<bottom> \<le> x"
    by (simp only: bot_def, rule the1I2, smt bot_ax, metis)

  lemma is_lub_lub [intro?]: "is_lub (\<Sigma> X) X"
  proof (unfold lub_def)
    from lub_ex obtain \<sigma> where "is_lub \<sigma> X" ..
    thus "is_lub (THE \<sigma>. is_lub \<sigma> X) X" by (metis lub_def lub_is_lub)
  qed

  lemma lub_greatest [intro?]: "(\<And>y. y \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> \<Sigma> X \<le> x"
    by (metis is_lub_eqiv is_lub_lub)

  lemma lub_least [intro?]: "x \<in> X \<Longrightarrow> x \<le> \<Sigma> X"
    by (metis is_lub_def is_lub_lub is_ub_def)

  lemma empty_lub: "\<Sigma> {} = \<bottom>" by (metis emptyE is_lub_eqiv lub_is_lub prop_bot)
end

class complete_meet_semilattice = order +
  assumes glb_ex: "\<exists>x. is_glb x A"
begin
  lemma top_ax: "\<exists>!t. \<forall>x. x \<le> t" by (metis empty_iff eq_iff glb_ex is_glb_def)

  definition top :: "'a" ("\<top>") where "\<top> \<equiv> THE x. \<forall> y. y \<le> x"

  lemma prop_top: "\<forall>x. x \<le> \<top>"
    by (simp only: top_def, rule the1I2, metis top_ax, metis)

 lemma is_glb_glb [intro?]: "is_glb (\<Pi> X) X"
  proof (unfold glb_def)
    from glb_ex obtain \<pi> where "is_glb \<pi> X" ..
    thus "is_glb (THE \<pi>. is_glb \<pi> X) X" by (metis glb_def glb_is_glb)
  qed

  lemma glb_greatest [intro?]: "(\<And>y. y \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> x \<le> \<Pi> X"
    by (metis is_glb_def is_glb_glb)

  lemma glb_least [intro?]: "x \<in> X \<Longrightarrow> \<Pi> X \<le> x"
    by (metis is_glb_def is_glb_glb is_lb_def)

  lemma empty_glb: "\<Pi> {} = \<top>" by (metis empty_iff glb_is_glb is_glb_def is_lb_def prop_top)
end

class complete_lattice = complete_join_semilattice + complete_meet_semilattice
begin
  lemma univ_lub: "\<Sigma> UNIV = \<top>" by (metis eq_iff is_lub_eqiv iso_tuple_UNIV_I lub_is_lub prop_top)

  lemma univ_glb: "\<Pi> UNIV = \<bottom>" by (metis eq_iff glb_is_glb is_glb_eqiv iso_tuple_UNIV_I prop_bot)
end

sublocale complete_meet_semilattice \<subseteq> meet_semilattice
  by (unfold_locales, metis glb_ex)

sublocale complete_join_semilattice \<subseteq> join_semilattice
  by (unfold_locales, metis lub_ex)

sublocale complete_lattice \<subseteq> lattice
  by unfold_locales

definition order_monomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_monomorphism f \<equiv> \<forall>x y. (f x \<le> f y) \<longleftrightarrow> (x \<le> y)"

definition order_isomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_isomorphism f \<equiv> order_monomorphism f \<and> surj f"

lemma order_monomorphism_inj: "order_monomorphism f \<Longrightarrow> inj f"
  by (simp add: order_monomorphism_def inj_on_def order_eq_iff)

end
