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

lemma is_lub_eqiv: "is_lub x A \<longleftrightarrow> (\<forall>z. (x \<le> z \<longleftrightarrow> (\<forall>y\<in>A. y \<le> z)))"
  by (metis is_lub_def is_ub_def order_refl order_trans)

lemma is_lub_unique: "is_lub x A \<longrightarrow> is_lub y A \<longrightarrow> x = y"
  by (metis antisym is_lub_def is_ub_def)

definition lub :: "'a set \<Rightarrow> 'a" ("\<Sigma>") where
  "\<Sigma> A = (THE x. is_lub x A)"

lemma the_lub_leq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<longrightarrow> z \<le> x\<rbrakk> \<Longrightarrow> \<Sigma> X \<le> x"
  by (metis is_lub_unique lub_def the_equality)

lemma lub_is_lub: "is_lub w A \<Longrightarrow> \<Sigma> A = w"
  by (metis is_lub_unique lub_def the_equality)

(*
lemma lub_is_lub_var: "\<exists>w\<in>A. (\<Sigma> A = w \<longrightarrow> is_lub w A)"
  apply (simp add: lub_def)
proof (rule exE)
  apply (rule the_equality)
  by (metis (full_types) eq_iff is_lub_def is_ub_def)
*)

definition is_lb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_lb x A \<longleftrightarrow> (\<forall>y\<in>A. x \<le> y)"

definition is_glb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_glb x A \<longleftrightarrow> is_lb x A \<and> (\<forall>y.(\<forall>z\<in>A. y \<le> z) \<longrightarrow> y \<le> x)"

lemma is_glb_eqiv: "is_glb x A \<longleftrightarrow> (\<forall>z. (z \<le> x \<longleftrightarrow> (\<forall>y\<in>A. z \<le> y)))"
  by (metis is_glb_def is_lb_def order_refl order_trans)

lemma is_glb_unique: "is_glb x A \<longrightarrow> is_glb y A \<longrightarrow> x = y"
  by (metis antisym is_glb_def is_lb_def)

definition glb :: "'a set \<Rightarrow> 'a" ("\<Pi>") where
  "\<Pi> A = (THE x. is_glb x A)"

lemma the_glb_leq: "\<lbrakk>\<exists>z. is_glb z X; \<And>z. is_glb z X \<longrightarrow> x \<le> z\<rbrakk> \<Longrightarrow> x \<le> \<Pi> X"
  by (metis glb_def is_glb_unique the_equality)

lemma glb_is_glb: "is_glb w A \<Longrightarrow> \<Pi> A = w"
by (metis is_glb_unique glb_def the_equality)

(*
lemma glb_is_glb_var: "\<exists>w. \<Pi> A = w \<longrightarrow> is_glb w A"
by (metis (full_types) eq_iff is_glb_def is_lb_def)
*)

(*
lemma glb_is_glb_var2: "\<exists>w. \<Pi> A = w \<longrightarrow> (\<exists>w. is_glb w A)"
by (metis (full_types) glb_is_glb_var)
*)

lemma is_glb_from_is_lub: "\<lbrakk>x \<in> A; is_lub x {b. \<forall>a\<in>A. b \<le> a}\<rbrakk> \<Longrightarrow> is_glb x A"
  by (simp add: is_lub_def is_ub_def is_glb_def is_lb_def)

end

definition ext_cup_junctive :: "('a::order \<Rightarrow> 'b::order) set" where
  "ext_cup_junctive f \<equiv> \<forall>X \<subseteq> UNIV. (\<exists>x. \<Sigma> X = x) \<longrightarrow> f (\<Sigma> X) = \<Sigma> (f ` X)"

class ord_join_semilattice = order +
  assumes join_ex: "\<forall>x y. \<exists>z. is_lub z {x,y}"

class ord_meet_semilattice = order +
  assumes meet_ex: "\<forall>x y. \<exists>z. is_glb z {x,y}"

class ord_lattice = ord_join_semilattice + ord_meet_semilattice

class complete_join_semilattice = order +
  assumes  lub_ex: "\<exists>x. is_lub x A"

class complete_lattice = complete_join_semilattice +
  assumes  glb_ex: "\<exists>x. is_glb x A"

begin
  lemma top_ax: "\<exists>t. \<forall>x. x \<le> t" by (metis empty_iff glb_ex is_glb_def)
  lemma bot_ax: "\<exists>b. \<forall>x. b \<le> x" by (metis emptyE is_lub_def lub_ex)

  definition Top :: "'a" where "Top \<equiv> SOME x. \<forall> y. y \<le> x"
  definition Bot :: "'a" where "Bot \<equiv> SOME x. \<forall> y. x \<le> y"

  lemma prop_top: "\<forall>x. x \<le> Top"
  apply (simp only: Top_def)
  apply (rule someI_ex)
  by (simp add: top_ax)

  lemma prop_bot: "\<forall>x. Bot \<le> x"
  apply (simp only: Bot_def)
  apply (rule someI_ex)
  by (simp add: bot_ax)
end

definition order_monomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_monomorphism f \<equiv> \<forall>x y. (f x \<le> f y) \<longleftrightarrow> (x \<le> y)"

definition order_isomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_isomorphism f \<equiv> order_monomorphism f \<and> surj f"

lemma order_monomorphism_inj: "order_monomorphism f \<Longrightarrow> inj f"
  by (simp add: order_monomorphism_def inj_on_def order_eq_iff)

lemma singleton_lub: "\<Sigma> {y} = y"
apply (simp only: lub_def)
apply (rule the_equality)
apply (simp_all add: is_lub_def is_ub_def)
by (metis order_eq_iff)

lemma empty_lub: "\<Sigma> {} = Bot" by (metis emptyE is_lub_eqiv lub_is_lub prop_bot)

lemma empty_lub_var: "\<Sigma> {} = (THE x. \<forall>y. x \<le> y)"
  by (simp add: lub_def is_lub_def is_ub_def All_def)

lemma surjective_lub: "surj \<Sigma>"
apply (simp only: surj_def)
proof
  fix y
  show "\<exists>x. y = \<Sigma> x" by (metis singleton_lub)
qed

end
