theory Galois
imports Main
begin

class leq =
  fixes leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)


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

lemma lub_is_lub: "is_lub w A \<Longrightarrow> \<Sigma> A = w"
  by (metis is_lub_unique lub_def the_equality)

lemma lub_is_lub_var: "\<exists>w. (\<Sigma> A = w \<longrightarrow> is_lub w A)"
  by (metis (full_types) eq_iff is_lub_def is_ub_def)

definition is_lb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_lb x A \<longleftrightarrow> (\<forall>y\<in>A. x \<le> y)"

definition is_glb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_glb x A \<longleftrightarrow> is_lb x A \<and> (\<forall>y.(\<forall>z\<in>A. y \<le> z) \<longrightarrow> y \<le> x)"

lemma is_glb_unique: "is_glb x A \<longrightarrow> is_glb y A \<longrightarrow> x = y"
  by (metis antisym is_glb_def is_lb_def)

definition glb :: "'a set \<Rightarrow> 'a" ("\<Pi>") where
  "\<Pi> A = (THE x. is_glb x A)"

lemma glb_is_glb: "is_glb w A \<Longrightarrow> \<Pi> A = w"
by (metis is_glb_unique glb_def the_equality)

lemma glb_is_glb_var: "\<exists>w. \<Pi> A = w \<longrightarrow> is_glb w A"
by (metis (full_types) eq_iff is_glb_def is_lb_def)

lemma glb_is_glb_var2: "\<exists>w. \<Pi> A = w \<longrightarrow> (\<exists>w. is_glb w A)"
by (metis (full_types) glb_is_glb_var)

lemma is_glb_from_is_lub: "is_lub x {b. \<forall>a\<in>A. b \<le> a} \<Longrightarrow> is_glb x A"
  by (simp add: is_lub_def is_ub_def is_glb_def is_lb_def)

end

class complete_lattice = order +
  assumes  lub_ex: "\<forall>A. \<exists>x. is_lub x A"
  assumes  glb_ex: "\<forall>A. \<exists>x. is_glb x A"

begin
  lemma top_ax: "\<exists>T. \<forall>x. x \<le> T" by (metis empty_iff glb_ex is_glb_def)
  lemma bot_ax: "\<exists>B. \<forall>x. B \<le> x" by (metis empty_iff is_lub_def lub_ex)

  definition Top :: "'a" where "Top \<equiv> SOME x. \<forall> y. y \<le> x"
  definition Bot :: "'a" where "Bot \<equiv> SOME x. \<forall> y. x \<le> y"

  lemma prop_top: "\<forall>x. x \<le> Top"
  apply (simp only: Top_def)
  apply (rule someI_ex)
  by (metis top_ax)

  lemma prop_bot: "\<forall>x. Bot \<le> x"
  apply (simp only: Bot_def)
  apply (rule someI_ex)
  by (smt bot_ax) (* metis fails here, why? *)
end

(*
typedef ('a :: complete_lattice, 'b :: complete_lattice)GC =
  "{(\<epsilon> :: 'a \<Rightarrow> 'b, \<pi> :: 'b \<Rightarrow> 'a). (\<forall>x y. (\<epsilon> x \<le> y) = (x \<le> \<pi> y))}"
apply (rule_tac x = "(\<lambda>x. Bot, \<lambda>x. Top)" in exI)
by clarify (metis prop_bot prop_top)

locale galois =
  fixes
    G :: "('a::complete_lattice, 'b::complete_lattice) GC"
*)

locale galois_connection =
  fixes \<epsilon> :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  and \<pi> :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice"
  assumes galois_property: "\<forall>x y. (\<epsilon> x \<le> y) = (x \<le> \<pi> y)"

begin
  (*
  definition \<epsilon> :: "'a \<Rightarrow> 'b" where "\<epsilon> = fst (Rep_GC G)"

  definition \<pi> :: "'b \<Rightarrow> 'a" where "\<pi> = snd (Rep_GC G)"

  theorem galois_property: "\<forall>x y. (\<epsilon> x \<le> y) = (x \<le> \<pi> y)" sorry
  *)

  lemma deflation: "\<epsilon> (\<pi> y) \<le> y" by (simp only: galois_property)
  lemma inflation: "x \<le> \<pi> (\<epsilon> x)" by (metis order_refl galois_property)

  lemma \<epsilon>_monotone: "x \<le> y \<Longrightarrow> \<epsilon> x \<le> \<epsilon> y" by (metis galois_property inflation order_trans)
  lemma \<pi>_monotone: "x \<le> y \<Longrightarrow> \<pi> x \<le> \<pi> y" by (metis galois_property deflation order_trans)

  lemma p1: "\<epsilon> \<circ> \<pi> \<circ> \<epsilon> = \<epsilon>"
  proof
    fix x
    show "(\<epsilon> \<circ> \<pi> \<circ> \<epsilon>) x = \<epsilon> x" by (metis \<epsilon>_monotone deflation inflation o_apply order_antisym)
  qed

  lemma p2: "\<pi> \<circ> \<epsilon> \<circ> \<pi> = \<pi>"
  proof
    fix x
    show "(\<pi> \<circ> \<epsilon> \<circ> \<pi>) x = \<pi> x" by (metis \<pi>_monotone deflation inflation o_apply order_antisym)
  qed

  lemma \<epsilon>\<pi>_idempotent: "\<epsilon>\<circ>\<pi> \<circ> \<epsilon>\<circ>\<pi> = \<epsilon>\<circ>\<pi>" by (metis p1)
  lemma \<pi>\<epsilon>_idempotent: "\<pi>\<circ>\<epsilon> \<circ> \<pi>\<circ>\<epsilon> = \<pi>\<circ>\<epsilon>" by (metis p2)

end
