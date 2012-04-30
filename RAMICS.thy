theory RAMICS
  imports Main Signatures
begin

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

context order
begin

(* Pointfree ordering *)

definition pleq :: "('a \<Rightarrow> 'b::order) \<Rightarrow> ('a \<Rightarrow> 'b::order) \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "pleq f g \<equiv> \<forall>x. f x \<le> g x"

(* Lub *)

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

(* TODO: Investigate *)
lemma "\<Sigma> A \<le> z \<Longrightarrow> (\<forall>x\<in>A. x \<le> z)" oops

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

lemma is_glb_from_is_lub: "\<lbrakk>is_lub x {b. \<forall>a\<in>A. b \<le> a}\<rbrakk> \<Longrightarrow> is_glb x A"
  by (smt Collect_def is_glb_def is_lb_def is_lub_equiv mem_def order_refl)

lemma is_lub_from_is_glb: "\<lbrakk>is_glb x {b. \<forall>a\<in>A. a \<le> b}\<rbrakk> \<Longrightarrow> is_lub x A"
  by (smt Collect_def is_lub_def is_ub_def is_glb_equiv mem_def order_refl)

definition join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 70) where
  "x \<squnion> y = \<Sigma> {x,y}"

definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70) where
  "x \<sqinter> y = \<Pi> {x,y}"

end

(* Join and meet preserving maps *)

definition ex_join_preserving :: "('a::order \<Rightarrow> 'b::order) set" where
  "ex_join_preserving f \<equiv> \<forall>X\<subseteq>UNIV. (\<exists>x. is_lub x X) \<longrightarrow> \<Sigma> (f ` X) = f (\<Sigma> X)"

definition ex_meet_preserving :: "('a::order \<Rightarrow> 'b::order) set" where
  "ex_meet_preserving g \<equiv> \<forall>X\<subseteq>UNIV. (\<exists>x. is_glb x X) \<longrightarrow> \<Pi> (g ` X) = g (\<Pi> X)"

definition join_preserving :: "('a::order \<Rightarrow> 'b::order) set" where
  "join_preserving f \<equiv> \<forall>X\<subseteq>UNIV. \<Sigma> (f ` X) = f (\<Sigma> X)"

definition meet_preserving :: "('a::order \<Rightarrow> 'b::order) set" where
  "meet_preserving g \<equiv> \<forall>X\<subseteq>UNIV. \<Pi> (g ` X) = g (\<Pi> X)"

(* Join and meet semilattices *)

class join_semilattice = order +
  assumes join_ex: "\<forall>x y. \<exists>z. is_lub z {x,y}"

begin
  lemma leq_def: "x \<le> y \<longleftrightarrow> x\<squnion>y = y"
    by (smt emptyE insertCI insertE is_lub_def is_ub_def join_ex le_less less_le_not_le lub_is_lub ord_eq_le_trans join_def)

  lemma add_idem: "x \<squnion> x = x" by (metis leq_def order_refl)

  lemma add_comm: "x \<squnion> y = y \<squnion> x" by (metis insert_commute join_def)

  (* TODO: Don't unfold *)
  lemma add_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)" unfolding join_def
  proof -
    have a: "\<Sigma> {\<Sigma> {x, y}, z} \<le> \<Sigma> {x, \<Sigma> {y, z}}"
      by (smt insertCI insertE is_lub_def is_lub_equiv is_ub_def join_ex lub_is_lub singletonE)
    have b: "\<Sigma> {x, \<Sigma> {y, z}} \<le> \<Sigma> {\<Sigma> {x, y}, z}"
      by (smt insertCI insertE is_lub_def is_ub_def join_ex lub_is_lub order_trans singletonE)
    with a b show "\<Sigma> {\<Sigma> {x, y}, z} = \<Sigma> {x, \<Sigma> {y, z}}" by (metis antisym)
  qed
end

class meet_semilattice = order +
  assumes meet_ex: "\<forall>x y. \<exists>z. is_glb z {x,y}"

begin

  lemma leq_def2: "x \<le> y \<longleftrightarrow> y\<sqinter>x = x"
    by (smt antisym emptyE glb_is_glb insertCI insertE is_glb_def is_lb_def meet_def meet_ex ord_le_eq_trans order_refl)

(*
end

sublocale meet_semilattice \<subseteq> dual!: join_semilattice
  "op \<ge>" "op >"
proof
  fix x y z :: 'a
  show "(y < x) = (y \<le> x \<and> \<not> x \<le> y)" using less_le_not_le .
  show "x \<le> x" by simp
  show "\<lbrakk>y \<le> x; z \<le> y\<rbrakk> \<Longrightarrow> z \<le> x" by simp
  show "\<lbrakk>y \<le> x; x \<le> y\<rbrakk> \<Longrightarrow> x = y" by simp
  have "\<forall>x y. \<exists>z. order.is_glb (\<lambda>x y. x \<le> y) z {x, y}" by (metis meet_ex)
  thus "\<forall>x y. \<exists>z. order.is_lub (\<lambda>x y. y \<le> x) z {x, y}" using is_lub_from_is_glb sorry
qed
*)

  lemma mult_idem: "x \<sqinter> x = x" by (metis leq_def2 order_refl)

  lemma mult_comm: "x \<sqinter> y = y \<sqinter> x" by (metis insert_commute meet_def)

  lemma bin_lub_var: "x\<sqinter>y \<ge> z \<longleftrightarrow> x \<ge> z \<and> y \<ge> z"
  proof
    assume a: "z \<le> x\<sqinter>y"
    hence "\<Pi> {x,z} = z" by (metis leq_def2 glb_is_glb insertI1 is_glb_equiv meet_ex meet_def)
    moreover have "\<Pi> {y,z} = z" by (metis a leq_def2 glb_is_glb insertI1 is_glb_equiv meet_ex mult_comm meet_def)
    ultimately show "z \<le> x \<and> z \<le> y" by (metis leq_def2 meet_def)
  next
    assume "z \<le> x \<and> z \<le> y"
    thus "z \<le> x \<sqinter> y"
      by (smt emptyE glb_is_glb insertE is_glb_equiv meet_ex meet_def ord_le_eq_trans)
  qed

  lemma mult_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  proof -
    have "(x \<sqinter> y) \<sqinter> z \<le> x \<sqinter> (y \<sqinter> z)"
      by (metis eq_refl bin_lub_var)
    thus ?thesis
      by (metis antisym bin_lub_var order_refl)
  qed

end

(* Lattices *)

class lattice = join_semilattice + meet_semilattice

begin

  lemma absorb1: "x \<squnion> (x \<sqinter> y) = x" by (metis add_comm leq_def2 leq_def mult_assoc mult_idem)

  lemma absorb2: "x \<sqinter> (x \<squnion> y) = x" by (metis add_assoc add_idem leq_def2 leq_def mult_comm)

  lemma order_change: "x\<sqinter>y = y \<longleftrightarrow> y\<squnion>x = x" by (metis leq_def2 leq_def)

end

(* Complete join semilattices *)

class complete_join_semilattice = order +
  assumes  lub_ex: "\<exists>x. is_lub x A"

sublocale complete_join_semilattice \<subseteq> join_semilattice
  by (unfold_locales, metis lub_ex)

context complete_join_semilattice
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
    by (metis is_lub_equiv is_lub_lub)

  lemma lub_least [intro?]: "x \<in> X \<Longrightarrow> x \<le> \<Sigma> X"
    by (metis is_lub_def is_lub_lub is_ub_def)

  lemma empty_lub [simp]: "\<Sigma> {} = \<bottom>" by (metis emptyE is_lub_equiv lub_is_lub prop_bot)

  lemma bot_oner [simp]: "x \<squnion> \<bottom> = x" by (metis add_comm leq_def prop_bot)
  lemma bot_onel [simp]: "\<bottom> \<squnion> x = x" by (metis leq_def prop_bot)

end


(* Complete meet semilattice *)

class complete_meet_semilattice = order +
  assumes glb_ex: "\<exists>x. is_glb x A"

sublocale complete_meet_semilattice \<subseteq> meet_semilattice
  by (unfold_locales, metis glb_ex)

context complete_meet_semilattice
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

  lemma empty_glb [simp]: "\<Pi> {} = \<top>" by (metis empty_iff glb_is_glb is_glb_def is_lb_def prop_top)

end

class complete_lattice = complete_join_semilattice + complete_meet_semilattice

begin

  lemma univ_lub: "\<Sigma> UNIV = \<top>" by (metis eq_iff is_lub_equiv iso_tuple_UNIV_I lub_is_lub prop_top)

  lemma univ_glb: "\<Pi> UNIV = \<bottom>" by (metis eq_iff glb_is_glb is_glb_equiv iso_tuple_UNIV_I prop_bot)

end

sublocale complete_lattice \<subseteq> lattice
  by unfold_locales

(*
sublocale complete_join_semilattice \<subseteq> complete_lattice
  by (unfold_locales, smt is_lub_lub Collect_def is_glb_from_is_lub)

sublocale complete_meet_semilattice \<subseteq> complete_lattice
  by (unfold_locales, smt is_glb_glb Collect_def is_lub_from_is_glb)
*)

definition order_monomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_monomorphism f \<equiv> \<forall>x y. (f x \<le> f y) \<longleftrightarrow> (x \<le> y)"

definition order_isomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_isomorphism f \<equiv> order_monomorphism f \<and> surj f"

lemma order_monomorphism_inj: "order_monomorphism f \<Longrightarrow> inj f"
  by (simp add: order_monomorphism_def inj_on_def order_eq_iff)

(* +------------------------------------------------------------------------+
   | Fixpoints and Prefix Points                                            |
   +------------------------------------------------------------------------+ *)

context complete_lattice
begin
  definition is_pre_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_pre_fp x f \<equiv> f x \<le> x"

  definition is_post_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_post_fp x f \<equiv> x \<le> f x"

  definition is_fp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_fp x f \<equiv> f x = x"

  lemma is_fp_def_var: "is_fp x f = (is_pre_fp x f \<and> is_post_fp x f)"
    by (metis antisym eq_refl is_fp_def is_post_fp_def is_pre_fp_def)

  definition is_lpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_lpp x f \<equiv> (is_pre_fp x f) \<and> (\<forall>y. f y \<le> y \<longrightarrow> x \<le> y)"

  lemma is_lpp_def_var: "is_lpp x f = (f x \<le> x \<and> (\<forall>y. f y \<le> y \<longrightarrow> x \<le> y))"
    by (simp add: is_lpp_def is_pre_fp_def)

  definition is_gpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_gpp x f \<equiv> (is_post_fp x f) \<and> (\<forall>y. y \<le> f y \<longrightarrow> y \<le> x)"

  lemma is_gpp_def_var: "is_gpp x f = (x \<le> f x \<and> (\<forall>y. y \<le> f y \<longrightarrow> y \<le> x))"
    by (simp add: is_gpp_def is_post_fp_def)

  definition is_lfp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_lfp x f \<equiv> is_fp x f \<and> (\<forall>y. is_fp y f \<longrightarrow> x \<le> y)"

  definition is_gfp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_gfp x f \<equiv> is_fp x f \<and> (\<forall>y. is_fp y f \<longrightarrow> y \<le> x)"

  definition least_prefix_point :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>\<^sub>\<le>") where
    "least_prefix_point f \<equiv> THE x. is_lpp x f"

  definition greatest_postfix_point :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>\<^sub>\<le>") where
    "greatest_postfix_point f \<equiv> THE x. is_gpp x f"

  definition least_fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>") where
    "least_fixpoint f \<equiv> THE x. is_lfp x f"

  definition greatest_fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>") where
    "greatest_fixpoint f \<equiv> THE x. is_gfp x f"
end

lemma lpp_unique: "\<lbrakk>is_lpp x f; is_lpp y f\<rbrakk> \<Longrightarrow> x = y"
  by (simp add: is_lpp_def is_pre_fp_def, metis order_eq_iff)

lemma gpp_unique: "\<lbrakk>is_gpp x f; is_gpp y f\<rbrakk> \<Longrightarrow> x = y"
  by (simp add: is_gpp_def is_post_fp_def, metis order_eq_iff)

lemma lpp_equality [intro?]: "is_lpp x f \<Longrightarrow> \<mu>\<^sub>\<le> f = x"
  by (simp add: least_prefix_point_def, rule the_equality, auto, metis antisym is_lpp_def is_pre_fp_def)

lemma gpp_equality [intro?]: "is_gpp x f \<Longrightarrow> \<nu>\<^sub>\<le> f = x"
  by (simp add: greatest_postfix_point_def, rule the_equality, auto, metis antisym is_gpp_def is_post_fp_def)

lemma lfp_equality: "is_lfp x f \<Longrightarrow> \<mu> f = x"
  by (simp add: least_fixpoint_def, rule the_equality, auto, metis antisym is_lfp_def)

lemma lfp_equality_var [intro?]: "\<lbrakk>f x = x; \<And>y. f y = y \<Longrightarrow> x \<le> y\<rbrakk> \<Longrightarrow> x = \<mu> f"
  by (rule lfp_equality[symmetric], simp add: is_lfp_def is_fp_def)

lemma gfp_equality: "is_gfp x f \<Longrightarrow> \<nu> f = x"
  by (simp add: greatest_fixpoint_def, rule the_equality, auto, metis antisym is_gfp_def)

lemma gfp_equality_var [intro?]: "\<lbrakk>f x = x; \<And>y. f y = y \<Longrightarrow> y \<le> x\<rbrakk> \<Longrightarrow> x = \<nu> f"
  by (rule gfp_equality[symmetric], simp add: is_gfp_def is_fp_def)

lemma lpp_is_lfp: "\<lbrakk>mono f; is_lpp x f\<rbrakk> \<Longrightarrow> is_lfp x f"
  apply (simp add: is_lpp_def is_lfp_def is_fp_def is_pre_fp_def)
  by (metis monoD order_eq_iff)

lemma gpp_is_gfp: "\<lbrakk>mono f; is_gpp x f\<rbrakk> \<Longrightarrow> is_gfp x f"
  apply (simp add: is_gpp_def is_gfp_def is_fp_def is_post_fp_def)
  by (metis monoD order_antisym)

(* +------------------------------------------------------------------------+
   | Knaster-Tarski                                                         |
   +------------------------------------------------------------------------+ *)

(* Modified version of Wenzel's proof of the Knaster-Tarski theorem *)

theorem knaster_tarski_lpp:
  assumes fmon: "mono f"
  obtains a :: "'a::complete_lattice" where "is_lpp a f"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Pi> ?H"
  have "is_pre_fp ?a f"
  proof -
    have "\<forall>x\<in>?H. ?a \<le> x" by (metis glb_least)
    hence "\<forall>x\<in>?H. f ?a \<le> x"
      by (metis (full_types) Collect_def assms glb_least mem_def monoD order_trans)
    hence "f ?a \<le> \<Pi> ?H" by (smt glb_greatest)
    thus ?thesis by (metis is_pre_fp_def)
  qed
  moreover have "f y \<le> y \<Longrightarrow> ?a \<le> y"
    by (metis Collect_def glb_least mem_def)
  ultimately show "is_lpp ?a f"
    by (smt is_lpp_def Collect_def glb_least mem_def)
qed

corollary is_lpp_lpp [intro?]: "mono f \<Longrightarrow> is_lpp (\<mu>\<^sub>\<le> f) f"
  using knaster_tarski_lpp by (metis lpp_equality)

theorem knaster_tarski:
  assumes fmon: "mono f"
  obtains a :: "'a::complete_lattice" where "is_lfp a f"
  by (metis assms is_lpp_lpp lpp_is_lfp)

corollary knaster_tarski_var: "mono f \<Longrightarrow> \<exists>!x. is_lfp x f"
  using knaster_tarski by (metis lfp_equality)

corollary is_lfp_lfp [intro?]: "mono f \<Longrightarrow> is_lfp (\<mu> f) f"
  using knaster_tarski by (metis lfp_equality)

(* Knaster-Tarski for greatest fixpoints *)

theorem knaster_tarski_gpp:
  assumes fmon: "mono f"
  obtains a :: "'a::complete_lattice" where "is_gpp a f"
proof
  let ?H = "{u. u \<le> f u}"
  let ?a = "\<Sigma> ?H"
  have "is_post_fp ?a f"
  proof -
    have "\<forall>x\<in>?H. x \<le> ?a" by (metis lub_least)
    hence "\<forall>x\<in>?H. x \<le> f ?a"
      by (metis (full_types) Collect_def assms lub_least mem_def monoD order_trans)
    hence "\<Sigma> ?H \<le> f ?a" by (smt lub_greatest)
    thus ?thesis by (metis is_post_fp_def)
  qed
  moreover have "y \<le> f y \<Longrightarrow> y \<le> ?a"
    by (metis Collect_def lub_least mem_def order_refl)
  ultimately show "is_gpp ?a f"
    by (smt is_gpp_def Collect_def lub_least mem_def)
qed

corollary is_gpp_gpp [intro?]: "mono f \<Longrightarrow> is_gpp (\<nu>\<^sub>\<le> f) f"
  using knaster_tarski_gpp by (metis gpp_equality)

theorem knaster_tarski_greatest:
  assumes fmon: "mono f"
  obtains a :: "'a::complete_lattice" where "is_gfp a f"
  by (metis assms is_gpp_gpp gpp_is_gfp)

corollary knaster_tarski_greatest_var: "mono f \<Longrightarrow> \<exists>!x. is_gfp x f"
  using knaster_tarski_greatest by (metis gfp_equality)

corollary is_gfp_gfp [intro?]: "mono f \<Longrightarrow> is_gfp (\<nu> f) f"
  using knaster_tarski_greatest by (metis gfp_equality)

(* We now show some more properties of fixpoints *)

(* +------------------------------------------------------------------------+
   | Fixpoint Computation                                                   |
   +------------------------------------------------------------------------+ *)

lemma prefix_point_computation [simp]: "mono f \<Longrightarrow> f (\<mu>\<^sub>\<le> f) = \<mu>\<^sub>\<le> f"
  by (metis is_lpp_lpp lpp_is_lfp is_lfp_def is_fp_def)

lemma fixpoint_computation [simp]: "mono f \<Longrightarrow> f (\<mu> f) = \<mu> f"
  by (metis is_lpp_lpp lfp_equality lpp_is_lfp prefix_point_computation)

lemma greatest_prefix_point_computation [simp]: "mono f \<Longrightarrow> f (\<nu>\<^sub>\<le> f) = \<nu>\<^sub>\<le> f"
  by (metis is_gpp_gpp gpp_is_gfp is_gfp_def is_fp_def)

lemma greatest_fixpoint_computation [simp]: "mono f \<Longrightarrow> f (\<nu> f) = \<nu> f"
  by (metis is_gpp_gpp gfp_equality gpp_is_gfp greatest_prefix_point_computation)

(* +------------------------------------------------------------------------+
   | Fixpoint Induction                                                     |
   +------------------------------------------------------------------------+ *)

lemma prefix_point_induction [intro?]:
  assumes fmon: "mono f"
  and pp: "f x \<le> x" shows "\<mu>\<^sub>\<le> f \<le> x"
proof (unfold least_prefix_point_def, rule the1I2)
  show "\<exists>!x. is_lpp x f" using knaster_tarski_lpp by (metis fmon lpp_equality)
next
  fix y
  show "is_lpp y f \<Longrightarrow> y \<le> x" unfolding is_lpp_def by (metis pp)
qed

lemma fixpoint_induction [intro?]:
  assumes fmon: "mono f"
  and fp: "f x \<le> x" shows "\<mu> f \<le> x"
  by (metis fmon fp is_lpp_lpp lfp_equality lpp_is_lfp prefix_point_induction)

lemma greatest_postfix_point_induction [intro?]:
  assumes fmon: "mono f"
  and pp: "x \<le> f x" shows "x \<le> \<nu>\<^sub>\<le> f"
proof (unfold greatest_postfix_point_def, rule the1I2)
  show "\<exists>!x. is_gpp x f" using knaster_tarski_gpp by (metis fmon gpp_equality)
next
  fix y
  show "is_gpp y f \<Longrightarrow> x \<le> y" unfolding is_gpp_def by (metis pp)
qed

lemma greatest_fixpoint_induction [intro?]:
  assumes fmon: "mono f"
  and fp: "x \<le> f x" shows "x \<le> \<nu> f"
  by (metis fmon fp is_gpp_gpp gfp_equality gpp_is_gfp greatest_postfix_point_induction)

lemma fixpoint_compose:
  assumes kmon: "mono k" and comp: "g\<circ>k = k\<circ>h" and fp: "is_fp x h"
  shows "is_fp (k x) g"
proof (unfold is_fp_def)
  have "h x = x" using fp by (unfold is_fp_def)
  hence "k (h x) = k x" by metis
  moreover have "g (k x) = (k (h x))" by (metis comp o_def)
  ultimately show "g (k x) = k x" by metis
qed

lemma fixpoint_mono:
  assumes fmon: "mono f" and gmon: "mono g"
  and fg: "f \<sqsubseteq> g" shows "\<mu> f \<le> \<mu> g"
proof -
  show "\<mu> f \<le> \<mu> g" using fmon
  proof (rule fixpoint_induction)
    have "f (\<mu> g) \<le> g (\<mu> g)" using fg unfolding pleq_def ..
    thus "f (\<mu> g) \<le> \<mu> g" using gmon by simp
  qed
qed

lemma greatest_fixpoint_mono:
  assumes fmon: "mono f" and gmon: "mono g"
  and fg: "f \<sqsubseteq> g" shows "\<nu> f \<le> \<nu> g"
proof -
  show "\<nu> f \<le> \<nu> g" using gmon
  proof (rule greatest_fixpoint_induction)
    have "f (\<nu> f) \<le> g (\<nu> f)" using fg unfolding pleq_def ..
    thus "\<nu> f \<le> g (\<nu> f)" using fmon by simp
  qed
qed

(* +------------------------------------------------------------------------+
   | Galois Connections                                                     |
   +------------------------------------------------------------------------+ *)

definition idempotent :: "('a \<Rightarrow> 'a) set" where
  "idempotent f \<equiv> f \<circ> f = f"

locale galois_connection =
  fixes lower :: "'a::order \<Rightarrow> 'b::order" ("\<pi>\<^sup>*")
  and upper :: "'b::order \<Rightarrow> 'a::order" ("\<pi>\<^sub>*")
  assumes galois_property: "\<forall>x y. (\<pi>\<^sup>* x \<le> y) = (x \<le> \<pi>\<^sub>* y)"

definition lower_adjoint :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "lower_adjoint f \<equiv> \<exists>g. galois_connection f g"

definition upper_adjoint :: "('b::order \<Rightarrow> 'a::order) \<Rightarrow> bool" where
  "upper_adjoint g \<equiv> \<exists>f. galois_connection f g"

locale dual_galois_connection =
  fixes dual_lower :: "'a::order \<Rightarrow> 'b::order" ("\<pi>\<^sup>*")
  and dual_upper :: "'b::order \<Rightarrow> 'a::order" ("\<pi>\<^sub>*")
  assumes dual_galois_property: "\<forall>x y. (\<pi>\<^sup>* x \<ge> y) = (x \<ge> \<pi>\<^sub>* y)"

sublocale dual_galois_connection \<subseteq> galois_connection
  where upper = dual_lower and lower = dual_upper
  by unfold_locales (metis dual_galois_property)

sublocale galois_connection \<subseteq> dual_galois_connection
  where dual_upper = lower and dual_lower = upper
  by unfold_locales (metis galois_property)

(* Basic properties of galois connections *)

context galois_connection
begin
  lemma deflation: "\<pi>\<^sup>* (\<pi>\<^sub>* y) \<le> y" by (simp only: galois_property)
  lemma inflation: "x \<le> \<pi>\<^sub>* (\<pi>\<^sup>* x)" by (metis galois_property order_eq_refl)

  lemma lower_mono: "mono \<pi>\<^sup>*"
    by (metis galois_property inflation order_trans mono_def)

  lemma upper_mono: "mono \<pi>\<^sub>*"
    by (metis galois_property deflation order_trans mono_def)

  lemma lower_comp: "\<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<circ> \<pi>\<^sup>* = \<pi>\<^sup>*"
  proof
    fix x
    show "(\<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<circ> \<pi>\<^sup>*) x = \<pi>\<^sup>* x"
      by (metis lower_mono mono_def deflation inflation o_apply order_antisym)
  qed

  lemma upper_comp: "\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>* = \<pi>\<^sub>*"
  proof
    fix x
    show "(\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>*) x = \<pi>\<^sub>* x"
      by (metis upper_mono mono_def deflation inflation o_apply order_antisym)
  qed

  lemma upper_idempotency1: "idempotent (\<pi>\<^sup>*\<circ>\<pi>\<^sub>*)" by (metis lower_comp idempotent_def o_assoc)
  lemma upper_idempotency2: "idempotent (\<pi>\<^sub>*\<circ>\<pi>\<^sup>*)" by (metis lower_comp idempotent_def o_assoc)

  lemma upper_dual: "(\<pi>\<^sub>* x \<ge> y) = (x \<ge> \<pi>\<^sup>* y)"
    by (metis galois_property)
end

lemma galois_dual: "galois_connection F G \<Longrightarrow> dual_galois_connection G F"
  by unfold_locales (metis galois_connection.galois_property)

lemma dual_galois_dual: "dual_galois_connection F G \<Longrightarrow> galois_connection G F"
  by unfold_locales (metis dual_galois_connection.dual_galois_property)

lemma galois_dualise: "\<lbrakk>galois_connection F G \<Longrightarrow> P F G; dual_galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
proof -
  assume dual: "dual_galois_connection G F" and p: "galois_connection F G \<Longrightarrow> P F G"
  have conn: "galois_connection F G" using dual by (rule dual_galois_dual)
  thus "P F G" by (rule p)
qed

lemma dual_galois_dualise: "\<lbrakk>dual_galois_connection F G \<Longrightarrow> P F G; galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
proof -
  assume g: "galois_connection G F" and p: "dual_galois_connection F G \<Longrightarrow> P F G"
  have dual_conn: "dual_galois_connection F G" using g by (rule galois_dual)
  thus "P F G" by (rule p)
qed

lemma galois_comp: assumes g1: "galois_connection F G" and g2 :"galois_connection H K"
  shows "galois_connection (F \<circ> H) (K \<circ> G)"
  by unfold_locales (metis g1 g2 galois_connection.galois_property o_def)

lemma galois_id: "galois_connection id id" by unfold_locales (metis id_def)

lemma galois_mono1: "galois_connection F G \<Longrightarrow> mono (G \<circ> F)"
proof -
  assume g: "galois_connection F G"
  hence "mono G" using galois_connection.upper_mono by auto
  moreover have "mono F" using g galois_connection.lower_mono by auto
  ultimately show "mono (G \<circ> F)" by (simp add: mono_def)
qed

lemma galois_mono2: "galois_connection F G \<Longrightarrow> mono (F \<circ> G)"
proof -
  assume g: "galois_connection F G"
  hence "mono G" using galois_connection.upper_mono by auto
  moreover have "mono F" using g galois_connection.lower_mono by auto
  ultimately show "mono (F \<circ> G)" by (simp add: mono_def)
qed

lemma point_id1: "galois_connection F G \<Longrightarrow> id \<sqsubseteq> G \<circ> F"
  by (metis galois_connection.inflation id_apply o_apply pleq_def)

lemma point_id2: "galois_connection F G \<Longrightarrow> F \<circ> G \<sqsubseteq> id"
  by (metis galois_connection.deflation id_apply o_apply pleq_def)

lemma point_cancel: assumes g: "galois_connection F G" shows "F \<circ> G \<sqsubseteq> G \<circ> F"
proof -
  have "F \<circ> G \<sqsubseteq> id" using g point_id2 by blast
  moreover
  have "id \<sqsubseteq> G \<circ> F" using g point_id1 by blast
  ultimately
  show "F \<circ> G \<sqsubseteq> G \<circ> F"
    apply (simp only: pleq_def) by (metis order_trans)
qed

lemma cancel: assumes g: "galois_connection F G" shows "F (G x) \<le> G (F x)"
proof -
  have "F \<circ> G \<sqsubseteq> G \<circ> F" by (metis g point_cancel)
  thus "F (G x) \<le> G (F x)" by (simp only: pleq_def o_def)
qed

lemma cancel_cor1: assumes g: "galois_connection F G"
  shows "(G x = G y) \<longleftrightarrow> (F (G x) = F (G y))"
  by (metis assms galois_connection.upper_comp o_apply)

lemma cancel_cor2: assumes g: "galois_connection F G"
  shows "(F x = F y) \<longleftrightarrow> (G (F x) = G (F y))"
  by (metis assms galois_connection.lower_comp o_apply)

lemma semi_inverse1: "galois_connection F G \<Longrightarrow> F x = F (G (F x))"
  by (metis galois_connection.lower_comp o_apply)

lemma semi_inverse2: "galois_connection F G \<Longrightarrow> G x = G (F (G x))"
  by (metis galois_connection.upper_comp o_apply)

lemma point_comp: "galois_connection F G \<Longrightarrow> (F \<circ> h \<sqsubseteq> k) = (h \<sqsubseteq> G \<circ> k)"
  by (metis galois_connection.galois_property o_def pleq_def)

lemma point_comp_2: "\<lbrakk>galois_connection F G; mono h; mono k\<rbrakk> \<Longrightarrow> (h \<circ> G \<sqsubseteq> k) = (h \<sqsubseteq> k \<circ> F)"
  apply (simp only: pleq_def o_def)
  by (metis (full_types) mono_def galois_connection.deflation galois_connection.inflation order_trans)

lemma upper_uniqueness: assumes g1: "galois_connection F G" and g2: "galois_connection H K"
  shows "(F \<sqsubseteq> H) = (K \<sqsubseteq> G)"
proof -
  have "(F \<sqsubseteq> H) = (id \<sqsubseteq> G \<circ> H)" by (metis g1 point_comp o_id)
  also have "... = (K \<sqsubseteq> G)" by (metis g1 g2 galois_connection.upper_mono galois_id id_o point_comp_2)
  thus ?thesis by (metis calculation)
qed

lemma universal_mapping_property1:
  assumes a: "mono g" and b: "\<forall>x. x \<le> g (f x)"
  and c: "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
  shows "galois_connection f g"
proof (unfold_locales, intro allI)
  fix x and y
  show "(f x \<le> y) = (x \<le> g y)" by (metis mono_def a b c order_trans)
qed

lemma universal_mapping_property2:
  assumes a: "mono f" and b: "\<forall>x. f (g x) \<le> x"
  and c: "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
  shows "galois_connection f g"
proof (unfold_locales, intro allI)
  fix x and y
  have "(x \<le> g y) \<longrightarrow> (f x \<le> y)" using a b c by (metis monoD order_trans)
  thus "(f x \<le> y) = (x \<le> g y)" using c by auto
qed

lemma galois_ump2: "galois_connection f g = (mono f \<and> (\<forall>y. f (g y) \<le> y) \<and> (\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y))"
  by (metis galois_connection.deflation galois_connection.lower_mono galois_connection.upper_dual universal_mapping_property2)

lemma galois_ump1: "galois_connection f g = (mono g \<and> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y))"
  by (metis galois_connection.inflation galois_connection.upper_dual galois_connection.upper_mono universal_mapping_property1)

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma ore_galois:
  assumes a: "\<forall>x. x \<le> g (f x)" and b: "\<forall>x. f (g x) \<le> x"
  and c: "mono f" and d: "mono g"
  shows "galois_connection f g"
proof (unfold_locales, intro allI)
  fix x and y
  show "(f x \<le> y) = (x \<le> g y)" using a b c d by (metis mono_def order_trans)
qed

(* +------------------------------------------------------------------------+
   | Theorems 4.32(a) and 4.32(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma perfect1: "galois_connection F G \<Longrightarrow> G (F x) = x \<longleftrightarrow> x \<in> range G"
proof -
  assume conn: "galois_connection F G"
  have "G (F x) = x \<Longrightarrow> x \<in> range G" by (metis range_eqI)
  moreover have "x \<in> range G \<Longrightarrow> G (F x) = x"
  proof -
    assume "x \<in> range G"
    hence "\<exists>y. x = G y" by (metis image_iff)
    hence "\<exists>y. (x = G y) \<and> (x = G (F (G y)))" using conn semi_inverse2 by metis
    thus ?thesis by metis
  qed
  ultimately show ?thesis by metis
qed

lemma perfect2: "galois_connection F G \<Longrightarrow> F (G x) = x \<longleftrightarrow> x \<in> range F"
proof -
  assume conn: "galois_connection F G"
  have "F (G x) = x \<Longrightarrow> x \<in> range F" by (metis range_eqI)
  moreover have "x \<in> range F \<Longrightarrow> F (G x) = x"
  proof -
    assume "x \<in> range F"
    hence "\<exists>y. x = F y" by (metis image_iff)
    hence "\<exists>y. (x = F y) \<and> (x = F (G (F y)))" using conn semi_inverse1 by metis
    thus ?thesis by metis
  qed
  ultimately show ?thesis by metis
qed

definition (in order) is_max :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_max x X \<equiv> x \<in> X \<and> is_lub x X"

definition (in order) is_min :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_min x X \<equiv> x \<in> X \<and> is_glb x X"

(* +------------------------------------------------------------------------+
   | Theorems 4.20(a) and 4.20(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma galois_max: assumes conn: "galois_connection f g" shows "is_max (g y) {x. f x \<le> y}"
  apply (simp add: is_max_def is_lub_equiv) by (metis assms galois_ump2 xt1(6))

lemma galois_min: assumes conn: "galois_connection f g" shows "is_min (f x) {y. x \<le> g y}"
  apply (simp add: is_min_def is_glb_equiv) by (metis assms galois_ump1 xt1(6))

theorem max_galois: "galois_connection f g = (mono f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y}))"
proof
  assume conn: "galois_connection f g"
  show "mono f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y})"
  proof
    show "mono f" using conn by (metis galois_connection.lower_mono mem_def)
  next
    show "\<forall>y. is_max (g y) {x. f x \<le> y}" using conn by (metis galois_max)
  qed
next
  assume "mono f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y})"
  hence fmon: "mono f" and max: "\<forall>y. is_max (g y) {x. f x \<le> y}" by auto+
  show "galois_connection f g"
  proof (rule universal_mapping_property2)
    show "mono f" by (metis fmon)
  next
    have max2: "\<forall>y. g y \<in> {x. f x \<le> y}" using is_max_def max by smt
    hence "(g y \<in> {x. f x \<le> y}) = (f (g y) \<le> y)" by (simp only: mem_Collect_eq)
    thus p: "\<forall>y. f (g y) \<le> y" using max2 by auto
  next
    show "\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y" apply (intro allI)
    proof (intro impI)
      fix x and y
      have lub1: "is_lub (g y) {x. f x \<le> y}" using is_max_def max
        by (smt Collect_def is_lub_equiv mem_def)
      assume "f x \<le> y"
      thus "x \<le> g y" using lub1 by (metis Collect_def is_lub_equiv mem_def order_refl)
    qed
  qed
qed

corollary max_galois_rule: "\<lbrakk>mono f; \<forall>y. is_max (g y) {x. f x \<le> y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis max_galois)

theorem min_galois: "galois_connection f g = (mono g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y}))"
proof
  assume conn: "galois_connection f g"
  show "mono g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y})"
  proof
    show "mono g" using conn by (metis galois_connection.upper_mono mem_def)
  next
    show "\<forall>x. is_min (f x) {y. x \<le> g y}" using conn by (metis galois_min)
  qed
next
  assume "mono g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y})"
  hence gmon: "mono g" and min: "\<forall>x. is_min (f x) {y. x \<le> g y}" by auto+
  show "galois_connection f g"
  proof (rule universal_mapping_property1)
    show "mono g" by (metis gmon)
  next
    have "\<forall>x. f x \<in> {y. x \<le> g y}" using is_min_def min by smt
    moreover have "(f x \<in> {y. x \<le> g y}) = (x \<le> g (f x))" by (simp only: mem_Collect_eq)
    ultimately show "\<forall>x. x \<le> g (f x)" by auto
  next
    show "\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y" apply (intro allI)
    proof (intro impI)
      fix x and y
      have glb1: "is_glb (f x) {y. x \<le> g y}" using is_min_def min
        by (smt Collect_def is_glb_equiv mem_def)
      assume "x \<le> g y"
      thus "f x \<le> y" using glb1 by (metis Collect_def is_glb_equiv mem_def order_refl)
    qed
  qed
qed

corollary min_galois_rule: "\<lbrakk>mono g; \<forall>x. is_min (f x) {y. x \<le> g y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis min_galois)

hide_fact galois_min galois_max

(* +------------------------------------------------------------------------+
   | Lemma 4.24(a) and 4.24(b)                                              |
   +------------------------------------------------------------------------+ *)

lemma galois_lub: "galois_connection f g \<Longrightarrow> is_lub (g y) {x. f x \<le> y}"
  by (simp add: is_lub_equiv, metis galois_ump2 order_trans)

lemma galois_glb: "galois_connection f g \<Longrightarrow> is_glb (f x) {y. x \<le> g y}"
  by (simp add: is_glb_equiv, metis galois_ump1 order_trans)


lemma lower_preserves_joins: assumes lower: "lower_adjoint f" shows "ex_join_preserving f"
proof (simp add: ex_join_preserving_def, intro allI impI)
  obtain g where conn: "galois_connection f g" by (metis lower lower_adjoint_def)
  fix X :: "'a set"
  show "(\<exists>x\<Colon>'a. is_lub x X) \<Longrightarrow> (\<Sigma> (f ` X) = f (\<Sigma> X))"
  proof -
    assume lub_exists: "\<exists>x. is_lub x X"
    have a: "\<forall>y. (f (\<Sigma> X) \<le> y) = (\<forall>z \<in> f`X. z \<le> y)" using conn lub_exists
      by (smt galois_connection.galois_property image_iff is_lub_equiv lub_is_lub rev_image_eqI)
    moreover have "\<forall>y. (\<forall>z \<in> f`X. z \<le> y) = (\<Sigma> (f ` X) \<le> y)"
    proof
      fix y
      have "\<forall>z \<in> f`X. z \<le> y \<Longrightarrow> \<Sigma> (f ` X) \<le> y"
        by (smt calculation is_lub_equiv lub_exists lub_is_lub)
      moreover have "\<Sigma> (f ` X) \<le> y \<Longrightarrow> \<forall>z \<in> f`X. z \<le> y"
        by (smt a is_lub_equiv lub_exists lub_is_lub)
      ultimately show "(\<forall>z \<in> f`X. z \<le> y) = (\<Sigma> (f ` X) \<le> y)" by auto
    qed
    ultimately have "\<forall>y. (f (\<Sigma> X) \<le> y) = (\<Sigma> (f ` X) \<le> y)" by metis
    thus "\<Sigma> (f ` X) = f (\<Sigma> X)" by (metis order_refl xt1(5))
  qed
qed

lemma upper_preserves_meets: assumes upper: "upper_adjoint g" shows "ex_meet_preserving g"
proof (simp add: ex_meet_preserving_def, intro allI impI)
  obtain f where conn: "galois_connection f g" by (metis upper upper_adjoint_def)
  fix X :: "'a set"
  assume glb_exists: "\<exists>x. is_glb x X"
  have a: "\<forall>y. (y \<le> g (\<Pi> X)) = (\<forall>z \<in> g`X. y \<le> z)" using conn glb_exists
    by (smt galois_connection.galois_property image_iff is_glb_equiv glb_is_glb rev_image_eqI)
  moreover have "\<forall>y. (\<forall>z \<in> g`X. y \<le> z) = (y \<le> \<Pi> (g ` X))"
  proof
    fix y
    have "\<forall>z \<in> g`X. y \<le> z \<Longrightarrow> y \<le> \<Pi> (g ` X)"
      by (smt calculation is_glb_equiv glb_exists glb_is_glb)
    moreover have "y \<le> \<Pi> (g ` X) \<Longrightarrow> \<forall>z \<in> g`X. y \<le> z"
      by (smt a is_glb_equiv glb_exists glb_is_glb)
    ultimately show "(\<forall>z \<in> g`X. y \<le> z) = (y \<le> \<Pi> (g ` X))" by auto
  qed
  ultimately have "\<forall>y. (y \<le> g (\<Pi> X)) = (y \<le> \<Pi> (g ` X))" by metis
  thus "\<Pi> (g ` X) = g (\<Pi> X)" by (metis order_refl xt1(5))
qed

(* +------------------------------------------------------------------------+
   | Connections between complete lattices                                  |
   +------------------------------------------------------------------------+ *)

locale cl_galois_connection =
  fixes cl_lower :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice" ("\<pi>\<^sup>*")
  and cl_upper :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice" ("\<pi>\<^sub>*")
  assumes cl_galois_property: "\<forall>x y. (\<pi>\<^sup>* x \<le> y) = (x \<le> \<pi>\<^sub>* y)"

locale dual_cl_galois_connection =
  fixes dual_cl_lower :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice" ("\<pi>\<^sup>*")
  and dual_cl_upper :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice" ("\<pi>\<^sub>*")
  assumes dual_cl_galois_property: "\<forall>x y. (\<pi>\<^sup>* x \<ge> y) = (x \<ge> \<pi>\<^sub>* y)"

sublocale dual_cl_galois_connection \<subseteq> cl_galois_connection
  where cl_upper = dual_cl_lower and cl_lower = dual_cl_upper
  by unfold_locales (metis dual_cl_galois_property)

lemma cl_galois_dual: "cl_galois_connection F G \<Longrightarrow> dual_cl_galois_connection G F"
  by unfold_locales (metis cl_galois_connection.cl_galois_property)

lemma dual_cl_galois_dual: "dual_cl_galois_connection F G \<Longrightarrow> cl_galois_connection G F"
  by unfold_locales (metis dual_cl_galois_connection.dual_cl_galois_property)

lemma cl_galois_dualise: "\<lbrakk>cl_galois_connection F G \<Longrightarrow> P F G; dual_cl_galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
  by (metis dual_cl_galois_dual)

lemma dual_cl_galois_dualise: "\<lbrakk>dual_cl_galois_connection F G \<Longrightarrow> P F G; cl_galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
  by (metis cl_galois_dual)

lemma (in cl_galois_connection) poset_conn: "galois_connection \<pi>\<^sup>* \<pi>\<^sub>*"
proof (unfold_locales, intro allI)
  fix x and y
  show "(\<pi>\<^sup>* x \<le> y) = (x \<le> \<pi>\<^sub>* y)" by (metis cl_galois_property)
qed

lemma poset_galois: "cl_galois_connection F G \<Longrightarrow> galois_connection F G"
  by (metis cl_galois_connection.poset_conn)

definition cl_lower_adjoint :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> bool" where
  "cl_lower_adjoint f \<equiv> \<exists>g. cl_galois_connection f g"

definition cl_upper_adjoint :: "('b::complete_lattice \<Rightarrow> 'a::complete_lattice) \<Rightarrow> bool" where
  "cl_upper_adjoint g \<equiv> \<exists>f. cl_galois_connection f g"

(* +------------------------------------------------------------------------+
   | Theorems 4.25(a) and 4.25(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma suprema_galois_aarts: "galois_connection f g = (ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y}))"
  nitpick oops

theorem suprema_galois: "cl_galois_connection f g = (mono f \<and> ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y}))"
proof
  assume "cl_galois_connection f g"
  thus "mono f \<and> ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y})"
    using galois_lub lower_preserves_joins poset_galois by (metis lower_adjoint_def max_galois)
next
  assume assms: "mono f \<and> ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y})"
  hence fmon: "mono f" and elj: "ex_join_preserving f" and a2: "\<forall>y. is_lub (g y) {x. f x \<le> y}" by metis+
  thus "cl_galois_connection f g"
  proof unfold_locales
    have left: "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
      by (metis Collect_def a2 is_lub_equiv mem_def order_refl)
    moreover have "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
    proof clarify
      fix x and y
      assume gr: "x \<le> g y"
      show "f x \<le> y"
      proof -
        have lem: "\<Sigma> (f ` {x. f x \<le> y}) \<le> y"
        proof (rule the_lub_leq)
          show "\<exists>z. is_lub z (f ` {x\<Colon>'a. f x \<le> y})" by (metis lub_ex)
        next
          fix z
          show "is_lub z (f ` {x\<Colon>'a. f x \<le> y}) \<longrightarrow> z \<le> y"
            by (smt Collect_def imageE is_lub_equiv mem_def)
        qed

        have "f x \<le> y \<Longrightarrow> x \<le> \<Sigma> {z. f z \<le> y}" by (metis a2 gr lub_is_lub)
        moreover have "x \<le> \<Sigma> {z. f z \<le> y} \<Longrightarrow> f x \<le> f (\<Sigma> {z. f z \<le> y})" by (metis fmon monoD)
        moreover have "(f x \<le> f (\<Sigma> {z. f z \<le> y})) = (f x \<le> \<Sigma> (f ` {z. f z \<le> y}))"
          by (metis a2 elj ex_join_preserving_def top_greatest)
        moreover have "... \<Longrightarrow> f x \<le> y" using lem by (metis order_trans)
        ultimately show ?thesis by (metis a2 gr lub_is_lub)
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)" by auto
  qed
qed

corollary suprema_galois_rule:
  "\<lbrakk>mono f; ex_join_preserving f; \<forall>y. is_lub (g y) {x. f x \<le> y}\<rbrakk> \<Longrightarrow> cl_galois_connection f g"
  using suprema_galois by auto

theorem infima_galois: "cl_galois_connection f g = (mono g \<and> ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y}))"
proof
  assume "cl_galois_connection f g"
  thus "mono g \<and> ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y})"
    using galois_glb upper_preserves_meets poset_galois by (metis min_galois upper_adjoint_def)
next
  assume assms: "mono g \<and> ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y})"
  hence gmon: "mono g" and elj: "ex_meet_preserving g" and a2: "\<forall>x. is_glb (f x) {y. x \<le> g y}"  by metis+
  thus "cl_galois_connection f g"
  proof unfold_locales
    have right: "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
      by (metis Collect_def a2 is_glb_equiv mem_def order_refl)
    moreover have "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
    proof clarify
      fix x and y
      assume gr: "f x \<le> y"
      show "x \<le> g y"
      proof -
        have lem: "x \<le> \<Pi> (g ` {y. x \<le> g y})"
        proof (rule the_glb_leq)
          show "\<exists>z. is_glb z (g ` {y\<Colon>'b. x \<le> g y})" by (metis glb_ex)
        next
          fix z
          show "is_glb z (g ` {y\<Colon>'b. x \<le> g y}) \<longrightarrow> x \<le> z"
            by (smt Collect_def imageE is_glb_equiv mem_def)
        qed

        have "x \<le> g y \<Longrightarrow> \<Pi> {z. x \<le> g z} \<le> y" by (metis a2 gr glb_is_glb)
        moreover have "\<Pi> {z. x \<le> g z} \<le> y \<Longrightarrow> g (\<Pi> {z. x \<le> g z}) \<le> g y" by (metis gmon monoD)
        moreover have "(g (\<Pi> {z. x \<le> g z}) \<le> g y) = (\<Pi> (g ` {z. x \<le> g z}) \<le> g y)"
          by (metis a2 elj ex_meet_preserving_def top_greatest)
        moreover have "... \<Longrightarrow> x \<le> g y" using lem by (metis order_trans)
        ultimately show ?thesis by (metis a2 gr glb_is_glb)
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)" by auto
  qed
qed

corollary infima_galois_rule:
  "\<lbrakk>mono g; ex_meet_preserving g; \<forall>x. is_glb (f x) {y. x \<le> g y}\<rbrakk> \<Longrightarrow> cl_galois_connection f g"
  using infima_galois by auto

(* +------------------------------------------------------------------------+
   | Theorems 4.26 and 4.27                                                 |
   +------------------------------------------------------------------------+ *)

theorem cl_lower_join_preserving: "cl_lower_adjoint f = (mono f \<and> ex_join_preserving f)"
proof
  assume lower: "cl_lower_adjoint f"
  show "mono f \<and> ex_join_preserving f"
  proof (intro conjI)
    show "mono f" by (metis lower cl_lower_adjoint_def suprema_galois)
  next
    show "ex_join_preserving f" by (metis cl_lower_adjoint_def lower lower_adjoint_def lower_preserves_joins poset_galois)
  qed
next
  assume "mono f \<and> ex_join_preserving f"
  hence fmon: "mono f" and elj: "ex_join_preserving f" and a: "\<forall>y. \<exists>z. is_lub z {x. f x \<le> y}" by (metis lub_ex)+
  have "\<exists>g. \<forall>y. is_lub (g y) {x. f x \<le> y}"
  proof
    show "\<forall>y. is_lub (\<Sigma> {x. f x \<le> y}) {x. f x \<le> y}" by (metis a lub_is_lub)
  qed
  thus "cl_lower_adjoint f" by (metis cl_lower_adjoint_def elj fmon suprema_galois_rule)
qed

theorem cl_upper_join_preserving: "cl_upper_adjoint g = (mono g \<and> ex_meet_preserving g)"
proof
  assume upper: "cl_upper_adjoint g"
  show "mono g \<and> ex_meet_preserving g"
  proof (intro conjI)
    show "mono g" by (metis upper cl_upper_adjoint_def infima_galois)
  next
    show "ex_meet_preserving g" by (metis cl_upper_adjoint_def upper upper_adjoint_def upper_preserves_meets poset_galois)
  qed
next
  assume "mono g \<and> ex_meet_preserving g"
  hence gmon: "mono g" and egj: "ex_meet_preserving g" and a: "\<forall>x. \<exists>z. is_glb z {y. x \<le> g y}" by (metis glb_ex)+
  have "\<exists>f. \<forall>x. is_glb (f x) {y. x \<le> g y}"
  proof
    show "\<forall>x. is_glb (\<Pi> {y. x \<le> g y}) {y. x \<le> g y}" by (metis a glb_is_glb)
  qed
  thus "cl_upper_adjoint g" by (metis cl_upper_adjoint_def egj gmon infima_galois_rule)
qed

(* +------------------------------------------------------------------------+
   | Definition 2.28                                                        |
   +------------------------------------------------------------------------+ *)


lemma join_preserving_is_ex: "join_preserving f \<Longrightarrow> ex_join_preserving f"
  by (metis ex_join_preserving_def join_preserving_def)

lemma meet_preserving_is_ex: "meet_preserving f \<Longrightarrow> ex_meet_preserving f"
  by (metis ex_meet_preserving_def meet_preserving_def)

lemma galois_join_preserving: "cl_galois_connection f g \<Longrightarrow> join_preserving f"
  by (metis ex_join_preserving_def lub_ex subset_UNIV suprema_galois join_preserving_def)

lemma galois_meet_preserving: "cl_galois_connection f g \<Longrightarrow> meet_preserving g"
  by (metis ex_meet_preserving_def glb_ex subset_UNIV infima_galois meet_preserving_def)

(* +------------------------------------------------------------------------+
   | Theorems 4.36 and 4.37                                                 |
   +------------------------------------------------------------------------+ *)

theorem upper_exists: "cl_lower_adjoint f = (mono f \<and> join_preserving f)"
  by (metis cl_lower_adjoint_def cl_lower_join_preserving galois_join_preserving join_preserving_is_ex)

theorem lower_exists: "cl_upper_adjoint g = (mono g \<and> meet_preserving g)"
  by (metis cl_upper_adjoint_def cl_upper_join_preserving galois_meet_preserving meet_preserving_is_ex)

(* +------------------------------------------------------------------------+
   | Fixpoints and Galois connections                                       |
   +------------------------------------------------------------------------+ *)

lemma fixpoint_rolling: assumes conn: "galois_connection f g"
  shows "f (\<mu> (g \<circ> f)) = \<mu> (f \<circ> g)"
proof
  show "(f \<circ> g) (f (\<mu> (g \<circ> f))) = f (\<mu> (g \<circ> f))" by (metis assms o_def semi_inverse1)
next
  fix y assume fgy: "(f \<circ> g) y = y"
  have "\<mu> (g \<circ> f) \<le> g y" (* Sledgehammer could do this in one step *)
  proof
    show "mono (g \<circ> f)" by (metis assms galois_mono1)
    show "(g \<circ> f) (g y) \<le> g y" by (metis fgy o_def order_refl)
  qed
  thus "f (\<mu> (g \<circ> f)) \<le> y" by (metis conn galois_connection.galois_property)
qed

lemma greatest_fixpoint_rolling: assumes conn: "galois_connection f g"
  shows "g (\<nu> (f \<circ> g)) = \<nu> (g \<circ> f)"
proof
  show "(g \<circ> f) (g (\<nu> (f \<circ> g))) = g (\<nu> (f \<circ> g))" by (metis assms o_def semi_inverse2)
next
  fix y assume gfy: "(g \<circ> f) y = y"
  have "f y \<le> \<nu> (f \<circ> g)"
  proof
    show "mono (f \<circ> g)" by (metis assms galois_mono2)
    show "f y \<le> (f \<circ> g) (f y)" by (metis gfy o_def order_refl)
  qed
  thus "y \<le> g (\<nu> (f \<circ> g))" by (metis conn galois_connection.galois_property)
qed

(* +------------------------------------------------------------------------+
   | Fixpoint Fusion                                                        |
   +------------------------------------------------------------------------+ *)

(* uses lfp_equality_var then fixpoint_induction *)

theorem fixpoint_fusion [simp]:
  assumes upper_ex: "lower_adjoint f"
  and hmon: "mono h" and kmon: "mono k"
  and comp: "f\<circ>h = k\<circ>f"
  shows "f (\<mu> h) = \<mu> k"
proof
  show "k (f (\<mu> h)) = f (\<mu> h)" by (metis comp fixpoint_computation hmon o_def)
next
  fix y assume ky: "k y = y"
  obtain g where conn: "galois_connection f g" by (metis lower_adjoint_def upper_ex)
  have "\<mu> h \<le> g y" using hmon
  proof (rule fixpoint_induction)
    have "f (g y) \<le> y" by (metis conn galois_connection.deflation)
    hence "f (h (g y)) \<le> y" by (metis comp kmon ky mem_def monoD o_def)
    thus "h (g y) \<le> g y" by (metis conn galois_connection.galois_property)
  qed
  thus "f (\<mu> h) \<le> y" by (metis conn galois_connection.galois_property)
qed

theorem greatest_fixpoint_fusion [simp]:
  assumes lower_ex: "upper_adjoint g"
  and hmon: "mono h" and kmon: "mono k"
  and comp: "g\<circ>h = k\<circ>g"
  shows "g (\<nu> h) = \<nu> k"
proof
  show "k (g (\<nu> h)) = g (\<nu> h)" by (metis comp greatest_fixpoint_computation hmon o_def)
next
  fix y assume ky: "k y = y"
  obtain f where conn: "galois_connection f g" by (metis lower_ex upper_adjoint_def)
  have "f y \<le> \<nu> h" using hmon
  proof (rule greatest_fixpoint_induction)
    have "y \<le> g (f y)" by (metis conn galois_connection.inflation)
    hence "y \<le> g (h (f y))" by (metis comp kmon ky mem_def monoD o_def)
    thus "f y \<le> h (f y)" by (metis conn galois_connection.galois_property)
  qed
  thus "y \<le> g (\<nu> h)" by (metis conn galois_connection.galois_property)
qed

(* +------------------------------------------------------------------------+
   | Join semilattices with zero and dioids                                 |
   +------------------------------------------------------------------------+ *)

translations "x+y" == "x\<squnion>y"

class join_semilattice_zero = join_semilattice + zero +
  assumes add_zerol: "0\<squnion>x = x"

begin

  lemma add_iso: "x \<le> y \<longrightarrow> x\<squnion>z \<le> y\<squnion>z"
    by (smt add_assoc add_comm add_idem leq_def)

  lemma add_ub: "x \<le> x\<squnion>y"
    by (metis add_assoc add_idem leq_def)

  lemma add_lub: "x\<squnion>y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
    by (metis add_comm add_iso add_ub leq_def)

  lemma min_zero: "0 \<le> x"
    by (metis add_zerol leq_def)

end

class dioid = join_semilattice_zero + one + mult_op +
  assumes mult_assoc: "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
  and distr: "(x\<squnion>y)\<cdot>z = x\<cdot>z\<squnion>y\<cdot>z"
  and distl: "x\<cdot>(y\<squnion>z) = x\<cdot>y\<squnion>x\<cdot>z"
  and mult_onel: "1\<cdot>x = x"
  and mult_oner: "x\<cdot>1 = x"
  and annir: "0\<cdot>x = 0"
  assumes annil: "x\<cdot>0 = 0"

begin

  lemma mult_isor: "x \<le> y \<longrightarrow> x\<cdot>z \<le> y\<cdot>z"
    by (metis distr leq_def)

  lemma mult_isol: "x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y"
    by (metis distl leq_def)

  lemma mult_double_iso: "w \<le> x \<and> y \<le> z \<longrightarrow> w\<cdot>y \<le> x\<cdot>z"
    by (metis mult_isol mult_isor order_trans)

  lemma order_prop: "(x \<le> y) \<longleftrightarrow> (\<exists>z.(x\<squnion>z = y))"
    by (metis leq_def add_ub)

end

(* +------------------------------------------------------------------------+
   | Kleene Algebra                                                         |
   +------------------------------------------------------------------------+ *)

(* This works extremely well until you want to use the plus for nat *)
translations "x+y" == "x\<squnion>y"

class kleene_algebra = dioid + star_op +
  assumes star_unfoldl: "1+x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_unfoldr: "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  and star_inductl: "z+x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"
  and star_inductr: "z+y\<cdot>x \<le> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"

begin

lemma star_ref: "1 \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldl)

lemma star_trans_eq: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis eq_iff mult_isor mult_onel  star_ref  add_lub eq_iff star_inductl star_unfoldl)

lemma star_1l: "x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldl)

lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  by (metis add_comm leq_def eq_iff star_inductl)

lemma star_subdist:  "x\<^sup>\<star> \<le> (x+y)\<^sup>\<star>"
  by (metis add_lub distr star_1l star_ref star_inductl mult_oner)

lemma star_iso: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis leq_def star_subdist)

lemma star_invol: "x\<^sup>\<star> = (x\<^sup>\<star>)\<^sup>\<star>"
by (smt antisym distl leq_def mult_oner star_1l star_inductl star_ref star_trans_eq)

lemma star2: "(1+x)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis add_comm distr leq_def mult_onel mult_oner star_1l star_inductl star_invol star_ref star_subdist eq_iff)

lemma star_ext: "x \<le> x\<^sup>\<star>"
  by (smt add_lub leq_def mult_oner star_unfoldl distl)

lemma star_sim1: "x\<cdot>z \<le> z\<cdot>y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> z\<cdot>y\<^sup>\<star>"
  by (smt add_comm add_lub distr leq_def mult_assoc mult_oner star_1l star_ext star_inductl star_invol star_iso star_ref distl)

lemma star_slide1: "(x\<cdot>y)\<^sup>\<star>\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  by (metis eq_iff mult_assoc star_sim1)

lemma star_unfoldl_eq: "x\<^sup>\<star> = 1+x\<cdot>x\<^sup>\<star>"
  by (smt add_comm add_iso distl leq_def star_1l star_ref mult_oner star_inductl antisym star_unfoldl)

lemma star_denest: "(x+y)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
proof -
  have "(x+y)\<^sup>\<star> \<le> (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
    by (metis add_lub mult_double_iso mult_onel mult_oner star_ext star_iso star_ref)
  thus ?thesis
    by (metis add_comm eq_iff mult_double_iso star_invol star_iso star_subdist star_trans_eq)
qed

lemma star_unfoldr_eq: "1+x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
  by (smt distl distr mult_assoc mult_onel mult_oner star_unfoldl_eq star_inductl  eq_iff star_unfoldr)

lemma star_slide: "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  by (smt add_comm mult_assoc star_unfoldr_eq star_slide1 mult_isor add_iso mult_isol distl mult_oner distr mult_onel star_unfoldl_eq eq_iff star_slide1)

lemma star_slide_var: "x\<^sup>\<star>\<cdot>x = x\<cdot>x\<^sup>\<star>"
  by (metis mult_onel mult_oner star_slide)

end

class star_continuous_ka = dioid + star_op +
  assumes ex_star: "\<forall>x y z. \<exists>w. is_lub w (powers_c x y z)"
  and star_def:"x\<cdot>y\<^sup>\<star>\<cdot>z = \<Sigma> (powers_c x y z)"


class quantale = complete_lattice + mult_op +
  assumes qmult_assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
  and inf_distl: "x \<cdot> \<Sigma> Y = \<Sigma> ((\<lambda>y. x\<cdot>y) ` Y)"
  and inf_distr: "\<Sigma> Y \<cdot> x = \<Sigma> ((\<lambda>y. y\<cdot>x) ` Y)"

begin

  lemma bot_zeror: "x \<cdot> \<bottom> = \<bottom>"
  proof -
    have "x \<cdot> \<Sigma> {} = \<Sigma> ((\<lambda>y. x\<cdot>y) ` {})" using inf_distl .
    thus ?thesis by simp
  qed

  lemma bot_zerol: "\<bottom> \<cdot> x = \<bottom>"
  proof -
    have "\<Sigma> {} \<cdot> x = \<Sigma> ((\<lambda>y. y\<cdot>x) ` {})" using inf_distr .
    thus ?thesis by simp
  qed

  lemma qdistl1: "x \<cdot> (y + z) = (x \<cdot> y) + (x \<cdot> z)"
  proof -
    have "x \<cdot> \<Sigma> {y,z} = \<Sigma> ((\<lambda>y. x\<cdot>y) ` {y,z})" using inf_distl .
    thus ?thesis by (simp add: join_def)
  qed

  lemma qdistr1: "(y + z) \<cdot> x = (y \<cdot> x) + (z \<cdot> x)"
  proof -
    have "\<Sigma> {y,z} \<cdot> x = \<Sigma> ((\<lambda>y. y\<cdot>x) ` {y,z})" using inf_distr .
    thus ?thesis by (simp add: join_def)
  qed

end

class unital_quantale = quantale + one +
  assumes qunitl: "1 \<cdot> x = x"
  and qunitr: "x \<cdot> 1 = x"

sublocale unital_quantale \<subseteq> dioid where zero = bot
proof
  fix x y z :: 'a
  show "\<bottom> + x = x" by simp
  show "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)" using qmult_assoc .
  show "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z" using qdistr1 .
  show "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z" using qdistl1 .
  show "1 \<cdot> x = x" using qunitl .
  show "x \<cdot> 1 = x" using qunitr .
  show "\<bottom> \<cdot> x = \<bottom>" using bot_zerol .
  show "x \<cdot> \<bottom> = \<bottom>" using bot_zeror .
qed

context unital_quantale
begin

  primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<^bsup>_\<^esup>" [101,50] 100) where
      "x\<^bsup>0\<^esup>  = 1"
    | "x\<^bsup>Suc n\<^esup> = x\<cdot>x\<^bsup>n\<^esup>"

  definition powers :: "'a \<Rightarrow> 'a set" where
    "powers x  = {y. (\<exists>i. y = power x i)}"

end


class star_quantale = unital_quantale + star_op +
  assumes qstar: "x\<^sup>\<star> = \<Sigma> (powers x)"

end
