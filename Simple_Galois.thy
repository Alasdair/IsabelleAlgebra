theory Simple_Galois
  imports Main
begin

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

context order
begin

(* Pointfree ordering *)

definition pleq :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "pleq f g \<equiv> \<forall>x. f x \<le> g x"

definition isotone :: "('a \<Rightarrow> 'a) set" where
  "isotone f \<equiv> \<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y"

lemma isotoneD: "\<lbrakk>isotone f; x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> f y"
  by (metis isotone_def)

definition idempotent :: "('a \<Rightarrow> 'a) set" where
  "idempotent f \<equiv> f \<circ> f = f"

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

lemma the_lub_geq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<Longrightarrow> x \<le> z\<rbrakk> \<Longrightarrow> x \<le> \<Sigma> X"
  by (metis is_lub_unique lub_def the_equality)

lemma singleton_lub: "\<Sigma> {y} = y"
  by (simp only: lub_def, rule the_equality, simp_all add: is_lub_def is_ub_def, metis eq_iff)

lemma surjective_lub: "surj \<Sigma>"
proof (simp only: surj_def, clarify)
  fix y
  show "\<exists>x. y = \<Sigma> x" by (metis singleton_lub)
qed

lemma lub_subset: "\<lbrakk>X \<subseteq> Y; is_lub x X; is_lub y Y\<rbrakk> \<Longrightarrow> x \<le> y" by (metis in_mono is_lub_def is_ub_def)

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

(* Join and meet preserving maps *)

definition ex_join_preserving :: "('a \<Rightarrow> 'a) set" where
  "ex_join_preserving f \<equiv> \<forall>X\<subseteq>UNIV. (\<exists>x. is_lub x X) \<longrightarrow> \<Sigma> (f ` X) = f (\<Sigma> X)"

definition ex_meet_preserving :: "('a \<Rightarrow> 'a) set" where
  "ex_meet_preserving g \<equiv> \<forall>X\<subseteq>UNIV. (\<exists>x. is_glb x X) \<longrightarrow> \<Pi> (g ` X) = g (\<Pi> X)"

definition join_preserving :: "('a \<Rightarrow> 'a) set" where
  "join_preserving f \<equiv> \<forall>X\<subseteq>UNIV. \<Sigma> (f ` X) = f (\<Sigma> X)"

definition meet_preserving :: "('a \<Rightarrow> 'a) set" where
  "meet_preserving g \<equiv> \<forall>X\<subseteq>UNIV. \<Pi> (g ` X) = g (\<Pi> X)"

end

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

lemma lpp_unique: "\<lbrakk>is_lpp x f; is_lpp y f\<rbrakk> \<Longrightarrow> x = y"
  by (metis eq_iff is_lpp_def_var)

lemma gpp_unique: "\<lbrakk>is_gpp x f; is_gpp y f\<rbrakk> \<Longrightarrow> x = y"
  by (metis eq_iff is_gpp_def_var)

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

lemma lpp_is_lfp: "\<lbrakk>isotone f; is_lpp x f\<rbrakk> \<Longrightarrow> is_lfp x f"
  apply (simp add: is_lpp_def is_lfp_def is_fp_def is_pre_fp_def)
  by (metis eq_iff isotoneD)

lemma gpp_is_gfp: "\<lbrakk>isotone f; is_gpp x f\<rbrakk> \<Longrightarrow> is_gfp x f"
  apply (simp add: is_gpp_def is_gfp_def is_fp_def is_post_fp_def)
  by (metis isotone_def antisym)

(* +------------------------------------------------------------------------+
   | Knaster-Tarski                                                         |
   +------------------------------------------------------------------------+ *)

(* Modified version of Wenzel's proof of the Knaster-Tarski theorem *)

theorem knaster_tarski_lpp:
  assumes fmon: "isotone f"
  obtains a where "is_lpp a f"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Pi> ?H"
  have "is_pre_fp ?a f"
  proof -
    have "\<forall>x\<in>?H. ?a \<le> x" by (metis glb_least)
    hence "\<forall>x\<in>?H. f ?a \<le> f x" by (metis assms glb_least isotoneD)
    hence "\<forall>x\<in>?H. f ?a \<le> x" by (metis Collect_def mem_def order_trans)
    hence "f ?a \<le> \<Pi> ?H" by (smt glb_greatest)
    thus ?thesis by (metis is_pre_fp_def)
  qed
  moreover have "f y \<le> y \<Longrightarrow> ?a \<le> y"
    by (metis Collect_def glb_least mem_def)
  ultimately show "is_lpp ?a f"
    by (smt is_lpp_def Collect_def glb_least mem_def)
qed

corollary is_lpp_lpp [intro?]: "isotone f \<Longrightarrow> is_lpp (\<mu>\<^sub>\<le> f) f"
  using knaster_tarski_lpp by (metis lpp_equality)

theorem knaster_tarski:
  assumes fmon: "isotone f"
  obtains a where "is_lfp a f"
  by (metis assms is_lpp_lpp lpp_is_lfp)

corollary knaster_tarski_var: "isotone f \<Longrightarrow> \<exists>!x. is_lfp x f"
  using knaster_tarski by (metis lfp_equality)

corollary is_lfp_lfp [intro?]: "isotone f \<Longrightarrow> is_lfp (\<mu> f) f"
  using knaster_tarski by (metis lfp_equality)

(* Knaster-Tarski for greatest fixpoints *)

theorem knaster_tarski_gpp:
  assumes fmon: "isotone f"
  obtains a :: "'a" where "is_gpp a f"
proof
  let ?H = "{u. u \<le> f u}"
  let ?a = "\<Sigma> ?H"
  have "is_post_fp ?a f"
  proof -
    have "\<forall>x\<in>?H. x \<le> ?a" by (metis lub_least)
    hence "\<forall>x\<in>?H. x \<le> f ?a"
      by (metis (full_types) Collect_def assms lub_least mem_def isotoneD order_trans)
    hence "\<Sigma> ?H \<le> f ?a" by (smt lub_greatest)
    thus ?thesis by (metis is_post_fp_def)
  qed
  moreover have "y \<le> f y \<Longrightarrow> y \<le> ?a"
    by (metis Collect_def lub_least mem_def order_refl)
  ultimately show "is_gpp ?a f"
    by (smt is_gpp_def Collect_def lub_least mem_def)
qed

corollary is_gpp_gpp [intro?]: "isotone f \<Longrightarrow> is_gpp (\<nu>\<^sub>\<le> f) f"
  using knaster_tarski_gpp by (metis gpp_equality)

theorem knaster_tarski_greatest:
  assumes fmon: "isotone f"
  obtains a :: "'a" where "is_gfp a f"
  by (metis assms is_gpp_gpp gpp_is_gfp)

corollary knaster_tarski_greatest_var: "isotone f \<Longrightarrow> \<exists>!x. is_gfp x f"
  using knaster_tarski_greatest by (metis gfp_equality)

corollary is_gfp_gfp [intro?]: "isotone f \<Longrightarrow> is_gfp (\<nu> f) f"
  using knaster_tarski_greatest by (metis gfp_equality)

lemma lfp_is_lpp: "\<lbrakk>isotone f; is_lfp x f\<rbrakk> \<Longrightarrow>  is_lpp x f"
  by (metis lfp_equality lpp_is_lfp is_lpp_lpp)

lemma lfp_is_lpp_var: "isotone f \<Longrightarrow> \<mu> f = \<mu>\<^sub>\<le> f"
  by (metis lfp_is_lpp lpp_equality is_lfp_lfp)

lemma gfp_is_gpp: "\<lbrakk>isotone f; is_gfp x f\<rbrakk> \<Longrightarrow>  is_gpp x f"
  by (metis gfp_equality gpp_is_gfp is_gpp_gpp)

lemma gfp_is_gpp_var: "isotone f \<Longrightarrow> \<nu> f = \<nu>\<^sub>\<le> f"
  by (metis gfp_is_gpp gpp_equality is_gfp_gfp)

(* We now show some more properties of fixpoints *)

(* +------------------------------------------------------------------------+
   | Fixpoint Computation                                                   |
   +------------------------------------------------------------------------+ *)

lemma prefix_point_computation [simp]: "isotone f \<Longrightarrow> f (\<mu>\<^sub>\<le> f) = \<mu>\<^sub>\<le> f"
  by (metis is_lpp_lpp lpp_is_lfp is_lfp_def is_fp_def)

lemma fixpoint_computation [simp]: "isotone f \<Longrightarrow> f (\<mu> f) = \<mu> f"
  by (metis is_lpp_lpp lfp_equality lpp_is_lfp prefix_point_computation)

lemma greatest_prefix_point_computation [simp]: "isotone f \<Longrightarrow> f (\<nu>\<^sub>\<le> f) = \<nu>\<^sub>\<le> f"
  by (metis is_gpp_gpp gpp_is_gfp is_gfp_def is_fp_def)

lemma greatest_fixpoint_computation [simp]: "isotone f \<Longrightarrow> f (\<nu> f) = \<nu> f"
  by (metis is_gpp_gpp gfp_equality gpp_is_gfp greatest_prefix_point_computation)

(* +------------------------------------------------------------------------+
   | Fixpoint Induction                                                     |
   +------------------------------------------------------------------------+ *)

lemma prefix_point_induction [intro?]:
  assumes fmon: "isotone f"
  and pp: "f x \<le> x" shows "\<mu>\<^sub>\<le> f \<le> x"
proof (unfold least_prefix_point_def, rule the1I2)
  show "\<exists>!x. is_lpp x f" using knaster_tarski_lpp by (metis fmon lpp_equality)
next
  fix y
  show "is_lpp y f \<Longrightarrow> y \<le> x" unfolding is_lpp_def by (metis pp)
qed

lemma fixpoint_induction [intro?]:
  assumes fmon: "isotone f"
  and fp: "f x \<le> x" shows "\<mu> f \<le> x"
  by (metis fmon fp is_lpp_lpp lfp_equality lpp_is_lfp prefix_point_induction)

lemma greatest_postfix_point_induction [intro?]:
  assumes fmon: "isotone f"
  and pp: "x \<le> f x" shows "x \<le> \<nu>\<^sub>\<le> f"
proof (unfold greatest_postfix_point_def, rule the1I2)
  show "\<exists>!x. is_gpp x f" using knaster_tarski_gpp by (metis fmon gpp_equality)
next
  fix y
  show "is_gpp y f \<Longrightarrow> x \<le> y" unfolding is_gpp_def by (metis pp)
qed

lemma greatest_fixpoint_induction [intro?]:
  assumes fmon: "isotone f"
  and fp: "x \<le> f x" shows "x \<le> \<nu> f"
  by (metis fmon fp is_gpp_gpp gfp_equality gpp_is_gfp greatest_postfix_point_induction)

lemma fixpoint_compose:
  assumes kmon: "isotone k" and comp: "g\<circ>k = k\<circ>h" and fp: "is_fp x h"
  shows "is_fp (k x) g"
proof (unfold is_fp_def)
  have "h x = x" using fp by (unfold is_fp_def)
  hence "k (h x) = k x" by metis
  moreover have "g (k x) = (k (h x))" by (metis comp o_def)
  ultimately show "g (k x) = k x" by metis
qed

lemma fixpoint_mono:
  assumes fmon: "isotone f" and gmon: "isotone g"
  and fg: "f \<sqsubseteq> g" shows "\<mu> f \<le> \<mu> g"
proof -
  show "\<mu> f \<le> \<mu> g" using fmon
  proof (rule fixpoint_induction)
    have "f (\<mu> g) \<le> g (\<mu> g)" using fg unfolding pleq_def ..
    thus "f (\<mu> g) \<le> \<mu> g" using gmon by simp
  qed
qed

lemma greatest_fixpoint_mono:
  assumes fmon: "isotone f" and gmon: "isotone g"
  and fg: "f \<sqsubseteq> g" shows "\<nu> f \<le> \<nu> g"
proof -
  show "\<nu> f \<le> \<nu> g" using gmon
  proof (rule greatest_fixpoint_induction)
    have "f (\<nu> f) \<le> g (\<nu> f)" using fg unfolding pleq_def ..
    thus "\<nu> f \<le> g (\<nu> f)" using fmon by simp
  qed
qed

end

(* +------------------------------------------------------------------------+
   | Galois Connections                                                     |
   +------------------------------------------------------------------------+ *)

context order
begin

definition galois_connection :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "galois_connection f g \<equiv> \<forall>x y. (f x \<le> y) \<longleftrightarrow> (x \<le> g y)"

definition dual_galois_connection :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "dual_galois_connection f g \<equiv> \<forall>x y. (f x \<ge> y) \<longleftrightarrow> (x \<ge> g y)"

definition lower_adjoint :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "lower_adjoint f \<equiv> \<exists>g. galois_connection f g"

definition upper_adjoint :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "upper_adjoint g \<equiv> \<exists>f. galois_connection f g"

lemma deflation: "galois_connection f g \<Longrightarrow> f (g y) \<le> y" by (metis galois_connection_def le_less)

lemma inflation: "galois_connection f g \<Longrightarrow> x \<le> g (f x)" by (metis galois_connection_def le_less)

lemma lower_iso: "galois_connection f g \<Longrightarrow> isotone f"
  by (metis galois_connection_def inflation isotone_def order_trans)

lemma upper_iso: "galois_connection f g \<Longrightarrow> isotone g"
  by (metis deflation galois_connection_def isotone_def order_trans)

lemma lower_comp: "galois_connection f g \<Longrightarrow> f \<circ> g \<circ> f = f"
proof
  fix x assume "galois_connection f g"
  thus "(f \<circ> g \<circ> f) x = f x"
    by (metis (full_types) antisym deflation inflation isotone_def lower_iso o_apply)
qed

lemma upper_comp: "galois_connection f g \<Longrightarrow> g \<circ> f \<circ> g = g"
proof
  fix x assume "galois_connection f g"
  thus "(g \<circ> f \<circ> g) x = g x"
    by (metis (full_types) antisym deflation inflation isotone_def o_apply upper_iso)
qed

lemma upper_idempotency1: "galois_connection f g \<Longrightarrow> idempotent (f \<circ> g)"
  by (metis idempotent_def o_assoc upper_comp)

lemma upper_idempotency2: "galois_connection f g \<Longrightarrow> idempotent (g \<circ> f)"
  by (metis idempotent_def o_assoc lower_comp)

lemma galois_dual: "galois_connection f g \<Longrightarrow> dual_galois_connection g f"
  by (metis dual_galois_connection_def galois_connection_def)

lemma dual_galois_dual: "dual_galois_connection f g \<Longrightarrow> galois_connection g f"
  by (metis dual_galois_connection_def galois_connection_def)

lemma galois_dualize: "\<lbrakk>galois_connection F G \<Longrightarrow> P F G; dual_galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
proof -
  assume dual: "dual_galois_connection G F" and p: "galois_connection F G \<Longrightarrow> P F G"
  have conn: "galois_connection F G" using dual by (rule dual_galois_dual)
  thus "P F G" by (rule p)
qed

lemma dual_galois_dualize: "\<lbrakk>dual_galois_connection F G \<Longrightarrow> P F G; galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
proof -
  assume g: "galois_connection G F" and p: "dual_galois_connection F G \<Longrightarrow> P F G"
  have dual_conn: "dual_galois_connection F G" using g by (rule galois_dual)
  thus "P F G" by (rule p)
qed

lemma galois_comp: assumes g1: "galois_connection F G" and g2 :"galois_connection H K"
  shows "galois_connection (F \<circ> H) (K \<circ> G)"
  by (smt g1 g2 galois_connection_def o_apply)

lemma galois_id: "galois_connection id id" by (metis galois_connection_def id_def)

lemma galois_isotone1: "galois_connection f g \<Longrightarrow> isotone (g \<circ> f)"
proof -
  assume g: "galois_connection f g"
  hence "isotone g" by (metis upper_iso)
  moreover have "isotone f" by (metis g lower_iso)
  ultimately show "isotone (g \<circ> f)" by (simp add: isotone_def)
qed

lemma galois_isotone2: "galois_connection f g \<Longrightarrow> isotone (f \<circ> g)"
proof -
  assume g: "galois_connection f g"
  hence "isotone g" by (metis upper_iso)
  moreover have "isotone f" by (metis g lower_iso)
  ultimately show "isotone (f \<circ> g)" by (simp add: isotone_def)
qed

lemma point_id1: "galois_connection f g \<Longrightarrow> id \<sqsubseteq> g \<circ> f"
  by (metis inflation id_apply o_apply pleq_def)

lemma point_id2: "galois_connection f g \<Longrightarrow> f \<circ> g \<sqsubseteq> id"
  by (metis deflation id_apply o_apply pleq_def)

lemma point_cancel: assumes g: "galois_connection f g" shows "f \<circ> g \<sqsubseteq> g \<circ> f"
proof -
  have "f \<circ> g \<sqsubseteq> id" using g point_id2 by blast
  moreover
  have "id \<sqsubseteq> g \<circ> f" using g point_id1 by blast
  ultimately
  show "f \<circ> g \<sqsubseteq> g \<circ> f"
    apply (simp only: pleq_def) by (metis order_trans)
qed

lemma cancel: assumes g: "galois_connection f g" shows "f (g x) \<le> g (f x)"
proof -
  have "f \<circ> g \<sqsubseteq> g \<circ> f" by (metis g point_cancel)
  thus "f (g x) \<le> g (f x)" by (simp only: pleq_def o_def)
qed

lemma cancel_cor1: assumes g: "galois_connection f g"
  shows "(g x = g y) \<longleftrightarrow> (f (g x) = f (g y))"
  by (metis assms upper_comp o_apply)

lemma cancel_cor2: assumes g: "galois_connection f g"
  shows "(f x = f y) \<longleftrightarrow> (g (f x) = g (f y))"
  by (metis assms lower_comp o_apply)

lemma semi_inverse1: "galois_connection f g \<Longrightarrow> f x = f (g (f x))"
  by (metis o_def lower_comp)

lemma semi_inverse2: "galois_connection f g \<Longrightarrow> g x = g (f (g x))"
  by (metis o_def upper_comp)

lemma universal_mapping_property1:
  assumes a: "isotone g" and b: "\<forall>x. x \<le> g (f x)"
  and c: "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
  shows "galois_connection f g"
proof (simp add: galois_connection_def, intro allI)
  fix x and y
  show "(f x \<le> y) = (x \<le> g y)" by (metis isotone_def a b c order_trans)
qed

lemma universal_mapping_property2:
  assumes a: "isotone f" and b: "\<forall>x. f (g x) \<le> x"
  and c: "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
  shows "galois_connection f g"
proof (simp add: galois_connection_def, intro allI)
  fix x and y
  show "(f x \<le> y) = (x \<le> g y)" by (metis a b c isotone_def order_trans)
qed

lemma galois_ump2: "galois_connection f g = (isotone f \<and> (\<forall>y. f (g y) \<le> y) \<and> (\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y))"
  by (metis deflation dual_galois_connection_def galois_dual lower_iso universal_mapping_property2)

lemma galois_ump1: "galois_connection f g = (isotone g \<and> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y))"
  by (metis galois_connection_def inflation universal_mapping_property1 upper_iso)

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma ore_galois:
  assumes a: "\<forall>x. x \<le> g (f x)" and b: "\<forall>x. f (g x) \<le> x"
  and c: "isotone f" and d: "isotone g"
  shows "galois_connection f g"
proof (simp add: galois_connection_def, intro allI)
  fix x and y
  show "(f x \<le> y) = (x \<le> g y)" by (metis a b c d isotone_def order_trans)
qed

(* +------------------------------------------------------------------------+
   | Theorems 4.32(a) and 4.32(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma perfect1: "galois_connection f g \<Longrightarrow> g (f x) = x \<longleftrightarrow> x \<in> range g"
proof -
  assume conn: "galois_connection f g"
  have "g (f x) = x \<Longrightarrow> x \<in> range g" by (metis range_eqI)
  moreover have "x \<in> range g \<Longrightarrow> g (f x) = x"
  proof -
    assume "x \<in> range g"
    hence "\<exists>y. x = g y" by (metis image_iff)
    hence "\<exists>y. (x = g y) \<and> (x = g (f (g y)))" using conn semi_inverse2 by metis
    thus ?thesis by metis
  qed
  ultimately show ?thesis by metis
qed

lemma perfect2: "galois_connection f g \<Longrightarrow> f (g x) = x \<longleftrightarrow> x \<in> range f"
proof -
  assume conn: "galois_connection f g"
  have "f (g x) = x \<Longrightarrow> x \<in> range f" by (metis range_eqI)
  moreover have "x \<in> range f \<Longrightarrow> f (g x) = x"
  proof -
    assume "x \<in> range f"
    hence "\<exists>y. x = f y" by (metis image_iff)
    hence "\<exists>y. (x = f y) \<and> (x = f (g (f y)))" using conn semi_inverse1 by metis
    thus ?thesis by metis
  qed
  ultimately show ?thesis by metis
qed

(* +------------------------------------------------------------------------+
   | Theorems 4.20(a) and 4.20(b)                                           |
   +------------------------------------------------------------------------+ *)

definition is_max :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_max x X \<equiv> x \<in> X \<and> is_lub x X"

definition is_min :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_min x X \<equiv> x \<in> X \<and> is_glb x X"

lemma galois_max: assumes conn: "galois_connection f g" shows "is_max (g y) {x. f x \<le> y}"
  by (simp add: is_max_def is_lub_equiv, metis assms galois_ump2 order_trans)

lemma galois_min: assumes conn: "galois_connection f g" shows "is_min (f x) {y. x \<le> g y}"
  by (simp add: is_min_def is_glb_equiv, metis assms galois_ump1 order_trans)

theorem max_galois: "galois_connection f g = (isotone f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y}))"
proof
  assume conn: "galois_connection f g"
  show "isotone f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y})"
  proof
    show "isotone f" by (metis conn lower_iso)
  next
    show "\<forall>y. is_max (g y) {x. f x \<le> y}" by (metis conn galois_max)
  qed
next
  assume "isotone f \<and> (\<forall>y. is_max (g y) {x. f x \<le> y})"
  hence fmon: "isotone f" and max: "\<forall>y. is_max (g y) {x. f x \<le> y}" by auto+
  show "galois_connection f g"
  proof (rule universal_mapping_property2)
    show "isotone f" by (metis fmon)
  next
    have max2: "\<forall>y. g y \<in> {x. f x \<le> y}" by (smt is_max_def max)
    hence "(g y \<in> {x. f x \<le> y}) = (f (g y) \<le> y)" by (simp only: mem_Collect_eq)
    thus p: "\<forall>y. f (g y) \<le> y" using max2 by auto
  next
    show "\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y"
    proof clarify
      fix x and y
      have lub1: "is_lub (g y) {x. f x \<le> y}"
        by (smt is_max_def max Collect_def is_lub_equiv mem_def)
      assume "f x \<le> y"
      thus "x \<le> g y" by (metis lub1 Collect_def is_lub_equiv mem_def order_refl)
    qed
  qed
qed

corollary max_galois_rule: "\<lbrakk>isotone f; \<forall>y. is_max (g y) {x. f x \<le> y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis max_galois)

theorem min_galois: "galois_connection f g = (isotone g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y}))"
proof
  assume conn: "galois_connection f g"
  show "isotone g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y})"
  proof
    show "isotone g" by (metis conn upper_iso)
  next
    show "\<forall>x. is_min (f x) {y. x \<le> g y}" by (metis conn galois_min)
  qed
next
  assume "isotone g \<and> (\<forall>x. is_min (f x) {y. x \<le> g y})"
  hence gmon: "isotone g" and min: "\<forall>x. is_min (f x) {y. x \<le> g y}" by auto+
  show "galois_connection f g"
  proof (rule universal_mapping_property1)
    show "isotone g" by (metis gmon)
  next
    have "\<forall>x. f x \<in> {y. x \<le> g y}" by (smt is_min_def min)
    moreover have "(f x \<in> {y. x \<le> g y}) = (x \<le> g (f x))" by (simp only: mem_Collect_eq)
    ultimately show "\<forall>x. x \<le> g (f x)" by auto
  next
    show "\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y"
    proof clarify
      fix x and y
      have glb1: "is_glb (f x) {y. x \<le> g y}" using is_min_def min
        by (smt Collect_def is_glb_equiv mem_def)
      assume "x \<le> g y"
      thus "f x \<le> y" by (metis glb1 Collect_def is_glb_equiv mem_def order_refl)
    qed
  qed
qed

corollary min_galois_rule: "\<lbrakk>isotone g; \<forall>x. is_min (f x) {y. x \<le> g y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis min_galois)

(* hide_fact galois_min galois_max *)

(* Corollary 4.21 *)

lemma galois_lub: "galois_connection f g \<Longrightarrow> is_lub (g y) {x. f x \<le> y}"
  by (simp add: is_lub_equiv, metis galois_ump2 order_trans)

lemma galois_glb: "galois_connection f g \<Longrightarrow> is_glb (f x) {y. x \<le> g y}"
  by (simp add: is_glb_equiv, metis galois_ump1 order_trans)

lemma galois_lub_var: "galois_connection f g \<Longrightarrow> g y = \<Sigma> {x. f x \<le> y}"
  by (metis galois_lub lub_is_lub)

lemma galois_glb_var: "galois_connection f g \<Longrightarrow> f x = \<Pi> {y. x \<le> g y}"
  by (metis galois_glb glb_is_glb)

(* +------------------------------------------------------------------------+
   | Lemma 4.24(a) and 4.24(b)                                              |
   +------------------------------------------------------------------------+ *)

lemma lower_lub: "\<lbrakk>is_lub x X; lower_adjoint f\<rbrakk> \<Longrightarrow> is_lub (f x) (f ` X)"
  by (smt galois_ump1 galois_ump2 image_iff is_lub_equiv lower_adjoint_def)

lemma upper_glb: "\<lbrakk>is_glb x X; upper_adjoint g\<rbrakk> \<Longrightarrow> is_glb (g x) (g ` X)" sorry

(* TODO: Make these proofs simpler *)

lemma lower_preserves_joins: assumes lower: "lower_adjoint f" shows "ex_join_preserving f"
proof (simp add: ex_join_preserving_def, intro allI impI)
  obtain g where conn: "galois_connection f g" by (metis lower lower_adjoint_def)
  fix X :: "'a set"
  show "(\<exists>x\<Colon>'a. is_lub x X) \<Longrightarrow> (\<Sigma> (f ` X) = f (\<Sigma> X))"
  proof -
    assume lub_exists: "\<exists>x. is_lub x X"
    have a: "\<forall>y. (f (\<Sigma> X) \<le> y) = (\<forall>z \<in> f`X. z \<le> y)"
      by (smt conn lub_exists galois_connection_def image_iff is_lub_equiv lub_is_lub rev_image_eqI)
    moreover have "\<forall>y. (\<forall>z \<in> f`X. z \<le> y) = (\<Sigma> (f ` X) \<le> y)"
    proof
      fix y
      have "\<forall>z \<in> f`X. z \<le> y \<Longrightarrow> \<Sigma> (f ` X) \<le> y"
        by (smt calculation is_lub_equiv lub_exists lub_is_lub)
      moreover have "\<Sigma> (f ` X) \<le> y \<Longrightarrow> \<forall>z \<in> f`X. z \<le> y"
        by (metis a assms lower_lub lub_exists lub_is_lub)
      ultimately show "(\<forall>z \<in> f`X. z \<le> y) = (\<Sigma> (f ` X) \<le> y)" by auto
    qed
    ultimately have "\<forall>y. (f (\<Sigma> X) \<le> y) = (\<Sigma> (f ` X) \<le> y)" by metis
    thus "\<Sigma> (f ` X) = f (\<Sigma> X)" by (metis eq_iff)
  qed
qed

lemma upper_preserves_meets: assumes upper: "upper_adjoint g" shows "ex_meet_preserving g"
proof (simp add: ex_meet_preserving_def, intro allI impI)
  obtain f where conn: "galois_connection f g" by (metis upper upper_adjoint_def)
  fix X :: "'a set"
  assume glb_exists: "\<exists>x. is_glb x X"
  have a: "\<forall>y. (y \<le> g (\<Pi> X)) = (\<forall>z \<in> g`X. y \<le> z)" using conn glb_exists
    by (smt galois_connection_def image_iff is_glb_equiv glb_is_glb rev_image_eqI)
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
  thus "\<Pi> (g ` X) = g (\<Pi> X)" by (metis eq_iff)
qed

end

context complete_lattice
begin

(* +------------------------------------------------------------------------+
   | Theorems 4.25(a) and 4.25(b)                                           |
   +------------------------------------------------------------------------+ *)

theorem suprema_galois: "galois_connection f g = (isotone f \<and> ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y}))"
proof
  assume "galois_connection f g"
  thus "isotone f \<and> ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y})"
    using galois_lub lower_preserves_joins by (metis lower_adjoint_def max_galois)
next
  assume assms: "isotone f \<and> ex_join_preserving f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y})"
  hence fmon: "isotone f" and elj: "ex_join_preserving f" and a2: "\<forall>y. is_lub (g y) {x. f x \<le> y}" by metis+
  thus "galois_connection f g"
  proof (simp add: galois_connection_def)
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
        moreover have "x \<le> \<Sigma> {z. f z \<le> y} \<Longrightarrow> f x \<le> f (\<Sigma> {z. f z \<le> y})" by (metis fmon isotoneD)
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
  "\<lbrakk>isotone f; ex_join_preserving f; \<forall>y. is_lub (g y) {x. f x \<le> y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  using suprema_galois by auto

theorem infima_galois: "galois_connection f g = (isotone g \<and> ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y}))"
proof
  assume "galois_connection f g"
  thus "isotone g \<and> ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y})"
    using galois_glb upper_preserves_meets by (metis min_galois upper_adjoint_def)
next
  assume assms: "isotone g \<and> ex_meet_preserving g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y})"
  hence gmon: "isotone g" and elj: "ex_meet_preserving g" and a2: "\<forall>x. is_glb (f x) {y. x \<le> g y}"  by metis+
  thus "galois_connection f g"
  proof (simp add: galois_connection_def)
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
          show "\<exists>z. is_glb z (g ` {y. x \<le> g y})" by (metis glb_ex)
        next
          fix z
          show "is_glb z (g ` {y. x \<le> g y}) \<longrightarrow> x \<le> z"
            by (smt Collect_def imageE is_glb_equiv mem_def)
        qed

        have "x \<le> g y \<Longrightarrow> \<Pi> {z. x \<le> g z} \<le> y" by (metis a2 gr glb_is_glb)
        moreover have "\<Pi> {z. x \<le> g z} \<le> y \<Longrightarrow> g (\<Pi> {z. x \<le> g z}) \<le> g y" by (metis gmon isotoneD)
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
  "\<lbrakk>isotone g; ex_meet_preserving g; \<forall>x. is_glb (f x) {y. x \<le> g y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  using infima_galois by auto

(* +------------------------------------------------------------------------+
   | Theorems 4.26 and 4.27                                                 |
   +------------------------------------------------------------------------+ *)

theorem cl_lower_join_preserving: "lower_adjoint f = (isotone f \<and> ex_join_preserving f)"
proof
  assume lower: "lower_adjoint f"
  show "isotone f \<and> ex_join_preserving f"
  proof (intro conjI)
    show "isotone f" by (metis lower lower_adjoint_def suprema_galois)
  next
    show "ex_join_preserving f" by (metis lower lower_preserves_joins)
  qed
next
  assume "isotone f \<and> ex_join_preserving f"
  hence fmon: "isotone f" and elj: "ex_join_preserving f" and a: "\<forall>y. \<exists>z. is_lub z {x. f x \<le> y}" by (metis lub_ex)+
  have "\<exists>g. \<forall>y. is_lub (g y) {x. f x \<le> y}"
  proof
    show "\<forall>y. is_lub (\<Sigma> {x. f x \<le> y}) {x. f x \<le> y}" by (metis a lub_is_lub)
  qed
  thus "lower_adjoint f" by (metis lower_adjoint_def elj fmon suprema_galois_rule)
qed

theorem cl_upper_join_preserving: "upper_adjoint g = (isotone g \<and> ex_meet_preserving g)"
proof
  assume upper: "upper_adjoint g"
  show "isotone g \<and> ex_meet_preserving g"
  proof (intro conjI)
    show "isotone g" by (metis upper upper_adjoint_def infima_galois)
  next
    show "ex_meet_preserving g" by (metis upper upper_preserves_meets)
  qed
next
  assume "isotone g \<and> ex_meet_preserving g"
  hence gmon: "isotone g" and egj: "ex_meet_preserving g" and a: "\<forall>x. \<exists>z. is_glb z {y. x \<le> g y}" by (metis glb_ex)+
  have "\<exists>f. \<forall>x. is_glb (f x) {y. x \<le> g y}"
  proof
    show "\<forall>x. is_glb (\<Pi> {y. x \<le> g y}) {y. x \<le> g y}" by (metis a glb_is_glb)
  qed
  thus "upper_adjoint g" by (metis upper_adjoint_def egj gmon infima_galois_rule)
qed

lemma join_preserving_is_ex: "join_preserving f \<Longrightarrow> ex_join_preserving f"
  by (metis ex_join_preserving_def join_preserving_def)

lemma meet_preserving_is_ex: "meet_preserving f \<Longrightarrow> ex_meet_preserving f"
  by (metis ex_meet_preserving_def meet_preserving_def)

lemma galois_join_preserving: "galois_connection f g \<Longrightarrow> join_preserving f"
  by (metis ex_join_preserving_def lub_ex subset_UNIV suprema_galois join_preserving_def)

lemma galois_meet_preserving: "galois_connection f g \<Longrightarrow> meet_preserving g"
  by (metis ex_meet_preserving_def glb_ex subset_UNIV infima_galois meet_preserving_def)

(* +------------------------------------------------------------------------+
   | Theorems 4.36 and 4.37                                                 |
   +------------------------------------------------------------------------+ *)

theorem upper_exists: "lower_adjoint f = (isotone f \<and> join_preserving f)"
  by (metis lower_adjoint_def cl_lower_join_preserving galois_join_preserving join_preserving_is_ex)

theorem lower_exists: "upper_adjoint g = (isotone g \<and> meet_preserving g)"
  by (metis upper_adjoint_def cl_upper_join_preserving galois_meet_preserving meet_preserving_is_ex)

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
    show "isotone (g \<circ> f)" by (metis assms galois_isotone1)
    show "(g \<circ> f) (g y) \<le> g y" by (metis fgy o_def order_refl)
  qed
  thus "f (\<mu> (g \<circ> f)) \<le> y" by (metis conn galois_connection_def)
qed

lemma greatest_fixpoint_rolling: assumes conn: "galois_connection f g"
  shows "g (\<nu> (f \<circ> g)) = \<nu> (g \<circ> f)"
proof
  show "(g \<circ> f) (g (\<nu> (f \<circ> g))) = g (\<nu> (f \<circ> g))" by (metis assms o_def semi_inverse2)
next
  fix y assume gfy: "(g \<circ> f) y = y"
  have "f y \<le> \<nu> (f \<circ> g)"
  proof
    show "isotone (f \<circ> g)" by (metis assms galois_isotone2)
    show "f y \<le> (f \<circ> g) (f y)" by (metis gfy o_def order_refl)
  qed
  thus "y \<le> g (\<nu> (f \<circ> g))" by (metis conn galois_connection_def)
qed

(* +------------------------------------------------------------------------+
   | Fixpoint Fusion                                                        |
   +------------------------------------------------------------------------+ *)

(* uses lfp_equality_var then fixpoint_induction *)

theorem fixpoint_fusion [simp]:
  assumes upper_ex: "lower_adjoint f"
  and hiso: "isotone h" and kiso: "isotone k"
  and comm: "f\<circ>h = k\<circ>f"
  shows "f (\<mu> h) = \<mu> k"
proof
  show "k (f (\<mu> h)) = f (\<mu> h)" by (metis comm fixpoint_computation hiso o_def)
next
  fix y assume ky: "k y = y"
  obtain g where conn: "galois_connection f g" by (metis lower_adjoint_def upper_ex)
  have "\<mu> h \<le> g y" using hiso
  proof (rule fixpoint_induction)
    have "f (g y) \<le> y" by (metis conn deflation)
    hence "f (h (g y)) \<le> y" by (metis comm kiso ky mem_def isotoneD o_def)
    thus "h (g y) \<le> g y" by (metis conn galois_connection_def)
  qed
  thus "f (\<mu> h) \<le> y" by (metis conn galois_connection_def)
qed

theorem greatest_fixpoint_fusion [simp]:
  assumes lower_ex: "upper_adjoint g"
  and hiso: "isotone h" and kiso: "isotone k"
  and comm: "g\<circ>h = k\<circ>g"
  shows "g (\<nu> h) = \<nu> k"
proof
  show "k (g (\<nu> h)) = g (\<nu> h)" by (metis comm greatest_fixpoint_computation hiso o_def)
next
  fix y assume ky: "k y = y"
  obtain f where conn: "galois_connection f g" by (metis lower_ex upper_adjoint_def)
  have "f y \<le> \<nu> h" using hiso
  proof (rule greatest_fixpoint_induction)
    have "y \<le> g (f y)" by (metis conn inflation)
    hence "y \<le> g (h (f y))" by (metis comm kiso ky mem_def isotoneD o_def)
    thus "f y \<le> h (f y)" by (metis conn galois_connection_def)
  qed
  thus "y \<le> g (\<nu> h)" by (metis conn galois_connection_def)
qed

end

(* +------------------------------------------------------------------------+
   | Join semilattices with zero and dioids                                 |
   +------------------------------------------------------------------------+ *)

class join_semilattice_zero = join_semilattice +
  fixes zero :: 'a
  assumes add_zerol: "zero\<squnion>x = x"

begin

  lemma add_iso: "x \<le> y \<longrightarrow> x\<squnion>z \<le> y\<squnion>z"
    by (smt add_assoc add_comm add_idem leq_def)

  lemma add_ub: "x \<le> x\<squnion>y"
    by (metis add_assoc add_idem leq_def)

  lemma add_lub: "x\<squnion>y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
    by (metis add_comm add_iso add_ub leq_def)

  lemma min_zero: "zero \<le> x"
    by (metis add_zerol leq_def)

  lemma lub_un: "is_lub w A \<Longrightarrow> is_lub (x\<squnion>w) ({x}\<union>A)"
    by (simp add: is_lub_equiv add_lub)

end

class dioid = join_semilattice_zero +
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 80)
  and one :: "'a"
  assumes mult_assoc: "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
  and distr: "(x\<squnion>y)\<cdot>z = x\<cdot>z\<squnion>y\<cdot>z"
  and distl: "x\<cdot>(y\<squnion>z) = x\<cdot>y\<squnion>x\<cdot>z"
  and mult_onel: "one\<cdot>x = x"
  and mult_oner: "x\<cdot>one = x"
  and annir: "zero\<cdot>x = zero"
  and annil: "x\<cdot>zero = zero"

begin

  lemma mult_isor: "x \<le> y \<longrightarrow> x\<cdot>z \<le> y\<cdot>z"
    by (metis distr leq_def)

  lemma mult_isol: "x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y"
    by (metis distl leq_def)

  lemma subdistr: "x\<cdot>z \<le> (x\<squnion>y)\<cdot>z"
    by (metis add_ub mult_isor)

  lemma subdistl: "z\<cdot>x \<le> z\<cdot>(x\<squnion>y)"
    by (metis add_ub mult_isol)

  lemma mult_double_iso: "w \<le> x \<and> y \<le> z \<longrightarrow> w\<cdot>y \<le> x\<cdot>z"
    by (metis mult_isol mult_isor order_trans)

  lemma order_prop: "(x \<le> y) \<longleftrightarrow> (\<exists>z.(x\<squnion>z = y))"
    by (metis leq_def add_ub)

  (* Powers *)

  primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<^bsup>_\<^esup>" [101,50] 100) where
    "x\<^bsup>0\<^esup>  = one"
  | "x\<^bsup>Suc n\<^esup> = x\<cdot>x\<^bsup>n\<^esup>"

  lemma power_add: "x\<^bsup>m\<^esup>\<cdot>x\<^bsup>n\<^esup> = x\<^bsup>m+n\<^esup>"
  proof (induct m)
    case 0 show ?case by (metis add_0_left mult_onel power.simps(1))
    case (Suc m) show ?case by (smt Suc add_Suc mult_assoc power.simps(2))
  qed

  lemma power_commutes: "x\<^bsup>n\<^esup>\<cdot>x = x\<cdot>x\<^bsup>n\<^esup>"
    by (smt power_add mult_oner power.simps)

  lemma power_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> (power x n)\<cdot>y \<le> y"
    by (induct n,  metis eq_refl mult_onel power.simps(1), smt add_assoc distl leq_def mult_assoc order_prop power.simps(2) power_commutes)

  lemma power_inductr_var: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>(power x n) \<le> y"
    by (induct n, metis mult_oner power.simps(1) order_refl, smt add_assoc distr leq_def mult_assoc order_prop power.simps(2)) --"5"
  definition powers :: "'a \<Rightarrow> 'a set" where
    "powers x  = {y. (\<exists>i. y = power x i)}"

  definition powers_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
    "powers_c x y z = {x\<cdot>w\<cdot>z| w. (\<exists>i. w = power y i)}"

  lemma powers_c_elim: "v\<in>(powers_c x y z) \<longleftrightarrow> (\<exists>w. v = x\<cdot>w\<cdot>z \<and> (\<exists>i. w = power y i))"
    by (simp add: powers_c_def)

  lemma powers_to_powers_c: "powers x = powers_c one x one"
    by auto (simp add: powers_c_elim mult_onel mult_oner, smt Collect_def mem_def powers_def)+

  lemma power_in_powers_c: "\<forall>i. x\<cdot>(power y i)\<cdot>z \<in> powers_c x y z"
    by (metis powers_c_elim)

  lemma powers_sucl: "powers_c x x one = {y. (\<exists>i. y = power x (Suc i))}"
    by  auto (metis mult_oner powers_c_elim, metis mult_oner power_in_powers_c)

  lemma powers_sucr: "powers_c one x x = {y. (\<exists>i. y = power x (Suc i))}"
    by auto (metis mult_onel power_commutes powers_c_elim, metis mult_onel power_commutes power_in_powers_c)

  lemma powers_suc: "powers_c x x one = powers_c one x x"
    by (metis powers_sucl powers_sucr)

  lemma powers_unfoldl: "{one}\<union>(powers_c x x one) = powers x"
  proof -
    have  "{one}\<union>(powers_c x x one) = {y. y = power x 0 \<or> (\<exists>i. y = power x (Suc i))}"
      by (metis insert_def insert_is_Un power.simps(1) powers_sucl Collect_disj_eq)
    also have "... = {y. (\<exists>i. y = power x i)}"
      by auto (smt power.simps(1), metis power.simps(2), metis (full_types) nat.exhaust power.simps(1) power.simps(2))
    ultimately show ?thesis
      by (metis powers_def)
  qed

end

(* +------------------------------------------------------------------------+
   | Kleene Algebra                                                         |
   +------------------------------------------------------------------------+ *)

(* This works extremely well until you want to use the plus for nat *)
(* translations "x+y" == "x\<squnion>y" *)

class kleene_algebra = dioid +
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)
  assumes star_unfoldl: "one\<squnion>x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_unfoldr: "one\<squnion>x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  and star_inductl: "z\<squnion>x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"
  and star_inductr: "z\<squnion>y\<cdot>x \<le> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"

begin

lemma star_ref: "one \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldl)

lemma star_trans_eq: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis eq_iff mult_isor mult_onel  star_ref  add_lub eq_iff star_inductl star_unfoldl)

lemma star_1l: "x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldl)

lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  by (metis add_comm leq_def eq_iff star_inductl)

lemma star_subdist:  "x\<^sup>\<star> \<le> (x\<squnion>y)\<^sup>\<star>"
  by (metis add_lub distr star_1l star_ref star_inductl mult_oner)

lemma star_iso: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis leq_def star_subdist)

lemma star_invol: "x\<^sup>\<star> = (x\<^sup>\<star>)\<^sup>\<star>"
by (smt antisym distl leq_def mult_oner star_1l star_inductl star_ref star_trans_eq)

lemma star2: "(one\<squnion>x)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis add_comm distr leq_def mult_onel mult_oner star_1l star_inductl star_invol star_ref star_subdist eq_iff)

lemma star_ext: "x \<le> x\<^sup>\<star>"
  by (smt add_lub leq_def mult_oner star_unfoldl distl)

lemma star_sim1: "x\<cdot>z \<le> z\<cdot>y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> z\<cdot>y\<^sup>\<star>"
  by (smt add_comm add_lub distr leq_def mult_assoc mult_oner star_1l star_ext star_inductl star_invol star_iso star_ref distl)

lemma star_slide1: "(x\<cdot>y)\<^sup>\<star>\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  by (metis eq_iff mult_assoc star_sim1)

lemma star_unfoldl_eq: "x\<^sup>\<star> = one\<squnion>x\<cdot>x\<^sup>\<star>"
  by (smt add_comm add_iso distl leq_def star_1l star_ref mult_oner star_inductl antisym star_unfoldl)

lemma star_denest: "(x\<squnion>y)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
proof -
  have "(x\<squnion>y)\<^sup>\<star> \<le> (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
    by (metis add_lub mult_double_iso mult_onel mult_oner star_ext star_iso star_ref)
  thus ?thesis
    by (metis add_comm eq_iff mult_double_iso star_invol star_iso star_subdist star_trans_eq)
qed

lemma star_unfoldr_eq: "one\<squnion>x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
  by (smt distl distr mult_assoc mult_onel mult_oner star_unfoldl_eq star_inductl  eq_iff star_unfoldr)

lemma star_slide: "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  by (smt add_comm mult_assoc star_unfoldr_eq star_slide1 mult_isor add_iso mult_isol distl mult_oner distr mult_onel star_unfoldl_eq eq_iff star_slide1)

lemma star_slide_var: "x\<^sup>\<star>\<cdot>x = x\<cdot>x\<^sup>\<star>"
  by (metis mult_onel mult_oner star_slide)

end

(* +------------------------------------------------------------------------+
   | Star continuous KA                                                     |
   +------------------------------------------------------------------------+ *)

class star_continuous_ka = dioid +
  fixes cstar :: "'a \<Rightarrow> 'a"
  assumes ex_cstar: "\<forall>x y z. \<exists>w. is_lub w (powers_c x y z)"
  and cstar_def:"x\<cdot>(cstar y)\<cdot>z = \<Sigma> (powers_c x y z)"

begin

  lemma prod_cstar_unique: "is_lub w (powers_c x y z) \<Longrightarrow> x\<cdot>(cstar y)\<cdot>z = w"
    by (metis cstar_def is_lub_unique the_equality lub_def)

  lemma cstar_unique: "is_lub w (powers x) \<Longrightarrow> cstar x = w"
    by (metis mult_onel mult_oner powers_to_powers_c prod_cstar_unique)

  lemma prod_cstar_is_lub: "is_lub (x\<cdot>(cstar y)\<cdot>z) (powers_c x y z)"
    by (metis ex_cstar prod_cstar_unique)

  lemma cstar_lub: "(\<forall>v\<in>(powers_c x y z). v \<le> w) \<longleftrightarrow> x\<cdot>(cstar y)\<cdot>z \<le> w"
    by (metis is_lub_equiv prod_cstar_is_lub)

  lemma cstar_unfoldl: "one\<squnion>x\<cdot>(cstar x) = cstar x"
  proof -
    have "is_lub (one\<squnion>x\<cdot>(cstar x)) (powers x)"
      by (metis ex_cstar mult_oner prod_cstar_unique lub_un powers_unfoldl)
    thus ?thesis
      by (metis cstar_unique)
  qed

  lemma cstar_unfoldr: "one\<squnion>(cstar x)\<cdot>x = cstar x"
    by (smt mult_onel mult_oner powers_suc prod_cstar_is_lub prod_cstar_unique cstar_unfoldl)

  lemma cstar_inductl: "x\<cdot>y \<le> y \<longrightarrow> (cstar x)\<cdot>y \<le> y"
    by (metis power_inductl_var mult_onel powers_c_elim cstar_lub)

  lemma cstar_inductr: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>(cstar x) \<le> y"
    by (metis power_inductr_var mult_oner powers_c_elim cstar_lub)

end

sublocale star_continuous_ka \<subseteq> kleene_algebra
  where star = cstar
  apply (unfold_locales)
  apply (metis cstar_unfoldl eq_refl)
  apply (metis order_refl cstar_unfoldr)
  apply (metis add_lub cstar_inductl mult_isol order_trans)
  by (metis add_lub cstar_inductr distr order_prop)

(* +------------------------------------------------------------------------+
   | Quantales                                                              |
   +------------------------------------------------------------------------+ *)

class quantale = complete_lattice +
  fixes qmult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 80)
  assumes qmult_assoc: "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  and inf_distl: "x \<odot> \<Sigma> Y = \<Sigma> ((\<lambda>y. x\<odot>y) ` Y)"
  and inf_distr: "\<Sigma> Y \<odot> x = \<Sigma> ((\<lambda>y. y\<odot>x) ` Y)"

begin

  lemma bot_zeror: "x \<odot> \<bottom> = \<bottom>"
  proof -
    have "x \<odot> \<Sigma> {} = \<Sigma> ((\<lambda>y. x\<odot>y) ` {})" using inf_distl .
    thus ?thesis by simp
  qed

  lemma bot_zerol: "\<bottom> \<odot> x = \<bottom>"
  proof -
    have "\<Sigma> {} \<odot> x = \<Sigma> ((\<lambda>y. y\<odot>x) ` {})" using inf_distr .
    thus ?thesis by simp
  qed

  lemma qdistl1: "x \<odot> (y \<squnion> z) = (x \<odot> y) \<squnion> (x \<odot> z)"
  proof -
    have "x \<odot> \<Sigma> {y,z} = \<Sigma> ((\<lambda>y. x\<odot>y) ` {y,z})" using inf_distl .
    thus ?thesis by (simp add: join_def)
  qed

  lemma qdistr1: "(y \<squnion> z) \<odot> x = (y \<odot> x) \<squnion> (z \<odot> x)"
  proof -
    have "\<Sigma> {y,z} \<odot> x = \<Sigma> ((\<lambda>y. y\<odot>x) ` {y,z})" using inf_distr .
    thus ?thesis by (simp add: join_def)
  qed

  lemma qmult_isotonel: "isotone (\<lambda>y. x\<odot>y)"
    by (metis isotone_def leq_def qdistl1)

  lemma qmult_left_join_preserving: "join_preserving (\<lambda>y. x\<odot>y)"
    by (metis inf_distl join_preserving_def)

  lemma qmult_left_lower: "lower_adjoint (\<lambda>y. x\<odot>y)"
    by (metis qmult_isotonel qmult_left_join_preserving upper_exists)

  lemma qmult_isotoner: "isotone (\<lambda>y. y\<odot>x)"
    by (metis isotone_def leq_def qdistr1)

  lemma qmult_right_join_preserving: "join_preserving (\<lambda>y. y\<odot>x)"
    by (metis inf_distr join_preserving_def)

  lemma qmult_right_lower: "lower_adjoint (\<lambda>y. y\<odot>x)"
    by (metis qmult_right_join_preserving qmult_isotoner upper_exists)

  definition qpreimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
    "qpreimp x y \<equiv> \<Sigma> {z. x \<odot> z \<le> y}"

  definition qpostimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
    "qpostimp x y \<equiv> \<Sigma> {z. z \<odot> y \<le> x}"

  lemma qpreimp_conn: "galois_connection (\<lambda>y. x\<odot>y) (qpreimp x)"
  proof (unfold galois_connection_def, clarify)
    fix z y
    obtain g where conn: "galois_connection (\<lambda>y. x\<odot>y) g"
      by (metis lower_adjoint_def qmult_left_lower)
    show "(x \<odot> z \<le> y) \<longleftrightarrow> (z \<le> qpreimp x y)"
      by (simp add: qpreimp_def, metis conn galois_connection_def galois_lub_var)
  qed

  lemma qpostimp_conn: "galois_connection (\<lambda>y. y\<odot>x) (\<lambda>y. qpostimp y x)"
  proof (unfold galois_connection_def, clarify)
    fix z y
    obtain g where conn: "galois_connection (\<lambda>y. y\<odot>x) g"
      by (metis lower_adjoint_def qmult_right_lower)
    thus "(z \<odot> x \<le> y) \<longleftrightarrow> (z \<le> qpostimp y x)"
      by (simp add: qpostimp_def, metis galois_connection_def galois_lub_var)
  qed

end

(* +------------------------------------------------------------------------+
   | Unital Quantales                                                       |
   +------------------------------------------------------------------------+ *)

class unital_quantale = quantale +
  fixes qone :: 'a
  assumes qunitl: "qone \<odot> x = x"
  and qunitr: "x \<odot> qone = x"

sublocale unital_quantale \<subseteq> dioid
  where zero = bot and mult = qmult and one = qone
proof
  fix x y z :: 'a
  show "\<bottom> \<squnion> x = x" by simp
  show "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)" using qmult_assoc .
  show "(x \<squnion> y) \<odot> z = x \<odot> z \<squnion> y \<odot> z" using qdistr1 .
  show "x \<odot> (y \<squnion> z) = x \<odot> y \<squnion> x \<odot> z" using qdistl1 .
  show "qone \<odot> x = x" using qunitl .
  show "x \<odot> qone = x" using qunitr .
  show "\<bottom> \<odot> x = \<bottom>" using bot_zerol .
  show "x \<odot> \<bottom> = \<bottom>" using bot_zeror .
qed

context unital_quantale
begin

  definition qstar :: "'a \<Rightarrow> 'a" where
    "qstar x \<equiv> \<Sigma> (powers x)"

  (* Really ugly proofs *)

  lemma set_predicate_eq: "\<forall>x. P x = Q x \<Longrightarrow> {x. P x} = {x. Q x}" by (metis (no_types) order_eq_iff predicate1I)

  lemma qstar_distl: "x \<odot> qstar y = \<Sigma> {x\<odot>z|z. (\<exists>i. z = power y i)}"
  proof (simp add: qstar_def powers_def inf_distl, rule_tac f = "\<lambda>x. \<Sigma> x" in arg_cong)
    have "op \<odot> x ` {z. \<exists>i. z = dioid.power op \<odot> qone y i} = {z. \<exists>p. (\<exists>i. p = dioid.power op \<odot> qone y i) \<and> z = x \<odot> p}"
      by (simp add: image_def)
    also have "... = {z. \<exists>i. z = x \<odot> dioid.power op \<odot> qone y i}"
      by (rule set_predicate_eq, blast)
    also have "... = {x \<odot> w |w. \<exists>i. w = dioid.power op \<odot> qone y i}"
      by (simp add: Collect_def, metis)
    finally show "op \<odot> x ` {z. \<exists>i. z = dioid.power op \<odot> qone y i} = {x \<odot> w |w. \<exists>i. w = dioid.power op \<odot> qone y i}"
      by metis
  qed

  lemma qmult_imager: "(\<lambda>z. z \<odot> y) ` {z. \<exists>i. z = dioid.power op \<odot> qone x i} = {w \<odot> y |w. \<exists>i. w = dioid.power op \<odot> qone x i}"
  proof -
    have "(\<lambda>z. z\<odot>y) ` {z. \<exists>i. z = dioid.power op \<odot> qone x i} = {z. \<exists>p. (\<exists>i. p = dioid.power op \<odot> qone x i) \<and> z = p \<odot> y}"
      by (simp add: image_def)
    also have "... = {z. \<exists>i. z = dioid.power op \<odot> qone x i \<odot> y}"
      by (rule set_predicate_eq, blast)
    also have "... = {w \<odot> y |w. \<exists>i. w = dioid.power op \<odot> qone x i}"
      by (simp add: Collect_def, metis)
    finally show ?thesis by metis
  qed

  lemma qstar_distr: "qstar x \<odot> y = \<Sigma> {z\<odot>y|z. (\<exists>i. z = power x i)}"
    by (simp add: qstar_def powers_def inf_distr, rule_tac f = "\<lambda>x. \<Sigma> x" in arg_cong, metis qmult_imager)

  lemma function_image: "f ` {P y|y. Q y} = {f (P y) |y. Q y}"
  proof -
    have "{y. \<exists>x. (\<exists>y. x = P y \<and> Q y) \<and> y = f x} = {z. \<exists>y. z = f (P y) \<and> Q y}"
      by (rule set_predicate_eq, blast)
    hence "{y. \<exists>x. (\<exists>y. x = P y \<and> Q y) \<and> y = f x} = {f (P y) |y. Q y}"
      by (simp add: Collect_def)
    thus ?thesis by (simp add: image_def)
  qed

end

sublocale unital_quantale \<subseteq> star_continuous_ka
  where zero = bot and mult = qmult and one = qone and cstar = qstar
proof (unfold_locales, clarify)
  fix x y z :: 'a
  show "\<exists>w. is_lub w (dioid.powers_c op \<odot> qone x y z)" by (metis lub_ex)
  show "x \<odot> qstar y \<odot> z = \<Sigma> (dioid.powers_c op \<odot> qone x y z)"
    apply (simp only: qstar_distl inf_distr)
    apply (rule_tac f = "\<lambda>X. \<Sigma> X" in arg_cong)
    by (simp only: powers_c_def, rule function_image)
qed

lemma (in unital_quantale) "qstar x = \<mu>(\<lambda>y. qone \<squnion> y\<odot>x)"
proof
  show "qone \<squnion> qstar x \<odot> x = qstar x" by (metis cstar_unfoldr)
next
  fix y assume "qone \<squnion> y\<odot>x = y"
  thus "qstar x \<le> y"
    by (metis mult_onel order_refl star_inductr)
qed

lemma (in unital_quantale) "qstar x = \<mu>(\<lambda>y. qone \<squnion> x\<odot>y)"
proof
  show "qone \<squnion> x \<odot> qstar x = qstar x" by (metis cstar_unfoldl)
next
  fix y assume "qone \<squnion> x\<odot>y = y"
  thus "qstar x \<le> y"
    by (metis mult_oner order_refl star_inductl)
qed

(* +------------------------------------------------------------------------+
   | Involutive Quantales                                                   |
   +------------------------------------------------------------------------+ *)

class involutive_quantale = quantale +
  fixes invol :: "'a \<Rightarrow> 'a" ("_\<^sup>\<circ>" [101] 100)
  assumes "(x\<odot>y)\<^sup>\<circ> = y\<^sup>\<circ>\<odot>x\<^sup>\<circ>"
  and "(\<Sigma> X)\<^sup>\<circ> = \<Sigma> ((\<lambda>x. x\<^sup>\<circ>) ` X)"

class involutive_unital_quantale = unital_quantale + involutive_quantale

(* +------------------------------------------------------------------------+
   | Action Algebra                                                         |
   +------------------------------------------------------------------------+ *)

class boffa = dioid +
  fixes bstar :: "'a \<Rightarrow> 'a"
  assumes boffa1: "one \<squnion> x \<squnion> (bstar x)\<cdot>(bstar x) \<le> bstar x"
  and boffa2: "one \<squnion> x \<squnion> y\<cdot>y \<le> y \<longrightarrow> bstar x \<le> y"

class boffa_original = dioid +
  fixes b2star :: "'a \<Rightarrow> 'a"
  assumes boffa_orig1: "one \<squnion> x \<le> b2star x"
  and boffa_orig2: "(b2star x)\<cdot>(b2star x) = b2star x"
  and boffa_orig3: "one \<squnion> x \<le> y \<and> y\<cdot>y = y \<longrightarrow> b2star x \<le> y"

(* We have found a new slightly weaker version of Boffa's
axioms. These are complete for the equational theory of regular
expressions, since they are equivalent to Boffa's original axioms. We
can now base Pratt's action algebras on these axioms. Action algebras
are therefore complete by this extension. *)

sublocale boffa \<subseteq> boffa_original
  where b2star = bstar
proof
  fix x y
  show "one \<squnion> x \<le> bstar x"
    by (metis add_lub boffa1)
  show "(bstar x)\<cdot>(bstar x) = bstar x"
    by (metis add_comm add_idem add_lub boffa1 distl leq_def mult_oner)
  show "one \<squnion> x \<le> y \<and> y\<cdot>y = y \<longrightarrow> bstar x \<le> y"
    by (metis boffa2 leq_def order_refl)
qed

sublocale boffa_original \<subseteq> boffa
  where bstar = b2star
proof
  fix x y
  show "one \<squnion> x \<squnion> (b2star x)\<cdot>(b2star x) \<le> b2star x"
    by (metis boffa_orig1 boffa_orig2 eq_refl leq_def)
  show "one \<squnion> x \<squnion> y\<cdot>y \<le> y \<longrightarrow> b2star x \<le> y"
    by (metis add_lub antisym boffa_orig3 mult_isol mult_oner)
qed

class action_algebra = boffa +
  fixes preimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightarrow>" 60)
  and postimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leftarrow>" 60)
  assumes act_galois1: "galois_connection (\<lambda>x. x\<cdot>y) (\<lambda>x. x\<leftarrow>y)"
  and act_galois2: "galois_connection (\<lambda>y. x\<cdot>y) (\<lambda>y. x\<rightarrow>y)"

sublocale unital_quantale \<subseteq> action_algebra
  where zero = bot and mult = qmult and one = qone and bstar = qstar
  and preimp = qpreimp and postimp = qpostimp
  apply unfold_locales
  apply (metis add_lub cstar_inductl star_1l star_ext star_ref)
  apply (metis add_lub leq_def mult_onel star_inductr star_subdist star_unfoldl_eq)
  apply (metis qpostimp_conn)
  by (metis qpreimp_conn)

context action_algebra
begin
  lemma act1L: "(x \<le> z \<leftarrow> y) \<longleftrightarrow> (x\<cdot>y \<le> z)" by (metis galois_connection_def act_galois1)

  lemma act1R: "(x\<cdot>y \<le> z) \<longleftrightarrow> y \<le> x \<rightarrow> z" by (metis galois_connection_def act_galois2)

  (* We can obtain these by instantiating proofs from galois connections *)

  lemma galois_unitR: "y \<le> x \<rightarrow> x\<cdot>y" by (metis act_galois2 inflation)

  lemma galois_counitR: "x \<cdot> (x \<rightarrow> y) \<le> y" by (metis act_galois2 deflation)

  lemma galois_unitL: "x \<le> x\<cdot>y \<leftarrow> y" by (metis act_galois1 inflation)

  lemma galois_counitL: "(y \<leftarrow> x) \<cdot> x \<le> y" by (metis act_galois1 deflation)

  lemma eq_ax1: "x \<rightarrow> y \<le> x \<rightarrow> (y \<squnion> y')" by (metis act_galois2 add_ub galois_ump1 isotoneD)

  lemma eq_ax1': "x \<leftarrow> y \<le> (x \<squnion> x') \<leftarrow> y" by (metis act_galois1 add_ub galois_ump1 isotoneD)

  lemma postimp_trans: "(x \<rightarrow> y) \<cdot> (y \<rightarrow> z) \<le> x \<rightarrow> z"
    by (smt act1L act1R galois_counitR mult_assoc order_trans)

  lemma preimp_trans: "(x \<leftarrow> y) \<cdot> (y \<leftarrow> z) \<le> x \<leftarrow> z"
    by (smt act1L act1R galois_counitL mult_assoc order_trans)

  lemma postimp_refl: "one \<le> x \<rightarrow> x" by (metis act1R mult_oner order_refl)
  lemma preimp_refl: "one \<le> x \<leftarrow> x" by (metis galois_unitL mult_onel)

  lemma postimp_pure_induction: "bstar (x \<rightarrow> x) \<le> (x \<rightarrow> x)"
    by (metis add_lub boffa2 order_refl postimp_refl postimp_trans)

  lemma postimp_pure_induction_uncurried: "x\<cdot>bstar (x \<rightarrow> x) \<le> x"
    by (metis act1R postimp_pure_induction)

  lemma preimp_pure_induction: "bstar (x \<leftarrow> x) \<le> (x \<leftarrow> x)"
    by (metis add_lub boffa2 order_refl preimp_refl preimp_trans)

  lemma star_refl: "one \<le> bstar x" by (metis boffa1 add_lub)
  lemma star3: "x \<le> bstar x" by (metis boffa1 add_lub)

  lemma star_mon: "(x \<le> y) \<longrightarrow> (bstar x \<le> bstar y)"
    by (metis add_lub boffa_orig2 boffa_orig3 order_trans star3 star_refl)

  lemma star_left_preserves: "(x\<cdot>y \<le> y) \<longrightarrow> ((bstar x)\<cdot>y \<le> y)"
    by (metis act1L order_trans preimp_pure_induction star_mon)

  lemma star_right_preserves: "(y\<cdot>x \<le> y) \<longrightarrow> (y\<cdot>bstar x \<le> y)"
    by (metis act1R order_trans postimp_pure_induction star_mon)
end

sublocale action_algebra \<subseteq> kleene_algebra
  where star = bstar
proof
  fix x y z :: 'a
  show "one \<squnion> x\<cdot>bstar x \<le> bstar x"
    by (metis boffa1 add_assoc add_comm distl distr leq_def mult_oner star3 star_refl)
  show "one \<squnion> bstar x \<cdot> x \<le> bstar x"
    by (metis boffa1 add_assoc add_comm distl distr leq_def mult_oner star3 star_refl)
  show "z \<squnion> x \<cdot> y \<le> y \<longrightarrow> bstar x \<cdot> z \<le> y"
    by (metis add_lub mult_isol order_trans star_left_preserves)
  show "z \<squnion> y \<cdot> x \<le> y \<longrightarrow> z \<cdot> bstar x \<le> y"
    by (metis add_lub mult_isor order_trans star_right_preserves)
qed

class equational_action_algebra = dioid +
  fixes eqstar :: "'a \<Rightarrow> 'a"
  and eqpreimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and eqpostimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes eq1: "eqpreimp x y \<le> eqpreimp x (y \<squnion> y')"
  and eq2L: "x\<cdot>(eqpreimp x y) \<le> y"
  and eq2R: "y \<le> eqpreimp x (x\<cdot>y)"
  and eq3: "eqpostimp y x \<le> eqpostimp (y \<squnion> y') x"
  and eq4L: "(eqpostimp y x)\<cdot>x \<le> y"
  and eq4R: "y \<le> eqpostimp (y\<cdot>x) x"
  and eq5: "one \<squnion> (eqstar x)\<cdot>(eqstar x) \<squnion> x \<le> eqstar x"
  and eq6: "eqstar x \<le> eqstar (x \<squnion> y)"
  and eq7: "eqstar (eqpreimp x x) \<le> (eqpreimp x x)"

sublocale action_algebra \<subseteq> equational_action_algebra
  where eqstar = bstar and eqpreimp = preimp and eqpostimp = postimp
  apply unfold_locales
  apply (metis act1R add_ub galois_counitR order_trans)
  apply (metis galois_counitR)
  apply (metis galois_unitR)
  apply (metis act1L add_ub galois_counitL order_trans)
  apply (metis galois_counitL)
  apply (metis galois_unitL)
  apply (metis add_assoc add_comm boffa1)
  apply (metis star_subdist)
  by (metis postimp_pure_induction)

sublocale equational_action_algebra \<subseteq> action_algebra
  where bstar = eqstar and preimp = eqpreimp and postimp = eqpostimp
  apply unfold_locales
  apply (metis add_assoc add_comm eq5)
  apply (metis add_lub eq2L eq2R eq6 eq7 eq_iff leq_def mult_onel subdistl subdistr)
  apply (simp add: galois_connection_def, metis eq3 eq4L eq4R leq_def order_trans subdistr)
  by (simp add: galois_connection_def, metis eq1 eq2L eq2R order_prop order_trans subdistl)

sublocale equational_action_algebra \<subseteq> kleene_algebra
  where star = eqstar
  by intro_locales

(* +------------------------------------------------------------------------+
   | Deflationarity aka wellfoundedness vs UEP                              |
   +------------------------------------------------------------------------+ *)

class completely_distributive_quantale = unital_quantale +
  assumes jm_inf_distributive: "x \<squnion> \<Pi> Y = \<Pi> ((\<lambda>y. x\<squnion>y) ` Y)"

begin

lemma lambda_eq: "\<forall>x. P x = Q x \<Longrightarrow> (\<lambda>x. P x) = (\<lambda>x. Q x)" by metis

lemma arden_fusion: "\<nu> (\<lambda>y. x\<odot>y \<squnion> z) = qstar x \<odot> z \<squnion> \<nu> (\<lambda>y. x\<odot>y)"
proof -
  have lower_ex: "upper_adjoint (\<lambda>y. qstar x \<odot> z \<squnion> y)"
  proof (unfold lower_exists, safe)
    show "isotone (\<lambda>y. qstar x \<odot> z \<squnion> y)"
      by (metis add_comm add_lub add_ub isotone_def order_trans)
    show "meet_preserving (\<lambda>y. qstar x \<odot> z \<squnion> y)"
      by (metis jm_inf_distributive meet_preserving_def)
  qed

  have kiso: "isotone (\<lambda>y. x\<odot>y \<squnion> z)"
    by (smt add_iso isotone_def order_prop subdistl)

  have hiso: "isotone (\<lambda>y. x\<odot>y)"
    by (metis qmult_isotonel)

  have comm: "(\<lambda>y. qstar x \<odot> z \<squnion> y)\<circ>(\<lambda>y. x\<odot>y) = (\<lambda>y. x\<odot>y \<squnion> z)\<circ>(\<lambda>y. qstar x \<odot> z \<squnion> y)"
    proof (unfold o_def, rule lambda_eq, safe)
      fix y
      have "x \<odot> (qstar x \<odot> z \<squnion> y) \<squnion> z = x\<odot>(qstar x)\<odot>z \<squnion> x\<odot>y \<squnion> z" by (metis distl mult_assoc)
      also have "... = (qone \<squnion> x\<odot>(qstar x))\<odot>z \<squnion> x\<odot>y"
        by (smt add_assoc add_comm mult_assoc mult_onel qdistr1)
      also have "... = (qstar x)\<odot>z \<squnion> x\<odot>y" by (metis star_unfoldl_eq)
      finally show "qstar x \<odot> z \<squnion> x \<odot> y = x \<odot> (qstar x \<odot> z \<squnion> y) \<squnion> z" by metis
   qed

   show ?thesis
     by (metis comm greatest_fixpoint_fusion hiso kiso lower_ex)
qed

lemma gfp_is_gpp: "\<lbrakk>isotone f; is_gfp x f\<rbrakk> \<Longrightarrow>  is_gpp x f"
  by (metis gfp_equality gpp_is_gfp is_gpp_gpp)

lemma gfp_is_gpp_var: "isotone f \<Longrightarrow> \<nu> f = \<nu>\<^sub>\<le> f"
  by (metis gfp_is_gpp gpp_equality is_gfp_gfp)

lemma deflationarity_implies_uep:
  "(\<forall>y. y \<le> x\<odot>y \<longrightarrow> y = \<bottom>) \<longleftrightarrow> (\<forall>y z. y \<le> x\<odot>y \<squnion> z \<longrightarrow> y \<le> (qstar x) \<odot> z)"
proof
  assume "\<forall>y z. y \<le> x \<odot> y \<squnion> z \<longrightarrow> y \<le> (qstar x) \<odot> z"
  thus "\<forall>y. y \<le> x \<odot> y \<longrightarrow> y = \<bottom>" by (metis annil bot_oner leq_def)
next
  have kiso: "\<forall>z. isotone (\<lambda>y. x\<odot>y \<squnion> z)"
    by (smt add_iso isotone_def order_prop subdistl)

  assume "\<forall>y. y \<le> x \<odot> y \<longrightarrow> y = \<bottom>"
  hence "\<nu> (\<lambda>y. x\<odot>y) = \<bottom>"
    by (metis annil gfp_equality_var order_refl)
  hence "\<forall>z. \<nu> (\<lambda>y. x\<odot>y \<squnion> z) = qstar x \<odot> z"
    by (metis arden_fusion bot_oner)
  thus "\<forall>y z. y \<le> x \<odot> y \<squnion> z \<longrightarrow> y \<le> qstar x \<odot> z"
    by (metis greatest_fixpoint_induction kiso)
qed

end

end
