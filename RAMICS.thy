theory RAMICS
  imports Main Signatures
begin

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

context order
begin

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

begin

  subclass join_semilattice
    by (unfold_locales, metis lub_ex)

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

begin

  subclass meet_semilattice
    by (unfold_locales, metis glb_ex)

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

sublocale complete_join_semilattice \<subseteq> complete_lattice
  by (unfold_locales, smt is_lub_lub Collect_def is_glb_from_is_lub)

sublocale complete_meet_semilattice \<subseteq> complete_lattice
  by (unfold_locales, smt is_glb_glb Collect_def is_lub_from_is_glb)

definition order_monomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_monomorphism f \<equiv> \<forall>x y. (f x \<le> f y) \<longleftrightarrow> (x \<le> y)"

definition order_isomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_isomorphism f \<equiv> order_monomorphism f \<and> surj f"

lemma order_monomorphism_inj: "order_monomorphism f \<Longrightarrow> inj f"
  by (simp add: order_monomorphism_def inj_on_def order_eq_iff)

(* +------------------------------------------------------------------------+
   | Fixpoints and Prefix Points                                            |
   +------------------------------------------------------------------------+ *)

context order
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

  definition is_gpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
    "is_gpp x f \<equiv> (is_post_fp x f) \<and> (\<forall>y. y \<le> f y \<longrightarrow> y \<le> x)"

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

lemma knaster_tarski_lpp:
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
    by (metis Collect_def glb_least mem_def order_refl)
  ultimately show "is_lpp ?a f"
    by (smt is_lpp_def Collect_def glb_least mem_def)
qed

corollary is_lpp_lpp [intro?]: "mono (f::'a::complete_lattice \<Rightarrow> 'a) \<Longrightarrow> is_lpp (\<mu>\<^sub>\<le> f) f"
  using knaster_tarski_lpp by (metis lpp_equality)

theorem knaster_tarski:
  assumes fmon: "mono f"
  obtains a :: "'a::complete_lattice" where "is_lfp a f"
  by (metis assms is_lpp_lpp lpp_is_lfp)

corollary knaster_tarski_var: "mono f \<Longrightarrow> \<exists>!x::'a::complete_lattice. is_lfp x f"
  using knaster_tarski by (metis lfp_equality)

corollary is_lfp_lfp [intro?]: "mono (f::'a::complete_lattice \<Rightarrow> 'a) \<Longrightarrow> is_lfp (\<mu> f) f"
  using knaster_tarski by (metis lfp_equality)

(* Knaster-Tarski for greatest fixpoints *)

theorem knaster_tarski_greatest:
  assumes fmon: "f \<in> mono"
  obtains a :: "'a::complete_lattice" where "is_gfp a f"
proof
  have mono: "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y" using fmon by (metis mem_def monoD)
  let ?H = "{u. u \<le> f u}"
  let ?a = "\<Sigma> ?H"
  show "is_gfp ?a f"
  proof (simp add: is_gfp_def is_fp_def, safe)
    have le: "?a \<le> f ?a"
    proof
      fix x assume x: "x \<in> ?H"
      hence "x \<le> ?a" ..
      hence "f x \<le> f ?a" by (rule mono)
      moreover from x have "x \<le> f x" ..
      ultimately show "x \<le> f ?a" by (metis order_trans)
    qed
    also have "f ?a \<le> ?a"
    proof
      from le have "f ?a \<le> f (f ?a)" by (rule mono)
      thus "f ?a \<in> ?H" ..
    qed
    finally show "f ?a = ?a" ..
  next
    fix y
    show "f y = y \<Longrightarrow> y \<le> \<Sigma> {u. u \<le> f u}"
      by (metis Collect_def complete_join_semilattice_class.lub_least mem_def order_refl)
  qed
qed

corollary knaster_tarski_greatest_var: "f \<in> mono \<Longrightarrow> \<exists>!x. is_gfp x f"
  using knaster_tarski_greatest by (metis gfp_equality)

corollary is_gfp_gfp [intro?]: "f \<in> mono \<Longrightarrow> is_gfp (\<nu> f) f"
  using knaster_tarski_greatest by (metis gfp_equality)

lemma gpp_exists:
  assumes fmon: "f \<in> mono"
  obtains a :: "'a::complete_lattice" where "is_gpp a f"
proof
  have mono: "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y" using fmon by (metis mem_def monoD)
  let ?H = "{u. u \<le> f u}"
  let ?a = "\<Sigma> ?H"
  show "is_gpp ?a f"
  proof (simp add: is_gpp_def, safe)
    show "?a \<le> f ?a"
    proof
      fix x assume x: "x \<in> ?H"
      hence "x \<le> ?a" ..
      hence "f x \<le> f ?a" by (rule mono)
      moreover from x have "x \<le> f x" ..
      ultimately show "x \<le> f ?a" by (metis order_trans)
    qed
  next
    fix y
    assume fy: "y \<le> f y"
    show "y \<le> \<Sigma> {u. u \<le> f u}"
    proof
      show "y \<in> {u. u \<le> f u}" by (metis Collect_def fy mem_def)
    qed
  qed
qed

corollary is_gpp_gpp [intro?]: "f \<in> mono \<Longrightarrow> is_gpp (\<nu>\<^sub>\<le> f) f"
  using gpp_exists by (metis gpp_equality)
