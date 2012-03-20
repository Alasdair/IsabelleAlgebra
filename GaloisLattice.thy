theory GaloisLattice
  imports Lattice Main
begin

definition (in order) pleq :: "('a \<Rightarrow> 'b::order) \<Rightarrow> ('a \<Rightarrow> 'b::order) \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "pleq f g \<equiv> \<forall>x. f x \<le> g x"

definition idempotent :: "('a \<Rightarrow> 'a) set" where
  "idempotent f \<equiv> f \<circ> f = f"

locale galois_connection =
  fixes lower :: "'a::order \<Rightarrow> 'b::order" ("\<pi>\<^sup>*")
  and upper :: "'b::order \<Rightarrow> 'a::order" ("\<pi>\<^sub>*")
  assumes galois_property: "\<forall>x y. (\<pi>\<^sup>* x \<le> y) = (x \<le> \<pi>\<^sub>* y)"

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

context galois_connection
begin
  lemma deflation: "\<pi>\<^sup>* (\<pi>\<^sub>* y) \<le> y" by (simp only: galois_property)
  lemma inflation: "x \<le> \<pi>\<^sub>* (\<pi>\<^sup>* x)" by (metis galois_property order_eq_refl)

  lemma lower_mono: "\<pi>\<^sup>* \<in> mono"
    by (metis galois_property inflation order_trans mem_def mono_def)

  lemma upper_mono: "\<pi>\<^sub>* \<in> mono"
    by (metis galois_property deflation order_trans mem_def mono_def)

  lemma lower_comp: "\<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<circ> \<pi>\<^sup>* = \<pi>\<^sup>*"
  proof
    fix x
    show "(\<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<circ> \<pi>\<^sup>*) x = \<pi>\<^sup>* x"
      by (metis lower_mono mono_def mem_def deflation inflation o_apply order_antisym)
  qed

  lemma upper_comp: "\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>* = \<pi>\<^sub>*"
  proof
    fix x
    show "(\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>*) x = \<pi>\<^sub>* x"
      by (metis upper_mono mono_def mem_def deflation inflation o_apply order_antisym)
  qed

  lemma upper_idempotentcy1: "\<pi>\<^sup>*\<circ>\<pi>\<^sub>* \<in> idempotent" by (metis lower_comp idempotent_def mem_def o_assoc)
  lemma upper_idempotentcy2: "\<pi>\<^sub>*\<circ>\<pi>\<^sup>* \<in> idempotent" by (metis lower_comp idempotent_def mem_def o_assoc)

  lemma upper_dual: "(\<pi>\<^sub>* x \<ge> y) = (x \<ge> \<pi>\<^sup>* y)"
    by (metis galois_property)
end

lemma galois_dual: "galois_connection F G \<Longrightarrow> dual_galois_connection G F"
  by unfold_locales (metis galois_connection.galois_property)

lemma dual_galois_dual: "dual_galois_connection F G \<Longrightarrow> galois_connection G F"
  by unfold_locales (metis dual_galois_connection.dual_galois_property)

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
  by unfold_locales (metis g1 g2 galois_connection.galois_property o_def)

lemma galois_id: "galois_connection id id" by unfold_locales (metis id_def)

lemma galois_mono1: "galois_connection F G \<Longrightarrow> G \<circ> F \<in> mono"
proof -
  assume g: "galois_connection F G"
  hence "G \<in> mono" using galois_connection.upper_mono by auto
  moreover have "F \<in> mono" using g galois_connection.lower_mono by auto
  ultimately show "G \<circ> F \<in> mono" by (simp add: mem_def mono_def)
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

lemma point_comp_2: "\<lbrakk>galois_connection F G; h \<in> mono; k \<in> mono\<rbrakk> \<Longrightarrow> (h \<circ> G \<sqsubseteq> k) = (h \<sqsubseteq> k \<circ> F)"
  apply (simp only: pleq_def o_def)
  by (metis (full_types) mono_def galois_connection.deflation galois_connection.inflation mem_def order_trans)

lemma upper_uniqueness: assumes g1: "galois_connection F G" and g2: "galois_connection H K"
  shows "(F \<sqsubseteq> H) = (K \<sqsubseteq> G)"
proof -
  have "(F \<sqsubseteq> H) = (id \<sqsubseteq> G \<circ> H)" by (metis g1 point_comp o_id)
  also have "... = (K \<sqsubseteq> G)" by (metis g1 g2 galois_connection.upper_mono galois_id id_o point_comp_2)
  thus ?thesis by (metis calculation)
qed

lemma universal_mapping_property1:
  assumes a: "G \<in> mono" and b: "\<forall>x. x \<le> G (F x)"
  and c: "\<forall>x y. (x \<le> G y) \<longrightarrow> (F x \<le> y)"
  shows "galois_connection F G"
proof (unfold_locales, intro allI)
  fix x and y
  show "(F x \<le> y) = (x \<le> G y)" by (metis mono_def a b c mem_def order_trans)
qed

lemma universal_mapping_property2:
  assumes a: "F \<in> mono" and b: "\<forall>x. F (G x) \<le> x"
  and c: "\<forall>x y. (F x \<le> y) \<longrightarrow> (x \<le> G y)"
  shows "galois_connection F G"
proof (unfold_locales, intro allI)
  fix x and y
  have "(x \<le> G y) \<longrightarrow> (F x \<le> y)" using a b c
    apply (simp only: mem_def mono_def) by (metis order_trans)
  thus "(F x \<le> y) = (x \<le> G y)" using c by auto
qed

lemma galois_ump2: "galois_connection f g = (f \<in> mono \<and> (\<forall>y. f (g y) \<le> y) \<and> (\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y))"
  by (metis (no_types) galois_connection.lower_mono galois_connection.upper_dual galois_connection.upper_mono order_refl universal_mapping_property2)

lemma galois_ump1: "galois_connection f g = (g \<in> mono \<and> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y))"
  by (metis galois_connection.inflation galois_connection.upper_dual galois_connection.upper_mono universal_mapping_property1)

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma ore_galois:
  assumes a: "\<forall>x. x \<le> G (F x)" and b: "\<forall>x. F (G x) \<le> x"
  and c: "F \<in> mono" and d: "G \<in> mono"
  shows "galois_connection F G"
proof (unfold_locales, intro allI)
  fix x and y
  show "(F x \<le> y) = (x \<le> G y)" using a b c d
    apply (simp only: mem_def mono_def) by (metis order_trans)
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
  apply (simp add: is_max_def is_lub_eqiv) by (metis assms galois_ump2 xt1(6))

lemma galois_min: assumes conn: "galois_connection f g" shows "is_min (f x) {y. x \<le> g y}"
  apply (simp add: is_min_def is_glb_eqiv) by (metis assms galois_ump1 xt1(6))

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
    show "f \<in> mono" using fmon mem_def by metis
  next
    have max2: "\<forall>y. g y \<in> {x. f x \<le> y}" using is_max_def max by smt
    hence "(g y \<in> {x. f x \<le> y}) = (f (g y) \<le> y)" by (simp only: mem_Collect_eq)
    thus p: "\<forall>y. f (g y) \<le> y" using max2 by auto
  next
    show "\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y" apply (intro allI)
    proof (intro impI)
      fix x and y
      have lub1: "is_lub (g y) {x. f x \<le> y}" using is_max_def max
        by (smt Collect_def is_lub_eqiv mem_def)
      assume "f x \<le> y"
      thus "x \<le> g y" using lub1 by (metis Collect_def is_lub_eqiv mem_def order_refl)
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
    show "g \<in> mono" using gmon mem_def by metis
  next
    have "\<forall>x. f x \<in> {y. x \<le> g y}" using is_min_def min by smt
    moreover have "(f x \<in> {y. x \<le> g y}) = (x \<le> g (f x))" by (simp only: mem_Collect_eq)
    ultimately show "\<forall>x. x \<le> g (f x)" by auto
  next
    show "\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y" apply (intro allI)
    proof (intro impI)
      fix x and y
      have glb1: "is_glb (f x) {y. x \<le> g y}" using is_min_def min
        by (smt Collect_def is_glb_eqiv mem_def)
      assume "x \<le> g y"
      thus "f x \<le> y" using glb1 by (metis Collect_def is_glb_eqiv mem_def order_refl)
    qed
  qed
qed

corollary min_galois_rule: "\<lbrakk>mono g; \<forall>x. is_min (f x) {y. x \<le> g y}\<rbrakk> \<Longrightarrow> galois_connection f g"
  by (metis min_galois)

hide_fact galois_min galois_max

(* +------------------------------------------------------------------------+
   | Definition 2.27                                                        |
   +------------------------------------------------------------------------+ *)

definition ex_lub_junctive :: "('a::order \<Rightarrow> 'b::order) set" where
  "ex_lub_junctive f \<equiv> \<forall>X\<subseteq>UNIV. (\<exists>x. is_lub x X) \<longrightarrow> \<Sigma> (f ` X) = f (\<Sigma> X)"

definition ex_glb_junctive :: "('a::order \<Rightarrow> 'b::order) set" where
  "ex_glb_junctive g \<equiv> \<forall>X\<subseteq>UNIV. (\<exists>x. is_glb x X) \<longrightarrow> \<Pi> (g ` X) = g (\<Pi> X)"

lemma galois_lub: "galois_connection f g \<Longrightarrow> is_lub (g y) {x. f x \<le> y}"
  apply (simp add: is_lub_eqiv) by (metis galois_ump2 order_trans)

lemma galois_glb: "galois_connection f g \<Longrightarrow> is_glb (f x) {y. x \<le> g y}"
  apply (simp add: is_glb_eqiv) by (metis galois_ump1 order_trans)

(* Lemma 4.24(a) and 4.24(b) *)

lemma galois_lub_junc: assumes conn: "galois_connection f g" shows "ex_lub_junctive f"
proof (simp add: ex_lub_junctive_def, intro allI, intro impI)
  fix X :: "'a set"
  show "(\<exists>x\<Colon>'a. is_lub x X) \<Longrightarrow> (\<Sigma> (f ` X) = f (\<Sigma> X))"
  proof -
    assume lub_exists: "\<exists>x. is_lub x X"
    have a: "\<forall>y. (f (\<Sigma> X) \<le> y) = (\<forall>z \<in> f`X. z \<le> y)" using conn lub_exists
      by (smt galois_connection.galois_property image_iff is_lub_eqiv lub_is_lub rev_image_eqI)
    moreover have "\<forall>y. (\<forall>z \<in> f`X. z \<le> y) = (\<Sigma> (f ` X) \<le> y)"
    proof
      fix y
      have "\<forall>z \<in> f`X. z \<le> y \<Longrightarrow> \<Sigma> (f ` X) \<le> y"
        by (metis calculation is_lub_eqiv lub_exists lub_is_lub) (* takes ages *)
      moreover have "\<Sigma> (f ` X) \<le> y \<Longrightarrow> \<forall>z \<in> f`X. z \<le> y"
        by (metis a is_lub_eqiv lub_exists lub_is_lub)
      ultimately show "(\<forall>z \<in> f`X. z \<le> y) = (\<Sigma> (f ` X) \<le> y)" by auto
    qed
    ultimately have "\<forall>y. (f (\<Sigma> X) \<le> y) = (\<Sigma> (f ` X) \<le> y)" by metis
    thus "\<Sigma> (f ` X) = f (\<Sigma> X)" by (metis order_refl xt1(5))
  qed
qed

lemma galois_glb_junc: assumes conn: "galois_connection f g" shows "ex_glb_junctive g"
proof (simp add: ex_glb_junctive_def, intro allI, intro impI)
  fix X :: "'b set"
  assume glb_exists: "\<exists>x. is_glb x X"
  have a: "\<forall>y. (y \<le> g (\<Pi> X)) = (\<forall>z \<in> g`X. y \<le> z)" using conn glb_exists
    by (smt galois_connection.galois_property image_iff is_glb_eqiv glb_is_glb rev_image_eqI)
  moreover have "\<forall>y. (\<forall>z \<in> g`X. y \<le> z) = (y \<le> \<Pi> (g ` X))"
  proof
    fix y
    have "\<forall>z \<in> g`X. y \<le> z \<Longrightarrow> y \<le> \<Pi> (g ` X)"
      by (metis calculation is_glb_eqiv glb_exists glb_is_glb)
    moreover have "y \<le> \<Pi> (g ` X) \<Longrightarrow> \<forall>z \<in> g`X. y \<le> z"
      by (metis a is_glb_eqiv glb_exists glb_is_glb)
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

lemma cl_galois_dualize: "\<lbrakk>cl_galois_connection F G \<Longrightarrow> P F G; dual_cl_galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
  by (metis dual_cl_galois_dual)

lemma dual_cl_galois_dualize: "\<lbrakk>dual_cl_galois_connection F G \<Longrightarrow> P F G; cl_galois_connection G F\<rbrakk> \<Longrightarrow> P F G"
  by (metis cl_galois_dual)

lemma (in cl_galois_connection) poset_conn: "galois_connection \<pi>\<^sup>* \<pi>\<^sub>*"
proof (unfold_locales, intro allI)
  fix x and y
  show "(\<pi>\<^sup>* x \<le> y) = (x \<le> \<pi>\<^sub>* y)" by (metis cl_galois_property)
qed

lemma poset_galois: "cl_galois_connection F G \<Longrightarrow> galois_connection F G"
  by (metis cl_galois_connection.poset_conn)

(* Least upper bounds with explicit carrier sets *)
context order
begin
  definition is_sub_lub :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_sub_lub x Y Z \<longleftrightarrow> Y \<subseteq> Z \<and> x \<in> Z \<and> (\<forall>z\<in>Z. x \<le> z \<longleftrightarrow> (\<forall>y\<in>Y. y \<le> z))"

  definition sub_lub :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
    "sub_lub B A \<equiv> (THE x. is_sub_lub x A B)"

  lemma sub_lub_univ_as_lub: "(\<exists>x. is_lub x X) \<Longrightarrow> (\<exists>x. is_sub_lub x X UNIV)"
    by (simp add: is_sub_lub_def is_lub_eqiv)

  lemma sub_lub_univ: "sub_lub UNIV A = \<Sigma> A"
    by (simp add: sub_lub_def lub_def is_lub_eqiv is_sub_lub_def)

  lemma is_sub_lub_unique: "is_sub_lub x A B \<longrightarrow> is_sub_lub y A B \<longrightarrow> x = y"
    by (smt antisym is_sub_lub_def order_refl)

  lemma is_sub_lub_unique_var: "\<lbrakk>is_sub_lub x Y Z; is_sub_lub y Y Z\<rbrakk> \<Longrightarrow> x = y"
    by (metis is_sub_lub_unique)

  lemma sub_lub_is_sub_lub: "is_sub_lub x A B \<Longrightarrow> sub_lub B A = x"
  proof -
    assume x_is_sub_lub: "is_sub_lub x A B"
    thus "sub_lub B A = x"
    proof (simp add: sub_lub_def)
      show "(THE x. is_sub_lub x A B) = x" using x_is_sub_lub
        by (metis is_sub_lub_unique the_equality)
    qed
  qed

  lemma sub_lub_leq:
    assumes subsets: "X \<subseteq> Y \<and> Y \<subseteq> Z"
    and exists_Y: "\<exists>y. is_sub_lub y X Y"
    and exists_Z: "\<exists>z. is_sub_lub z X Z"
    shows "sub_lub Z X \<le> sub_lub Y X"
    by (metis eq_refl exists_Y exists_Z in_mono is_sub_lub_def sub_lub_is_sub_lub subsets)

  corollary sub_lub_leq_rule: "\<lbrakk>X \<subseteq> Y; Y \<subseteq> Z; \<exists>y. is_sub_lub y Y X; \<exists>z. is_sub_lub z Z X\<rbrakk> \<Longrightarrow> sub_lub Z X \<le> sub_lub Y X"
    by (metis eq_iff equalityI is_sub_lub_def)
end

(* +------------------------------------------------------------------------+
   | Theorems 4.25(a) and 4.25(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma suprema_galois_aarts: "galois_connection f g = (ex_lub_junctive f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y}))"
  nitpick oops

theorem suprema_galois: "cl_galois_connection f g = (mono f \<and> ex_lub_junctive f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y}))"
proof
  assume "cl_galois_connection f g"
  thus "mono f \<and> ex_lub_junctive f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y})"
    using galois_lub galois_lub_junc poset_galois by (metis galois_connection.lower_mono mem_def)
next
  assume assms: "mono f \<and> ex_lub_junctive f \<and> (\<forall>y. is_lub (g y) {x. f x \<le> y})"
  hence fmon: "mono f" and elj: "ex_lub_junctive f" and a2: "\<forall>y. is_lub (g y) {x. f x \<le> y}" by metis+
  thus "cl_galois_connection f g"
  proof unfold_locales
    have left: "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
      by (metis Collect_def a2 is_lub_eqiv mem_def order_refl)
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
            by (smt Collect_def imageE is_lub_eqiv mem_def)
        qed

        have "f x \<le> y \<Longrightarrow> x \<le> \<Sigma> {z. f z \<le> y}" by (metis a2 gr lub_is_lub)
        moreover have "x \<le> \<Sigma> {z. f z \<le> y} \<Longrightarrow> f x \<le> f (\<Sigma> {z. f z \<le> y})" by (metis fmon monoD)
        moreover have "(f x \<le> f (\<Sigma> {z. f z \<le> y})) = (f x \<le> \<Sigma> (f ` {z. f z \<le> y}))"
          by (metis a2 elj ex_lub_junctive_def top_greatest)
        moreover have "... \<Longrightarrow> f x \<le> y" using lem by (metis order_trans)
        ultimately show ?thesis by (metis a2 gr lub_is_lub)
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)" by auto
  qed
qed

corollary suprema_galois_rule:
  "\<lbrakk>mono f; ex_lub_junctive f; \<forall>y. is_lub (g y) {x. f x \<le> y}\<rbrakk> \<Longrightarrow> cl_galois_connection f g"
  using suprema_galois by auto

theorem infima_galois: "cl_galois_connection f g = (mono g \<and> ex_glb_junctive g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y}))"
proof
  assume "cl_galois_connection f g"
  thus "mono g \<and> ex_glb_junctive g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y})"
    using galois_glb galois_glb_junc poset_galois by (metis galois_connection.upper_mono mem_def)
next
  assume assms: "mono g \<and> ex_glb_junctive g \<and> (\<forall>x. is_glb (f x) {y. x \<le> g y})"
  hence gmon: "mono g" and elj: "ex_glb_junctive g" and a2: "\<forall>x. is_glb (f x) {y. x \<le> g y}"  by metis+
  thus "cl_galois_connection f g"
  proof unfold_locales
    have right: "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
      by (metis Collect_def a2 is_glb_eqiv mem_def order_refl)
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
            by (smt Collect_def imageE is_glb_eqiv mem_def)
        qed

        have "x \<le> g y \<Longrightarrow> \<Pi> {z. x \<le> g z} \<le> y" by (metis a2 gr glb_is_glb)
        moreover have "\<Pi> {z. x \<le> g z} \<le> y \<Longrightarrow> g (\<Pi> {z. x \<le> g z}) \<le> g y" by (metis gmon monoD)
        moreover have "(g (\<Pi> {z. x \<le> g z}) \<le> g y) = (\<Pi> (g ` {z. x \<le> g z}) \<le> g y)"
          by (metis a2 elj ex_glb_junctive_def top_greatest)
        moreover have "... \<Longrightarrow> x \<le> g y" using lem by (metis order_trans)
        ultimately show ?thesis by (metis a2 gr glb_is_glb)
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)" by auto
  qed
qed

corollary infima_galois_rule:
  "\<lbrakk>mono g; ex_glb_junctive g; \<forall>x. is_glb (f x) {y. x \<le> g y}\<rbrakk> \<Longrightarrow> cl_galois_connection f g"
  using infima_galois by auto

(* +------------------------------------------------------------------------+
   | Theorems 4.26 and 4.27                                                 |
   +------------------------------------------------------------------------+ *)

theorem upper_exists_ex: "(\<exists>g. cl_galois_connection f g) = (mono f \<and> ex_lub_junctive f)"
proof
  assume upper: "\<exists>g. cl_galois_connection f g"
  show "mono f \<and> ex_lub_junctive f"
  proof (intro conjI)
    show "mono f" using upper by (metis galois_ump2 mem_def poset_galois)
  next
    show "ex_lub_junctive f" using upper by (metis galois_lub_junc poset_galois)
  qed
next
  assume "mono f \<and> ex_lub_junctive f"
  hence fmon: "mono f" and elj: "ex_lub_junctive f" and a: "\<forall>y. \<exists>z. is_lub z {x. f x \<le> y}" by (metis lub_ex)+
  have "\<exists>g. \<forall>y. is_lub (g y) {x. f x \<le> y}"
  proof
    show "\<forall>y. is_lub (\<Sigma> {x. f x \<le> y}) {x. f x \<le> y}" by (metis a lub_is_lub)
  qed
  thus "\<exists>g. cl_galois_connection f g" using suprema_galois by (metis elj fmon)
qed

theorem lower_exists_ex: "(\<exists>f. cl_galois_connection f g) = (mono g \<and> ex_glb_junctive g)"
proof
  assume upper: "\<exists>f. cl_galois_connection f g"
  show "mono g \<and> ex_glb_junctive g"
  proof (intro conjI)
    show "mono g" using upper by (metis galois_ump1 mem_def poset_galois)
  next
    show "ex_glb_junctive g" using upper by (metis galois_glb_junc poset_galois)
  qed
next
  assume "mono g \<and> ex_glb_junctive g"
  hence gmon: "mono g" and egj: "ex_glb_junctive g" and a: "\<forall>x. \<exists>z. is_glb z {y. x \<le> g y}" by (metis glb_ex)+
  have "\<exists>f. \<forall>x. is_glb (f x) {y. x \<le> g y}"
  proof
    show "\<forall>x. is_glb (\<Pi> {y. x \<le> g y}) {y. x \<le> g y}" by (metis a glb_is_glb)
  qed
  thus "\<exists>f. cl_galois_connection f g" using infima_galois by (metis egj gmon)
qed

(* +------------------------------------------------------------------------+
   | Definition 2.28                                                        |
   +------------------------------------------------------------------------+ *)

definition univ_lub_junctive :: "('a::order \<Rightarrow> 'b::complete_lattice) set" where
  "univ_lub_junctive f \<equiv> \<forall>X. \<Sigma> (f ` X) = f (\<Sigma> X)"

definition univ_glb_junctive :: "('a::order \<Rightarrow> 'b::complete_lattice) set" where
  "univ_glb_junctive f \<equiv> \<forall>X. \<Pi> (f ` X) = f (\<Pi> X)"

lemma univ_lub_is_ex: "univ_lub_junctive f \<Longrightarrow> ex_lub_junctive f"
  by (metis ex_lub_junctive_def univ_lub_junctive_def)

lemma univ_glb_is_ex: "univ_glb_junctive f \<Longrightarrow> ex_glb_junctive f"
  by (metis ex_glb_junctive_def univ_glb_junctive_def)

lemma galois_univ_lub_junc: "cl_galois_connection f g \<Longrightarrow> univ_lub_junctive f"
  by (metis ex_lub_junctive_def lub_ex subset_UNIV suprema_galois univ_lub_junctive_def)

lemma galois_univ_glb_junc: "cl_galois_connection f g \<Longrightarrow> univ_glb_junctive g"
  by (metis ex_glb_junctive_def glb_ex subset_UNIV infima_galois univ_glb_junctive_def)

(* +------------------------------------------------------------------------+
   | Theorems 4.36 and 4.37                                                 |
   +------------------------------------------------------------------------+ *)

theorem upper_exists: "(\<exists>g. cl_galois_connection f g) = (mono f \<and> univ_lub_junctive f)"
  using univ_lub_is_ex upper_exists_ex galois_univ_lub_junc by auto

theorem lower_exists: "(\<exists>f. cl_galois_connection f g) = (mono g \<and> univ_glb_junctive g)"
  using univ_glb_is_ex lower_exists_ex galois_univ_glb_junc by auto

(* +------------------------------------------------------------------------+
   | Theorems 4.39                                                          |
   +------------------------------------------------------------------------+ *)


theorem sup_eq:
  assumes conn: "cl_galois_connection f g"
  and xrange: "X \<subseteq> range g"
  (* and lex: "\<exists>x. is_sub_lub x X (range g)" *)
  and cpr: "sub_lub (range g) X \<le> g (f (\<Sigma> X))"
  shows "sub_lub (range g) X = g (f (\<Sigma> X))"
proof -
  have "\<exists>x. is_sub_lub x X (range g)" sledgehammer [timeout = 300]
  have "g (f (sub_lub UNIV X)) \<le> g (f (sub_lub (range g) X))"
  proof -
    have "sub_lub UNIV X \<le> sub_lub (range g) X"
    proof (rule sub_lub_leq)
      show "X \<subseteq> range g \<and> range g \<subseteq> UNIV" by (metis subset_UNIV xrange)
      show "\<exists>y. is_sub_lub y X (range g)" by (metis lex)
      show "\<exists>x. is_sub_lub x X UNIV" by (metis lub_ex sub_lub_univ_as_lub)
    qed
    thus ?thesis by (metis conn lower_exists monoD upper_exists)
  qed
  moreover have "g (f (sub_lub (range g) X)) = sub_lub (range g) X"
  proof -
    have "(THE x. is_sub_lub x X (range g)) \<in> range g"
    proof (rule the1I2)
      show "\<exists>!x. is_sub_lub x X (range g)" by (metis is_sub_lub_unique lex)
    next
      fix x
      show "is_sub_lub x X (range g) \<Longrightarrow> x \<in> range g" by (simp add: is_sub_lub_def)
    qed
    hence "sub_lub (range g) X \<in> range g" by (simp only: sub_lub_def)
    thus ?thesis using poset_galois perfect1 conn by metis
  qed
  ultimately show ?thesis using cpr by (metis order_eq_iff sub_lub_univ)
qed

end

