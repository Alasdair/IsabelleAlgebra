theory GaloisConnection
  imports Main
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
  apply (unfold_locales)
proof (intro allI)
  fix x and y
  show "(F x \<le> y) = (x \<le> G y)" by (metis mono_def a b c mem_def order_trans)
qed

lemma universal_mapping_property2:
  assumes a: "F \<in> mono" and b: "\<forall>x. F (G x) \<le> x"
  and c: "\<forall>x y. (F x \<le> y) \<longrightarrow> (x \<le> G y)"
  shows "galois_connection F G"
  apply unfold_locales
proof (intro allI)
  fix x and y
  have "(x \<le> G y) \<longrightarrow> (F x \<le> y)" using a b c
    apply (simp only: mem_def mono_def) by (metis order_trans)
  thus "(F x \<le> y) = (x \<le> G y)" using c by auto
qed

lemma galois_ump2: "galois_connection f g = (f \<in> mono \<and> (\<forall>y. f (g y) \<le> y) \<and> (\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y))"
  by (metis (no_types) galois_connection.lower_mono galois_connection.upper_dual galois_connection.upper_mono order_refl universal_mapping_property2)

lemma galois_ump1: "galois_connection f g = (g \<in> mono \<and> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y))"
  by (metis galois_connection.inflation galois_connection.upper_dual galois_connection.upper_mono universal_mapping_property1)

lemma ore_galois:
  assumes a: "\<forall>x. x \<le> G (F x)" and b: "\<forall>x. F (G x) \<le> x"
  and c: "F \<in> mono" and d: "G \<in> mono"
  shows "galois_connection F G"
  apply unfold_locales
proof (intro allI)
  fix x and y
  show "(F x \<le> y) = (x \<le> G y)" using a b c d
    apply (simp only: mem_def mono_def) by (metis order_trans)
qed

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

end
