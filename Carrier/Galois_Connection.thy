theory Galois_Connection
  imports Lattice
begin

locale galois_connection =
  fixes orderA :: "'a ord" ("\<alpha>")
  and orderB :: "'b ord" ("\<beta>")
  and lower :: "'a \<Rightarrow> 'b" ("\<pi>\<^sup>*")
  and upper :: "'b \<Rightarrow> 'a" ("\<pi>\<^sub>*")
  assumes is_order_A: "order \<alpha>"
  and is_order_B: "order \<beta>"
  and lower_closure: "x \<in> carrier \<alpha> \<longleftrightarrow> \<pi>\<^sup>* x \<in> carrier \<beta>"
  and upper_closure: "y \<in> carrier \<beta> \<longleftrightarrow> \<pi>\<^sub>* y \<in> carrier \<alpha>"
  and galois_property: "\<lbrakk>\<pi>\<^sup>* x \<in> carrier \<beta>; x \<in> carrier \<alpha>; y \<in> carrier \<beta>; \<pi>\<^sub>* y \<in> carrier \<alpha>\<rbrakk> \<Longrightarrow> \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<beta>\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>\<alpha>\<^esub> \<pi>\<^sub>* y"

begin
  lemma right: "\<lbrakk>\<pi>\<^sup>* x \<in> carrier \<beta>; x \<in> carrier \<alpha>; y \<in> carrier \<beta>; \<pi>\<^sub>* y \<in> carrier \<alpha>; \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<beta>\<^esub> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<alpha>\<^esub> \<pi>\<^sub>* y"
    by (metis galois_property)

  lemma left: "\<lbrakk>\<pi>\<^sup>* x \<in> carrier \<beta>; x \<in> carrier \<alpha>; y \<in> carrier \<beta>; \<pi>\<^sub>* y \<in> carrier \<alpha>; x \<sqsubseteq>\<^bsub>\<alpha>\<^esub> \<pi>\<^sub>* y\<rbrakk> \<Longrightarrow> \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<beta>\<^esub> y"
    by (metis galois_property)

  lemma deflation: "y \<in> carrier \<beta> \<Longrightarrow> \<pi>\<^sup>* (\<pi>\<^sub>* y) \<sqsubseteq>\<^bsub>\<beta>\<^esub> y"
    by (metis galois_property is_order_A lower_closure order.order_refl upper_closure)

  lemma inflation: "x \<in> carrier \<alpha> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<alpha>\<^esub> \<pi>\<^sub>* (\<pi>\<^sup>* x)"
    by (metis galois_property is_order_B lower_closure order.order_refl upper_closure)

  lemma lower_iso: "isotone \<alpha> \<beta> \<pi>\<^sup>*"
    by (smt galois_property inflation is_order_A is_order_B isotone_def lower_closure order.order_trans upper_closure)

  lemma upper_iso: "isotone \<beta> \<alpha> \<pi>\<^sub>*"
    by (smt deflation galois_property is_order_A is_order_B isotone_def lower_closure order.order_trans upper_closure)

  lemma lower_comp: "x \<in> carrier \<alpha> \<Longrightarrow> (\<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<circ> \<pi>\<^sup>*) x = \<pi>\<^sup>* x"
    by (metis (no_types) order.antisym deflation inflation isotone_def lower_closure lower_iso o_apply upper_closure)

  lemma upper_comp: "y \<in> carrier \<beta> \<Longrightarrow> (\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>*) y = \<pi>\<^sub>* y"
    by (smt order.antisym deflation inflation isotone_def lower_closure o_apply upper_closure upper_iso)

  lemma adjoint_idem1: "idempotent (carrier \<beta>) (\<pi>\<^sup>* \<circ> \<pi>\<^sub>*)"
    by (smt idempotent_def o_apply o_assoc upper_comp)

  lemma adjoint_idem2: "idempotent (carrier \<alpha>) (\<pi>\<^sub>* \<circ> \<pi>\<^sup>*)"
    by (smt idempotent_def o_apply o_assoc lower_comp)

end

definition lower_adjoint :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "lower_adjoint A B f \<equiv> \<exists>g. galois_connection A B f g"

definition upper_adjoint :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "upper_adjoint A B g \<equiv> \<exists>f. galois_connection A B f g"

lemma lower_type: "lower_adjoint A B f \<Longrightarrow> f \<in> carrier A \<rightarrow> carrier B"
  by (smt mem_def galois_connection.lower_closure lower_adjoint_def)

lemma upper_type: "upper_adjoint A B g \<Longrightarrow> g \<in> carrier B \<rightarrow> carrier A"
  by (smt mem_def galois_connection.upper_closure upper_adjoint_def)

lemma lower_type_var: "galois_connection A B f g \<Longrightarrow> f \<in> carrier A \<rightarrow> carrier B"
  by (smt mem_def galois_connection.lower_closure lower_adjoint_def)

lemma upper_type_var: "galois_connection A B f g \<Longrightarrow> g \<in> carrier B \<rightarrow> carrier A"
  by (smt mem_def galois_connection.upper_closure upper_adjoint_def)

lemma id_galois: "order A \<Longrightarrow> galois_connection A A id id"
  by (simp add: galois_connection_def)

lemma semi_inverse1: "\<lbrakk>x \<in> carrier A; galois_connection A B f g\<rbrakk> \<Longrightarrow> f x = f (g (f x))"
  by (metis galois_connection.lower_comp o_apply)

lemma semi_inverse2: "\<lbrakk>x \<in> carrier B; galois_connection A B f g\<rbrakk> \<Longrightarrow> g x = g (f (g x))"
  by (metis galois_connection.upper_comp o_def)

lemma galois_ump1: "galois_connection A B f g = (f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A \<and> isotone A B f \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y))"
proof
  assume "galois_connection A B f g"
  thus "f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A \<and> isotone A B f \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y)"
    by (smt mem_def galois_connection.deflation galois_connection.galois_property galois_connection.lower_closure galois_connection.lower_iso galois_connection.upper_closure)
next
  assume "f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A \<and> isotone A B f \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y)"
  thus "galois_connection A B f g"
    by (unfold galois_connection_def, safe, (smt mem_def isotone_def order.order_trans)+)
qed

lemma galois_ump2: "galois_connection A B f g = (isotone B A g \<and> (\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. x \<sqsubseteq>\<^bsub>A\<^esub> g y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A)"
proof
  assume "galois_connection A B f g"
  thus "isotone B A g \<and> (\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. x \<sqsubseteq>\<^bsub>A\<^esub> g y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A"
    by (smt mem_def galois_connection.inflation galois_connection.galois_property galois_connection.lower_closure galois_connection.upper_iso galois_connection.upper_closure)
next
  assume "isotone B A g \<and> (\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. x \<sqsubseteq>\<^bsub>A\<^esub> g y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A"
  thus "galois_connection A B f g"
    by (unfold galois_connection_def, safe, (smt mem_def isotone_def order.order_trans)+)
qed

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma ore_galois:
  assumes fclosed: "f \<in> carrier A \<rightarrow> carrier B" and gclosed: "g \<in> carrier B \<rightarrow> carrier A"
  and a: "\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)" and b: "\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y"
  and c: "isotone A B f" and d: "isotone B A g"
  shows "galois_connection A B f g"
  by (unfold galois_connection_def, safe, (smt mem_def a b c d gclosed fclosed isotone_def order.order_trans)+)

(* +------------------------------------------------------------------------+
   | Theorems 4.20(a) and 4.20(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma perfect1: "\<lbrakk>galois_connection A B f g; x \<in> carrier A\<rbrakk> \<Longrightarrow> g (f x) = x \<longleftrightarrow> x \<in> range g"
  by (smt mem_def Lattice.order.antisym galois_ump2 image_iff isotone_def order.order_refl range_eqI)

lemma perfect2: "\<lbrakk>galois_connection A B f g; x \<in> carrier B\<rbrakk> \<Longrightarrow> f (g x) = x \<longleftrightarrow> x \<in> range f"
  by (smt mem_def Lattice.order.antisym galois_connection.is_order_B galois_ump2 image_iff perfect1 range_eqI)

(* +------------------------------------------------------------------------+
   | Theorems 4.20(a) and 4.20(b)                                           |
   +------------------------------------------------------------------------+ *)

context order
begin

  definition is_max :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_max x X \<equiv> x \<in> X \<and> is_lub x X"

  definition is_min :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_min x X \<equiv> x \<in> X \<and> is_glb x X"

end

lemma galois_max:
  assumes conn: "galois_connection A B f g" and yc: "y \<in> carrier B"
  shows "order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
proof -
  have "order A" by (metis conn galois_connection.is_order_A)
  thus ?thesis
    apply (simp add: order.is_max_def order.is_lub_def order.is_ub_def mem_def)
    by (smt Collect_def conn galois_ump1 mem_def predicate1I yc)
qed

lemma galois_min:
  assumes conn: "galois_connection A B f g" and xc: "x \<in> carrier A"
  shows "order.is_min B (f x) {y. x \<sqsubseteq>\<^bsub>A \<^esub>g y \<and> y \<in> carrier B}"
proof -
  have "order B" by (metis conn galois_connection.is_order_B)
  thus ?thesis
    apply (simp add: order.is_min_def order.is_glb_def order.is_lb_def mem_def)
    by (smt Collect_def conn galois_ump2 mem_def predicate1I xc)
qed

theorem max_galois: "galois_connection A B f g = (isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<in> carrier B \<rightarrow> carrier A \<and> f \<in> carrier A \<rightarrow> carrier B)"
proof
  assume conn: "galois_connection A B f g"
  have "isotone A B f" by (metis conn galois_connection.lower_iso)
  moreover have "\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
    using galois_max conn by fast
  ultimately show "isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<in> carrier B \<rightarrow> carrier A \<and> f \<in> carrier A \<rightarrow> carrier B"
    by (smt mem_def conn galois_connection.lower_closure galois_connection.upper_closure)
next
  assume "isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<in> carrier B \<rightarrow> carrier A \<and> f \<in> carrier A \<rightarrow> carrier B"
  hence f_iso: "isotone A B f"
    and max: "\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
    and g_closed: "g \<in> carrier B \<rightarrow> carrier A"
    and f_closed: "f \<in> carrier A \<rightarrow> carrier B"
    by fast+
  show "galois_connection A B f g"
  proof (simp add: galois_ump1, safe, (smt mem_def g_closed f_closed)+)
    show "isotone A B f" by (metis f_iso)
  next
    fix y assume yc: "y \<in> carrier B"
    have "order A" and "order B" by (metis f_iso isotone_def)+
    hence "g y \<in> {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
      using max yc by (simp add: order.is_max_def)
    thus "f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y" by (metis Collect_def mem_def)
  next
    fix x y assume xc: "x \<in> carrier A" and yc: "y \<in> carrier B" and lower: "f x \<sqsubseteq>\<^bsub>B\<^esub> y"
    have oa: "order A" and ob: "order B" by (metis f_iso isotone_def)+
    hence lub1: "order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
      using max yc by (simp add: order.is_max_def)
    thus "x \<sqsubseteq>\<^bsub>A\<^esub> g y" using oa by (simp add: order.is_lub_def order.is_ub_def, metis lower xc)
  qed
qed

(* +------------------------------------------------------------------------+
   | Lemma 4.24(a) and 4.24(b)                                              |
   +------------------------------------------------------------------------+ *)

lemma set_image_type: "\<lbrakk>X \<subseteq> A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> f ` X \<subseteq> B"
  by (smt mem_def image_subsetI set_rev_mp)

lemma lower_ub: "\<lbrakk>X\<subseteq>carrier A; x \<in> carrier A; order.is_lub A x X; lower_adjoint A B f\<rbrakk> \<Longrightarrow> order.is_ub B (f x) (f ` X)"
  apply (simp add: lower_adjoint_def)
  apply (unfold galois_connection_def)
  apply clarify
  apply (unfold order.is_lub_def order.is_ub_def)
  apply safe
  apply (metis in_mono)
  apply metis
  by (smt in_mono order.order_refl order.order_trans)

lemma lower_lub:
  assumes Xc: "X\<subseteq>carrier A" and xc: "x \<in> carrier A"
  and il: "order.is_lub A x X" and la: "lower_adjoint A B f"
  shows "order.is_lub B (f x) (f ` X)"
proof -
  have ord_B: "order B" and ord_A: "order A"
    by (metis galois_connection.is_order_B galois_connection.is_order_A la lower_adjoint_def)+
  thus ?thesis apply (simp add: order.is_lub_def)
  proof
    show "order.is_ub B (f x) (f ` X)"
      by (metis Xc il la lower_ub xc)

    obtain g where gc: "galois_connection A B f g"
      by (metis la lower_adjoint_def)

    thus "\<forall>y\<in>carrier B. (\<forall>z\<in>X. f z \<sqsubseteq>\<^bsub>B\<^esub> y) \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y"
      by (smt Xc galois_ump1 gc galois_connection_def set_rev_mp xc il ord_A order.is_lub_def)
  qed
qed

lemma upper_lb: "\<lbrakk>X\<subseteq>carrier B; x \<in> carrier B; order.is_glb B x X; upper_adjoint A B g\<rbrakk> \<Longrightarrow> order.is_lb A (g x) (g ` X)"
  apply (simp add: upper_adjoint_def)
  apply (unfold galois_connection_def)
  apply clarify
  apply (unfold order.is_glb_def order.is_lb_def)
  apply safe
  apply (metis in_mono)
  apply metis
  by (smt in_mono order.order_refl order.order_trans)

lemma upper_glb:
  assumes Xc: "X\<subseteq>carrier B" and xc: "x \<in> carrier B"
  and ig: "order.is_glb B x X" and ua: "upper_adjoint A B g"
  shows "order.is_glb A (g x) (g ` X)"
proof -
  have ord_B: "order B" and ord_A: "order A"
    by (metis galois_connection.is_order_B galois_connection.is_order_A ua upper_adjoint_def)+
  thus ?thesis apply (simp add: order.is_glb_def)
  proof
    show "order.is_lb A (g x) (g ` X)"
      by (metis Xc ig ua upper_lb xc)

    obtain f where gc: "galois_connection A B f g"
      by (metis ua upper_adjoint_def)

    thus "\<forall>y\<in>carrier A. (\<forall>x\<in>X. y \<sqsubseteq>\<^bsub>A\<^esub> g x) \<longrightarrow> y \<sqsubseteq>\<^bsub>A\<^esub> g x"
      by (smt Xc galois_ump2 gc galois_connection_def set_rev_mp xc ig ord_A order.is_glb_def)
  qed
qed

lemma lower_preserves_ex_joins: assumes lower: "lower_adjoint A B f" shows "ex_join_preserving A B f"
proof (simp add: ex_join_preserving_def, safe)
  fix X x assume Xc: "X \<subseteq> carrier A" and xc: "x \<in> carrier A" and il: "order.is_lub A x X"
  have "order B"
    by (metis assms galois_connection.is_order_B lower_adjoint_def)
  thus "order.lub B (f ` X) = f (order.lub A X)"
    by (metis order.lub_is_lub Xc assms galois_connection.is_order_A il lower_adjoint_def lower_lub xc)
qed

lemma upper_preserves_ex_meets: assumes upper: "upper_adjoint A B g" shows "ex_meet_preserving B A g"
proof (simp add: ex_meet_preserving_def, safe)
  fix X x assume Xc: "X \<subseteq> carrier B" and xc: "x \<in> carrier B" and ig: "order.is_glb B x X"
  have "order A"
    by (metis assms galois_connection.is_order_A upper_adjoint_def)
  thus "order.glb A (g ` X) = g (order.glb B X)"
    by (metis order.glb_is_glb Xc assms galois_connection.is_order_B ig upper_adjoint_def upper_glb xc)
qed

(* +------------------------------------------------------------------------+
   | Galois Connections for Complete Lattices                               |
   +------------------------------------------------------------------------+ *)

locale complete_lattice_connection = galois_connection +
  assumes is_cl_A: "complete_lattice \<alpha>"
  and is_cl_B: "complete_lattice \<beta>"

definition cl_lower_adjoint :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "cl_lower_adjoint A B f \<equiv> \<exists>g. complete_lattice_connection A B f g"

definition cl_upper_adjoint :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "cl_upper_adjoint A B g \<equiv> \<exists>f. complete_lattice_connection A B f g"

lemma cl_to_galois: "complete_lattice_connection A B f g \<Longrightarrow> galois_connection A B f g"
  by (simp add: complete_lattice_connection_def)

lemma cl_is_order: "complete_lattice A \<Longrightarrow> order A"
  by (simp add: complete_lattice_def complete_join_semilattice_def)

lemma suprema_galois: "complete_lattice_connection A B f g =
                       (complete_lattice A \<and> complete_lattice B
                       \<and> f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A
                       \<and> ex_join_preserving A B f
                       \<and> (\<forall>y\<in>carrier B. order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}))" sorry
(*
  apply default
  apply safe
  apply (metis complete_lattice_connection.is_cl_A)
  apply (metis complete_lattice_connection.is_cl_B)
  apply (smt mem_def cl_to_galois galois_connection.lower_closure)
  apply (smt cl_to_galois galois_connection.upper_closure mem_def)
  apply (metis cl_to_galois lower_adjoint_def lower_preserves_ex_joins)
proof -
  fix y
  assume conn: "complete_lattice_connection A B f g" and yc: "y \<in> carrier B"
  hence poset_galois: "galois_connection A B f g" by (metis cl_to_galois)
  hence ord_A: "order A" by (metis galois_connection.is_order_A)
  thus "order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
    apply (simp add: order.is_lub_def order.is_ub_def)
    apply safe
    apply (metis galois_connection.upper_closure poset_galois yc)
    apply (smt mem_def galois_ump1 poset_galois yc)
    by (smt mem_def galois_ump1 poset_galois yc)
next
  assume clA: "complete_lattice A" and clB: "complete_lattice B"
  and f_closed: "\<forall>x. (x \<in> carrier A) = (f x \<in> carrier B)"
  and g_closed: "\<forall>x. (x \<in> carrier B) = (g x \<in> carrier A)"
  and ejp: "ex_join_preserving A B f"
  and lub: "\<forall>y\<in>carrier B. order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
  thus "complete_lattice_connection A B f g"
    apply (unfold complete_lattice_connection_def)
    apply safe
    defer
    apply (unfold complete_lattice_connection_axioms_def)
    apply metis
    apply (unfold galois_connection_def)
    apply safe
    apply (metis cl_is_order)
    apply (metis cl_is_order)
    apply (simp add: complete_lattice_def complete_join_semilattice_def complete_meet_semilattice_def)
    apply (simp add: complete_join_semilattice_axioms_def complete_meet_semilattice_axioms_def)
    apply (simp add: ex_join_preserving_def)
    apply safe
    sorry
qed
*)

lemma infima_galois: "complete_lattice_connection A B f g =
                      (complete_lattice A \<and> complete_lattice B
                      \<and> f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A
                      \<and> ex_meet_preserving B A g
                      \<and> (\<forall>x\<in>carrier A. order.is_glb B (f x) {y. x \<sqsubseteq>\<^bsub>A\<^esub> g y \<and> y \<in> carrier B}))"
  sorry

lemma cl_lower_join_preserving:
  assumes lower: "cl_lower_adjoint A B f" shows "join_preserving A B f"
proof -
  have "lower_adjoint A B f"
    by (metis assms cl_lower_adjoint_def cl_to_galois lower_adjoint_def)
  hence ejp: "ex_join_preserving A B f"
    by (metis lower_preserves_ex_joins)
  have "complete_lattice A"
    by (metis assms cl_lower_adjoint_def complete_lattice_connection.is_cl_A)
  hence "\<forall>X\<subseteq>carrier A. \<exists>x\<in>carrier A. order.is_lub A x X"
    by (simp add: complete_lattice_def complete_join_semilattice_def complete_join_semilattice_axioms_def)
  hence "\<forall>X\<subseteq>carrier A. order.lub B (f ` X) = f (order.lub A X)"
    by (metis ex_join_preserving_def ejp)
  thus ?thesis
    by (metis join_preserving_def)
qed

lemma cl_upper_meet_preserving:
  assumes upper: "cl_upper_adjoint A B g" shows "meet_preserving B A g"
proof -
  have "upper_adjoint A B g"
    by (metis assms cl_to_galois cl_upper_adjoint_def upper_adjoint_def)
  hence emp: "ex_meet_preserving B A g"
    by (metis upper_preserves_ex_meets)
  have "complete_lattice B"
    by (metis assms cl_upper_adjoint_def complete_lattice_connection.is_cl_B)
  hence "\<forall>X\<subseteq>carrier B. (\<exists>x\<in>carrier B. order.is_glb B x X)"
    by (simp add: complete_lattice_def complete_meet_semilattice_def complete_meet_semilattice_axioms_def)
  hence "\<forall>X\<subseteq>carrier B. order.glb A (g ` X) = g (order.glb B X)"
    by (metis ex_meet_preserving_def emp)
  thus ?thesis
    by (metis meet_preserving_def)
qed

(* +------------------------------------------------------------------------+
   | Fixpoints and Galois connections                                       |
   +------------------------------------------------------------------------+ *)

abbreviation least_fixpoint_car :: "'a ord \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "\<mu>\<^bsub>A\<^esub> f \<equiv> complete_lattice.least_fixpoint A f"

lemma lfp_equality_ind: "\<lbrakk>complete_lattice A; complete_lattice.is_lfp A x f\<rbrakk> \<Longrightarrow> \<mu>\<^bsub>A\<^esub> f = x"
  apply (simp add: complete_lattice.least_fixpoint_def)
  apply (rule the_equality)
  apply auto
  by (metis complete_lattice.lfp_equality)

(*
lemma lfp_equality_var [intro?]: "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; x \<in> carrier A; f x = x; \<forall>y\<in>carrier A. f y = y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> x = \<mu>\<^bsub>A\<^esub> f"
  apply (rule complete_lattice.lfp_equality[symmetric])
    by (smt mem_def is_fp_def is_lfp_def lfp_equality)
*)

lemma galois_dual: "galois_connection A B f g \<Longrightarrow> galois_connection B A g f" sorry

lemma truncate_simp [simp]: "ord.truncate A = A"
  by (simp add: ord.truncate_def)

lemma fixpoint_rolling: assumes conn: "complete_lattice_connection A B f g"
  shows "f (\<mu>\<^bsub>A\<^esub> (g \<circ> f)) = \<mu>\<^bsub>B\<^esub> (f \<circ> g)"
proof (rule complete_lattice.lfp_equality_var)
  show clB: "complete_lattice B"
    by (metis assms complete_lattice_connection.is_cl_B)

  show closure1: "f \<circ> g \<in> carrier B \<rightarrow> carrier B"
    apply (simp add: mem_def)
    by (smt assms cl_to_galois galois_connection.lower_closure galois_connection.upper_closure mem_def o_apply)

  have cl_A: "complete_lattice A" by (metis assms complete_lattice_connection.is_cl_A)
  hence fp_exists: "\<exists>!x. complete_lattice.is_lfp A x (g \<circ> f)"
    apply (rule complete_lattice.knaster_tarski_var)
    apply (smt assms cl_to_galois galois_connection.lower_closure galois_connection.upper_closure mem_def o_apply)
    using conn apply (simp add: isotone_def)
    by (metis (full_types) cl_to_galois galois_connection.lower_closure galois_connection.lower_iso galois_connection.upper_iso isotone_def)
  hence closure2: "(\<mu>\<^bsub>A\<^esub> (g \<circ> f)) \<in> carrier A"
    by (metis cl_A complete_lattice.least_fixpoint_set)
  thus closure3: "(f (\<mu>\<^bsub>A \<^esub>(g \<circ> f))) \<in> carrier B"
    by (metis assms cl_to_galois galois_connection.lower_closure)

  have "f (g (f (\<mu>\<^bsub>A\<^esub>(g \<circ> f)))) = f (\<mu>\<^bsub>A\<^esub>(g \<circ> f))"
    by (rule_tac f = f and A = A and B = B in semi_inverse1[symmetric], metis closure2, metis assms cl_to_galois)
  thus "(f \<circ> g) (f (\<mu>\<^bsub>A\<^esub>(g \<circ> f))) = f (\<mu>\<^bsub>A\<^esub>(g \<circ> f))"
    by (metis o_def)

  show "\<forall>y\<in>carrier B. (f \<circ> g) y = y \<longrightarrow> f (\<mu>\<^bsub>A\<^esub>(g \<circ> f)) \<sqsubseteq>\<^bsub>B\<^esub> y"
  proof safe
    fix y assume yc: "y \<in> carrier B" and fgy: "(f \<circ> g) y = y"
    have "complete_lattice A" by (metis cl_A)
    hence "\<mu>\<^bsub>A\<^esub>(g \<circ> f) \<sqsubseteq>\<^bsub>A\<^esub> g y"
      apply (rule complete_lattice.fixpoint_induction)
      apply (metis (no_types) fp_exists cl_A complete_lattice.is_lfp_closed)
      apply (metis assms cl_to_galois galois_connection.upper_closure yc)
      using conn apply (simp add: isotone_def, safe)
      apply (metis cl_A cl_is_order)
      apply (smt cl_A cl_is_order cl_to_galois galois_connection.deflation galois_connection.galois_property galois_connection.upper_closure galois_dual order.order_trans)
      by (metis cl_A cl_is_order cl_to_galois fgy galois_connection.upper_closure o_apply order.order_refl yc)
    thus "f (\<mu>\<^bsub>A\<^esub>(g \<circ> f)) \<sqsubseteq>\<^bsub>B\<^esub> y"
      by (smt assms cl_to_galois closure3 fgy galois_connection.galois_property galois_connection.lower_closure o_apply yc)
  qed
qed

lemma least_fixpoint_closed:
  assumes cl: "complete_lattice A"
  and f_type: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "\<mu>\<^bsub>A\<^esub>f \<in> carrier A"
proof -
  have "\<exists>!x. complete_lattice.is_lfp A x f" using cl f_type
    by (rule complete_lattice.knaster_tarski_var, simp, metis f_iso)
  thus ?thesis
    by (metis cl complete_lattice.least_fixpoint_set)
qed

lemma use_iso2: "\<lbrakk>isotone A A f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>A\<^esub> f y"
  by (simp add: isotone_def)

lemma fixpoint_computation_var:
  "\<lbrakk>complete_lattice A; f \<in> carrier A \<rightarrow> carrier A; isotone A A f\<rbrakk> \<Longrightarrow> f (\<mu>\<^bsub>A\<^esub>f) = \<mu>\<^bsub>A\<^esub>f"
  by (rule complete_lattice.fixpoint_computation, auto+)

theorem fixpoint_fusion [simp]:
  assumes upper_ex: "cl_lower_adjoint A B f"
  and ft: "f \<in> carrier A \<rightarrow> carrier B" and ht: "h \<in> carrier A \<rightarrow> carrier A" and kt: "k \<in> carrier B \<rightarrow> carrier B"
  and hiso: "isotone A A h" and kiso: "isotone B B k"
  and comm: "f\<circ>h = k\<circ>f"
  shows "f (\<mu>\<^bsub>A\<^esub> h) = \<mu>\<^bsub>B\<^esub> k"
proof (rule complete_lattice.lfp_equality_var)
  obtain g where conn: "complete_lattice_connection A B f g"
    by (metis cl_lower_adjoint_def upper_ex)

  have cl_A: "complete_lattice A"
    by (metis cl_lower_adjoint_def complete_lattice_connection.is_cl_A upper_ex)

  show cl_B: "complete_lattice B"
    by (metis cl_lower_adjoint_def complete_lattice_connection.is_cl_B upper_ex)

  show "k \<in> carrier B \<rightarrow> carrier B" by (metis kt)

  have closure1: "\<mu>\<^bsub>A\<^esub>h \<in> carrier A" using cl_A ht hiso
    by (rule least_fixpoint_closed)

  thus closure2: "f (\<mu>\<^bsub>A\<^esub>h) \<in> carrier B"
    by (metis cl_to_galois conn galois_connection.lower_closure)

  have comm_var: "\<And>x. k (f x) = f (h x)"
    by (metis comm o_apply)

  show "k (f (\<mu>\<^bsub>A\<^esub>h)) = f (\<mu>\<^bsub>A\<^esub>h)"
    by (smt cl_A comm_var fixpoint_computation_var hiso ht mem_def)

  show "\<forall>y\<in>carrier B. k y = y \<longrightarrow> f (\<mu>\<^bsub>A\<^esub>h) \<sqsubseteq>\<^bsub>B\<^esub> y"
  proof clarify
    fix y assume yc: "y \<in> carrier B" and ky: "k y = y"

    have gy: "g y \<in> carrier A"
      by (metis cl_to_galois conn galois_connection.upper_closure yc)
    hence hgy: "h (g y) \<in> carrier A"
      by (rule_tac f = h and A = "carrier A" in closed_application, (metis ht)+)
    hence fhgy: "f (h (g y)) \<in> carrier B"
      by (rule_tac f = f and A = "carrier A" in closed_application, (metis ft)+)

    have "\<mu>\<^bsub>A\<^esub> h \<sqsubseteq>\<^bsub>A\<^esub> g y" using cl_A ht gy
    proof (rule complete_lattice.fixpoint_induction)
      show "isotone (ord.truncate A) (ord.truncate A) h"
        by (simp, metis hiso)
      have "f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y"
        by (metis cl_to_galois conn galois_connection.deflation yc)
      hence "k (f (g y)) \<sqsubseteq>\<^bsub>B\<^esub> k y"
        by (metis cl_to_galois conn galois_connection.lower_closure gy kiso use_iso2 yc)
      hence "f (h (g y)) \<sqsubseteq>\<^bsub>B\<^esub> y"
        by (simp only: comm_var[symmetric] ky)
      thus "h (g y) \<sqsubseteq>\<^bsub>A\<^esub> g y" using gy hgy fhgy yc
        by (rule_tac lower = f and orderB = B in galois_connection.right, metis cl_to_galois conn, auto+)
    qed
    thus "f (\<mu>\<^bsub>A\<^esub> h) \<sqsubseteq>\<^bsub>B\<^esub> y"
      by (metis closure1 closure2 cl_to_galois conn galois_connection.left gy yc)
  qed
qed
