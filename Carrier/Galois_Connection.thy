theory Galois_Connection
  imports Lattice
begin

(*
record ('a, 'b) adjoints = "('a, 'b) bi_ord" +
  lower :: "'a \<Rightarrow> 'b" ("\<pi>\<^sup>*\<index>")
  upper :: "'b \<Rightarrow> 'a" ("\<pi>\<^sub>*\<index>")

locale galois_connection = fixes G (structure)"
  assumes is_order_A: "order \<alpha>"
  and is_order_B: "order \<beta>"
  and lower_closure: "x \<in> carrier \<alpha> \<Longrightarrow> \<pi>\<^sup>* x \<in> carrier \<beta>"
  and upper_closure: "y \<in> carrier \<beta> \<Longrightarrow> \<pi>\<^sub>* y \<in> carrier \<alpha>"
  and galois_property: "\<lbrakk>\<pi>\<^sup>* x \<in> carrier \<beta>; x \<in> carrier \<alpha>; y \<in> carrier \<beta>; \<pi>\<^sub>* y \<in> carrier \<alpha>\<rbrakk> \<Longrightarrow> \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<beta>\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>\<alpha>\<^esub> \<pi>\<^sub>* y"
*)

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

lemma lower_type: "lower_adjoint A B f \<Longrightarrow> f \<Colon> carrier A \<rightarrow> carrier B"
  by (metis galois_connection.lower_closure lower_adjoint_def)

lemma upper_type: "upper_adjoint A B g \<Longrightarrow> g \<Colon> carrier B \<rightarrow> carrier A"
  by (metis galois_connection.upper_closure upper_adjoint_def)

lemma galois_ump1: "galois_connection A B f g = (f \<Colon> carrier A \<rightarrow> carrier B \<and> g \<Colon> carrier B \<rightarrow> carrier A \<and> isotone A B f \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y))"
proof
  assume "galois_connection A B f g"
  thus "f \<Colon> carrier A \<rightarrow> carrier B \<and> g \<Colon> carrier B \<rightarrow> carrier A \<and> isotone A B f \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y)"
    by (smt galois_connection.deflation galois_connection.galois_property galois_connection.lower_closure galois_connection.lower_iso galois_connection.upper_closure)
next
  assume "f \<Colon> carrier A \<rightarrow> carrier B \<and> g \<Colon> carrier B \<rightarrow> carrier A \<and> isotone A B f \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y)"
  thus "galois_connection A B f g"
    by (unfold galois_connection_def, safe, (metis isotone_def order.order_trans)+)
qed

lemma galois_ump2: "galois_connection A B f g = (isotone B A g \<and> (\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. x \<sqsubseteq>\<^bsub>A\<^esub> g y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> f \<Colon> carrier A \<rightarrow> carrier B \<and> g \<Colon> carrier B \<rightarrow> carrier A)"
proof
  assume "galois_connection A B f g"
  thus "isotone B A g \<and> (\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. x \<sqsubseteq>\<^bsub>A\<^esub> g y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> f \<Colon> carrier A \<rightarrow> carrier B \<and> g \<Colon> carrier B \<rightarrow> carrier A"
    by (smt galois_connection.inflation galois_connection.galois_property galois_connection.lower_closure galois_connection.upper_iso galois_connection.upper_closure)
next
  assume "isotone B A g \<and> (\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. x \<sqsubseteq>\<^bsub>A\<^esub> g y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> f \<Colon> carrier A \<rightarrow> carrier B \<and> g \<Colon> carrier B \<rightarrow> carrier A"
  thus "galois_connection A B f g"
    by (unfold galois_connection_def, safe, (metis isotone_def order.order_trans)+)
qed

(*
If we used our first definition of galois connections with carrier sets.
lemma galois_ump1: "galois_connection G = (isotone \<alpha>\<^bsub>G\<^esub> \<beta>\<^bsub>G\<^esub> \<pi>\<^sup>*\<^bsub>G\<^esub> \<and> (\<forall>y\<in>carrier \<beta>\<^bsub>G\<^esub>. \<pi>\<^sup>*\<^bsub>G\<^esub> (\<pi>\<^sub>*\<^bsub>G\<^esub> y) \<sqsubseteq>\<^bsub>(orderB G)\<^esub> y) \<and> (\<forall>x\<in>carrier \<alpha>\<^bsub>G\<^esub>. \<forall>y\<in>carrier \<beta>\<^bsub>G\<^esub>. \<pi>\<^sup>*\<^bsub>G\<^esub> x \<sqsubseteq>\<^bsub>(orderB G)\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>(orderA G)\<^esub> \<pi>\<^sub>*\<^bsub>G\<^esub> y))"
*)

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma ore_galois:
  assumes fclosed: "f \<Colon> carrier A \<rightarrow> carrier B" and gclosed: "g \<Colon> carrier B \<rightarrow> carrier A"
  and a: "\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)" and b: "\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y"
  and c: "isotone A B f" and d: "isotone B A g"
  shows "galois_connection A B f g"
  by (unfold galois_connection_def, safe, (metis a b c d gclosed fclosed isotone_def order.order_trans)+)

(* +------------------------------------------------------------------------+
   | Theorems 4.20(a) and 4.20(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma perfect1: "\<lbrakk>galois_connection A B f g; x \<in> carrier A\<rbrakk> \<Longrightarrow> g (f x) = x \<longleftrightarrow> x \<in> range g"
  by (smt Lattice.order.antisym galois_ump2 image_iff isotone_def order.order_refl range_eqI)

lemma perfect2: "\<lbrakk>galois_connection A B f g; x \<in> carrier B\<rbrakk> \<Longrightarrow> f (g x) = x \<longleftrightarrow> x \<in> range f"
  by (smt Lattice.order.antisym galois_connection.is_order_B galois_ump2 image_iff perfect1 range_eqI)

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
    apply (simp add: order.is_max_def order.is_lub_def order.is_ub_def)
    by (smt Collect_def conn galois_ump1 mem_def predicate1I yc)
qed

lemma galois_min:
  assumes conn: "galois_connection A B f g" and xc: "x \<in> carrier A"
  shows "order.is_min B (f x) {y. x \<sqsubseteq>\<^bsub>A \<^esub>g y \<and> y \<in> carrier B}"
proof -
  have "order B" by (metis conn galois_connection.is_order_B)
  thus ?thesis
    apply (simp add: order.is_min_def order.is_glb_def order.is_lb_def)
    by (smt Collect_def conn galois_ump2 mem_def predicate1I xc)
qed

theorem max_galois: "galois_connection A B f g = (isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<Colon> carrier B \<rightarrow> carrier A \<and> f \<Colon> carrier A \<rightarrow> carrier B)"
proof
  assume conn: "galois_connection A B f g"
  have "isotone A B f" by (metis conn galois_connection.lower_iso)
  moreover have "\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
    using galois_max conn by fast
  ultimately show "isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<Colon> carrier B \<rightarrow> carrier A \<and> f \<Colon> carrier A \<rightarrow> carrier B"
    by (smt conn galois_connection.lower_closure galois_connection.upper_closure)
next
  assume "isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<Colon> carrier B \<rightarrow> carrier A \<and> f \<Colon> carrier A \<rightarrow> carrier B"
  hence f_iso: "isotone A B f"
    and max: "\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
    and g_closed: "g \<Colon> carrier B \<rightarrow> carrier A"
    and f_closed: "f \<Colon> carrier A \<rightarrow> carrier B"
    by fast+
  show "galois_connection A B f g"
  proof (simp add: galois_ump1, safe, (metis g_closed f_closed)+)
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

lemma set_image_type: "\<lbrakk>X \<subseteq> A; f \<Colon> A \<rightarrow> B\<rbrakk> \<Longrightarrow> f ` X \<subseteq> B"
  by (metis image_subsetI set_rev_mp)

definition ex_join_preserving :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "ex_join_preserving A B f \<equiv> \<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_lub A x X) \<longrightarrow> order.lub B (f ` X) = f (order.lub A X))"

lemma lower_ub: "\<lbrakk>X\<subseteq>carrier A; x \<in> carrier A; order.is_lub A x X; lower_adjoint A B f\<rbrakk> \<Longrightarrow> order.is_ub B (f x) (f ` X)"
  apply (simp add: lower_adjoint_def)
  apply (unfold galois_connection_def)
  apply clarify
  apply (unfold order.is_lub_def order.is_ub_def)
  apply safe
  apply (metis in_mono)
  apply metis
  by (smt in_mono order.order_refl order.order_trans)

definition (in order) is_f_lub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_f_lub x X \<equiv>  is_ub x X \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y)"

lemma lower_lub: "\<lbrakk>X\<subseteq>carrier A; x \<in> carrier A; order.is_f_lub A x X; lower_adjoint A B f\<rbrakk> \<Longrightarrow> order.is_f_lub B (f x) (f ` X)" nitpick

lemma upper_glb: "\<lbrakk>X\<subseteq>carrier A; x \<in> carrier A; order.is_lub B x X; upper_adjoint A B g\<rbrakk> \<Longrightarrow> order.is_lb A (g x) (g ` X)"

locale complete_lattice_connection = galois_connection +
  assumes is_cl_A: "complete_lattice \<alpha>"
  and is_cl_B: "complete_lattice \<beta>"

definition cl_lower_adjoint :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "cl_lower_adjoint A B f \<equiv> \<exists>g. complete_lattice_connection A B f g"

lemma cl_to_galois: "complete_lattice_connection A B f g \<Longrightarrow> galois_connection A B f g"
  by (simp add: complete_lattice_connection_def)

lemma lower_preserves_joins: "\<lbrakk>cl_lower_adjoint A B f\<rbrakk> \<Longrightarrow> \<forall>X\<subseteq>carrier A. order.lub B (f ` X) = f (order.lub A X)" nitpick
  apply (simp add: lower_adjoint_def galois_connection_def order.ex_join_preserving_def)
proof

qed

 

(*
lemma lower_lub: "\<lbrakk>order.is_lub A x X; x \<in> carrier A; X \<subseteq> carrier A; lower_adjoint A B f; f\<rbrakk> \<Longrightarrow> order.is_lub B (f x) (f ` X)" nitpick

  by (smt galois_ump1 galois_ump2 image_iff is_lub_equiv lower_adjoint_def)

lemma upper_glb: "\<lbrakk>is_glb x X; upper_adjoint g\<rbrakk> \<Longrightarrow> is_glb (g x) (g ` X)"
  apply (simp add: is_glb_def upper_adjoint_def is_lb_def galois_connection_def)
  by (metis order_refl order_trans)
*)

lemma lower_preserves_joins: assumes lower: "lower_adjoint A B f" shows "order.join_preserving A f"
  using lower apply (simp add: lower_adjoint_def galois_connection_def) apply safe
  apply (simp add: order.join_preserving_def order.lub_def order.is_lub_def order.is_ub_def) nitpick

  by (metis assms ex_join_preserving_def lower_lub lub_is_lub)

lemma upper_preserves_meets: assumes upper: "upper_adjoint g" shows "ex_meet_preserving g"
  by (metis assms ex_meet_preserving_def upper_glb glb_is_glb)
end
