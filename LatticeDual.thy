header {* Boolean Algebras *}

theory Lattice
  imports Main Signatures Duality
begin

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

instantiation dual :: (ord) ord
begin
  definition less_eq_dual: "x \<le> y \<equiv> undual y \<le> undual x"
  definition less_dual: "x < y \<equiv> undual y < undual x"

  instance ..
end

instance dual :: (order) order
proof
  fix x y z :: "'a dual"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (metis less_dual less_eq_dual less_le_not_le)
  show "x \<le> x" by (metis less_eq_dual order_refl)
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z" by (metis less_eq_dual order_trans)
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y" by (metis dual_undual less_eq_dual order_eq_iff)
qed

lemma dual_leq [iff?]: "(dual x \<le> dual y) \<longleftrightarrow> (y \<le> x)"
  by (metis less_eq_dual_raw undual.simps)

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

definition image :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where
  "image f \<equiv> {y. \<exists>x. y = f x}"

definition (in order) cup_junctive :: "('a \<Rightarrow> 'a) set" where
  "cup_junctive f \<equiv> \<forall>X \<subseteq> (image f). \<exists>x. is_lub x X"

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

lemma dual_undual_leq [simp]: "undual (dual x) \<le> x" by (simp add: undual_dual)

end

definition ext_cup_junctive :: "('a::order \<Rightarrow> 'b::order) set" where
  "ext_cup_junctive f \<equiv> \<forall>X \<subseteq> UNIV. (\<exists>x. is_lub x X) \<longrightarrow> f (\<Sigma> X) = \<Sigma> (f ` X)"

lemma undual_to_dual: "(undual x \<le> y) = (dual y \<le> x)" by (metis dual_leq dual_undual)

lemma dual_to_undual: "(x \<le> undual y) = (y \<le> dual x)" by (metis less_eq_dual undual.simps)

lemma undual_leq: "(undual x \<le> undual y) = (y \<le> x)" by (metis less_eq_dual)

theorem dual_is_lub [iff?]: "is_lub (dual x) (dual ` A) = is_glb x A"
by (simp add: is_glb_def is_lub_def is_ub_def is_lb_def dual_all [symmetric] dual_leq)

lemma undual_all [iff?]: "(\<forall>x. P (undual x)) \<longleftrightarrow> (\<forall>x. P x)"
by (metis undual.simps)

theorem undual_is_lub [iff?]: "is_lub (undual x) (undual ` A) = is_glb x A"
apply (simp add: is_glb_def is_lub_def is_ub_def is_lb_def)
by (metis undual_leq undual_to_dual)

lemma undual_dual_set: "(undual ` (dual ` A)) = A"
by (metis dual_undual image_surj_f_inv_f surjI surj_imp_inv_eq undual.simps)

(*
theorem dual_is_glb [iff?]: "is_glb (dual x) (dual ` A) = is_lub x A"
proof -
  have "is_glb (dual x) (dual ` A) = is_lub (undual (dual x)) (undual ` (dual ` A))" by (simp only: undual_is_lub)
  also have "... = is_lub x A" by (simp only: undual_dual undual_dual_set)
qed
*)

(* by (simp add: is_glb_def is_lub_def is_ub_def is_lb_def dual_all [symmetric] dual_leq) *)

theorem undual_is_glb [iff?]: "is_lub (undual x) (undual ` A) = is_glb x A"
apply (simp add: is_glb_def is_lub_def is_ub_def is_lb_def)
apply (simp add: dual_all [symmetric] dual_leq undual_equality [symmetric] undual_leq)
by (simp add: undual_to_dual)

theorem dual_is_glb [iff?]: "is_lub (dual x) (dual ` A) = is_glb x A"
apply (simp add: is_glb_def is_lub_def is_ub_def is_lb_def)
by (simp add: dual_all [symmetric] dual_leq undual_equality [symmetric] undual_leq)

class ord_join_semilattice = order +
  assumes join_ex: "\<forall>x y. \<exists>z. is_lub z {x,y}"

class ord_meet_semilattice = order +
  assumes meet_ex: "\<forall>x y. \<exists>z. is_glb z {x,y}"

instance dual :: (ord_join_semilattice) ord_meet_semilattice
apply intro_classes
proof (intro allI)
  fix x y :: "'a dual"
  show "\<exists>z. is_glb z {x, y}"
  proof -
    have "\<exists>z. is_lub z (undual ` {x, y})" by (metis image_empty image_insert join_ex)
    hence "\<exists>z. is_glb z (dual ` (undual ` {x, y}))"
      by (metis undual.simps undual_dual_set undual_is_glb)
    thus ?thesis by (metis undual_dual_set undual_is_glb)
  qed
qed

instance dual :: (ord_meet_semilattice) ord_join_semilattice
apply (intro_classes)
proof (intro allI)
  fix x y :: "'a dual"
  show "\<exists>z. is_lub z {x, y}"
  proof -
    have "\<exists>z. is_glb z (undual ` {x, y})" by (metis image_empty image_insert meet_ex)
    hence "\<exists>z. is_lub z (dual ` (undual ` {x, y}))" by (metis dual_is_lub)
    thus ?thesis by (metis dual_undual image_empty image_insert)
  qed
qed

class ord_lattice = ord_join_semilattice + ord_meet_semilattice

instance dual :: (ord_lattice) ord_lattice ..

class complete_join_semilattice = order +
  assumes  lub_ex: "\<forall>A. \<exists>x. is_lub x A"

class complete_lattice = complete_join_semilattice +
  assumes  glb_ex: "\<forall>A. \<exists>x. is_glb x A"

definition univ_cup_junctive :: "('a::order \<Rightarrow> 'b::complete_lattice) set" where
  "univ_cup_junctive f \<equiv> \<forall>X \<subseteq> UNIV. f (\<Sigma> X) = \<Sigma> (f ` X)"

definition pos_cup_junctive :: "('a::order \<Rightarrow> 'b::complete_lattice) set" where
  "pos_cup_junctive f \<equiv> \<forall>X \<subseteq> UNIV. X \<noteq> {} \<longrightarrow> f (\<Sigma> X) = \<Sigma> (f ` X)"

definition cup_junctive :: "('a::order \<Rightarrow> 'b::complete_lattice) set" where
  "cup_junctive f \<equiv> \<forall>X \<subseteq> UNIV. (X \<noteq> {} \<and> finite X) \<longrightarrow> f (\<Sigma> X) = \<Sigma> (f ` X)"

definition univ_cap_junctive :: "('a::order \<Rightarrow> 'b::complete_lattice) set" where
  "univ_cap_junctive f \<equiv> \<forall>X \<subseteq> UNIV. f (\<Pi> X) = \<Pi> (f ` X)"

definition pos_cap_junctive :: "('a::order \<Rightarrow> 'b::complete_lattice) set" where
  "pos_cap_junctive f \<equiv> \<forall>X \<subseteq> UNIV. X \<noteq> {} \<longrightarrow> f (\<Pi> X) = \<Pi> (f ` X)"

definition cap_junctive :: "('a::order \<Rightarrow> 'b::complete_lattice) set" where
  "cap_junctive f \<equiv> \<forall>X \<subseteq> UNIV. (X \<noteq> {} \<and> finite X) \<longrightarrow> f (\<Pi> X) = \<Pi> (f ` X)"

definition order_monomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_monomorphism f \<equiv> \<forall>x y. (f x \<le> f y) = (x \<le> y)"

definition order_isomorphism :: "('a::order \<Rightarrow> 'b::order) set" where
  "order_isomorphism f \<equiv> order_monomorphism f \<and> surj f"

lemma order_monomorphism_inj: "order_monomorphism f \<Longrightarrow> inj f"
  by (simp add: order_monomorphism_def inj_on_def order_eq_iff)

lemma singleton_lub: "\<Sigma> {y} = y"
apply (simp only: lub_def)
apply (rule the_equality)
apply (simp_all add: is_lub_def is_ub_def)
by (metis order_eq_iff)

lemma injective_lub: "surj \<Sigma>"
apply (simp only: surj_def)
proof
  fix y
  show "\<exists>x. y = \<Sigma> x" by (metis singleton_lub)
qed

(* lemma test: assumes a: "surj f" and b: "surj g" shows "f (g X) = g (f ` X)" *)

lemma "\<forall>x. is_ub x {}" by (simp add: is_ub_def)

lemma 
  fixes x y :: nat
  assumes "x \<le> y"
  shows "False" nitpick oops
lemma "\<not> (\<exists>x. is_lub x {})" nitpick oops

lemma "\<exists>x. \<Sigma> {} = x" by (simp add: lub_def is_lub_def is_ub_def All_def)

definition (in order) empty_lub :: 'a where "empty_lub \<equiv> THE x. \<Sigma> {} = x"

lemma empty_lub_uniq: "\<exists>x. (\<Sigma> {} = x) \<and> (x = empty_lub)"
by (simp add: empty_lub_def lub_def is_ub_def is_lub_def)

lemma order_monomorphism_ext_cup_junctive: "order_isomorphism f \<longrightarrow> ext_cup_junctive f"
apply (simp only: order_isomorphism_def)
apply (intro impI)
apply (erule conjE)
apply (simp add: ext_cup_junctive_def)
proof
  fix X
  assume f_mono: "order_monomorphism f" and f_sur: "surj f"
  hence f_inj: "inj f" by (metis order_monomorphism_inj)
  show "(\<exists>x. is_lub x X) \<longrightarrow> f (\<Sigma> X) = \<Sigma> (f ` X)"
  proof (intro impI)
    assume "\<exists>x. is_lub x X"
    thus "f (\<Sigma> X) = \<Sigma> (f ` X)"
    proof (cases "X = {}")
      assume c: "X = {}"
      have "f empty_lub = empty_lub" sorry
      hence "f (\<Sigma> {}) = \<Sigma> (f ` {})" by (metis empty_lub_uniq image_empty)
      thus "f (\<Sigma> X) = \<Sigma> (f ` X)" using c by metis
    next
      assume c: "X \<noteq> {}"
      thus "f (\<Sigma> X) = \<Sigma> (f ` X)"

      apply (simp add: lub_def is_lub_def is_ub_def)
      apply (drule the_equality)

  apply (simp only: lub_def)
  apply (intro impI) sledgehammer [timeout = 300]
  apply (erule exE) sledgehammer [timeout = 300] (mono sur)
  apply (drule the_equality)
  

    assume as: "\<exists>x. is_lub x X"
    apply (erule exE)

sledgehammer [timeout = 300]
  proof
    show "f (\<Sigma> X) = \<Sigma> (f ` X)"
  qed
qed

instance dual :: (complete_lattice) complete_lattice
apply (intro_classes)
proof safe
  fix A :: "'a :: complete_lattice dual set"
  show "\<exists>x. is_lub x A"
  proof -
    have "\<exists>x. is_glb x (undual ` A)" by (metis glb_ex)
    hence "\<exists>x. is_lub x (dual ` (undual ` A))" by (metis dual_is_lub)
    thus ?thesis by (simp add: dual_ex [symmetric] image_compose [symmetric])
  qed
next
  fix A :: "'a :: complete_lattice dual set"
  show "\<exists>x. is_glb x A"
  proof -
    have "\<exists>x. is_lub x (undual ` A)" by (metis lub_ex)
    hence "\<exists>x. is_glb x (dual ` (undual ` A))"
      by (metis undual.simps undual_dual_set undual_is_glb)
    thus ?thesis by (simp add: dual_ex [symmetric] image_compose [symmetric])
  qed
qed

instantiation dual :: (plus) mult_op
begin
  definition mult_dual: "x \<cdot> y \<equiv> dual (undual x + undual y)"
  instance by (intro_classes)
end

instantiation dual :: (mult_op) plus
begin
  definition plus_dual: "x + y \<equiv> dual (undual x \<cdot> undual y)"
  instance by (intro_classes)
end

class alg_join_semilattice = plus +
  assumes join_assoc: "(x+y)+z = x+(y+z)"
  and join_comm: "x+y = y+x"
  and join_idem: "x+x = x"

class alg_meet_semilattice = mult_op +
  assumes meet_assoc: "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
  and meet_comm: "x\<cdot>y = y\<cdot>x"
  and meet_idem: "x\<cdot>x = x"

instance dual :: (alg_join_semilattice) alg_meet_semilattice
proof
  fix x y z :: "'a dual"
  show "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)" by (simp add: mult_dual join_assoc)
  show "x\<cdot>y = y\<cdot>x" by (simp add: mult_dual join_comm)
  show "x\<cdot>x = x" by (simp add: mult_dual join_idem)
qed

instance dual :: (alg_meet_semilattice) alg_join_semilattice
proof
  fix x y z :: "'a dual"
  show "(x+y)+z = x+(y+z)" by (simp add: plus_dual meet_assoc)
  show "x+y = y+x" by (simp add: plus_dual meet_comm)
  show "x+x = x" by (simp add: plus_dual meet_idem)
qed

class alg_lattice = alg_join_semilattice + alg_meet_semilattice +
  assumes absorb1: "x\<cdot>(x+y) = x"
  and absorb2: "x+x\<cdot>y = x"

instance dual :: (alg_lattice) alg_lattice
proof
  fix x y :: "'a dual"
  show "x\<cdot>(x+y) = x" by (simp add: plus_dual mult_dual absorb2)
  show "x+x\<cdot>y = x" by (simp add: plus_dual mult_dual absorb1)
qed

context alg_join_semilattice
begin

definition join_leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
  "join_leq x y \<longleftrightarrow> x+y = y"

definition join_sle :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50) where
  "join_sle x y \<longleftrightarrow> join_leq x y \<and> \<not> join_leq y x"

end

sublocale alg_join_semilattice \<subseteq> order join_leq join_sle
proof
  fix x y z :: 'a
  show "x \<sqsubseteq> x"
    by (metis join_idem join_leq_def)
  show "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
    by (metis join_assoc join_leq_def)
  show "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
    by (metis join_comm join_leq_def)
  show "x \<sqsubset> y = (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)"
    by (metis join_sle_def)
qed

context alg_join_semilattice
begin

lemma join_iso: "x \<sqsubseteq> y \<longrightarrow> x+z \<sqsubseteq> y+z"
  by (metis join_assoc join_comm join_leq_def order_refl)

lemma join_ub: "x \<sqsubseteq> x+y"
by (metis join_assoc join_idem join_leq_def)

lemma join_lub: "x+y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  by (metis join_comm join_iso join_ub join_leq_def)

lemma join_is_join: "is_lub (x+y) {x,y}"
  by (simp add: is_lub_def is_ub_def, metis join_comm join_lub join_ub)

end

sublocale alg_join_semilattice \<subseteq> ord_join_semilattice join_leq join_sle
by unfold_locales (metis join_is_join)

context ord_join_semilattice
begin

lemma join_singleton: "(x::'a) = \<Sigma> {x}"
  by (metis eq_iff insertI1 insert_absorb is_lub_def is_ub_def join_ex lub_is_lub singletonE)

definition bin_lub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "bin_lub x y = \<Sigma> {x,y}"

lemma bin_lub_lub: "(x::'a) \<le> z \<and> y \<le> z \<longleftrightarrow> bin_lub x y \<le> z"
  by (smt bin_lub_def emptyE insertCI insertE is_lub_eqiv join_ex join_singleton lub_is_lub ord_eq_le_trans)

lemma x_le_binlub: "(x::'a) \<le> bin_lub x y"
by (metis bin_lub_def insert_iff is_lub_def is_ub_def join_ex lub_is_lub)

end

(*

sublocale ord_join_semilattice \<subseteq> alg_join_semilattice bin_lub
proof
  fix x y z
  show "bin_lub x x = x"
    by (metis bin_lub_def insert_absorb2 join_singleton)
  show "bin_lub x y = bin_lub y x"
    by (metis bin_lub_def insert_commute)
  show "bin_lub (bin_lub x y) z = bin_lub x (bin_lub y z)"
  proof -
    have "bin_lub (bin_lub x y) z \<le> bin_lub x (bin_lub y z)"
      by (metis bin_lub_lub order_refl)
    also have "bin_lub x (bin_lub y z) \<le> bin_lub (bin_lub x y) z"
      by (metis bin_lub_lub order_refl)
    ultimately show ?thesis by auto
  qed
qed
*)

context complete_join_semilattice
begin

lemma glb_from_lub: "\<Sigma> {(b::'a). \<forall>a\<in>A. b \<le> a} = \<Pi> A"
by (metis lub_ex glb_is_glb is_glb_from_is_lub lub_is_lub)

end

sublocale complete_join_semilattice \<subseteq> complete_lattice
by unfold_locales  (metis lub_ex is_glb_from_is_lub)

end
