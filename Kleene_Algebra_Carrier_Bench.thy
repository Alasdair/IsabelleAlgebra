theory Kleene_Algebra_Carrier_Bench
  imports "~~/src/HOL/Algebra/Lattice" Dioid_Carrier
begin

declare [[ smt_solver = remote_z3 ]]

record 'a kleene_algebra = "'a dioid" +
  star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>\<index>" [101] 100)

locale kleene_algebra = dioid K for K (structure) +
  assumes star_closed: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star> \<in> carrier K"
  and star_unfoldl: "x \<in> carrier K \<Longrightarrow> \<one> \<oplus> x\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  and star_unfoldr: "x \<in> carrier K \<Longrightarrow> \<one> \<oplus> x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<^sup>\<star>"
  and star_inductl: "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> z\<oplus>x\<otimes>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star>\<otimes>z \<sqsubseteq> y"
  and star_inductr: "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> z\<oplus>y\<otimes>x \<sqsubseteq> y \<longrightarrow> z\<otimes>x\<^sup>\<star> \<sqsubseteq> y"

begin

lemma star_ref: "x \<in> carrier K \<Longrightarrow> \<one> \<sqsubseteq> x\<^sup>\<star>" by (metis add_lub mult_closed one_closed star_closed star_unfoldl)
lemma star_plus_one: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star> = \<one>\<oplus>x\<^sup>\<star>" by (metis add_lub leq_def star_unfoldl one_closed star_closed mult_closed)
lemma star_trans: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>" by (metis add_lub le_refl mult_closed one_closed star_closed star_inductl star_unfoldl)
lemma star_1l: "x \<in> carrier K \<Longrightarrow> x\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>" by (metis add_lub mult_closed one_closed star_closed star_unfoldl)
lemma star_subid: "x \<in> carrier K \<Longrightarrow> x \<sqsubseteq> \<one> \<longrightarrow> x\<^sup>\<star> = \<one>" by (metis add_comm add_lub leq_def mult_closed mult_onel one_closed star_closed star_inductr star_unfoldl subdistl)
lemma star_inductl_var: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> x\<otimes>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star>\<otimes>y \<sqsubseteq> y" by (metis add_lub le_refl mult_closed star_inductl)
lemma star_inductl_eq:  "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> z\<oplus>x\<otimes>y = y \<longrightarrow> x\<^sup>\<star>\<otimes>z \<sqsubseteq> y" by (metis le_refl star_inductl)
lemma star_inductl_var_eq:  "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> x\<otimes>y = y \<longrightarrow> x\<^sup>\<star>\<otimes>y \<sqsubseteq> y" by (metis idem le_refl star_inductl)
lemma sum_star_closure: "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z\<^sup>\<star> \<and> y \<sqsubseteq> z\<^sup>\<star> \<longrightarrow> x\<oplus>y \<sqsubseteq> z\<^sup>\<star>" by (metis add_lub star_closed)
lemma star_ext: "x \<in> carrier K \<Longrightarrow> x \<sqsubseteq> x\<^sup>\<star>" by (metis (no_types) add_lub le_trans leq_def mult_closed mult_oner one_closed star_closed star_unfoldl subdistl)
lemma star_1r: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<^sup>\<star>" by (metis add_lub mult_closed one_closed star_closed star_unfoldr)
lemma star_slide_var1: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<otimes>x\<^sup>\<star>" by (smt add_closed distl leq_def mult_closed mult_oner one_closed star_closed star_inductl star_unfoldl)
lemma star_rtc1: "x \<in> carrier K \<Longrightarrow> \<one>\<oplus>x\<oplus>x\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>" by (metis (no_types) add_closed add_lub leq_def mult_closed mult_oner one_closed star_closed star_inductl star_unfoldl subdistl)
lemma sup_id_star1: "x \<in> carrier K \<Longrightarrow> \<one> \<sqsubseteq> x \<longrightarrow> x\<otimes>x\<^sup>\<star> = x\<^sup>\<star>" by (metis (no_types) add_comm add_lub leq_def mult_closed mult_isor mult_onel one_closed star_closed star_unfoldl)
lemma sup_id_star2: "x \<in> carrier K \<Longrightarrow> \<one> \<sqsubseteq> x \<longrightarrow> x\<^sup>\<star>\<otimes>x = x\<^sup>\<star>" by (metis add_comm add_lub distl leq_def mult_closed mult_oner one_closed star_closed star_unfoldr)
lemma star_zero: "\<zero>\<^sup>\<star> = \<one>" by (metis add_comm add_zeror annir leq_def mult_assoc mult_closed mult_onel one_closed star_closed star_inductr star_unfoldl subdistl zero_closed)
lemma star_inductr_var: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> y\<otimes>x \<sqsubseteq> y \<longrightarrow> y\<otimes>x\<^sup>\<star> \<sqsubseteq> y" by (metis add_lub le_refl mult_closed star_inductr)
lemma star_inductr_var_eq: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> y\<otimes>x = y \<longrightarrow> y\<otimes>x\<^sup>\<star> \<sqsubseteq> y" by (metis idem le_refl star_inductr)

end

end
