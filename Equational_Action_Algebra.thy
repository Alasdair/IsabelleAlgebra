theory Equational_Action_Algebra
  imports Dioid
begin

declare [[ smt_solver = remote_z3 ]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

class equational_action_algebra = dioid_one_zero + star_op + postimp_op + preimp_op +
  assumes right_addition: "x \<rightarrow> y \<le> x \<rightarrow> (y + y')"
  and right_galois_counit: "x\<cdot>(x \<rightarrow> y) \<le> y"
  and right_galois_unit: "y \<le> x \<rightarrow> x\<cdot>y"
  and left_addition: "y \<leftarrow> x \<le> (y + y') \<leftarrow> x"
  and left_galois_counit: "(y \<leftarrow> x)\<cdot>x \<le> y"
  and left_galois_unit: "y \<le> y\<cdot>x \<leftarrow> x"
  and star_ax: "1 + x\<^sup>\<star>\<cdot>x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
  and star_subdist: "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  and right_pure_induction: "(x \<rightarrow> x)\<^sup>\<star> \<le> x \<rightarrow> x"
  and left_pure_induction: "(x \<leftarrow> x)\<^sup>\<star> \<le> x \<leftarrow> x"

begin

lemma star_ref: "1 \<le> x\<^sup>\<star>"
  apply (metis add_lub star_ax)
  oops

lemma star_plus_one: "x\<^sup>\<star> = 1+x\<^sup>\<star>"
  apply (metis add_lub leq_def star_ax)
  oops

lemma star_trans: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  apply (metis add_lub star_ax)
  oops

lemma star_trans_eq: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  apply (smt add_comm add_lub distl leq_def mult_oner star_ax)
  oops

lemma star_subid: "x \<le> 1 \<longrightarrow> x\<^sup>\<star> = 1"
  apply (metis add_lub eq_iff left_galois_counit left_galois_unit left_pure_induction leq_def mult_oner star_ax star_subdist)
  oops

lemma star_one: "1\<^sup>\<star> = 1"
  apply (metis add_lub eq_iff left_galois_counit left_pure_induction mult_oner star_ax)
  oops

lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  apply (metis add_comm add_lub distr left_galois_counit left_galois_unit left_pure_induction leq_def mult_isor mult_onel order_trans star_subdist)
  oops

lemma star_iso: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  apply (metis leq_def star_subdist)
  oops

lemma star_inductl_var_eq:  "x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  apply (metis left_galois_counit left_galois_unit left_pure_induction leq_def order_trans star_subdist subdistr)
  oops

lemma sum_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x+y \<le> z\<^sup>\<star>"
  apply (metis add_lub)
  oops

lemma star_ext: "x \<le> x\<^sup>\<star>"
  apply (metis add_lub star_ax)
  oops

lemma star_unfoldr: "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  apply (smt add_lub iso_subdist mult_isol order_prop order_trans star_ax)
  oops

lemma star_rtc1: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  apply (metis add_lub star_ax)
  oops

lemma star_rtc1_eq: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  apply (smt add_assoc add_comm add_idem distl leq_def mult_oner order_refl star_ax)
  oops

lemma star_rtc2_eq: "1+x+y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
  apply (metis add_assoc add_lub eq_iff left_galois_counit left_galois_unit left_pure_induction leq_def mult_oner order_trans star_subdist subdistl)
  oops

lemma star_subdist_var_1: "x \<le> (x+y)\<^sup>\<star>"
  apply (metis add_lub star_ax)
  oops

lemma star_subdist_var_3: "x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<le> (x+y)\<^sup>\<star>"
  apply (smt add_comm add_lub distl leq_def mult_double_iso mult_oner star_ax star_subdist)
  oops

lemma confluence_to_local_confluence: "y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> y\<cdot>x \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  apply (metis add_lub mult_double_iso order_trans star_ax)
  oops

lemma star_zero: "0\<^sup>\<star> = 1"
  apply (metis add_lub add_zerol eq_iff left_galois_counit left_pure_induction mult_oner star_ax star_subdist)
  oops

lemma star_inductr_var_eq: "y\<cdot>x = y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
  apply (metis leq_def mult_isol order_trans right_galois_counit right_galois_unit right_pure_induction star_subdist)
  oops

lemma star_inductr_var_eq2: "y\<cdot>x = y \<longrightarrow> y\<cdot>x\<^sup>\<star> = y"
  apply (metis add_assoc add_idem distl eq_iff leq_def mult_isol mult_oner right_galois_counit right_galois_unit right_pure_induction star_ax star_subdist subdistl)
  oops

lemma unnamed: "(\<forall> x y.(y \<le> x\<cdot>y \<longrightarrow> y = 0)) \<longrightarrow> (\<forall> x y z. (y \<le> x\<cdot>y+z \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>z))"
  apply (metis eq_refl mult_onel)
  oops

lemma sum_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x+y \<le> z\<^sup>\<star>"
  apply (metis add_lub)
  oops

lemma star_invol: "x\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
  apply (metis add_lub star_ax)
  oops

lemma star_left_preserves: "(x\<cdot>y \<le> y) \<longrightarrow> (x\<^sup>\<star>\<cdot>y \<le> y)"
  apply (metis add_comm distr left_galois_counit left_galois_unit left_pure_induction leq_def mult_onel order_trans star_subdist)
  oops

lemma star_right_preserves: "(y\<cdot>x \<le> y) \<longrightarrow> (y\<cdot>x\<^sup>\<star> \<le> y)"
  apply (metis distl leq_def mult_oner order_trans right_galois_counit right_galois_unit right_pure_induction star_subdist)
  oops

lemma star_mon: "(x \<le> y) \<longrightarrow> (x\<^sup>\<star> \<le> y\<^sup>\<star>)"
  apply (metis leq_def star_subdist)
  oops

end

end
