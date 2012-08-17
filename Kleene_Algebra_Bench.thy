header {* Kleene Algebras *}

theory Kleene_Algebra_Bench
  imports Dioid
begin

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

class kleene_algebra = dioid_one_zero + star_op +
  assumes star_unfoldl: "1 + x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_unfoldr: "1 + x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  and star_inductl: "z+x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"
  and star_inductr: "z+y\<cdot>x \<le> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"

begin

lemma star_ref: "1 \<le> x\<^sup>\<star>"
  apply (metis add_lub star_unfoldl)
  oops

lemma star_plus_one: "x\<^sup>\<star> = 1+x\<^sup>\<star>"
  apply (metis add_lub leq_def star_unfoldl)
  oops

lemma star_trans: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  apply (metis add_lub eq_iff star_inductl star_unfoldl)
  oops

lemma star_trans_eq: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  apply (metis add_lub distl eq_iff leq_def mult_onel mult_oner star_inductr star_unfoldl star_unfoldr)
  oops

lemma star_1l: "x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  apply (metis add_lub star_unfoldl)
  oops

lemma star_subid: "x \<le> 1 \<longrightarrow> x\<^sup>\<star> = 1"
  apply (metis add_comm add_lub leq_def mult_oner order_refl star_inductl star_unfoldl)
  oops

lemma star_one: "1\<^sup>\<star> = 1"
  apply (metis add_lub antisym mult_onel order_refl star_inductr star_unfoldl)
  oops

lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  apply (metis add_comm leq_def eq_iff star_inductl)
  oops

lemma star_inductl_var_equiv: "x\<cdot>y \<le> y \<longleftrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  apply (smt add_comm add_idem add_iso add_lub add_ub eq_iff le_neq_trans less_le_not_le mult_assoc mult_isor mult_onel star_inductl star_unfoldl the_elem_eq)
  oops

lemma star_invol: "x\<^sup>\<star> = (x\<^sup>\<star>)\<^sup>\<star>"
  apply (metis add_comm add_lub distl leq_def mult_oner star_inductl star_unfoldl)
  oops

lemma star_inductl_eq:  "z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"
  apply (metis eq_iff star_inductl)
  oops


lemma star_inductl_var_eq:  "x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  apply (metis add_idem eq_refl star_inductl)
  oops

lemma star_inductl_var_eq2: "y=x\<cdot>y \<longrightarrow> y=x\<^sup>\<star>\<cdot>y"
  apply (metis add_assoc add_comm add_idem leq_def mult_onel star_inductl star_unfoldl subdistr)
  oops

lemma sum_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x+y \<le> z\<^sup>\<star>"
  apply (metis add_lub)
  oops

lemma prod_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x\<cdot>y \<le> z\<^sup>\<star>"
  apply (metis add_lub mult_double_iso order_refl order_trans star_inductl star_unfoldl)
  oops

lemma star_ext: "x \<le> x\<^sup>\<star>"
  apply (metis add_lub leq_def mult_oner star_unfoldl subdistl)
  oops

lemma star_unfoldr: "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  apply (metis star_unfoldr)
  oops

lemma star_1r: "x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  apply (metis add_lub star_unfoldr)
  oops

lemma star_slide_var1: "x\<^sup>\<star>\<cdot>x \<le> x\<cdot>x\<^sup>\<star>"
  apply (smt distl leq_def mult_oner star_inductl star_unfoldl)
  oops

lemma star_rtc1: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  apply (metis add_lub distl leq_def mult_oner order_refl star_inductr star_unfoldl star_unfoldr)
  oops

lemma star_rtc1_eq: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  apply (metis add_comm add_lub distr leq_def mult_onel star_inductr star_unfoldr)
  oops

lemma star_rtc2_eq: "1+x+y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
  apply (metis add_comm add_lub add_ub distl mult_onel star_inductr)
  oops

lemma star_subdist_var_1: "x \<le> (x+y)\<^sup>\<star>"
  apply (metis add_lub leq_def mult_oner star_unfoldl subdistl)
  oops

lemma confluence_to_local_confluence: "y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> y\<cdot>x \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  apply (metis add_lub mult_double_iso mult_isor mult_onel order_trans star_unfoldr)
  oops

lemma sup_id_star1: "1 \<le> x \<longrightarrow> x\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  apply (metis add_lub antisym mult_onel order_prop star_unfoldl subdistr)
  oops

lemma sup_id_star2: "1 \<le> x \<longrightarrow> x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
  apply (metis add_lub antisym mult_oner order_prop star_unfoldr subdistl)
  oops

lemma star_zero: "0\<^sup>\<star> = 1"
  apply (metis add_zeror annir antisym mult_oner order_refl star_inductl star_unfoldl)
  oops

lemma star_inductr_var: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
  apply (metis add_lub order_refl star_inductr)
  oops

lemma star_inductr_var_equiv: "y\<cdot>x \<le> y \<longleftrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
  apply (metis add_lub mult_isol mult_oner order_refl order_trans star_inductr star_unfoldl)
  oops

lemma star_inductr_eq: "z+y\<cdot> x= y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"
  apply (metis eq_iff star_inductr)
  oops

lemma star_inductr_var_eq: "y\<cdot>x = y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
  apply (metis add_idem eq_refl star_inductr)
  oops

lemma star_inductr_var_eq2: "y\<cdot>x = y \<longrightarrow> y\<cdot>x\<^sup>\<star> = y"
  apply (metis add_comm add_idem add_lub distl leq_def mult_oner star_inductr star_unfoldl)
  oops

lemma independence1: "x\<cdot>y = 0 \<longrightarrow> x\<^sup>\<star>\<cdot>y = y"
  apply (metis add_lub add_zerol eq_iff mult_isor mult_onel star_inductl star_unfoldl)
  oops

lemma independence2: "x\<cdot>y = 0 \<longrightarrow> x\<cdot>y\<^sup>\<star> = x"
  apply (metis add_comm add_lub add_zerol eq_iff mult_isol mult_oner star_inductr star_unfoldl)
  oops

lemma arden: "\<forall> x z w.(\<forall>y v.(y \<le> x\<cdot>y+v \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>v)) \<longrightarrow> (z = x\<cdot>z+w \<longrightarrow> z = x\<^sup>\<star>\<cdot>w)"
  apply (metis add_comm eq_iff star_inductl)
  oops

lemma unnamed: "(\<forall> x y.(y \<le> x\<cdot>y \<longrightarrow> y = 0)) \<longrightarrow> (\<forall> x y z. (y \<le> x\<cdot>y+z \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>z))"
  apply (metis eq_refl mult_onel)
  oops


lemma star_slide_l: "(x\<cdot>y)\<^sup>\<star>\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  apply (smt distl mult_assoc mult_oner order_prop star_inductl star_unfoldl subdistl)
  oops
(* Cannot prove right *)

lemma star_slide_var: "x\<^sup>\<star>\<cdot>x \<le> x\<cdot>x\<^sup>\<star>"
  apply (smt distl leq_def mult_oner star_inductl star_unfoldl)
  oops

lemma troeger: "x\<^sup>\<star>\<cdot>(y\<cdot>((x+y)\<^sup>\<star>\<cdot>z)+z) \<le> (x+y)\<^sup>\<star>\<cdot>z"
  apply (smt add_assoc add_comm distr leq_def mult_assoc mult_onel mult_oner star_inductl star_unfoldl subdistr)
  oops

lemma sum_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x+y \<le> z\<^sup>\<star>"
  apply (metis add_lub)
  oops

lemma star_star_closure: "x\<^sup>\<star> \<le> z\<^sup>\<star> \<longrightarrow> (x\<^sup>\<star>)\<^sup>\<star> \<le> z\<^sup>\<star>"
  apply (metis add_assoc add_lub mult_oner star_inductl star_inductr star_unfoldr)
  oops

lemma star2: "(1+x)\<^sup>\<star> \<le> x\<^sup>\<star>"
  apply (smt add_assoc add_comm distl leq_def mult_onel mult_oner star_inductr star_unfoldr)
  oops

lemma star_invol: "x\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
  apply (metis add_lub leq_def mult_oner star_unfoldl subdistl)
  oops

lemma star_left_preserves: "(x\<cdot>y \<le> y) \<longrightarrow> (x\<^sup>\<star>\<cdot>y \<le> y)"
  apply (metis add_comm eq_iff leq_def star_inductl)
  oops

lemma star_right_preserves: "(y\<cdot>x \<le> y) \<longrightarrow> (y\<cdot>x\<^sup>\<star> \<le> y)"
  apply (metis add_comm eq_refl leq_def star_inductr)
  oops

lemma star_mon: "(x \<le> y) \<longrightarrow> (x\<^sup>\<star> \<le> y\<^sup>\<star>)"
  by (smt add_lub leq_def mult_oner star_inductl star_unfoldl subdistr)


end

end

