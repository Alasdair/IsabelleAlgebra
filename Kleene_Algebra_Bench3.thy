header {* Kleene Algebras *}

theory Kleene_Algebra_Bench
  imports Dioid
begin

declare [[ smt_solver = remote_z3]]

class kleene_algebra = dioid_one_zero + star_op +
  assumes star_unfoldl: "1 + x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_unfoldr: "1 + x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  and star_inductl: "z+x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"
  and star_inductr: "z+y\<cdot>x \<le> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"

begin

lemma star_ref: "1 \<le> x\<^sup>\<star>" by (metis add_lub star_unfoldl)
lemma star_plus_one: "x\<^sup>\<star> = 1+x\<^sup>\<star>" by (metis add_lub leq_def star_unfoldl)
lemma star_trans: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>" by (metis add_lub eq_iff star_inductl star_unfoldl)
lemma star_1l: "x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>" by (metis add_lub star_unfoldl)
lemma star_subid: "x \<le> 1 \<longrightarrow> x\<^sup>\<star> = 1" by (metis add_comm add_lub leq_def mult_oner order_refl star_inductl star_unfoldl)
lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y" by (metis add_comm leq_def eq_iff star_inductl)
lemma star_inductl_eq:  "z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y" by (metis eq_iff star_inductl)
lemma star_inductl_var_eq:  "x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y" by (metis add_idem eq_refl star_inductl)
lemma sum_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x+y \<le> z\<^sup>\<star>" by (metis add_lub)
lemma star_ext: "x \<le> x\<^sup>\<star>" by (metis add_lub leq_def mult_oner star_unfoldl subdistl)
lemma star_1r: "x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>" by (metis add_lub star_unfoldr)
lemma star_slide_var1: "x\<^sup>\<star>\<cdot>x \<le> x\<cdot>x\<^sup>\<star>" by (smt distl leq_def mult_oner star_inductl star_unfoldl)
lemma star_rtc1: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>" by (metis add_lub distl leq_def mult_oner order_refl star_inductr star_unfoldl star_unfoldr)
lemma sup_id_star1: "1 \<le> x \<longrightarrow> x\<cdot>x\<^sup>\<star> = x\<^sup>\<star>" by (metis add_lub antisym mult_onel order_prop star_unfoldl subdistr)
lemma sup_id_star2: "1 \<le> x \<longrightarrow> x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>" by (metis add_lub antisym mult_oner order_prop star_unfoldr subdistl)
lemma star_zero: "0\<^sup>\<star> = 1" by (metis add_zeror annir antisym mult_oner order_refl star_inductl star_unfoldl)
lemma star_inductr_var: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y" by (metis add_lub order_refl star_inductr)
lemma star_inductr_var_eq: "y\<cdot>x = y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y" by (metis add_idem eq_refl star_inductr)

end

end

