theory Kleene_Algebra_Carrier
  imports "~~/src/HOL/Algebra/Lattice"
begin

declare [[ smt_solver = remote_z3 ]]

record 'a dioid = "'a gorder" +
  plus :: "['a , 'a]  \<Rightarrow> 'a" (infixl "\<oplus>\<index>" 70)
  mult :: "['a , 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 80)
  one  :: "'a" ("\<one>\<index>")
  zero :: "'a" ("\<zero>\<index>")

locale dioid = weak_partial_order D for D (structure) +
  assumes leq_def: "\<lbrakk>x\<in>carrier D; y\<in>carrier D\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y \<longleftrightarrow> x\<oplus>y=y)"
  and add_closed: "\<lbrakk> x\<in>carrier D; y\<in>carrier D\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<in>carrier D"
  and mult_closed: "\<lbrakk> x\<in>carrier D; y\<in>carrier D\<rbrakk> \<Longrightarrow> (x\<otimes>y)\<in>carrier D"
  and one_closed: "\<one>\<in>carrier D"
  and zero_closed: "\<zero>\<in>carrier D"
  and mult_assoc: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x\<otimes>(y\<otimes>z) = (x\<otimes>y)\<otimes>z"
  assumes add_assoc: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x\<oplus>(y\<oplus>z) = (x\<oplus>y)\<oplus>z"
  and add_comm: "\<lbrakk>x\<in>carrier D; y\<in>carrier D\<rbrakk> \<Longrightarrow> x\<oplus>y = y\<oplus>x"
  and idem: "x\<in>carrier D \<Longrightarrow> x\<oplus>x = x"
  and distl: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x\<otimes>(y\<oplus>z) = (x\<otimes>y)\<oplus>(x\<otimes>z)"
  and distr: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<otimes>z = (x\<otimes>z)\<oplus>(y\<otimes>z)"
  and mult_onel: "x\<in>carrier D \<Longrightarrow> \<one>\<otimes>x = x"
  and mult_oner: "x\<in>carrier D \<Longrightarrow> x\<otimes>\<one> = x"
  and add_zerol: "x\<in>carrier D \<Longrightarrow> \<zero>\<oplus>x = x"
  and annir: "x\<in>carrier D \<Longrightarrow> \<zero>\<otimes>x = \<zero>"
  and annil: "x\<in>carrier D \<Longrightarrow> x\<otimes>\<zero> = \<zero>"

context dioid
begin

lemma order_prop: "\<lbrakk> x \<in> carrier D ; y \<in> carrier D \<rbrakk> \<Longrightarrow> (\<forall>z\<in>carrier D.((x \<sqsubseteq> z) \<longleftrightarrow> (y \<sqsubseteq> z))) \<longrightarrow> x = y"
  by (metis add_comm le_refl leq_def)

lemma add_zeror: "x\<in>carrier D \<Longrightarrow> x\<oplus>\<zero> = x"
  by (metis add_comm add_zerol zero_closed)

lemma add_lub: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z  \<longleftrightarrow> x\<oplus>y \<sqsubseteq> z"
  by (metis (no_types) add_assoc add_closed add_comm idem leq_def)

lemma add_iso: "\<lbrakk>x\<in>carrier D;y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> z\<oplus>x \<sqsubseteq> z\<oplus>y"
  by (metis add_closed add_comm add_lub idem leq_def)

lemma mult_isol: "\<lbrakk>x\<in>carrier D;y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> z\<otimes>x \<sqsubseteq> z\<otimes>y"
  by (metis (no_types) distl leq_def mult_closed)

lemma mult_isor: "\<lbrakk>x\<in>carrier D;y\<in>carrier D;z\<in>carrier D\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> x\<otimes>z \<sqsubseteq> y\<otimes>z"
by (metis (no_types) distr leq_def mult_closed)

lemma mult_double_iso: "\<lbrakk>w\<in>carrier D; x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> w \<sqsubseteq> x \<and> y \<sqsubseteq> z \<longrightarrow> w\<otimes>y \<sqsubseteq> x\<otimes>z"
  by (smt add_assoc distl distr idem leq_def mult_closed)

lemma subdistl: "\<lbrakk>x\<in> carrier D; y\<in>carrier D;z\<in>carrier D\<rbrakk> \<Longrightarrow> z\<otimes>x \<sqsubseteq> z\<otimes>(x\<oplus>y)"
  by (metis add_assoc add_closed idem leq_def mult_double_iso)

end

record 'a kleene_algebra = "'a dioid" +
  star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>\<index>" [101] 100)

locale kleene_algebra = dioid K for K (structure) +
  assumes star_closed: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star> \<in> carrier K"
  and star_unfoldl: "x \<in> carrier K \<Longrightarrow> \<one> \<oplus> x\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  and star_unfoldr: "x \<in> carrier K \<Longrightarrow> \<one> \<oplus> x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<^sup>\<star>"
  and star_inductl: "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> z\<oplus>x\<otimes>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star>\<otimes>z \<sqsubseteq> y"
  and star_inductr: "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> z\<oplus>y\<otimes>x \<sqsubseteq> y \<longrightarrow> z\<otimes>x\<^sup>\<star> \<sqsubseteq> y"

begin

lemma star_ref: "x \<in> carrier K \<Longrightarrow> \<one> \<sqsubseteq> x\<^sup>\<star>"
   by (metis add_lub mult_closed one_closed star_closed star_unfoldl)

lemma star_plus_one: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star> = \<one>\<oplus>x\<^sup>\<star>"
  by (metis add_lub leq_def star_unfoldl one_closed star_closed mult_closed)

lemma star_trans: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  by (metis add_lub le_refl mult_closed one_closed star_closed star_inductl star_unfoldl)

lemma star_trans_eq: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star>\<otimes>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis add_comm distl leq_def mult_closed mult_oner one_closed star_closed star_plus_one star_trans)

lemma star_1l: "x \<in> carrier K \<Longrightarrow> x\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  by (metis add_lub mult_closed one_closed star_closed star_unfoldl)

lemma star_subid: "x \<in> carrier K \<Longrightarrow> x \<sqsubseteq> \<one> \<longrightarrow> x\<^sup>\<star> = \<one>"
  by (metis add_comm le_refl leq_def mult_onel one_closed star_closed star_inductr star_plus_one)

lemma star_one: "\<one>\<^sup>\<star> = \<one>"
  by (metis le_refl one_closed star_subid)

lemma star_inductl_var: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> x\<otimes>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star>\<otimes>y \<sqsubseteq> y"
  by (metis add_lub le_refl mult_closed star_inductl)

lemma star_inductl_var_equiv: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> x\<otimes>y \<sqsubseteq> y \<longleftrightarrow> x\<^sup>\<star>\<otimes>y \<sqsubseteq> y"
  by (metis (no_types) le_trans mult_closed mult_isor mult_oner one_closed star_1l star_closed star_inductl_var star_plus_one subdistl)

lemma star_invol: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star> = (x\<^sup>\<star>)\<^sup>\<star>"
sorry

lemma star_inductl_eq:  "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> z\<oplus>x\<otimes>y = y \<longrightarrow> x\<^sup>\<star>\<otimes>z \<sqsubseteq> y"
by (metis le_refl star_inductl)

lemma star_inductl_var_eq:  "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> x\<otimes>y = y \<longrightarrow> x\<^sup>\<star>\<otimes>y \<sqsubseteq> y"
  by (metis idem star_inductl_eq)

lemma star_inductl_var_eq2: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> y=x\<otimes>y \<longrightarrow> y=x\<^sup>\<star>\<otimes>y"
(*
  by (metis add_comm distr le_trans leq_def mult_closed mult_oner one_closed star_1l star_closed star_inductl_var_eq star_plus_one subdistl)
*)
sorry

lemma sum_star_closure: "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z\<^sup>\<star> \<and> y \<sqsubseteq> z\<^sup>\<star> \<longrightarrow> x\<oplus>y \<sqsubseteq> z\<^sup>\<star>"
  by (metis add_lub star_closed)

lemma prod_star_closure: "\<lbrakk> x \<in> carrier K; y \<in> carrier K; z \<in> carrier K \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z\<^sup>\<star> \<and> y \<sqsubseteq> z\<^sup>\<star> \<longrightarrow> x\<otimes>y \<sqsubseteq> z\<^sup>\<star>"
  by (metis mult_double_iso star_closed star_trans_eq)

lemma star_ext: "x \<in> carrier K \<Longrightarrow> x \<sqsubseteq> x\<^sup>\<star>"
by (metis add_lub distl mult_closed mult_oner one_closed star_1l star_closed star_plus_one)


lemma star_1r: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<^sup>\<star>"
by (metis le_refl prod_star_closure star_closed star_ext)

lemma star_slide_var1: "x \<in> carrier K \<Longrightarrow> x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<otimes>x\<^sup>\<star>"
by (metis add_lub mult_closed mult_isol mult_oner one_closed star_1l star_closed star_inductl star_ref)

lemma star_rtc1: "x \<in> carrier K \<Longrightarrow> \<one>\<oplus>x\<oplus>x\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
by (metis add_closed mult_closed one_closed star_closed star_ext star_ref star_trans sum_star_closure)

lemma star_rtc1_eq: "x \<in> carrier K \<Longrightarrow> \<one>\<oplus>x\<oplus>x\<^sup>\<star>\<otimes>x\<^sup>\<star> = x\<^sup>\<star>"
by (metis add_assoc leq_def one_closed star_closed star_ext star_plus_one star_trans_eq)

lemma star_rtc2_eq: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> \<one>\<oplus>x\<oplus>y\<otimes>y = y \<longrightarrow> x\<^sup>\<star> \<sqsubseteq> y"
sorry

lemma star_subdist_var_1: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> x \<sqsubseteq> (x\<oplus>y)\<^sup>\<star>"
  by (metis add_closed add_lub star_closed star_ext)

lemma confluence_to_local_confluence: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> y\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>\<otimes>y\<^sup>\<star> \<longrightarrow> y\<otimes>x \<sqsubseteq> x\<^sup>\<star>\<otimes>y\<^sup>\<star>"
(* by (metis le_trans mult_closed mult_double_iso star_closed star_ext) *)
sorry

lemma sup_id_star1: "x \<in> carrier K \<Longrightarrow> \<one> \<sqsubseteq> x \<longrightarrow> x\<otimes>x\<^sup>\<star> = x\<^sup>\<star>"
by (metis (no_types) add_comm distr leq_def mult_closed mult_onel one_closed star_1l star_closed)

lemma sup_id_star2: "x \<in> carrier K \<Longrightarrow> \<one> \<sqsubseteq> x \<longrightarrow> x\<^sup>\<star>\<otimes>x = x\<^sup>\<star>"
sorry

lemma star_zero: "\<zero>\<^sup>\<star> = \<one>"
by (metis add_zerol leq_def one_closed star_subid zero_closed)

lemma star_inductr_var: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> y\<otimes>x \<sqsubseteq> y \<longrightarrow> y\<otimes>x\<^sup>\<star> \<sqsubseteq> y"
by (metis add_lub le_refl mult_closed star_inductr)

lemma star_inductr_var_equiv: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> y\<otimes>x \<sqsubseteq> y \<longleftrightarrow> y\<otimes>x\<^sup>\<star> \<sqsubseteq> y"
by (metis (no_types) le_trans mult_closed mult_isol star_closed star_ext star_inductr_var)

lemma star_inductr_eq: "z\<oplus>y\<otimes> x= y \<longrightarrow> z\<otimes>x\<^sup>\<star> \<sqsubseteq> y"
  by (metis eq_iff star_inductr)

lemma star_inductr_var_eq: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> y\<otimes>x = y \<longrightarrow> y\<otimes>x\<^sup>\<star> \<sqsubseteq> y"
  by (metis add_idem eq_refl star_inductr)

lemma star_inductr_var_eq2: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> y\<otimes>x = y \<longrightarrow> y\<otimes>x\<^sup>\<star> = y"
  by (metis add_comm add_idem add_lub distl leq_def mult_oner star_inductr star_unfoldl)

lemma independence1: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> x\<otimes>y = \<zero> \<longrightarrow> x\<^sup>\<star>\<otimes>y = y"
  by (metis add_lub add_zerol eq_iff mult_isor mult_onel star_inductl star_unfoldl)

lemma independence2: "\<lbrakk> x \<in> carrier K; y \<in> carrier K \<rbrakk> \<Longrightarrow> x\<otimes>y = \<zero> \<longrightarrow> x\<otimes>y\<^sup>\<star> = x"
  by (metis add_comm add_lub add_zerol eq_iff mult_isol mult_oner star_inductr star_unfoldl)

lemma arden: "\<forall> x z w.(\<forall>y v.(y \<sqsubseteq> x\<otimes>y\<oplus>v \<longrightarrow> y \<sqsubseteq> x\<^sup>\<star>\<otimes>v)) \<longrightarrow> (z = x\<otimes>z\<oplus>w \<longrightarrow> z = x\<^sup>\<star>\<otimes>w)"
  by (metis add_comm eq_iff star_inductl)

lemma "(\<forall> x y.(y \<sqsubseteq> x\<otimes>y \<longrightarrow> y = \<zero>)) \<longrightarrow> (\<forall> x y z. (y \<sqsubseteq> x\<otimes>y\<oplus>z \<longrightarrow> y \<sqsubseteq> x\<^sup>\<star>\<otimes>z))"
  by (metis eq_refl mult_onel)

end

end
