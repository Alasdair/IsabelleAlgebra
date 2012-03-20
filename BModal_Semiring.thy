header {* Backward Modal Semirings *}

theory BModal_Semiring
  imports FModal_Semiring Range_Semiring
begin

context antirange_semiring 
begin

section{* Backward Diamond *}

definition bdiamond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("( \<langle> _ \<bar> _)" 90)
  where  "(\<langle>x\<bar>y)  =  r(y\<cdot>x)" 

lemma bdia_ran: "r(x) =\<langle>x\<bar>1"
  by (metis dual.fdia_dom bdiamond_def dual.fdiamond_def opp_mult_def)

lemma bdia_add1: "\<langle>x\<bar>(y+z) = (\<langle>x\<bar>y)+(\<langle>x\<bar>z)"
  by (metis dual.fdia_add1 bdiamond_def dual.fdiamond_def opp_mult_def)

lemma bdia_add2: "\<langle>x+y\<bar>z = (\<langle>x\<bar>z)+(\<langle>y\<bar>z)"
  by (metis dual.fdia_add2 bdiamond_def dual.fdiamond_def opp_mult_def)

lemma bdia_mult: "\<langle>x\<cdot>y\<bar>z = \<langle>y\<bar>(\<langle>x\<bar>z)"
  by (metis dual.fdia_mult bdiamond_def dual.fdiamond_def opp_mult_def)

lemma rdia_one: "\<langle>1\<bar>x = r(x)"
  by (metis dual.fdia_one bdiamond_def dual.fdiamond_def opp_mult_def)

lemma rdia_zero: "\<langle>x\<bar>0 = 0"
  by (metis dual.fdia_zero bdiamond_def dual.fdiamond_def opp_mult_def)

lemma rdemodalisation1: "(\<langle>x\<bar>y)\<cdot>r(z) = 0 \<longleftrightarrow> r(y)\<cdot>(x\<cdot>r(z)) = 0"
  by (metis dual.fdemodalisation1 bdiamond_def dual.fdiamond_def opp_mult_def)

lemma rdemodalisation2: "\<langle>x\<bar>y \<le> r(z) \<longleftrightarrow> r(y)\<cdot>(x\<cdot>ar(z)) = 0"
  by (metis dual.fdemodalisation2 bdiamond_def dual.fdiamond_def opp_mult_def)

lemma rdemodalisation_aux: "r(z)\<cdot>(x\<cdot>ar(y)) = 0 \<longleftrightarrow> r(z)\<cdot>x \<le> x\<cdot>r(y)"
 by (metis dual.fdemodalisation_aux bdiamond_def dual.fdiamond_def opp_mult_def)

lemma rdemodalisation_aux_2: "r(z)\<cdot>(x\<cdot>ar(y)) = 0 \<longleftrightarrow> x\<cdot>ar(y) \<le> ar(z)\<cdot>x"
 by (metis dual.fdemodalisation_aux_2 bdiamond_def dual.fdiamond_def opp_mult_def)

lemma rdemodalisation3: "\<langle>x\<bar>y \<le> r(z) \<longleftrightarrow> r(y)\<cdot>x \<le> x\<cdot>r(z)"
 by (metis dual.fdemodalisation3 bdiamond_def dual.fdiamond_def opp_mult_def)

lemma rdia_iso: "r(x) \<le> r(y) \<longrightarrow> \<langle>z\<bar>x \<le> \<langle>z\<bar>y"
 by (metis dual.fdia_iso bdiamond_def dual.fdiamond_def opp_mult_def)

lemma bdia_zero_var: "\<langle>0\<bar>x = 0"
 by (metis dual.fdia_zero_var bdiamond_def dual.fdiamond_def opp_mult_def)

section {* Backward Box *}

definition 
  bbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("( [  _ \<bar> _)" 90)
  where  "([x\<bar>y) = ar(ar(y)\<cdot>x)"

lemma bbox_bdia: "[x\<bar>y = ar(\<langle>x\<bar>ar(y))"
 by (metis dual.fbox_fdia bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bdia_bbox: "\<langle>x\<bar>y = ar([x\<bar>ar(y))"
 by (metis dual.fdia_fbox bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_ran: "ar(x) =[x\<bar>0"
 by (metis dual.fbox_dom bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_add1: "[x\<bar>(r(y)\<cdot>r(z)) = ([x\<bar>y)\<cdot>([x\<bar>z)"
 by (metis dual.fbox_add1 bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_add2: "[x+y\<bar>z = ([y\<bar>z)\<cdot>([x\<bar>z)"
 by (metis dual.fbox_add2 bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_mult: "[x\<cdot>y\<bar>z = [y\<bar>([x\<bar>z)"
 by (metis dual.fbox_mult bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_one: "[1\<bar>x = r(x)"
 by (metis dual.fbox_one bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_one_1: "[x\<bar>1 = 1"
 by (metis dual.fbox_one_1 bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_demodalisation3: "r(y) \<le> [x\<bar>r(z) \<longleftrightarrow> x\<cdot>r(y) \<le> r(z)\<cdot>x"
 by (metis dual.fbox_demodalisation3 bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_iso: "r(x) \<le> r(y) \<longrightarrow> [z\<bar>x \<le> [z\<bar>y"
 by (metis dual.fbox_iso bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)

lemma bbox_zero_var: "[0\<bar>x = 1"
 by (metis dual.fbox_zero_var bdiamond_def bbox_def dual.fdiamond_def dual.fbox_def opp_mult_def)
  
end

class antirange_kleene_algebra = antirange_semiring + kleene_algebra

sublocale antirange_kleene_algebra \<subseteq> dual!: antidomain_kleene_algebra
"op +" "op \<le>" "op <" "op \<odot>" "(1\<Colon>'a)" "(0\<Colon>'a)" "ar" "r" "star"
proof
  fix x y z :: 'a
  show  "(1\<Colon>'a) + (1\<Colon>'a) = (1\<Colon>'a)"
    by (metis dual.idem)
  show "(1\<Colon>'a) + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis opp_mult_def order_refl star_unfoldr_eq)
  show  "z + x \<odot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<odot> z \<le> y"
    by (metis opp_mult_def star_inductr)
  show  "z + y \<odot> x \<le> y \<longrightarrow> z \<odot> x\<^sup>\<star> \<le> y"
    by (metis opp_mult_def star_inductl)
qed

context antirange_kleene_algebra
begin

lemma brange_star: "r(x\<^sup>\<star>) = 1"
  by (metis dual.fdom_star opp_mult_def)

lemma bdia_star_unfold: "(\<langle>1\<bar>z)+(\<langle>x\<bar>(\<langle>x\<^sup>\<star>\<bar>z)) = \<langle>x\<^sup>\<star>\<bar>z"
 by (metis dual.fdia_star_unfold bdiamond_def bdia_mult dual.fdiamond_def opp_mult_def)

lemma bdia_star_unfold_var: "r(z)+(\<langle>x\<bar>(\<langle>x\<^sup>\<star>\<bar>z)) = \<langle>x\<^sup>\<star>\<bar>z"
 by (metis dual.fdia_star_unfold_var bdiamond_def bdia_mult dual.fdiamond_def opp_mult_def)

lemma bdia_star_induct_var: "\<langle>x\<bar>r(y) \<le> r(y) \<longrightarrow> \<langle>x\<^sup>\<star>\<bar>r(y) \<le> r(y)"
 by (metis dual.fdia_star_induct_var bdiamond_def bdia_mult dual.fdiamond_def opp_mult_def)

lemma bdia_star_induct: "r(z)+(\<langle>x\<bar>r(y)) \<le> r(y) \<longrightarrow> \<langle>x\<^sup>\<star>\<bar>r(z) \<le> r(y)"
 by (metis dual.fdia_star_induct bdiamond_def bdia_mult dual.fdiamond_def opp_mult_def)

lemma bsegerberg: "(\<langle>x\<^sup>\<star>\<bar>r(y)) \<le> r(y)+\<langle>x\<^sup>\<star>\<bar>(ar(y)\<cdot>(\<langle>x\<bar>r(y)))"
 by (metis dual.fsegerberg bdiamond_def bdia_mult dual.fdiamond_def opp_mult_def)

end

text {* Hence all range theorems have been derived by duality in a generic way *}

text {* The next step would be to exploit De Morgan duality *}

end

