header {* Range Semirings *}

theory Range_Semiring
  imports Domain_Semiring
begin

section {* Range Semirings  *}

class range_op =
  fixes r :: "'a \<Rightarrow> 'a"

class range_semiring = semiring_one_zero + plus_ord + range_op +
  assumes r1: "x+(x\<cdot>r(x)) = x\<cdot>r(x)"
  and r2: "r(x\<cdot>y) = r(r(x)\<cdot>y)"
  and r3: "r(x)+1 = 1"
  and r4: "r(0) = 0"
  and r5: "r(x+y) = r(x)+r(y)"

sublocale range_semiring \<subseteq> dual!: domain_semiring 
"op +" "op \<le>" "op <" "op \<odot>" "(1\<Colon>'a)" "(0\<Colon>'a)" "r"
proof 
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult_assoc opp_mult_def)
  show "x + y + z = x + (y + z)"
    by (metis add_assoc')
  show "x + y = y + x"
    by (metis add_comm')
  show  "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distl opp_mult_def)
  show  "(1\<Colon>'a) \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> (1\<Colon>'a) = x"
    by (metis mult_onel opp_mult_def)
  show  "(0\<Colon>'a) + x = x"
    by (metis add_zerol)
  show "(0\<Colon>'a) \<odot> x = (0\<Colon>'a)"
    by (metis annil opp_mult_def)
  show  "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distr opp_mult_def)
  show "x \<odot> (0\<Colon>'a) = (0\<Colon>'a)"
    by (metis annir opp_mult_def)
  show  "x + r x \<odot> x = r x \<odot> x"
    by (metis opp_mult_def r1)
  show "r (x \<odot> y) = r (x \<odot> r y)"
    by (metis opp_mult_def r2)
  show  "r x + (1\<Colon>'a) = (1\<Colon>'a)"
    by (metis r3)
  show "r (0\<Colon>'a) = (0\<Colon>'a)"
    by (metis r4)
  show "r (x + y) = r x + r y"
    by (metis r5)
qed

context range_semiring
begin

subclass dioid_one_zero
proof
  fix x y z :: 'a
  show "x+x = x"
    by (metis add_comm' r1 r3 distr mult_onel)
qed

lemma r1_eq: "x = x\<cdot>r(x)"
  by (metis dual.d1_eq opp_mult_def)

lemma range_invol: "r(r(x)) = r(x)"
  by (metis dual.domain_invol opp_mult_def)

lemma range_fixed_point: "(\<exists>y.(x=r(y))) \<longleftrightarrow> x=r(x)"
  by (metis dual.domain_fixed_point opp_mult_def)

lemma range_1: "r(x\<cdot>y) \<le> r(y)"
  by (metis dual.domain_1  opp_mult_def)

lemma range_subid: "x \<le> 1 \<longrightarrow> x \<le> r(x)"
   by (metis dual.domain_subid  opp_mult_def)

lemma range_very_strict: "r(x) = 0 \<longleftrightarrow> x = 0"
  by (metis dual.domain_very_strict  opp_mult_def)

lemma range_one: "r(1) = 1"
  by (metis dual.domain_one  opp_mult_def)

lemma ran_subid: "r(x) \<le> 1"
 by (metis dual.dom_subid opp_mult_def)

lemma range_iso: "x \<le> y \<longrightarrow> r(x) \<le> r(y)"
  by (metis dual.domain_iso)

lemma range_export: "r(x\<cdot>r(y)) = r(x)\<cdot>r(y)"
 by (metis dual.domain_export opp_mult_def)

lemma ran_el_idemp: "r(x)\<cdot>r(x) = r(x)"
  by (metis dual.dom_el_idemp opp_mult_def)

lemma ran_el_comm: "r(x)\<cdot>r(y) = r(y)\<cdot>r(x)"
  by (metis dual.dom_el_comm opp_mult_def)

lemma ran_llp: "x \<le> x\<cdot>r(y) \<longleftrightarrow> r(x) \<le> r(y)"
  by (metis dual.dom_llp opp_mult_def)

lemma ran_weakly_local: "x\<cdot>y = 0 \<longleftrightarrow> r(x)\<cdot>y = 0"
 by (metis dual.dom_weakly_local opp_mult_def)

lemma ran_add_closed: "r(r(x)+r(y)) = r(x)+r(y)" 
  by (metis dual.dom_add_closed)

lemma ran_mult_closed: "r(r(x)\<cdot>r(y)) = r(x)\<cdot>r(y)"
  by (metis dual.dom_mult_closed opp_mult_def)

lemma ran_lb: "r(x)\<cdot>r(y) \<le> r(y)"
  by (metis dual.dom_lb opp_mult_def)

lemma ran_glb: "r(x) \<le> r(y)\<cdot>r(z) \<longleftrightarrow> (r(x) \<le> r(y) \<and> r(x) \<le> r(z))"
  by (metis dual.dom_glb opp_mult_def)

lemma range_absorption_1: "(r(x)+r(y))\<cdot>r(x)=r(x)"
  by (metis dual.domain_absorption_1 opp_mult_def)

lemma range_absorption_2: "r(x)+(r(y)\<cdot>r(x))=r(x)"
  by (metis dual.domain_absorption_2 opp_mult_def)

lemma range_distributivity: "r(x)+(r(z)\<cdot>r(y))=(r(x)+r(z))\<cdot>(r(x)+r(y))"
  by (metis dual.domain_distributivity opp_mult_def)

lemma range_order: "r(x) \<le> r(y) \<longleftrightarrow> r(x)=r(y)\<cdot>r(x)"
  by (metis dual.domain_order opp_mult_def)
 
end

section {* Antirange Semirings *}

class antirange_op =
  fixes ar :: "'a \<Rightarrow> 'a"

class antirange_semiring = semiring_one_zero + plus_ord + range_op + antirange_op +
  assumes ar1: "x\<cdot>ar(x) = 0"
  and ar2: "ar(x\<cdot>y)+ar(ar(ar(x))\<cdot>y) = ar(ar(ar(x))\<cdot>y)"
  and ar3: "ar(ar(x))+ar(x) = 1"
  and r_def: "r(x) = ar(ar(x))"

sublocale antirange_semiring \<subseteq> dual!: antidomain_semiring 
"op +" "op \<le>" "op <" "op \<odot>" "(1\<Colon>'a)" "(0\<Colon>'a)" "ar" "r"
proof 
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult_assoc opp_mult_def)
  show "x + y + z = x + (y + z)"
    by (metis add_assoc')
  show "x + y = y + x"
    by (metis add_comm')
  show  "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distl opp_mult_def)
  show  "(1\<Colon>'a) \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> (1\<Colon>'a) = x"
    by (metis mult_onel opp_mult_def)
  show  "(0\<Colon>'a) + x = x"
    by (metis add_zerol)
  show "(0\<Colon>'a) \<odot> x = (0\<Colon>'a)"
    by (metis annil opp_mult_def)
  show  "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distr opp_mult_def)
  show "x \<odot> (0\<Colon>'a) = (0\<Colon>'a)"
    by (metis annir opp_mult_def)
  show "ar x \<odot> x = (0\<Colon>'a)"
by (metis ar1 opp_mult_def)
    show "ar (x \<odot> y) + ar (x \<odot> ar (ar y)) = ar (x \<odot> ar (ar y))"
by (metis ar2 opp_mult_def r_def)
      show "ar (ar x) + ar x = (1\<Colon>'a)"
by (metis add_comm' ar3)
        show  "r x = ar (ar x)"
by (metis r_def)
qed

context antirange_semiring
begin

subclass dioid
proof
  fix x y z :: 'a
  show "x+x = x"
    by (metis dual.add_idem)
  show "z\<cdot>x \<le> z\<cdot>(x+y)"
    by (metis distl dual.order_prop)
 qed

lemma ar_subid: "ar(x) \<le> 1"
  by (metis dual.a_subid)

lemma ar_gla: "x\<cdot>ar(y) = 0 \<longleftrightarrow> ar(y) \<le> ar(x)"
 by (metis dual.a_gla opp_mult_def)

lemma ar2_eq: "ar(x\<cdot>y) = ar(r(x)\<cdot>y)"
  by (metis dual.a2_eq opp_mult_def)

lemma ar_closure:  "r(ar(x)) = ar(x)"
  by (metis dual.a_closure opp_mult_def)

lemma ar_subdist: "ar(x+y) \<le> ar(x)"
  by (metis dual.a_subdist opp_mult_def)

lemma ar_idem: "ar(x)\<cdot>ar(x) = ar(x)"
  by (metis dual.a_idem opp_mult_def)

lemma ar_1: "ar(x) = 1 \<longrightarrow> x = 0"
 by (metis dual.a_1 opp_mult_def)

lemma ar_3: "r(x+y)\<cdot>(ar(y)\<cdot>ar(x)) = 0"
  by (metis dual.a_3 opp_mult_def)

lemma ar_add: "ar(y)\<cdot>ar(x) = ar(x+y)"
  by (metis dual.a_add opp_mult_def)

lemma ar_export: "ar(y\<cdot>ar(x)) = r(x)+ar(y)"
 by (metis dual.a_export opp_mult_def)

subclass range_semiring
proof
  fix x y :: 'a
  have  "x = x\<cdot>r(x)"
    by (metis ar1 distl dual.a3 dual.add_comm' dual.add_zerol' dual.d_def mult_oner)
   thus "x+(x\<cdot>r(x)) = x\<cdot>r(x)"
     by (metis dual.order_refl leq_def)
   show  "r(x\<cdot>y) = r(r(x)\<cdot>y)"
     by (metis ar2_eq dual.d_def)
  show "r(x)+1 = 1"
    by (metis dual.d3 dual.d_def)
  show  "r(0) = 0"
    by (metis dual.domain_very_strict)
  show  "r(x+y) = r(x)+r(y)"
    by (metis dual.d5)
qed

lemma ar_zero: "ar(0) = 1"
  by (metis dual.a_zero)

lemma ar_one: "ar(1) = 0"
   by (metis dual.a_one)

lemma ar_comp_1: "ar(x)\<cdot>r(x) = 0"
    by (metis dual.a_comp_1 opp_mult_def)

lemma ar_comp_2: "r(x)\<cdot>ar(x) = 0"
 by (metis dual.a_comp_2 opp_mult_def)

lemma ar_2_var: "r(x)\<cdot>ar(y) = 0 \<longleftrightarrow> ar(y) \<le> ar(x)"
 by (metis dual.a_2_var opp_mult_def)

lemma ar_antitone: "x \<le> y \<longrightarrow> ar(y) \<le> ar(x)"
 by (metis dual.a_antitone opp_mult_def)

lemma ar_de_morgan: "ar(ar(y)\<cdot>ar(x)) = r(x+y)"
by (metis dual.a_de_morgan opp_mult_def)

lemma ar_de_morgan_var_1: "ar(ar(y)\<cdot>ar(x)) = r(x)+r(y)"
  by (metis dual.a_de_morgan_var_1 opp_mult_def)

lemma ar_de_morgan_var_2: "ar(ar(x)+ar(y)) = r(y)\<cdot>r(x)"
  by (metis dual.a_de_morgan_var_2 opp_mult_def)

lemma ar_comm: "ar(x)\<cdot>ar(y) = ar(y)\<cdot>ar(x)"
  by (metis dual.a_comm opp_mult_def)

lemma ar_4: "ar(x) \<le> ar(y\<cdot>x)"
  by (metis dual.a_4 opp_mult_def)

lemma ar_5: "ar(r(x)) = ar(x)"
  by (metis dual.a_5 opp_mult_def)

lemma ar_6: "ar(x\<cdot>r(y)) = ar(y)+ar(x)"
  by (metis dual.a_6 opp_mult_def)

lemma r_ar_galois1: "ar(x)\<cdot>r(y) \<le> r(z) \<longleftrightarrow> r(y) \<le> r(z)+r(x)"
  by (metis dual.d_a_galois1 opp_mult_def)

lemma r_ar_galois2: "r(y)\<cdot>r(x) \<le> r(z) \<longleftrightarrow> r(x) \<le> r(z)+ar(y)"
  by (metis dual.d_a_galois2 opp_mult_def)

lemma ar_r_add_closure: "r(ar(x)+ar(y))=ar(x)+ar(y)"
  by (metis dual.a_d_add_closure opp_mult_def)

lemma ar_r_mult_closure: "r(ar(x)\<cdot>ar(y))=ar(x)\<cdot>ar(y)"
  by (metis dual.a_d_mult_closure opp_mult_def)

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

