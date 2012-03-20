header {* Experiments with the axioms of Boffa,  Conway,  Krob and Salomaa *}

theory Boffa_Conway_Krob
  imports Dioid

begin

text {* We analyse some syntactic arguments from papers of Boffa,
Conway, Krob, Salomaa and Kozen *}

(**************************************************************************)

text {* We first introduce the o-Notation that determines the value
of a Kleene algebra term when each variable is zero. In the context of
regular languages this tells us whether or not a word has the empty word property. to be done. *}

class salomaa = semiring_one_zero + star_op +
assumes S11: "(1+x)\<^sup>\<star> = x\<^sup>\<star>"
and S12: "x\<^sup>\<star> = 1+x\<^sup>\<star>\<cdot>x"

begin

lemma zero_star: "0\<^sup>\<star> = 1"
  by (metis S12 add_comm' add_zerol annil)
  
lemma one_star: "1\<^sup>\<star> = 1"
  by (metis S11 add_comm' add_zerol zero_star)


lemma one_idem: "1+1 = 1"
  by (metis S12 mult_oner one_star)

lemma add_idem: "x+x = x"
  by (metis distl mult_oner one_idem)


(*
lemma starstar: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
nitpick --- 5-element counterexample
*)

end

text {* Here we need to add $S^+$ with Arden's rule, which requires an
axiomatisation of terms and the o-function. *}

class pre_conway = semiring_one_zero + star_op +
  assumes C11: "(x+y)\<^sup>\<star>=(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
  and C12: "(x\<cdot>y)\<^sup>\<star> = 1+x\<cdot>((y\<cdot>x)\<^sup>\<star>)\<cdot>y"
  and C13: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>" 

class pre_boffa = pre_conway +
  assumes B:"x\<cdot>x = x \<longrightarrow> x\<^sup>\<star> = 1+x"

class pre_conway_one = pre_conway +
  assumes arden_var: "x = x\<cdot>y \<longrightarrow> x = x\<cdot>y\<^sup>\<star>"

begin

subclass pre_boffa
proof
fix x :: 'a
show  "x\<cdot>x = x \<longrightarrow> x\<^sup>\<star> = 1+x"
  by (metis arden_var C12)
qed

(*
lemma "x\<cdot>y \<le> x \<longrightarrow> x\<cdot>y\<^sup>\<star> \<le> x"
nitpick --- 3-element counterexample
*)

end

class boffa_2 = dioid_one_zero + star_op +
assumes B1: "(x+y)\<^sup>\<star>=(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
and B2: "(x\<cdot>y)\<^sup>\<star> = 1+x\<cdot>((y\<cdot>x)\<^sup>\<star>)\<cdot>y"
and R:"x\<cdot>x = x \<longrightarrow> x\<^sup>\<star> = 1+x" 

begin

subclass pre_boffa
proof
fix x y :: 'a
show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
  by (metis B1)
show "(x \<cdot> y)\<^sup>\<star> = (1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
  by (metis B2)
show "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B1 B2 R add_idem mult_assoc mult_onel mult_oner)
show "x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = (1\<Colon>'a) + x"
by (metis R)
qed

lemma onestar: "1\<^sup>\<star> = 1"
by (metis R add_idem mult_onel)

end

class boffa_3 = dioid_one_zero + star_op +
assumes B3: "1+x \<le> x\<^sup>\<star>"
and B4: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
and B5: "1+x \<le> y \<and> y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"

begin

lemma aux_01: "x\<^sup>\<star> = (1+x)\<^sup>\<star>"
  by (metis B3 B4 B5 add_ub antisym_conv leq_def)

lemma aux_02: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis B3 B4 B5 add_lub order_trans)

lemma aux_03: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B3 B4 B5 add_lub antisym leq_def)

lemma aux_04: "x \<le> x\<^sup>\<star>"
  by (metis B3 add_lub)

lemma aux_1: " x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = (1\<Colon>'a) + x"
  by (smt add_assoc add_idem distl distr mult_onel mult_oner B3 B5 antisym order_refl)

lemma aux_2: "(x\<cdot>y)\<^sup>\<star> \<le> 1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y"
proof -
have "1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y = (1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y)\<cdot>(1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y)"
  by (smt distl mult_oner add_assoc mult_assoc distr leq_def mult_onel subdistr
aux_04 mult_isol mult_isor B4 add_comm leq_def)
hence "... = (1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y)\<^sup>\<star>"
by (metis add_ub aux_1 leq_def)
have "x\<cdot>y \<le> x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y"
by (smt B3 add_lub mult_isol mult_isor mult_oner)
hence "... \<le> 1+ x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y"
by (metis `((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) \<cdot> ((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) =((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y)\<^sup>\<star>` `(1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y =((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) \<cdot> ((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y)` aux_01 aux_04)
thus ?thesis
by (metis `((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) \<cdot> ((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) =((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y)\<^sup>\<star>` `(1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y =((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) \<cdot> ((1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y)` `x \<cdot> y \<le> x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y` aux_01 aux_02)
qed

lemma aux_3: "1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y \<le> (x\<cdot>y)\<^sup>\<star>"
proof -
have "1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y \<le> 1+x\<cdot>(1+y\<cdot>(x\<cdot>y)\<^sup>\<star>\<cdot>x)\<cdot>y"
by (smt add_comm add_iso distr leq_def subdistl aux_2)
hence "... \<le> 1+x\<cdot>y+(x\<cdot>y)\<cdot>(x\<cdot>y)\<^sup>\<star>\<cdot>(x\<cdot>y)"
by (metis add_assoc distl distr eq_refl mult_assoc mult_oner)
hence "... \<le> (x\<cdot>y)\<^sup>\<star>+(x\<cdot>y)\<^sup>\<star>\<cdot>(x\<cdot>y)\<^sup>\<star>\<cdot>(x\<cdot>y)\<^sup>\<star>"
by (metis aux_04 mult_double_iso order_refl B4 add_assoc leq_def opp_mult_def B3 add_idem add_lub)
thus ?thesis
by (smt B4 `(1\<Colon>'a) + x \<cdot> ((1\<Colon>'a) + y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> x) \<cdot> y\<le> (1\<Colon>'a) + x \<cdot> y + x \<cdot> y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x \<cdot> y)` `(1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<le> (1\<Colon>'a) + x \<cdot> ((1\<Colon>'a) + y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> x) \<cdot> y` add_idem order_trans)
qed

lemma aux_4: "(x\<cdot>y)\<^sup>\<star> = 1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y"
  by (metis antisym aux_2 aux_3)

lemma aux_05: "x\<^sup>\<star> = 1+x\<cdot>x\<^sup>\<star>"
by (metis aux_4 mult_onel mult_oner)

lemma aux_06: "x\<^sup>\<star> = 1+x\<^sup>\<star>\<cdot>x"
by (metis aux_4 mult_onel mult_oner)

lemma aux_07: "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
by (smt aux_4 distr mult_onel distl mult_assoc mult_oner aux_06)

lemma aux_08: "1+x\<^sup>\<star> = x\<^sup>\<star>"
by (metis B4 aux_03 aux_1)

lemma aux_5: "(x+y)\<^sup>\<star> \<le> (x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
proof -
have "(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
by (metis B4 aux_07 mult_assoc)
hence "((x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
by (smt aux_08 aux_1 iso_subdist leq_def mult_assoc mult_isol mult_oner order_trans)
thus ?thesis
by (smt add_lub aux_02 aux_04 aux_07 aux_08 mult_double_iso mult_onel mult_oner order_trans subdistl)
qed

lemma aux_6: "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
by (metis B4 add_lub aux_02 aux_03 aux_04 mult_double_iso)

subclass boffa_2
proof
fix x y :: 'a
show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
by (metis antisym aux_5 aux_6)
show " (x \<cdot> y)\<^sup>\<star> = (1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
by (metis aux_4)
show " x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = (1\<Colon>'a) + x"
by (metis aux_1)
qed

end

class left_kozen = dioid_one_zero + star_op +
assumes k1: "1+x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
and k2: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"

begin

subclass boffa_3
proof
fix x y :: 'a
show "1+x \<le> x\<^sup>\<star>"
by (smt add_lub distl k1 leq_def mult_oner)
show "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
by (metis add_lub antisym k1 k2 mult_isol mult_oner)
show "1+x \<le> y \<and> y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
by (metis add_lub distr k2 mult_oner order_prop order_trans subdistl)
qed


end

(* now all these krob and conway discussions, and adding the other axioms. *)






lemma star_ref: "1 \<le> x\<^sup>\<star>"
  by (metis c12 mult_oner order_prop)
  
lemma star_plus_one: "x\<^sup>\<star> = 1+x\<^sup>\<star>"
  by (metis leq_def star_ref)

lemma star_trans: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_idem c11 c12 leq_def mult_assoc mult_onel mult_oner)

lemma star_trans_eq: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis antisym mult_oner star_plus_one star_trans subdistl)

lemma star_1l: "x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_lub c12 mult_onel mult_oner order_refl)

(*
lemma star_subid: "x \<le> 1 \<longrightarrow> x\<^sup>\<star> = 1"

lemma star_one: "1\<^sup>\<star> = 1"
nitpick
  by (metis eq_iff star_subid)


lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
nitpick
  by (metis add_comm leq_def eq_iff star_inductl)

lemma star_inductl_var_equiv: "x\<cdot>y \<le> y \<longleftrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  by (metis eq_iff mult_assoc mult_isor mult_onel star_1l star_inductl_var star_ref)

*)

lemma star_subdist:  "x\<^sup>\<star> \<le> (x+y)\<^sup>\<star>"
  by (metis c11 mult_onel star_plus_one subdistr)

lemma star_iso: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis leq_def star_subdist)

lemma star2: "(1+x)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis add_comm c11 c13 mult_oner star_trans_eq)

(*
lemma star_inductl_eq:  "z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"
by (metis eq_iff star_inductl)

lemma star_inductl_var_eq:  "x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
by (metis eq_iff star_inductl_var)

(* lemma star_unfoldr: "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
 nitpick -- "3-element counterexample" *)

(* lemma star_ext: "x \<le> x\<^sup>\<star>"
nitpick -- "3-element counterexample" *)

(* lemma star_1r: "x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
nitpick -- "3-element counterexample" *)

(* lemma star_sim1: "x\<cdot>z \<le> z\<cdot>y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> z\<cdot>y\<^sup>\<star>"
nitpick -- "3-element counterexample" *)

(* lemma star_unfoldl_eq: "1+x\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
nitpick -- "4-element counterexample" *)
*)

lemma sum_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x+y \<le> z\<^sup>\<star>"
  by (metis add_lub) 

lemma prod_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x\<cdot>y \<le> z\<^sup>\<star>"
  by (metis mult_double_iso star_trans_eq)

lemma star_star_closure: "x\<^sup>\<star> \<le> z\<^sup>\<star> \<longrightarrow> (x\<^sup>\<star>)\<^sup>\<star> \<le> z\<^sup>\<star>"
  by (metis c13)

lemma star_ext: "x \<le> x\<^sup>\<star>"
  by (metis mult_isol mult_oner order_trans star_1l star_ref)

lemma star_unfoldr: "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  by (metis add_lub order_refl prod_star_closure star_ext star_ref)

lemma star_1r: "x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  by (metis order_refl prod_star_closure star_ext)

(*
lemma star_sim1: "x\<cdot>z \<le> z\<cdot>y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> z\<cdot>y\<^sup>\<star>"
  by (smt add_comm add_lub distr leq_def mult_assoc mult_oner star_1l star_ext star_inductl star_invol star_iso star_ref subdistl)


lemma quasicomm_var: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star> \<longleftrightarrow> y\<^sup>\<star>\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>"
  by (smt distr order_prop order_trans star_ext star_invol star_sim1)


lemma star_slide1: "(x\<cdot>y)\<^sup>\<star>\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>\<star>"
    by (metis eq_iff mult_assoc star_sim1)


lemma star_slide_var1: "x\<^sup>\<star>\<cdot>x \<le> x\<cdot>x\<^sup>\<star>"
  by (metis le_less star_sim1)
*)

lemma star_unfoldl_eq: " x\<^sup>\<star> = 1+x\<cdot>x\<^sup>\<star>"
by (metis c12 mult_onel mult_oner)
 
lemma star_rtc1: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
by (metis add_lub eq_refl star_ext star_ref star_trans_eq)

lemma star_rtc1_eq: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
by (metis add_assoc leq_def star_ext star_plus_one star_trans_eq)

(*
lemma star_rtc2_eq: "1+x+y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
  by (metis add_lub leq_def mult_oner star_inductl_var_equiv star_subdist subdistl)
*)

lemma star_subdist_var_1: "x \<le> (x+y)\<^sup>\<star>"
by (metis add_lub star_ext)

lemma star_subdist_var_2: "x\<cdot>y \<le> (x+y)\<^sup>\<star>"
by (metis add_lub prod_star_closure star_ext)

lemma star_subdist_var_3: "x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<le> (x+y)\<^sup>\<star>"
by (metis add_lub order_refl prod_star_closure star_iso)

lemma star_denest: "(x+y)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
sorry 
(*
by (metis add_comm c11 c13 mult_assoc star_trans_eq)
*)

lemma star_sum_var: "(x+y)\<^sup>\<star>  = (x\<^sup>\<star>+y\<^sup>\<star>)\<^sup>\<star>"
by (metis c13 star_denest)

(*
lemma star_denest_var: "(x+y)\<^sup>\<star> = x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
proof -
  have "(x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
    by (smt add_lub mult_oner star_unfoldl_eq subdistl mult_isor star_1l 
add_ub distr mult_onel order_trans mult_assoc star_inductl)
  thus ?thesis  
    by (metis add_comm' mult_double_iso star_invol star_iso star_subdist star_subdist_var_2 star_sum_var star_trans_eq eq_iff)
qed


lemma star_denest_var_2: "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var)
*)
lemma star_denest_var_3: "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<cdot>(y\<^sup>\<star>\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  by (smt add_comm c11 distr mult_assoc star_denest star_plus_one star_trans_eq star_unfoldl_eq)

lemma star_denest_var_4:  "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = (y\<^sup>\<star>\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
by (metis add_comm star_denest)

(*
lemma star_denest_var_5: "x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star> = y\<^sup>\<star>\<cdot>(x\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm' star_denest_var)
*)

lemma star_denest_var_6: "(x+y)\<^sup>\<star> = x\<^sup>\<star>\<cdot>y\<^sup>\<star>\<cdot>(x+y)\<^sup>\<star>"
by (metis mult_assoc star_denest star_denest_var_3)

lemma star_denest_var_7: "(x+y)\<^sup>\<star> = (x+y)\<^sup>\<star>\<cdot>x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
by (metis add_comm c11 mult_assoc star_trans_eq)

lemma star_denest_var_8: "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<cdot>y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
by (metis star_denest star_denest_var_6)

lemma star_denest_var_9: " (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>\<cdot>x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
by (metis star_denest star_denest_var_7)

(*
lemma confluence_var: "y\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longleftrightarrow> y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis mult_isor order_trans star_ext star_invol star_sim1)

lemma church_rosser_var: "y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
(*
    by (metis mult_assoc mult_isol mult_isor star_trans_eq star_inductl_var star_denest_var_9 star_denest)
*)
proof
  assume "y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  hence "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>\<le>  x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
    by (metis mult_assoc mult_isol mult_isor star_trans_eq star_inductl_var star_denest_var_9)
  thus  "(x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
    by (metis star_denest)
qed

text {* The automatic metis proof takes extremely long. *}

text {* The induction over peaks is interesting in its own right. *}

lemma church_rosser_peak_induct: "y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
    by (metis mult_assoc mult_isol mult_isor star_trans_eq star_inductl_var star_denest_var_9)

lemma church_rosser: "y\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
 by (metis church_rosser_var confluence_var)
(*
proof
  assume "y\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  hence "1+(x+y)\<cdot>(x\<^sup>\<star>\<cdot>y\<^sup>\<star>) \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
    by (metis add_lub mult_oner star_plus_one subdistl mult_isor star_1l  mult_assoc star_trans_eq distr)
  thus  "(x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
    by (metis star_inductl mult_oner)
qed
*)

text {* This is another proof by induction *}

lemma church_rosser_eq: "y\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<star> = x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis church_rosser eq_iff star_subdist_var_3)

lemma church_rosser_eq_var: "y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<star> = x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis church_rosser_eq confluence_var)

lemma church_rosser_to_confluence: "(x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis add_comm' eq_iff star_subdist_var_3)

lemma church_rosser_equiv: "y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longleftrightarrow> (x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis church_rosser_to_confluence church_rosser_var)

lemma confluence_to_local_confluence: "y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> y\<cdot>x \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis confluence_var mult_isol order_trans star_ext)

(* lemma local_confluence_to_confluence: "y\<cdot>x \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> y\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
nitpick -- "6-element counterexample" *)

(* lemma confluence_to_church_rosser: "y\<cdot>x \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
nitpick -- "6-element counterexample, as expected" *)

text {* More variations could easily be proved. The last counterexample shows that Newman's lemma needs a wellfoundedness assumption. This is well known *}
*)

lemma sup_id_star1: "1 \<le> x \<longrightarrow> x\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
by (metis atLeastAtMost_singleton' mult_isor mult_onel ord.atLeastAtMost_iff singletonE star_1l)

lemma sup_id_star2: "1 \<le> x \<longrightarrow> x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
by (metis antisym mult_isol mult_oner star_1r)

(* lemma star_unfoldr_eq: "1+x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
nitpick -- "4-element counterexample" *)

(* lemma star_slide: "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
nitpick -- "3-element counterexample" *)

(* lemma boffa: "x\<cdot>x=x \<longrightarrow> x\<^sup>\<star>=1+x"
nitpick -- "3-element counterexample" *)

lemma star_unfoldr_eq: "1+x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
by (metis c12 mult_onel mult_oner) 

(*
lemma star_slide: "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  by (smt add_comm mult_assoc star_unfoldr_eq star_slide1 mult_isor add_iso mult_isol
     distl mult_oner distr mult_onel star_unfoldl_eq eq_iff star_slide1)
*)

lemma star_slide_var: "x\<^sup>\<star>\<cdot>x = x\<cdot>x\<^sup>\<star>"
  by (smt distl distr mult_assoc mult_onel mult_oner star_unfoldl_eq star_unfoldr_eq)

lemma star_prod_unfold: "(x\<cdot>y)\<^sup>\<star> = 1+ x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y"
by (metis c12 opp_mult_def)

(*
lemma star_sum_unfold: "(x+y)\<^sup>\<star> = x\<^sup>\<star>+x\<^sup>\<star>\<cdot>y\<cdot>(x+y)\<^sup>\<star>"
  by (metis distl mult_assoc mult_oner star_denest_var star_unfoldl_eq)

lemma troeger: "x\<^sup>\<star>\<cdot>(y\<cdot>((x+y)\<^sup>\<star>\<cdot>z)+z) = (x+y)\<^sup>\<star>\<cdot>z"
  by (smt add_comm distl distr mult_assoc star_sum_unfold)


lemma dbw_lemma: "x\<^sup>\<star>\<cdot>y\<cdot>z\<^sup>\<star> = x\<^sup>\<star>\<cdot>y+x\<^sup>\<star>\<cdot>x\<cdot>y\<cdot>z\<cdot>z\<^sup>\<star>+y\<cdot>z\<^sup>\<star>"
  by (smt add_assoc add_comm distl distr mult_assoc mult_onel mult_oner star_slide_var star_unfoldl_eq add_idem)

lemma meyer_1: "x\<^sup>\<star> = (1+x)\<cdot>(x\<cdot>x)\<^sup>\<star>"
proof -
have  "x\<^sup>\<star> \<le> (1+x)\<cdot>(x\<cdot>x)\<^sup>\<star>"
by (smt add_assoc' add_comm' distl distr mult_onel mult_oner order_refl star_prod_unfold star_inductl mult_assoc mult_oner)
thus ?thesis by (metis add_lub  prod_star_closure star_ext star_invol star_iso star_ref eq_iff)
qed

lemma boffa: "x\<cdot>x=x \<longrightarrow> x\<^sup>\<star>=1+x"
  by (metis eq_iff mult_isol mult_oner star_inductl_var_eq star_ref star_slide_var star_unfoldr_eq)
*)

(* for the following two lemmas I could neither find a counterexample
nor a proof. I assume these facts are not valid in left Kleene
algebras. I didn't try Nitpick with very long time bounds.

lemma star_sim2: "z\<cdot>x \<le> y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y\<^sup>\<star>\<cdot>z"

lemma star_sim3: "z\<cdot>x = y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<star> = y\<^sup>\<star>\<cdot>z"


lemma star_zero: "0\<^sup>\<star> = 1"
  by (metis min_zero star_subid)

*)

(*
lemma star_inductr_var: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
  by (metis add_lub order_refl star_inductr)

lemma star_inductr_var_equiv: "y\<cdot>x \<le> y \<longleftrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
  by (metis order_trans mult_isol star_ext star_inductr_var)

text {* The following law could be immediate if we had proper duality
for Kleene algebras. *}

lemma star_sim2: "z\<cdot>x \<le> y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y\<^sup>\<star>\<cdot>z"
  by (smt add_comm add_lub distl leq_def mult_assoc mult_onel star_1r star_ext star_inductr star_invol star_iso star_ref subdistr)

lemma star_sim3: "z\<cdot>x = y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<star> = y\<^sup>\<star>\<cdot>z"
  by (metis eq_iff star_sim1 star_sim2)

lemma star_sim4: "x\<cdot>y \<le>  y\<cdot>x \<longrightarrow> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<le> y\<^sup>\<star>\<cdot>x\<^sup>\<star>"
  by (metis star_sim1 star_sim2)

lemma star_inductr_eq: "z+y\<cdot> x= y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"
by (metis eq_iff star_inductr)

lemma star_inductr_var_eq: "y\<cdot>x = y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
by (metis eq_iff star_inductr_var)

lemma bubble_sort:  "y\<cdot>x \<le> x\<cdot>y \<longrightarrow> (x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis church_rosser_eq_var order_refl star_sim4) 

lemma independence1: "x\<cdot>y = 0 \<longrightarrow> x\<^sup>\<star>\<cdot>y = y"
  by (metis annil mult_oner star_sim3 star_zero)

lemma independence2: "x\<cdot>y = 0 \<longrightarrow> x\<cdot>y\<^sup>\<star> = x"
  by (metis annir mult_onel star_sim3 star_zero)

lemma lazycomm_var: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>+y \<longleftrightarrow> y\<cdot>x\<^sup>\<star> \<le> x\<cdot>(x+y)\<^sup>\<star>+y"
proof - 
  have "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>+y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> x\<cdot>(x+y)\<^sup>\<star>+y"
    by (smt add_assoc' distr add_comm' add_iso add_idem add_lub distl order_prop leq_def mult_assoc order_refl star_1r add_idem star_inductr)
  thus ?thesis 
    by (metis mult_double_iso order_refl order_trans star_ext) 
qed
*)

end

end
