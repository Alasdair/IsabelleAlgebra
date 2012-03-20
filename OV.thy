header {* Variants of Omega Algebras *}


theory Omega_Algebra_Var
  imports My_Kleene_Algebra
begin

(************************************************************************)

section {* Four Omega Algebras *}

text {* We consider four variants of omega algebra. The difference
lies in the coinduction laws. The first one, abreviated LOA is Cohen's
variant. The second one, LOA1, uses a simplified form of
coinduction. The third one, LOA2, combines the first coinduction law
with a form of simulation. The fourth one, LOA3, is a simpler kind of
simulation law. *}

class pre_omega_algebra = left_kleene_algebra_zero + omega_op +
  assumes omega_unfold: "x\<^sup>\<omega> \<le> x\<cdot>x\<^sup>\<omega>"

class left_omega_algebra = pre_omega_algebra +
  assumes omega_coinduct: "y \<le> z+x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"

class left_omega_algebra_var1 = pre_omega_algebra +
  assumes omega_coinduct_var1: "y \<le> x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>"

class left_omega_algebra_var2 = pre_omega_algebra +
  assumes omega_coinduct_var2: "x\<cdot>y \<le> z\<cdot>x+w \<longrightarrow> x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>+z\<^sup>\<star>\<cdot>w\<cdot>y\<^sup>\<omega>"

class left_omega_algebra_var3 = pre_omega_algebra +
  assumes omega_coinduct_var3:  "x\<cdot>y \<le> z\<cdot>x \<longrightarrow> x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>"

(***************************************************************************)

text {* We now establish subclass relationships between these
variants. A class of algebras is a subclass of another one if the
axioms of the second can be derived from those of the first. In
Isabelle, subclass relationships can be captured by sublocale
statements. In particular, all theorems established in the superclass
become available in the subclass. *}

text {* First we compare LOA and LOA1. *}

sublocale left_omega_algebra \<subseteq> left_omega_algebra_var1
proof 
  fix x y :: 'a
  show "y \<le> x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>"
    by (metis add_zerol add_zeror annil omega_coinduct)

qed

text {* The coinduction axiom of LOA1 is derivable in LOA. Hence LOA
is a subclass of LOA1. *}

text {* Next we analyse whether LOA is a strict subclass or whether
LOA and LOA1 define the same class. Hence we try either to derive LOA
coinduction from LOA1 coinduction or to show that LOA coinduction is
independent in LOA1. *}

(*
context left_omega_algebra_var1

begin

lemma "y \<le> z+x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
nitpick

end
*)

text {* no proof no refutation *}

text {* Hence we know that LOA is a subclass of LOA1, but we neither
know whether it is a strict subclass nor whether the classes are the
same. *}

(*************************************************************************)

text {* Next we compare LOA and LOA2. *}

sublocale left_omega_algebra \<subseteq> left_omega_algebra_var2
proof
  fix w x y z :: 'a 
  show "x \<cdot> y \<le> z \<cdot> x + w \<longrightarrow> x \<cdot> y\<^sup>\<omega> \<le> z\<^sup>\<omega> + z\<^sup>\<star> \<cdot> w \<cdot> y\<^sup>\<omega>"
  proof 
    assume hyp: "x\<cdot>y \<le> z\<cdot>x+w"
    have "x\<cdot>y\<^sup>\<omega> \<le> x\<cdot>y\<cdot>y\<^sup>\<omega>"
      by (metis mult_assoc mult_isol omega_unfold)
    hence "x\<cdot>y\<^sup>\<omega> \<le> z\<cdot>x\<cdot>y\<^sup>\<omega>+w\<cdot>y\<^sup>\<omega>"
      by (metis hyp mult_isor order_trans distr)
    thus "x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>+z\<^sup>\<star>\<cdot>w\<cdot>y\<^sup>\<omega>"
      by (metis add_comm mult_assoc omega_coinduct)
  qed
qed

(*
context left_omega_algebra_var2

begin

lemma "y \<le> z+x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
nitpick (* 2-element counterexample *)

end
*)

text {* These results show that LOA is a strict subclass of LOA2. *}

(**************************************************************************)

text {* Next we compare LOA and LOA3. *}

sublocale left_omega_algebra \<subseteq> left_omega_algebra_var3
proof 
  fix x y z :: 'a
  show "x\<cdot>y \<le> z\<cdot>x \<longrightarrow> x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>"
  proof
    assume hyp: "x\<cdot>y \<le> z\<cdot>x"
    have "x\<cdot>y\<^sup>\<omega> \<le> x\<cdot>y\<cdot>y\<^sup>\<omega>"
      by (metis mult_assoc mult_isol omega_unfold)
    hence  "x\<cdot>y\<^sup>\<omega> \<le> z\<cdot>x\<cdot>y\<^sup>\<omega>"
      by (metis hyp mult_isor order_trans)
    thus "x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>"
      by (metis mult_assoc omega_coinduct_var1)
  qed
qed

(*
context left_omega_algebra_var3

begin

lemma "y \<le> z+x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
nitpick (* 2-element counterexample *)

end
*)

text {* Again we see that LOA is a strict subclass of LOA3 *}

(*****************************************************************************)

text {* We now compare LOA1 and LOA2. *}

(*
context left_omega_algebra_var1 

begin

lemma "x \<cdot> y \<le> z \<cdot> x + w \<longrightarrow> x \<cdot> y\<^sup>\<omega> \<le> z\<^sup>\<omega> + z\<^sup>\<star> \<cdot> w \<cdot> y\<^sup>\<omega>"
nitpick (* no proof no refutation *)

end
*)

(*
context left_omega_algebra_var2

begin

lemma "y \<le> x \<cdot> y \<longrightarrow> y \<le> x\<^sup>\<omega>"
nitpick (* 2-element counterexample *)

end
*)

text {* This shows that LOA2 is not a subclass of LOA1---the LOA1
coinduction law is not derivable in LOA2---but we cannot establish and
relationship in the converse direction. 

If we knew that LOA1 is a subclass of LOA, then LOA1 had to be a
subclass of LOA2, since LOA is a subclass of LOA2.

If we knew that LOA1 is not a subclass of LOA2, then LOA1 couldn't be
a subclass of LOA, since LOA is a subclass of LOA2.  *}

(************************************************************************)

text {* We now compare LOA1 and LOA3. *}

sublocale left_omega_algebra_var1 \<subseteq> left_omega_algebra_var3
proof 
  fix x y z :: 'a
  show "x\<cdot>y \<le> z\<cdot>x \<longrightarrow> x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>"
  proof
    assume hyp: "x\<cdot>y \<le> z\<cdot>x"
    have "x\<cdot>y\<^sup>\<omega> \<le> x\<cdot>y\<cdot>y\<^sup>\<omega>"
      by (metis mult_assoc mult_isol omega_unfold)
    hence  "x\<cdot>y\<^sup>\<omega> \<le> z\<cdot>x\<cdot>y\<^sup>\<omega>"
      by (metis hyp mult_isor order_trans)
    thus "x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>"
      by (metis mult_assoc omega_coinduct_var1)
  qed
qed

(*
context left_omega_algebra_var3

begin

lemma "x \<le> y\<cdot>x  \<longrightarrow> x \<le> y\<^sup>\<omega>"
nitpick (* 2-element counterexample *)

end
*)

text {* Hence LOA1 is a strict subclass of LOA3 *}

(****************************************************************************)

text {* Finaly, we compare LOA2 and LOA3. *}

sublocale left_omega_algebra_var2 \<subseteq> left_omega_algebra_var3
proof
fix x y z :: 'a
show " x \<cdot> y \<le> z \<cdot> x \<longrightarrow> x \<cdot> y\<^sup>\<omega> \<le> z\<^sup>\<omega>"
by (metis add_comm add_zerol omega_coinduct_var2 add_zeror annil annir)
qed

(*
context left_omega_algebra_var3

begin

lemma "x\<cdot>y \<le> z\<cdot>x+z  \<longrightarrow> x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>+z\<^sup>\<star>\<cdot>w\<cdot>y\<^sup>\<omega>"
nitpick (* 3-element counterexample *)

end
*)

text {* So LOA2 is a strict subclass of LOA3. *}

text {* Unfortunately the inclusion of LOA3 doesn't seem to tell us
anything more about the missing links between the other classes. But
it is instructive to derive further properties that might help with
proving such relationships. *}

text {* So far we can draw the following conclusion: LOA is a subclass
of LOA1 and a strict subclass of LOA2. LOA1 and LOA2 are strict
subclasses of LOA3. Consequently, LOA is a strict subclass of LOA3.

We know that LOA2 is not a subclass of LOA1, but we don't know whether
or not LOA1 is a subclass of LOA2. We also don't know whether or not
LOA1 is a subclass of LOA. *}

(***************************************************************************)

text {* To shed more light on these relationships we now take our list
of theorems of LOA (from another file) and try to derive as many as
possible in LOA3. *}

context left_omega_algebra_var3

begin

lemma omega_unfold_eq: "x\<cdot>x\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis antisym omega_coinduct_var3 omega_unfold order_refl) 

lemma omega_subdist: "x\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis omega_coinduct_var3 omega_unfold_eq subdistr)

lemma omega_iso: "x \<le> y \<longrightarrow> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
  by (metis omega_subdist order_prop)

(*
lemma omega_coinduct_var: "y \<le> x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>"
    nitpick -- 2-element counterexample

lemma omega_coinduct_eq: "y = z+x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
    nitpick -- 2-element counterexample
*)

lemma zero_omega: "0\<^sup>\<omega> = 0"
  by (metis annir omega_unfold_eq)

(*
lemma max_element: "x \<le> 1\<^sup>\<omega>"
    nitpick -- 2-element counterexample

definition (in left_omega_algebra)
  top :: "'a" ("\<top>")
  where "\<top> = 1\<^sup>\<omega>"
*)

lemma max_omega: "x\<^sup>\<omega> \<le> 1\<^sup>\<omega>" 
  by (metis eq_iff mult_isor mult_onel omega_coinduct_var3 omega_subdist omega_unfold_eq star_ext star_plus_one star_trans_eq)

(*
lemma "x\<^sup>\<star> \<le> 1\<^sup>\<omega>"
    nitpick -- 2-element counterexample
*)

lemma star_omega_1: "x\<^sup>\<star>\<cdot>x\<^sup>\<omega>  = x\<^sup>\<omega>"
  by (metis antisym_conv mult_isor omega_unfold_eq star_ext star_inductl_var_eq)

lemma star_omega_3: "(x\<^sup>\<star>)\<^sup>\<omega>  = 1\<^sup>\<omega>"
  by (metis antisym max_omega omega_subdist star_plus_one)

(*
lemma omega_1: "x\<^sup>\<omega>\<cdot>y \<le> x\<^sup>\<omega>"
    nitpick -- 4-element counterexample
*)

lemma omega_1_one: "x\<^sup>\<omega>\<cdot>1\<^sup>\<omega> \<le> x\<^sup>\<omega>"
  by (metis eq_refl mult_oner omega_coinduct_var3 omega_unfold_eq)

(*
lemma omega_top: "x\<^sup>\<omega>\<cdot>1\<^sup>\<omega> = x\<^sup>\<omega>" 
    nitpick -- 3-element counterexample
*)

lemma omega_1_var: "x\<^sup>\<omega>\<cdot>y\<^sup>\<omega> \<le> x\<^sup>\<omega>"
  by (metis max_omega mult_isol omega_1_one order_trans)

(*
lemma "x\<^sup>\<omega>\<cdot>x \<le> x\<^sup>\<omega>"
    nitpick --- 4-element counterexample
*)

lemma supid_omega:"1 \<le> x \<longrightarrow> x\<^sup>\<omega> = 1\<^sup>\<omega>"
  by (metis eq_iff max_omega omega_iso)

(*
lemma omega_simulation: "z\<cdot>x \<le> y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<omega> \<le> y\<^sup>\<omega> "
    by (smt mult_assoc mult_isor omega_coinduct_var omega_unfold_eq)
*)

lemma omega_omega: "(x\<^sup>\<omega>)\<^sup>\<omega> \<le>x\<^sup>\<omega>"
  by (metis omega_1_var omega_unfold_eq)

lemma wagner_1: "(x\<cdot>x\<^sup>\<star>)\<^sup>\<omega> = x\<^sup>\<omega>" 
sorry
(*
  by (smt distl leq_def mult_oner omega_iso star_plus_one mult_assoc omega_coinduct_var3 star2 star_omega_1 star_one star_slide_var1 star_sum_var star_trans_eq star_unfoldl_eq antisym)
*)

lemma wagner_2_ineq: "x\<cdot>(y\<cdot>x)\<^sup>\<omega> \<le> (x\<cdot>y)\<^sup>\<omega>"
  by (metis eq_refl mult_assoc omega_coinduct_var3)

lemma wagner_2: "x\<cdot>(y\<cdot>x)\<^sup>\<omega>=(x\<cdot>y)\<^sup>\<omega>"
  by (smt add_comm distl leq_def mult_assoc omega_unfold_eq wagner_2_ineq)

(*
lemma wagner_3: "(x+y)\<^sup>\<omega> = x\<cdot>(x+y)\<^sup>\<omega>+z \<longrightarrow> (x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
    nitpick --- no proof no refutation
*)

lemma wagner_3_ineq: "(x+y)\<^sup>\<omega> = x\<cdot>(x+y)\<^sup>\<omega>+z \<longrightarrow> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z \<le> (x+y)\<^sup>\<omega>"
  by (metis add_comm add_lub omega_subdist star_inductl_eq)

lemma wagner_1_var: "(x\<^sup>\<star>\<cdot>x)\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis star_slide_var wagner_1)

lemma wagner_1_gen:  "(x\<cdot>y\<^sup>\<star>)\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (smt add_lub distr mult_double_iso mult_onel omega_iso order_prop star_denest star_ext star_plus_one wagner_1)

lemma wagner_1_var_gen:  "(x\<^sup>\<star>\<cdot>y)\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis distl add_lub mult_isor star_subdist omega_iso wagner_1 star_slide_var)

lemma star_omega_5: "x\<^sup>\<omega>\<cdot>(x\<^sup>\<omega>)\<^sup>\<star> = x\<^sup>\<omega>" 
  by (metis antisym mult_onel omega_1_var star_inductl_var star_plus_one star_slide_var subdistr)

lemma star_omega_4: "(x\<^sup>\<omega>)\<^sup>\<star>  = 1+x\<^sup>\<omega> "
  by (metis star_omega_5 star_unfoldl_eq)

(*
lemma omega_sum_unfold: "(x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<cdot>(x+y)\<^sup>\<omega>"
    nitpick --- no proof no refutation
*)

lemma omega_sum_unfold_ineq: "x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<cdot>(x+y)\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis add_comm add_lub distr mult_assoc omega_subdist omega_unfold_eq star_inductl_eq)


(*
lemma omega_sum_unfold_coind: "(x+y)\<^sup>\<omega> \<le> (x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega>"
    nitpick --- no proof no refutation
*)

lemma omega_sum_unfold_ind: "(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis mult_double_iso omega_subdist star_denest star_invol star_iso star_omega_1 star_subdist_var_2)

(*
lemma omega_denest: "(x+y)\<^sup>\<omega> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega>"
nitpick -- no proof no refutation
*)

lemma omega_denest_ineq: "(x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis add_lub omega_sum_unfold_ind wagner_1_var_gen)


(*
lemma omega_sum_refine: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

lemma omega_sum_refine_ineq: "x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis add_comm add_lub mult_double_iso omega_subdist star_omega_1 star_subdist)

(*
lemma bachmair_dershowitz: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>  \<longrightarrow> ((x+y)\<^sup>\<omega> = 0 \<longleftrightarrow> x\<^sup>\<omega>+y\<^sup>\<omega> = 0)"
nitpick --- no proof no refutation
*)

lemma bd_ineq:"(x+y)\<^sup>\<omega> = 0 \<longrightarrow> x\<^sup>\<omega>+y\<^sup>\<omega> = 0"
  by (metis add_comm leq_def no_trivial_inverse omega_subdist)

definition  (in dioid_one_zero) 
  ewp :: "'a \<Rightarrow> bool"
  where "ewp(x) \<longleftrightarrow> \<not>(\<forall>y.((y \<le> x\<cdot>y) \<longrightarrow> (y = 0)))"

lemma ewp_super_id1: "\<not>(0 = 1) \<longrightarrow> ((1 \<le> x) \<longrightarrow> ewp(x))"
  by (metis ewp_def mult_oner)

lemma ewp_super_id2: "\<not>(0 = 1) \<longrightarrow> (\<not>ewp(x) \<longrightarrow> \<not>(1 \<le> x))"
  by (metis ewp_super_id1)  

lemma ewp_neg_and_omega_one: "\<not>ewp(x) \<longrightarrow> x\<^sup>\<omega> = 0"
by (metis eq_refl ewp_def omega_unfold_eq)

(*
lemma ewp_neg_and_omega: "\<not>ewp(x) \<longleftrightarrow> x\<^sup>\<omega> = 0"
nitpick -- 2-element counterexample
*)

(*
lemma omega_super_id1: "\<not>(0 = 1) \<longrightarrow> ((1 \<le> x) \<longrightarrow> \<not> (x\<^sup>\<omega> = 0))"
nitpick --- 2-element counterexample
*)

(*
lemma omega_super_id2: "\<not>(0 = 1) \<longrightarrow> ((x\<^sup>\<omega> = 0) \<longrightarrow> \<not>(1 \<le> x))"
nitpick --- 2-element counterexample
*)

(*
lemma arden's_lemma_var: "x\<^sup>\<omega> = 0 \<longrightarrow> z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z = y"
nitpick --- 2-element counterexample
*)

(**********************************************************************)

text {* I now consider which additional statements from Jules' note
hold in this setting *}

lemma jules_16: "(x\<^sup>\<omega>)\<^sup>\<omega> = x\<cdot>(x\<^sup>\<omega>)\<^sup>\<omega>"
by (metis mult_assoc omega_unfold_eq)


lemma jules_17: "(x\<^sup>\<omega>)\<^sup>\<omega> \<le> x\<^sup>\<omega>\<cdot>x\<^sup>\<omega>"
by (metis mult_isol omega_omega omega_unfold_eq)

lemma jules_20: "(x\<^sup>\<omega>)\<^sup>\<omega> = x\<^sup>\<omega> \<longleftrightarrow> x\<^sup>\<omega>\<cdot>x\<^sup>\<omega> = x\<^sup>\<omega>"
by (metis antisym max_omega mult_isol mult_oner omega_coinduct_var3 omega_unfold_eq order_refl) 

lemma jules_21: "x\<^sup>\<omega>\<cdot>x\<^sup>\<omega> = x\<^sup>\<omega> \<longrightarrow> (x\<^sup>\<omega>)\<^sup>\<omega> = x\<^sup>\<omega>\<cdot>x\<^sup>\<omega>"
by (metis jules_20)

lemma jules_22: "(x\<cdot>x)\<^sup>\<omega> \<le> x\<^sup>\<omega>"
by (metis add_idem omega_iso order_refl quasicomm_var star_slide_var wagner_1)

(*
lemma jules_24: "(x\<cdot>x)\<^sup>\<omega> = x\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

end

(***********************************************************************)

text {* We now analyse the remaining properties in LOA1 *}

context left_omega_algebra_var1

begin

lemma max_element: "x \<le> 1\<^sup>\<omega>"
by (metis mult_onel omega_coinduct_var1 order_refl)

lemma omega_1: "x\<^sup>\<omega>\<cdot>y \<le> x\<^sup>\<omega>"
by (metis eq_refl mult_assoc omega_coinduct_var1 omega_unfold_eq)

lemma omega_top: "x\<^sup>\<omega>\<cdot>1\<^sup>\<omega> = x\<^sup>\<omega>"
by (metis antisym_conv max_element mult_double_iso mult_oner omega_1_var omega_unfold omega_unfold_eq)

lemma omega_boundx: "x\<^sup>\<omega> \<le> x\<cdot>1\<^sup>\<omega>"
  by (metis eq_iff mult_isol mult_onel omega_coinduct_var1 omega_unfold_eq)

lemma omega_boundstar: "x\<^sup>\<omega> \<le> x\<^sup>\<star>\<cdot>1\<^sup>\<omega>"
by (metis max_element mult_isol star_omega_1)

(*
lemma omega_boundstar: "x\<^sup>\<omega> = x\<^sup>\<star>\<cdot>1\<^sup>\<omega>"
nitpick --- 2-element counterexample


lemma "x\<cdot>1\<^sup>\<omega> \<le> x\<^sup>\<omega>"
nitpick --- 3-element counterexample
*)

(*
lemma wagner_3: "(x+y)\<^sup>\<omega> = x\<cdot>(x+y)\<^sup>\<omega>+z \<longrightarrow> (x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
nitpick --- no proof no refutation
*)

(*
lemma omega_sum_unfold: "(x+y)\<^sup>\<omega> \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<cdot>(x+y)\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma omega_sum_unfold_coind: "(x+y)\<^sup>\<omega> \<le> (x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma omega_denest: "(x+y)\<^sup>\<omega> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega>"
nitpick  -- no proof no refutation
*)

(*
lemma omega_sum_refine: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<omega> \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma bachmair_dershowitz: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>  \<longrightarrow> ((x+y)\<^sup>\<omega> = 0 \<longleftrightarrow> x\<^sup>\<omega>+y\<^sup>\<omega> = 0)"
nitpick --- no proof no refutation
*)

lemma ewp_neg_and_omega: "\<not>ewp(x) \<longleftrightarrow> x\<^sup>\<omega> = 0"
by (metis ewp_def ewp_neg_and_omega_one leq_def no_trivial_inverse omega_coinduct_var1)

lemma omega_super_id1: "\<not>(0 = 1) \<longrightarrow> ((1 \<le> x) \<longrightarrow> \<not> (x\<^sup>\<omega> = 0))"
by (metis ewp_neg_and_omega ewp_super_id1)

lemma omega_super_id2: "\<not>(0 = 1) \<longrightarrow> ((x\<^sup>\<omega> = 0) \<longrightarrow> \<not>(1 \<le> x))"
by (metis omega_super_id1)

(*
lemma arden's_lemma_var: "x\<^sup>\<omega> = 0 \<longrightarrow> z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z = y"
nitpick --- no proof no refutation
*)

lemma jules_24: "(x\<cdot>x)\<^sup>\<omega> = x\<^sup>\<omega>"
by (metis antisym_conv jules_22 mult_assoc omega_coinduct_var1 omega_unfold omega_unfold_eq)

(*
lemma "x\<^sup>\<omega> \<le> x\<^sup>\<omega>\<cdot>x\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma "x\<^sup>\<omega> \<le> (x\<^sup>\<omega>)\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma "x\<^sup>\<omega>\<cdot>x\<^sup>\<omega> \<le> (x\<^sup>\<omega>)\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma "x\<^sup>\<omega>\<cdot>x\<^sup>\<omega> = (x\<^sup>\<omega>)\<^sup>\<omega> \<longrightarrow> x\<^sup>\<omega> = x\<^sup>\<omega>\<cdot>x\<^sup>\<omega>"
nitpick  --- no proof no refutation
*)

text {* At the end of this section I try to derive the other coinduction laws. *}

(*
lemma "x \<le> y\<cdot>x+z \<longrightarrow> x \<le> y\<^sup>\<omega>+y\<^sup>\<star>\<cdot>z"
lemma "x\<cdot>y \<le> z\<cdot>x+w \<longrightarrow> x\<cdot>y\<^sup>\<omega> \<le> z\<^sup>\<omega>+z\<^sup>\<star>\<cdot>w\<cdot>y\<^sup>\<omega>"
*)

text {* Neither is possible. *}

text {* The conclusion is that for each fact we couldn't prove we
couldn't find a counterexample either. Hence we still fail to
establish that LOA is a strict subclass of LOA1 or that they are the
same class.
*}

end
(***********************************************************************)

text {* We now analyse the same properties in LOA2 *}

context left_omega_algebra_var2

begin

(*
lemma max_element: "x \<le> 1\<^sup>\<omega>"
nitpick -- 2-element counterexample

same as in LOA3, derivable in LOA1
*)



definition (in left_omega_algebra)
  top :: "'a" ("\<top>")
  where "\<top> = 1\<^sup>\<omega>"

(*
lemma "x\<^sup>\<star> \<le> 1\<^sup>\<omega>"
nitpick -- 2-element counterexample

same as in LOA3
*)

(*
lemma omega_1: "x\<^sup>\<omega>\<cdot>y \<le> x\<^sup>\<omega>"
nitpick --- 4-element counterexample

same as in LOA3, derivable in LOA1
*)

(*
lemma omega_top: "x\<^sup>\<omega>\<cdot>1\<^sup>\<omega> = x\<^sup>\<omega>" 
nitpick  -- 3-element counterexample

same as in LOA3
*)

(*
lemma "x\<^sup>\<omega>\<cdot>x \<le> x\<^sup>\<omega>"
    nitpick --- 4-element counterexample

same as in LOA3, derivable in LOA1
*)

(*
lemma wagner_3: "(x+y)\<^sup>\<omega> = x\<cdot>(x+y)\<^sup>\<omega>+z \<longrightarrow> (x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
nitpick --- no proof no refutation

same as in LOA3 and LOA1
*)

lemma omega_sum_unfold: "(x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<cdot>(x+y)\<^sup>\<omega>"
  by (metis eq_refl mult_onel mult_oner omega_coinduct_var2 antisym_conv omega_sum_unfold_ineq)

text {* This could not be proved or refuted in LOA3 and LOA1*}

(*
lemma omega_sum_unfold_coind: "(x+y)\<^sup>\<omega> \<le> (x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega>"
nitpick 
end--- no proof no refutation

same as LOA3 and LOA1
*)

(*
lemma omega_denest: "(x+y)\<^sup>\<omega> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega>"
nitpick -- no proof no refutation

same as LOA3 and LOA1
*)

(*
lemma omega_sum_refine: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<omega> \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<^sup>\<omega>"
nitpick  --- no proof no refutation

as in LOA3 and LOA1
*)

(*
lemma bachmair_dershowitz: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>  \<longrightarrow> ((x+y)\<^sup>\<omega> = 0 \<longleftrightarrow> x\<^sup>\<omega>+y\<^sup>\<omega> = 0)"
nitpick  --- no proof no refutation

as in LOA3 and LOA1
*)

(*
lemma ewp_neg_and_omega: "\<not>ewp(x) \<longleftrightarrow> x\<^sup>\<omega> = 0"
nitpick  -- 2-element counterexample

derivable in LOA1
*)

(*
lemma omega_super_id1: "\<not>(0 = 1) \<longrightarrow> ((1 \<le> x) \<longrightarrow> \<not> (x\<^sup>\<omega> = 0))"
nitpick --- 2-element counterexample

derivable in LOA1
*)

(*
lemma omega_super_id2: "\<not>(0 = 1) \<longrightarrow> ((x\<^sup>\<omega> = 0) \<longrightarrow> \<not>(1 \<le> x))"
nitpick  --- 2-element counterexample

derivable in LOA1
*)

(*
lemma arden's_lemma_var: "x\<^sup>\<omega> = 0 \<longrightarrow> z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z = y"
nitpick  --- 2-element counterexample

same as in LOA3, no proof or refutation in LOA1
*)

(*
lemma jules_24: "(x\<cdot>x)\<^sup>\<omega> = x\<^sup>\<omega>"
nitpick --- no proof no refutation

derivable in LOA1
*)

(*
lemma "x\<^sup>\<omega> \<le> x\<^sup>\<omega>\<cdot>x\<^sup>\<omega>"
nitpick --- 3-element counterexample

no proof or refutation in LOA1
*)

(*
lemma "x\<^sup>\<omega> \<le> (x\<^sup>\<omega>)\<^sup>\<omega>"
nitpick --- 3-element counterexample
*)

(*
lemma "x\<^sup>\<omega>\<cdot>x\<^sup>\<omega> \<le> (x\<^sup>\<omega>)\<^sup>\<omega>"
nitpick --- 4-element counterexample

no proof or refutation in LOA1
*)

(*
lemma "x\<^sup>\<omega>\<cdot>x\<^sup>\<omega> = (x\<^sup>\<omega>)\<^sup>\<omega> \<longrightarrow> x\<^sup>\<omega> = x\<^sup>\<omega>\<cdot>x\<^sup>\<omega>"
nitpick --- 3-element counterexample

no proof or refutation in LOA1
*)

text {* Unfortunately, there is no statement with a counterexample in
LOA1 that was derivable in LOA2. By this needs to be checked
again. Hence we cannot establish that LOA1 is not a subclass of LOA2.
*}

end

(************************************************************************)

context left_omega_algebra

begin

(*
lemma "x\<^sup>\<omega> \<le> x\<^sup>\<omega>\<cdot>x"
nitpick --- 4-element counterexample
*)

(*
lemma "x\<^sup>\<omega> \<le> x\<^sup>\<omega>\<cdot>x\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma "x\<^sup>\<omega> \<le> (x\<^sup>\<omega>)\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma "x\<^sup>\<omega>\<cdot>x\<^sup>\<omega> \<le> (x\<^sup>\<omega>)\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

(*
lemma "x\<^sup>\<omega>\<cdot>x\<^sup>\<omega> = (x\<^sup>\<omega>)\<^sup>\<omega> \<longrightarrow> x\<^sup>\<omega> = x\<^sup>\<omega>\<cdot>x\<^sup>\<omega>"
nitpick --- no proof no refutation
*)

end

text {* I can reproduce Jules' results, but it seems I don't get
anything beyond that. I need to check the details. *}


(***********************************************************************)

class omega_algebra = kleene_algebra + left_omega_algebra

begin

lemma "x = y\<cdot>x+z \<longrightarrow> (y\<^sup>\<star>\<cdot>z \<le> x \<and> x \<le> y\<^sup>\<omega>+y\<^sup>\<star>\<cdot>z)"
by (metis add_comm eq_refl omega_coinduct star_inductl_eq)

end
end






































