header {* Kleene Algebras *}

theory My_Kleene_Algebra
  imports Dioid
begin
(*
declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]
*)
(**************************************************************************)

section {* Left Near Kleene Algebras *}

text {*

Following the hierarchy oposed in Dioid.thy we now add a star
operation. Since a multiplicative unit is needed for defining the star
we only consider variants with $1$, but $0$ is added separately. We
consider the left star induction axiom and the right star induction
axiom independently since in some applications, e.g., Salomaa's axioms
or probabilistic Kleene algebras the right star induction axiom is not
valid or not needed.

We start with near dioid, then consider predioids and finally
dioids. It turns out that many of the known laws of Kleene algebras
hold already in much weaker settings.

*}

text {* We should replace the star by the asterate *}


class left_near_kleene_algebra = near_dioid_one + star_op +
  assumes star_unfoldl: "1+x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_inductl: "z+x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"


begin

lemma star_ref: "1 \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldl)

lemma star_plus_one: "x\<^sup>\<star> = 1+x\<^sup>\<star>"
  by (metis leq_def star_ref)

lemma star_trans: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_lub eq_iff star_inductl star_unfoldl)

lemma star_trans_eq: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis eq_iff mult_isor mult_onel  star_ref star_trans)

lemma star_1l: "x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldl)

(*
 lemma star_1l: "x\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  nitpick -- "2-element counterexample"
*)

lemma star_subid: "x \<le> 1 \<longrightarrow> x\<^sup>\<star> = 1"
  by (metis add_lub eq_iff mult_oner star_inductl star_ref)

lemma star_one: "1\<^sup>\<star> = 1"
  by (metis eq_iff star_subid)

lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  by (metis add_comm leq_def eq_iff star_inductl)

lemma star_inductl_var_equiv: "x\<cdot>y \<le> y \<longleftrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  by (metis eq_iff mult_assoc mult_isor mult_onel star_1l star_inductl_var star_ref)

lemma star_subdist:  "x\<^sup>\<star> \<le> (x+y)\<^sup>\<star>"
  by (metis add_lub distr star_1l star_ref star_inductl mult_oner)

lemma star_iso: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis leq_def star_subdist)

lemma star_invol: "x\<^sup>\<star> = (x\<^sup>\<star>)\<^sup>\<star>"
(*by (metis add_lub leq_symm_intro mult_oner star_1l star_inductl star_inductl_var_equiv star_ref)*)
proof -
  have "x\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
    by (metis add_assoc leq_def mult_oner star_1l star_inductl star_inductl_var_equiv star_one star_plus_one)
  thus ?thesis
    by (metis add_lub eq_iff mult_oner star_inductl star_inductl_var_equiv star_ref star_trans_eq)
qed

lemma star2: "(1+x)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis add_comm distr leq_def mult_onel mult_oner star_1l star_inductl star_invol star_ref star_subdist eq_iff)

lemma star_inductl_eq:  "z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"
by (metis eq_iff star_inductl)

lemma star_inductl_var_eq:  "x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
by (metis eq_iff star_inductl_var)

lemma star_inductl_var_eq2: "y=x\<cdot>y \<longrightarrow> y=x\<^sup>\<star>\<cdot>y"
  by (smt add_comm distr leq_def mult_onel star_inductl_var_eq star_plus_one)

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

text {* Further counterexamples should be given. *}

text {* The following facts express inductive conditions for the fact that $(x+y)^\ast$ is the greatest term that can be built from $x$ and $y$. These might be useful\<dots>
*}

lemma sum_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x+y \<le> z\<^sup>\<star>"
  by (metis add_lub) 

lemma prod_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x\<cdot>y \<le> z\<^sup>\<star>"
  by (metis leq_def order_refl order_trans star_inductl star_invol star_trans_eq subdistr)

lemma star_star_closure: "x\<^sup>\<star> \<le> z\<^sup>\<star> \<longrightarrow> (x\<^sup>\<star>)\<^sup>\<star> \<le> z\<^sup>\<star>"
  by (metis star_invol)

end

(******************************************************************************)

section {* Left Pre-Kleene Algebras *}

class left_pre_kleene_algebra = pre_dioid_one + left_near_kleene_algebra
begin

lemma star_ext: "x \<le> x\<^sup>\<star>"
  by (metis add_lub leq_def mult_oner star_unfoldl subdistl)

lemma star_unfoldr: "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  by (metis add_lub leq_def mult_oner star_inductl star_unfoldl subdistl)


lemma star_1r: "x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldr)

lemma star_sim1: "x\<cdot>z \<le> z\<cdot>y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> z\<cdot>y\<^sup>\<star>"
  by (smt add_comm add_lub distr leq_def mult_assoc mult_oner star_1l star_ext star_inductl star_invol star_iso star_ref subdistl)

text {* Z3 was much faster than Metis *}

text{* The next lemmas are used in omega algebras to prove, for instance, Bachmair and Dershowitz's separation of termination theorem. *}

(*
lemma quasicomm_var: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star> \<longleftrightarrow> y\<^sup>\<star>\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>"
sorry
*)
(*
  by (smt distr order_prop order_trans star_ext star_invol star_sim1)
*)

lemma star_slide1: "(x\<cdot>y)\<^sup>\<star>\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>\<star>"
    by (metis eq_iff mult_assoc star_sim1)

lemma star_slide_var1: "x\<^sup>\<star>\<cdot>x \<le> x\<cdot>x\<^sup>\<star>"
  by (metis le_less star_sim1)


lemma star_unfoldl_eq: " x\<^sup>\<star> = 1+x\<cdot>x\<^sup>\<star>"
    by (smt add_comm add_ub mult_isol order_trans star_unfoldl add_assoc idemo leq_def mult_oner star_inductl star_plus_one star_unfoldl eq_iff) 

text {* Z3 is very fast on the previous lemma. Metis couldn't finish
within reasonable time. Is Z3 better at isotonicity? *}

lemma star_rtc1: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_assoc' leq_def order_refl star_ext star_ref star_trans_eq)

lemma star_rtc1_eq: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis leq_def star2 star_ext star_trans_eq)

(*
lemma star_rtc2: "1+x+y\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
sorry
*)

(* metis could do it but needed a long time 
by (metis add_lub eq_iff mult_isol mult_oner star_ext star_inductl_var_equiv star_subdist)
*)

lemma star_rtc2_eq: "1+x+y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
  by (metis add_lub leq_def mult_oner star_inductl_var_equiv star_subdist subdistl)

lemma star_subdist_var_1: "x \<le> (x+y)\<^sup>\<star>"
by (metis add_lub star_ext)

lemma star_subdist_var_2: "x\<cdot>y \<le> (x+y)\<^sup>\<star>"
  by (metis add_lub mult_double_iso star_ext star_trans_eq)

lemma star_subdist_var_3: "x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<le> (x+y)\<^sup>\<star>"
  by (metis add_comm' mult_double_iso star_subdist star_trans_eq)

lemma star_denest: "(x+y)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
proof -
  have "(x+y)\<^sup>\<star> \<le> (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
    by (metis add_lub mult_onel mult_oner star_iso star_plus_one star_rtc1_eq subdistl subdistr)
  thus ?thesis
    by (metis star_invol star_iso star_subdist_var_3 eq_iff)
qed

lemma star_sum_var: "(x+y)\<^sup>\<star>  = (x\<^sup>\<star>+y\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_invol)

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

lemma star_denest_var_3: "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<cdot>(y\<^sup>\<star>\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_sum_var star_denest_var star_invol)

lemma star_denest_var_4:  "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = (y\<^sup>\<star>\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm' star_denest)

lemma star_denest_var_5: "x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star> = y\<^sup>\<star>\<cdot>(x\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm' star_denest_var)

lemma star_denest_var_6: "(x+y)\<^sup>\<star> = x\<^sup>\<star>\<cdot>y\<^sup>\<star>\<cdot>(x+y)\<^sup>\<star>"
  by (metis mult_assoc star_denest star_denest_var_3)

lemma star_denest_var_7: "(x+y)\<^sup>\<star> = (x+y)\<^sup>\<star>\<cdot>x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis add_assoc' leq_def less_le mult_assoc mult_oner star_1r star_denest star_plus_one strict_leq_def subdistl)

lemma star_denest_var_8: "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<cdot>y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
  by (metis mult_assoc star_denest_var_2 star_invol)

lemma star_denest_var_9: " (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>\<cdot>x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis star_denest star_denest_var_7)

text {* The following statements are well known from term rewriting. They are all variants of the Church-Rosser theorem. *}

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

lemma sup_id_star1: "1 \<le> x \<longrightarrow> x\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis add_comm distr leq_def mult_onel star_1l)

lemma sup_id_star2: "1 \<le> x \<longrightarrow> x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
  by (metis eq_iff mult_isol mult_oner star_1r)

(* lemma star_unfoldr_eq: "1+x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
nitpick -- "4-element counterexample" *)

(* lemma star_slide: "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
nitpick -- "3-element counterexample" *)

(* lemma boffa: "x\<cdot>x=x \<longrightarrow> x\<^sup>\<star>=1+x"
nitpick -- "3-element counterexample" *)

end

(*******************************************************************************)

section {* Left Kleene Algebras *}

text {* Different names have been given to these structures in the past, I think "left inductive" and "righthanded" by Kozen. Which one is the best? *}

class left_kleene_algebra = left_pre_kleene_algebra + dioid_one
begin

text {* The following fact is a good challenge for counterexample generators. A model of left Kleene algebras in which the right star induction law does not hold has been given by Kozen (Complete Semirings \<dots>).
*}

(* lemma star_inductr: "z+y\<cdot>x \<le> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"
nitpick -- "no counterexample found" *)

lemma star_unfoldr_eq: "1+x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>" 
  by (smt distl distr mult_assoc mult_onel mult_oner star_unfoldl_eq
  star_inductl_eq  eq_iff star_unfoldr)

lemma star_slide: "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  by (smt add_comm mult_assoc star_unfoldr_eq star_slide1 mult_isor add_iso mult_isol
     distl mult_oner distr mult_onel star_unfoldl_eq eq_iff star_slide1)

lemma star_slide_var: "x\<^sup>\<star>\<cdot>x = x\<cdot>x\<^sup>\<star>"
  by (metis mult_onel mult_oner star_slide)

lemma star_prod_unfold: "(x\<cdot>y)\<^sup>\<star> = 1+ x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y"
  by (metis mult_assoc star_slide star_unfoldl_eq)

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




(* for the following two lemmas I could neither find a counterexample
nor a proof. I assume these facts are not valid in left Kleene
algebras. I didn't try Nitpick with very long time bounds.

lemma star_sim2: "z\<cdot>x \<le> y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y\<^sup>\<star>\<cdot>z"

lemma star_sim3: "z\<cdot>x = y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<star> = y\<^sup>\<star>\<cdot>z"
*)



end

(****************************************************************************)

section {* Left Kleene Algebras with Zero *}

text {* There are applications where only a left zero is assumed, for
instance in the context of total correctness and for demonic refinement algebras. This section might therefore need further splitting. *}

(* class left_kleene_algebra_zerol = left_kleene_algebra + dioid_one_zerol *)

(* This one *)
class left_kleene_algebra_zero = left_kleene_algebra + dioid_one_zero
begin

lemma star_zero: "0\<^sup>\<star> = 1"
  by (metis min_zero star_subid)

text {* In principle, $1$ could therefore be defined from $0$ in this
setting. *}

end

section {* Pre-Kleene Algebras and Kleene Algebras *}

text {* Pre-Kleene algebras are essentially probabilistic Kleene
algebras. They have a weaker right star unfold axiom.  We are still
looking for theorems that could be proved in this setting *}

class pre_kleene_algebra = left_pre_kleene_algebra +
  assumes weak_star_unfoldr: "z+y\<cdot>(x+1) \<le> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"
begin

end

(****************************************************************************)

text {* Finally, here come the Kleene algebras \`a la Kozen. We only
prove quasi-identities in this section. All identities we could find
hold already without the right star induction axiom. It would be very
interesting to find identities for this section. *}

(* This one too *)
class kleene_algebra = left_kleene_algebra_zero +
  assumes star_inductr: "z+y\<cdot>x \<le> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"

(* The following sublocale proof doesn't terminate.

sublocale kleene_algebra \<subseteq> dual!: kleene_algebra
"op +" "op \<odot>"
proof
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult_assoc opp_mult_def)
  show "x + y + z = x + (y + z)"
    by (metis add_assoc')
  show  "x + y = y + x"
    by (metis add_comm')
  show  "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distl opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol')
  show "0 \<odot> x = 0"
    by (metis annil opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distr opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annir opp_mult_def)
  show "z \<odot> x \<le> z \<odot> (x + y)"
    by (metis mult_isor opp_mult_def order_prop)
  show "1 + 1 = 1"
    by (metis add_idem)
  show "1 + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis opp_mult_def order_refl star_slide_var star_unfoldl_eq)
  show "z + x \<odot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<odot> z \<le> y"
    by (metis opp_mult_def star_inductr)
  show "z + y \<odot> x \<le> y \<longrightarrow> z \<odot> x\<^sup>\<star> \<le> y"
    by (metis opp_mult_def star_inductl)
qed

context kleene_algebra
*)

begin

text {* The next lemma shows that the opposites of Kleene algebras are Kleene algebras *}

lemma (in kleene_algebra) dual_kleene_algebra:
  "class.kleene_algebra (op +) (op \<odot>) (op \<le>) (op <) 1 0 star" 
proof 
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult_assoc opp_mult_def)
  show "x + y + z = x + (y + z)"
    by (metis add_assoc')
  show  "x + y = y + x"
    by (metis add_comm')
  show  "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distl opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol')
  show "0 \<odot> x = 0"
    by (metis annil opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distr opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annir opp_mult_def)
  show "z \<odot> x \<le> z \<odot> (x + y)"
    by (metis mult_isor opp_mult_def order_prop)
  show "1 + 1 = 1"
    by (metis add_idem)
  show "1 + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis opp_mult_def order_refl star_slide_var star_unfoldl_eq)
  show "z + x \<odot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<odot> z \<le> y"
    by (metis opp_mult_def star_inductr)
  show "z + y \<odot> x \<le> y \<longrightarrow> z \<odot> x\<^sup>\<star> \<le> y"
    by (metis opp_mult_def star_inductl)
qed

lemma star_inductr_var: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
  by (metis add_lub order_refl star_inductr)

lemma star_inductr_var_equiv: "y\<cdot>x \<le> y \<longleftrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
  by (metis order_trans mult_isol star_ext star_inductr_var)

text {* The following law could be immediate if we had proper duality
for Kleene algebras. *}

lemma star_sim2: "z\<cdot>x \<le> y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y\<^sup>\<star>\<cdot>z"
sorry

(*
  by (smt add_comm add_lub distl leq_def mult_assoc mult_onel star_1r star_ext star_inductr star_invol star_iso star_ref subdistr)
*)

lemma star_sim3: "z\<cdot>x = y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<star> = y\<^sup>\<star>\<cdot>z"
  by (metis eq_iff star_sim1 star_sim2)

lemma star_sim4: "x\<cdot>y \<le>  y\<cdot>x \<longrightarrow> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<le> y\<^sup>\<star>\<cdot>x\<^sup>\<star>"
  by (metis star_sim1 star_sim2)

lemma star_inductr_eq: "z+y\<cdot> x= y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<le> y"
by (metis eq_iff star_inductr)

lemma star_inductr_var_eq: "y\<cdot>x = y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"
by (metis eq_iff star_inductr_var)

lemma star_inductr_var_eq2: "y\<cdot>x = y \<longrightarrow> y\<cdot>x\<^sup>\<star> = y"
  by (metis antisym_conv iso_subdist mult_isol mult_oner star_inductr_var_eq star_unfoldl_eq)

lemma bubble_sort:  "y\<cdot>x \<le> x\<cdot>y \<longrightarrow> (x+y)\<^sup>\<star> \<le> x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis church_rosser_eq_var order_refl star_sim4) 

lemma independence1: "x\<cdot>y = 0 \<longrightarrow> x\<^sup>\<star>\<cdot>y = y"
  by (metis annil mult_oner star_sim3 star_zero)

lemma independence2: "x\<cdot>y = 0 \<longrightarrow> x\<cdot>y\<^sup>\<star> = x"
  by (metis annir mult_onel star_sim3 star_zero)

lemma lazycomm_var: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>+y \<longleftrightarrow> y\<cdot>x\<^sup>\<star> \<le> x\<cdot>(x+y)\<^sup>\<star>+y"
proof - 
  have "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>+y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> x\<cdot>(x+y)\<^sup>\<star>+y"
sorry
(*
    by (smt add_assoc' distr add_comm' add_iso add_idem add_lub distl order_prop leq_def mult_assoc order_refl star_1r add_idem star_inductr)
*)
  thus ?thesis 
    by (metis mult_double_iso order_refl order_trans star_ext) 
qed

lemma arden: "\<forall> x z w.(\<forall>y v.(y \<le> x\<cdot>y+v \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>v)) \<longrightarrow> (z = x\<cdot>z+w \<longrightarrow> z = x\<^sup>\<star>\<cdot>w)"by (metis add_comm eq_iff star_inductl_eq)


lemma "(\<forall> x y.(y \<le> x\<cdot>y \<longrightarrow> y = 0)) \<longrightarrow> (\<forall> x y z. (y \<le> x\<cdot>y+z \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>z))"
by (metis eq_refl mult_onel)

(*
lemma "\<forall> x. ((\<forall> y.(y \<le> x\<cdot>y \<longrightarrow> y = 0)) \<longrightarrow> (\<forall> y z. (y \<le> x\<cdot>y+z \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>z)))"
nitpick --- no proof no refutation
*)

(*
lemma "(y \<le> x\<cdot>y \<longrightarrow> y = 0) \<longrightarrow> (y \<le> x\<cdot>y+z \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>z)"
nitpick --- 4-element counterexample
*)

end

end
