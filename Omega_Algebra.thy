header {* Omega Algebras *}


theory Omega_Algebra
  imports My_Kleene_Algebra
begin

section {* Left Omega Algebras *}

class left_omega_algebra = left_kleene_algebra_zero + omega_op +
  assumes omega_unfold: "x\<^sup>\<omega> \<le> x\<cdot>x\<^sup>\<omega>"
  and omega_coinduct: "y \<le> z+x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
begin

text {* In this section we consider omega algebras based on left Kleene algebras and on Kleene algebras. Surprisingly, we are still looking for statements which do not already hold in left omega algebras (mentioning omega). *}

lemma omega_unfold_eq: "x\<cdot>x\<^sup>\<omega> = x\<^sup>\<omega>" 
  by (metis add_zerol add_zeror annil eq_iff mult_isol omega_coinduct omega_unfold )

lemma omega_subdist: "x\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis add_comm add_zerol annil add_lub eq_iff mult_isor omega_coinduct omega_unfold_eq)

lemma omega_iso: "x \<le> y \<longrightarrow> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
  by (metis leq_def omega_subdist)

lemma omega_coinduct_var: "y \<le> x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>"
  by (metis add_zerol add_zeror annil omega_coinduct)

lemma omega_coinduct_eq: "y = z+x\<cdot>y \<longrightarrow> y \<le> x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
  by (metis omega_coinduct order_refl)

lemma zero_omega: "0\<^sup>\<omega> = 0"
  by (metis annir omega_unfold_eq)

lemma max_element: "x \<le> 1\<^sup>\<omega>"
  by  (metis eq_iff mult_onel omega_coinduct_var)

text {* The previous lemma shows that, in every omega algebra,
$1^\omega$ is the maximal element. We therefore give it another name
in the following definition *}

definition (in left_omega_algebra)
  top :: "'a" ("\<top>")
  where "\<top> = 1\<^sup>\<omega>"

lemma star_omega_1: "x\<^sup>\<star>\<cdot>x\<^sup>\<omega>  = x\<^sup>\<omega>"
  by (metis antisym_conv mult_isor omega_unfold_eq star_ext star_inductl_var_eq)

lemma star_omega_3: "(x\<^sup>\<star>)\<^sup>\<omega>  = \<top>"
  by (metis eq_iff max_element omega_iso star_ref top_def)

lemma omega_1: "x\<^sup>\<omega>\<cdot>y \<le> x\<^sup>\<omega>"
  by (metis eq_iff mult_assoc omega_coinduct_var omega_unfold_eq)

lemma omega_top: "x\<^sup>\<omega>\<cdot>\<top> = x\<^sup>\<omega>" 
  by (metis add_comm distl leq_def max_element mult_oner omega_1 top_def) 

(*
lemma "x\<^sup>\<omega>\<cdot>y = x\<^sup>\<omega>"
nitpick -- 2-element counterexample
*)

lemma supid_omega:"1 \<le> x \<longrightarrow> x\<^sup>\<omega> = \<top>"
  by (metis eq_iff max_element omega_iso top_def)

(*
lemma "x\<^sup>\<omega> = \<top> \<longrightarrow> 1 \<le> x"
nitpick --- 4-element counterexample
*)

lemma omega_simulation: "z\<cdot>x \<le> y\<cdot>z \<longrightarrow> z\<cdot>x\<^sup>\<omega> \<le> y\<^sup>\<omega> "
  by (smt mult_assoc mult_isor omega_coinduct_var omega_unfold_eq)

lemma omega_omega: "(x\<^sup>\<omega>)\<^sup>\<omega> \<le>x\<^sup>\<omega>"
  by (metis omega_1 omega_unfold_eq)

text {* The next lemmas are axioms of Wagner's complete axiomatisation for omega-regular languages. *} 

lemma wagner_1: "(x\<cdot>x\<^sup>\<star>)\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis eq_iff mult_assoc omega_coinduct_var omega_unfold_eq star2 star_invol star_omega_1 star_unfoldl_eq annir min_zero mult_onel omega_iso star_sim1 star_zero)

lemma wagner_2: "x\<cdot>(y\<cdot>x)\<^sup>\<omega>=(x\<cdot>y)\<^sup>\<omega>"
  by (metis omega_unfold_eq mult_isol eq_iff mult_assoc omega_simulation eq_iff mult_assoc)


text {* This identity is called (A8) in Wagner's paper. *}

lemma wagner_3: "(x+y)\<^sup>\<omega> = x\<cdot>(x+y)\<^sup>\<omega>+z \<longrightarrow> (x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>z"
  by (metis add_comm add_lub eq_iff omega_coinduct omega_subdist star_inductl)

text {* This identity is called (R4) in Wagner's paper. *}

lemma wagner_1_var: "(x\<^sup>\<star>\<cdot>x)\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis star_slide_var wagner_1)

lemma wagner_1_gen:  "(x\<cdot>y\<^sup>\<star>)\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (smt add_lub distr mult_double_iso mult_onel omega_iso order_prop star_denest star_ext star_plus_one wagner_1)

lemma wagner_1_var_gen:  "(x\<^sup>\<star>\<cdot>y)\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis distl add_lub mult_isor star_subdist omega_iso wagner_1 star_slide_var)

lemma star_omega_4: "(x\<^sup>\<omega>)\<^sup>\<star>  = 1+x\<^sup>\<omega> "
  by (metis annir antisym_conv min_zero mult_onel omega_1 star_sim1 star_unfoldl_eq star_zero)

lemma star_omega_5: "x\<^sup>\<omega>\<cdot>(x\<^sup>\<omega>)\<^sup>\<star> = x\<^sup>\<omega>"
  by (metis eq_iff mult_isol mult_oner omega_1 star_ref)

lemma omega_sum_unfold: "(x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<cdot>(x+y)\<^sup>\<omega>"
  by (metis distr mult_assoc omega_unfold_eq wagner_3)

text {* The next two lemmas apply induction and coinduction to this law. *}

lemma omega_sum_unfold_coind: "(x+y)\<^sup>\<omega> \<le> (x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega>"
  by (metis eq_iff mult_assoc omega_coinduct omega_sum_unfold)

lemma omega_sum_unfold_ind: "(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega> \<le> (x+y)\<^sup>\<omega>"
  by (metis omega_sum_unfold star_inductl_eq)

lemma omega_denest: "(x+y)\<^sup>\<omega> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<omega>+(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<omega>"
  by  (metis omega_sum_unfold_coind  wagner_1_var_gen omega_sum_unfold_ind add_lub eq_iff)

text {* The next lemma yields a separation theorem for infinite
iteration. A nondeterministic loop over $x$ and $y$ can be refined
into separate infinite loops over $x$ and $y$. *}

lemma omega_sum_refine: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star> \<longrightarrow> (x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<^sup>\<omega>"
proof 
  assume  "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>"
  hence  "(x+y)\<^sup>\<omega> \<le> x\<cdot>(x+y)\<^sup>\<star>\<cdot>(x+y)\<^sup>\<omega>+y\<^sup>\<omega>"
    by (smt add_comm mult_assoc omega_sum_unfold quasicomm_var mult_isor add_iso) 
  thus  "(x+y)\<^sup>\<omega> = x\<^sup>\<omega>+x\<^sup>\<star>\<cdot>y\<^sup>\<omega>"
    by (metis mult_assoc star_omega_1 add_lub omega_subdist omega_unfold_eq subdistr eq_iff wagner_3)
qed



text {* The following theorem by Bachmair and Dershowitz is a corollary *}

lemma bachmair_dershowitz: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>  \<longrightarrow> ((x+y)\<^sup>\<omega> = 0 \<longleftrightarrow> x\<^sup>\<omega>+y\<^sup>\<omega> = 0)"
  by (metis add_comm' annil no_trivial_inverse omega_sum_refine omega_sum_unfold)

text {* The next lemmas consider an abstract variant of the empty word property from language theory and match it with absence of infinite iteration *}

definition  (in dioid_one_zero) 
  ewp :: "'a \<Rightarrow> bool"
  where "ewp(x) \<longleftrightarrow> \<not>(\<forall>y.((y \<le> x\<cdot>y) \<longrightarrow> (y = 0)))"

text{* This propery has also been called "definiteness" by Backhouse
and Carr\'e *}

lemma ewp_super_id1: "\<not>(0 = 1) \<longrightarrow> ((1 \<le> x) \<longrightarrow> ewp(x))"
  by (metis ewp_def mult_oner)

lemma ewp_super_id2: "\<not>(0 = 1) \<longrightarrow> (\<not>ewp(x) \<longrightarrow> \<not>(1 \<le> x))"
  by (metis ewp_super_id1)  

lemma ewp_neg_and_omega: "\<not>ewp(x) \<longleftrightarrow> x\<^sup>\<omega> = 0"
  by (metis add_comm add_zerol ewp_def leq_def eq_iff omega_coinduct_var omega_unfold_eq)

lemma ewp_alt1: "(\<forall> z. (x\<^sup>\<omega> \<le> x\<^sup>\<star>\<cdot>z)) \<longleftrightarrow> (\<forall> y z. (y \<le> x\<cdot>y+z \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>z))"
  by (metis add_comm add_ub leq_def omega_coinduct omega_unfold_eq)


lemma ewp_alt: "x\<^sup>\<omega> = 0 \<longleftrightarrow> (\<forall> y z. (y \<le> x\<cdot>y+z \<longrightarrow> y \<le> x\<^sup>\<star>\<cdot>z))"
by (metis add_comm annil eq_iff leq_def min_zero omega_coinduct omega_unfold_eq)

text {* So we got a nice KA condition for Arden's lemma. The proof is in the KA file... *}

lemma omega_super_id1: "\<not>(0 = 1) \<longrightarrow> ((1 \<le> x) \<longrightarrow> \<not> (x\<^sup>\<omega> = 0))"
  by (metis eq_iff max_element min_zero omega_iso)

lemma omega_super_id2: "\<not>(0 = 1) \<longrightarrow> ((x\<^sup>\<omega> = 0) \<longrightarrow> \<not>(1 \<le> x))"
  by (metis omega_super_id1)  

text {* The next lemma is an abstract version of Arden's lemma from
language theory *}

lemma arden's_lemma: "\<not>ewp(x) \<longrightarrow> z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z = y"
  by (metis add_zerol ewp_neg_and_omega eq_iff antisym_conv omega_coinduct star_inductl)

lemma arden's_lemma_var: "x\<^sup>\<omega> = 0 \<longrightarrow> z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z = y"
  by (metis add_zerol eq_iff antisym_conv omega_coinduct star_inductl)

lemma arden's_lemma_equiv: "\<not>ewp(x) \<longrightarrow> (z+x\<cdot>y = y \<longleftrightarrow> x\<^sup>\<star>\<cdot>z = y)"
  by (metis arden's_lemma distr mult_assoc mult_onel star_unfoldl_eq)

lemma arden's_lemma_var_equiv: "x\<^sup>\<omega> = 0 \<longrightarrow> (z+x\<cdot>y = y \<longleftrightarrow> x\<^sup>\<star>\<cdot>z = y)"
  by (metis arden's_lemma_var distr mult_assoc mult_onel star_unfoldl_eq)

lemma arden_conv1: "(\<forall>y.\<forall>z.(z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z = y)) \<longrightarrow> \<not>ewp(x)"
  by (metis add_zerol annil ewp_neg_and_omega omega_unfold_eq)

lemma arden_conv2: "(\<forall>y.\<forall>z.(z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z = y)) \<longrightarrow> x\<^sup>\<omega> = 0"
  by (metis add_zerol annil omega_unfold_eq)

lemma arden_var3: "(\<forall>y.\<forall>z.(z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z = y)) \<longleftrightarrow> x\<^sup>\<omega> = 0"
  by (metis add_zerol annil arden's_lemma_var omega_unfold_eq)

text {* The following lemmas are from Kleene alegebra and should perhaps be located there. I put them here because, like Arden's lemma, they deal with solvability of equations *}

lemma arden_sol1: "(1 \<le> x \<and> z \<le> w) \<longrightarrow> x\<cdot>x\<^sup>\<star>\<cdot>w+z =  x\<^sup>\<star>\<cdot>w"
  by (metis add_comm leq_def mult_assoc mult_isor mult_onel order_trans star_ext sup_id_star1)

end

(***********************************************************************)

class omega_algebra = kleene_algebra + left_omega_algebra

begin

end
end






































