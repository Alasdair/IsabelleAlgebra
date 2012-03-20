header {* Examples of Forward Modal Semirings *}

theory FModal_Examples
  imports Domain_Semiring
begin

context fmodal_kleene_algebra
begin

section {* A Reachability Algorithm *}

text {* We first prove a refined reachability algorithm *}

lemma opti_iterate_var: "\<bar>x\<^sup>\<star>\<rangle>d(y) = \<bar>(a(y)\<cdot>x)\<^sup>\<star>\<rangle>d(y)"
proof -
  have "\<bar>x\<rangle>(\<bar>(a(y)\<cdot>x)\<^sup>\<star>\<rangle>d(y)) \<le> \<bar>(a(y)\<cdot>x)\<^sup>\<star>\<rangle>d(y)"
    by (smt fdia_split fdia_export_2 a_subid antidomain_semiring_domain_def fdiamond_def mult_isol mult_oner add_iso fdia_star_unfold_var_2)
  hence "\<bar>x\<^sup>\<star>\<rangle>d(y) \<le> \<bar>(a(y)\<cdot>x)\<^sup>\<star>\<rangle>d(y)"
    by (smt annil d2 domain_iso fdiamond_def min_zero mult_oner star_sim2 star_zero add_lub  fdia_star_induct fdia_simp_2) 
  thus ?thesis 
    by (smt a_zero annil dia_iso_var domain_very_strict kat_1_equiv_opp min_zero mult_oner star_iso eq_iff)
qed

lemma opti_iterate: "\<bar>x\<^sup>\<star>\<rangle>d(y) = d(y)+\<bar>(x\<cdot>a(y))\<^sup>\<star>\<rangle>(\<bar>x\<rangle>d(y))"
  by (smt opti_iterate_var a2_eq antidomain_semiring_domain_def fdia_star_unfold_var fdiamond_def opti_iterate_var  fdia_mult star_slide)

lemma opti_iterate_var_2: "\<bar>x\<^sup>\<star>\<rangle>d(y) = d(y)+\<bar>a(y)\<cdot>x\<rangle>(\<bar>x\<^sup>\<star>\<rangle>d(y))"
  by (smt a2_eq a_add a_export antidomain_semiring_domain_def d_7 fdia_star_unfold_var fdiamond_def mult_assoc)


section {* The Segerberg Formula *}

text {* We first define those states of $p$ for which all $x$ actions come from the outside. *}

definition Alpha :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("A")
  where "A x p = d(x\<cdot>p)\<cdot>a(p)"

lemma  A_dom: "A x p = d(A x p)"
  by (smt Alpha_def a_add a_closure antidomain_semiring_domain_def)

lemma A_fdia:  "A x p = (\<bar>x\<rangle>p)\<cdot>a(p)"
  by (smt Alpha_def fdiamond_def)

lemma A_fdia_var:  "A x p = (\<bar>x\<rangle>d(p))\<cdot>a(p)"
  by (smt A_fdia fdia_simp)

lemma a_A: "a(A x (a(p))) =  (\<bar>x]d(p))+a(p)"
  by (smt A_fdia add_comm' antidomain_semiring_domain_def fbox_add2 fbox_dom fbox_export_1 fbox_simp_2 fdia_fbox)

text {* We can now prove Segerberg's formula *}

lemma fsegerberg: "\<bar>x\<^sup>\<star>\<rangle>d(y) = d(y)+\<bar>x\<^sup>\<star>\<rangle>(A x y)"
proof -
  have  "\<bar>x\<^sup>\<star>\<rangle>d(y) \<le> d(y)+\<bar>x\<^sup>\<star>\<rangle>(A x y)"
    by (smt fdia_simp  fdia_add1 add_assoc  a_closure antidomain_semiring_domain_def d_6 dom_el_comm  fdia_simp_2  A_fdia_var  fdia_star_unfold_var A_dom a_export fdiamond_def  fdia_star_induct_eq d5 domain_invol)
  thus ?thesis  
    by (smt A_fdia fdia_subdist_2 fdia_simp_2 a_closure add_iso add_comm fdia_star_unfoldr_var fdia_simp eq_iff)
qed

lemma fbox_segerberg: "\<bar>x\<^sup>\<star>]d(y) = d(y)\<cdot>\<bar>x\<^sup>\<star>]((\<bar>x]d(y))+a(y))"
(*
sledgehammer (fdia_simp fdia_simp_2 fbox_simp fbox_simp_2 a_closure a_5 dom_add_closed dom_mult_closed a_antitone a_de_morgan_var_1 a_de_morgan_var_2 a_de_morgan_var_3 a_de_morgan_var_4 fdia_fbox fbox_fdia a_one a_zero fbox_fdia_de_morgan_1 fdia_fbox_de_morgan_2  antidomain_semiring_domain_def a_A fsegerberg )
sledgehammer minimize [atp = remote_vampire] (a_A a_closure a_de_morgan_var_2 antidomain_semiring_domain_def fbox_simp fbox_simp_2 fdia_fbox fdia_simp fsegerberg)
*)
  by (smt a_A a_closure a_de_morgan_var_2 antidomain_semiring_domain_def fbox_simp_2 fdia_fbox fsegerberg)

(* lemma separability_extensionality: "(\<forall>p.\<bar>x\<rangle>p = \<bar>y\<rangle>p) \<longrightarrow> x = y"
nitpick -- nitpick found 3-element counterexample
*)

section {* Wellfoundedness and Loeb's Formula *}

text {* We now prove some facts about wellfoundedness *}

definition Omega :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<Omega>")
  where "\<Omega> x p = d(p)\<cdot>a(x\<cdot>p)"

text {* If $y$ is a set, then $\Omega(x,y)$ describes those elements
in $y$ from which no further $x$ transitions are possible
 *}

lemma omega_fdia: "\<Omega> x p = d(p)\<cdot>a(\<bar>x\<rangle>p)"
  by (smt Omega_def a_5 fdiamond_def)

lemma omega_le_1: "\<Omega> x p \<le> d(p)"
  by (smt Omega_def a_4 a_6 a_closure antidomain_semiring_domain_def d_a_galois1)

lemma omega_le_2: "\<Omega> x p \<le> a(\<bar>x\<rangle>p)"
  by (smt Omega_def a2_eq a_closure a_one a_zero annil antidomain_semiring_domain_def fbox_def fdia_fbox kat_1_equiv_opp min_zero mult_oner)

lemma omega_dom: "\<Omega> x p = d(\<Omega> x p)"
  by (smt Omega_def a_add a_de_morgan_var_3 antidomain_semiring_domain_def d5)

lemma omega_fbox: "\<Omega> x p = d(p)\<cdot>\<bar>x]a(p)"
  by (smt Omega_def a2_eq antidomain_semiring_domain_def fbox_def)

text {* The next lemma says that the states in $p$ that are non-final
are those from which there is an $x$-transition into $p$ *}

lemma a_omega: "a(\<Omega> x p) = a(p)+\<bar>x\<rangle>p"
  by (smt Omega_def a2_eq a_6 antidomain_semiring_domain_def fbox_def fdia_fbox)

lemma omega_fdia_3: "d(p)\<cdot>a(\<Omega> x p) = d(p)\<cdot>\<bar>x\<rangle>p"
  by (smt a_omega distl  a_comp_1 add_zerol')

text {* The next lemma says that if $p$ has n $x$-final states, then
$p$ is contained in the set of states from which there are
$x$-transitions into $p$. *}

lemma omega_zero_equiv_1: 
  "(\<Omega> x p) = 0 \<longleftrightarrow> d(p) \<le> \<bar>x\<rangle>p"
  by (smt a_gla antidomain_semiring_domain_def fdia_simp_2 omega_fdia)

text {* Next we define a variant of L\"ob's formula *}

definition Loebian :: "'a \<Rightarrow> bool"
  where  "Loebian(x) = (\<forall>p.\<bar>x\<rangle>p \<le> \<bar>x\<rangle>(\<Omega> x p))"

definition PreLoebian :: "'a \<Rightarrow> bool"
  where  "PreLoebian(x) = (\<forall>p.(d(p) \<le> \<bar>x\<^sup>\<star>\<rangle>(\<Omega> x p)))"

text {* Next we define Noethericity *}

definition Noetherian :: "'a \<Rightarrow> bool"
  where  "Noetherian(x) = (\<forall>p.(\<Omega> x p) = 0 \<longrightarrow> d(p) = 0)"

lemma noetherian_alt: 
  "Noetherian(x) \<longleftrightarrow> (\<forall>p.(d(p) \<le> \<bar>x\<rangle>p \<longrightarrow> d(p) = 0))"
  by (smt Noetherian_def a_gla antidomain_semiring_domain_def fdia_simp_2 omega_fdia)

text {* We now relate the three properties *}

lemma Noetherian_iff_PreLoebian: "Noetherian(x) = PreLoebian(x)"
proof
  assume hyp: "Noetherian(x)"
  have "\<forall>p.(d(p)\<cdot>a(\<bar>x\<^sup>\<star>\<rangle>(\<Omega> x p)) \<le> \<bar>x\<rangle>(d(p)\<cdot>a(\<bar>x\<^sup>\<star>\<rangle>(\<Omega> x p))))"
    by (smt omega_dom fdia_star_unfold_var_2 a_7 fdia_simp_2 omega_fdia_3 dom_subid mult_onel mult_isor dia_diff order_trans)
  with hyp show "PreLoebian(x)"
    by (smt noetherian_alt a_closure dom_mult_closed d_a_zero fdia_simp_2  PreLoebian_def)
next
  show "PreLoebian(x) ==> Noetherian(x)"
    by (smt Noetherian_def PreLoebian_def add_comm' add_zerol' fdia_zero leq_def)
qed

lemma Loebian_imp_Noetherian: "Loebian(x) \<Longrightarrow> Noetherian(x)"
  by (smt Loebian_def Noetherian_def Omega_def a_zero dom_weakly_local domain_very_strict fdemodalisation2 fdia_zero mult_onel mult_oner)

lemma d_transitive: "\<bar>x\<rangle>(\<bar>x\<rangle>p) \<le> \<bar>x\<rangle>p \<longrightarrow> \<bar>x\<rangle>p = \<bar>x\<^sup>\<star>\<rangle>\<bar>x\<rangle>p" 
    by (smt fdia_star_induct_var fdiamond_def domain_iso fdia_simp mult_assoc mult_isor mult_oner star_plus_one star_slide_var subdistl eq_iff)

lemma d_transitive_PreLoebian_imp_Loebian: 
  "\<lbrakk>(\<forall>p.\<bar>x\<rangle>(\<bar>x\<rangle>p) \<le> \<bar>x\<rangle>p);  PreLoebian(x)\<rbrakk> \<Longrightarrow> Loebian(x)"
  by (smt PreLoebian_def fdia_iso fdia_mult fdiamond_def mult_assoc star_slide_var d_transitive  Loebian_def)

lemma d_transitive_Noetherian_iff_Loebian: 
  "\<lbrakk>\<forall>p.\<bar>x\<rangle>(\<bar>x\<rangle>p) \<le> \<bar>x\<rangle>p\<rbrakk> \<Longrightarrow> (Noetherian(x) = Loebian(x))"
  by (smt Loebian_imp_Noetherian Noetherian_iff_PreLoebian d_transitive_PreLoebian_imp_Loebian)

lemma Loeb_iff_box_Loeb: "(\<forall>y.\<bar>x\<rangle>y \<le> \<bar>x\<rangle>(\<Omega> x y)) = (\<forall>p.\<bar>x](a(\<bar>x]d(p))+d(p)) \<le> \<bar>x]d(p))"
  by  (smt a_antitone fdia_fbox_de_morgan_2 antidomain_semiring_domain_def a_omega fbox_fdia_de_morgan_1 add_comm fbox_simp a_closure fbox_fdia_de_morgan_1 a_de_morgan_var_2 fdia_simp omega_fdia dom_el_comm)

end

section {* Divergence Kleene Algebras and Separation of Termination *}

class fdivergence_kleene_algebra = fmodal_kleene_algebra + nabla_op +
  assumes nabla_closure:  "d(\<nabla>(x)) = \<nabla>(x)"
  and nabla_unfold: "\<nabla>(x) \<le> \<bar>x\<rangle>(\<nabla>(x))"
  and nabla_coinduction: "d(y) \<le> (\<bar>x\<rangle>d(y))+d(z) \<longrightarrow> d(y) \<le> (\<nabla>(x))+\<bar>x\<^sup>\<star>\<rangle>d(z)" 

begin

lemma nabla_coinduction_var: "d(y) \<le> \<bar>x\<rangle>d(y) \<longrightarrow> d(y) \<le> \<nabla>(x)" 
  by (smt a_one a_zero add_zeror antidomain_semiring_domain_def nabla_coinduction fdia_zero add_zeror)

lemma nabla_unfold_eq:  "\<bar>x\<rangle>(\<nabla>(x)) = \<nabla>(x)"
  by (smt fdia_iso nabla_closure nabla_unfold fdia_simp_2 nabla_coinduction_var nabla_unfold eq_iff)

lemma nabla_subdist: "\<nabla>(x) \<le> \<nabla>(x+y)"
  by (smt dia_iso_var nabla_closure nabla_unfold_eq order_prop nabla_coinduction_var)

lemma nabla_iso: "x \<le> y \<longrightarrow> \<nabla>(x) \<le> \<nabla>(y)"
  by (metis leq_def nabla_subdist)

lemma nabla_omega: "\<Omega> x (d y) = 0 \<longrightarrow> d(y) \<le> \<nabla>(x)"
  by (smt omega_fdia domain_invol d_a_zero fdia_simp_2 nabla_coinduction_var)

lemma nabla_noether: "\<nabla>(x) = 0 \<Longrightarrow> Noetherian(x)"
  by (smt Noetherian_def add_comm' add_zerol' fdia_simp leq_def nabla_coinduction_var omega_zero_equiv_1)

lemma nabla_preloeb: "\<nabla>(x) = 0 \<Longrightarrow> PreLoebian(x)"
  by (smt Noetherian_iff_PreLoebian nabla_noether)

lemma star_nabla_1: "\<bar>x\<^sup>\<star>\<rangle>(\<nabla> x)  = (\<nabla> x)"
    by (smt d_transitive nabla_unfold_eq order_refl eq_iff)

lemma separation_of_termination: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>+y \<Longrightarrow> (((\<nabla> x)+(\<nabla> y) = 0) = (\<nabla>(x+y) = 0))"
proof 
  assume lazycomm: "y\<cdot>x \<le> x\<cdot>(x+y)\<^sup>\<star>+y" and  xy_wf: "(\<nabla> x)+(\<nabla> y) = 0"
  hence "\<nabla>(x+y) \<le> (\<bar>x\<rangle>(\<nabla>(x+y))) + \<bar>y\<rangle>(\<bar>x\<^sup>\<star>\<rangle>(\<Omega> x (\<nabla>(x+y))))"
    by (smt fdia_add2 nabla_unfold_eq no_trivial_inverse nabla_preloeb PreLoebian_def nabla_closure fdia_iso fdia_simp_2 add_iso add_comm)
  hence "\<nabla>(x+y) \<le> (\<bar>x\<rangle>(\<nabla>(x+y))) + (\<bar>x\<rangle>(\<bar>(x+y)\<^sup>\<star>\<rangle>(\<Omega> x (\<nabla>(x+y)))))  + \<bar>y\<rangle>(\<Omega> x (\<nabla>(x+y)))"  using lazycomm
    by (smt lazycomm_var dia_iso_var add_iso add_comm add_assoc' fdia_add2 fdia_mult order_prop)
  hence "\<nabla>(x+y) \<le> (\<bar>x\<rangle>(\<nabla>(x+y))) + \<bar>y\<rangle>(\<Omega> x (\<nabla>(x+y)))"
    by (smt add_comm add_iso domain_iso fdia_iso nabla_closure omega_le_1 star_nabla_1 add_idem order_trans)
  with xy_wf show "\<nabla>(x+y) = 0"
    by (smt domain_iso d5 d_a_galois1 add_comm omega_fdia fdia_simp_2  no_trivial_inverse nabla_noether noetherian_alt omega_dom Noetherian_def nabla_closure)
next 
show "\<nabla>(x+y) = 0 \<Longrightarrow> (\<nabla> x)+(\<nabla> y) = 0"
  by (smt add_comm' add_zerol' antisym_conv min_zero nabla_subdist)
qed

end

section {* A PDL Textbook Exercise *}

context fmodal_kleene_algebra
begin

text {* For showing the left-to-right inclusion we first derive two equations that espress the modalities of the left-hand side in terms of each other.*}

lemma meyer_aux_1: "(\<bar>(x\<cdot>x)\<^sup>\<star>]d(p)) = d(p)\<cdot>\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>](\<bar>x]d(p))"
  by (smt fbox_mult fbox_simp fbox_star_unfold_var star_slide)

lemma meyer_aux_2: "(\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]d(p)) = \<bar>(x\<cdot>x)\<^sup>\<star>](\<bar>x]d(p))"
  by (smt fbox_mult star_slide)

text {* This yields the following solutions for the lhs *}

lemma meyer_aux_3: "(\<bar>(x\<cdot>x)\<^sup>\<star>]d(p))\<cdot>(\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]a(p)) = d(p)\<cdot>\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>](a(p)\<cdot>\<bar>x]d(p))"
  by (smt meyer_aux_1 mult_assoc fbox_add1 fbox_simp_2 a_closure dom_el_comm)

lemma meyer_aux_4: "(\<bar>(x\<cdot>x)\<^sup>\<star>]d(p))\<cdot>(\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]a(p)) = \<bar>(x\<cdot>x)\<^sup>\<star>](d(p)\<cdot>\<bar>x]a(p))"
by (smt meyer_aux_2 fbox_add1 fbox_simp fbox_simp_2)

text {* The tests in the rhss can now be merged *}

lemma meyer_aux_5: "(\<bar>(x\<cdot>x)\<^sup>\<star>]d(p))\<cdot>(\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]a(p)) \<le> d(p)\<cdot>\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]((a(p)+\<bar>x]a(p))\<cdot>(d(p)+\<bar>x]d(p)))"
by (smt  add_comm' mult_double_iso order_prop domain_iso fbox_iso mult_isol meyer_aux_3)

lemma meyer_aux_6: "(\<bar>(x\<cdot>x)\<^sup>\<star>]d(p))\<cdot>(\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]a(p)) \<le> \<bar>(x\<cdot>x)\<^sup>\<star>]((a(p)+\<bar>x]a(p))\<cdot>(d(p)+\<bar>x]d(p)))"
by (smt  add_comm' mult_double_iso order_prop domain_iso fbox_iso meyer_aux_4 fbox_simp_2 dom_el_comm)

lemma meyer_ineq_1: "(\<bar>(x\<cdot>x)\<^sup>\<star>]d(p))\<cdot>(\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]a(p)) \<le> d(p)\<cdot>\<bar>x\<^sup>\<star>]((a(p)+\<bar>x]a(p))\<cdot>(d(p)+\<bar>x]d(p)))"
proof -
have "(\<bar>(x\<cdot>x)\<^sup>\<star>]d(p))\<cdot>(\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]a(p)) \<le>  d(p)\<cdot>\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]((a(p)+\<bar>x]a(p))\<cdot>(d(p)+\<bar>x]d(p))) \<cdot> \<bar>(x\<cdot>x)\<^sup>\<star>]((a(p)+\<bar>x]a(p))\<cdot>(d(p)+\<bar>x]d(p)))"
by (metis meyer_aux_5 meyer_aux_6 mult_double_iso dom_el)

lemma meyer_2: "(\<bar>(x\<cdot>x)\<^sup>\<star>]d(p))\<cdot>(\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]a(p)) = d(p)\<cdot>\<bar>x\<^sup>\<star>]((a(p)+\<bar>x]a(p))\<cdot>(d(p)+\<bar>x]d(p)))"
sorry


end

end

