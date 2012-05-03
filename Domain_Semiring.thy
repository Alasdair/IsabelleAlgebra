header {* Domain Semirings *}

theory Domain_Semiring
  imports My_Kleene_Algebra
begin

section {* Domain Semirings *}

text {* It is important to prove a dual statement for range semirings
with each statement for domain semirings! Perhaps, in the future,
these dual statements will be generated\<dots> *}


text{* We only consider domain semirings over semirings (and dioids)
with one and zero. A more refined hierarchy can of course be
obtained. We have already defined domain over near semirings and
pre-semirings with and without units. All this should eventually be
included.  *}

class domain_semiring = semiring_one_zero + plus_ord + d_op +
  assumes d1: "x+(d(x)\<cdot>x) = d(x)\<cdot>x"
  and d2: "d(x\<cdot>y) = d(x\<cdot>d(y))"
  and d3: "d(x)+1 = 1"
  and d4: "d(0) = 0"
  and d5: "d(x+y) = d(x)+d(y)"

begin

text {* We first show that every domain semiring is "automatically"
idempotent, hence a dioid *}

subclass dioid_one_zero
proof
  fix x y z :: 'a
  show "x+x = x"
    by (metis add_comm' d1 d3 distl mult_oner)
qed

lemma d1_eq: "x = d(x)\<cdot>x"
  by (metis d1 d3 eq_iff leq_def mult_isor mult_onel)

lemma domain_invol: "d(d(x)) = d(x)"
  by (metis d1_eq d2 mult_assoc)

text {* The next lemma formulates the fixed point lemma without
sets. It states that $x$ is a domain element (of some element $y$ if
and only if $x=d(x)$. *}

lemma domain_fixed_point: "(\<exists>y.(x = d(y))) \<longleftrightarrow> x = d(x)"
  by (metis domain_invol)

text {* One can now use $x=d(x)$ for typing domain elements. The next
lemma shows that two different ways of typing domain elements are
equivalent *}

lemma type_conv: "\<forall>P.(\<forall>x.(x = d(x) \<longrightarrow> P(x))) \<longleftrightarrow> (\<forall>x.(P(d(x))))"
  by (metis domain_invol) 

text {* We now continue proving properties. *}

lemma domain_1: "d(x\<cdot>y) \<le> d(x)"
  by (metis d2 d3 d5 distl leq_def mult_oner)

lemma domain_subid: "x \<le> 1 \<longrightarrow> x \<le> d(x)"
  by (metis d1_eq mult_isol mult_oner)

lemma domain_very_strict: "d(x) = 0 \<longleftrightarrow> x = 0"
  by (metis annir d1_eq d4)

lemma domain_one: "d(1) = 1"
  by (metis d1_eq mult_oner)

lemma dom_subid: "d(x) \<le> 1"
  by (metis domain_1 domain_one mult_onel)

lemma domain_iso: "x \<le> y \<longrightarrow> d(x) \<le> d(y)"
  by (metis d5 leq_def)

lemma domain_subdist: "d(x) \<le> d(x+y)"
  by (metis domain_iso order_prop)

lemma domain_export: "d(d(x)\<cdot>y) = d(x)\<cdot>d(y)"
(*
by (metis d1_eq d2 domain_1 domain_subdist leq_def leq_symm_intro mult_isol mult_isor mult_onel mult_oner)
*)
proof -
  have "d(d(x)\<cdot>y) \<le> d(x)\<cdot>d(y)"
    by (metis d1_eq d3 domain_1 domain_invol domain_iso mult_double_iso mult_onel subdistr)
  thus ?thesis 
    by (metis add_lub d2 distl domain_1 domain_one domain_subid eq_iff mult_onel mult_oner)
qed

text {* Metis takes very long *}

lemma dom_el_idemp: "d(x)\<cdot>d(x) = d(x)"
  by (metis d1_eq domain_export)

lemma dom_el_comm: "d(x)\<cdot>d(y) = d(y)\<cdot>d(x)"
    by (metis d1_eq d2 domain_1 domain_export mult_assoc mult_isor mult_onel antisym_conv)

text {* The next lemma shows that domain is a least left preserver; it
is the leas (domain) element for which the left hand side holds *}

lemma dom_llp: "x \<le> d(y)\<cdot>x \<longleftrightarrow> d(x) \<le> d(y)"
  by (metis add_comm d1_eq d3 domain_1 domain_invol leq_def mult_isor mult_onel)

lemma dom_weakly_local: "x\<cdot>y = 0 \<longleftrightarrow> x\<cdot>d(y) = 0"
  by (metis annir d1_eq d2 d4)

text {* We can now show that domain elements are closed under addition
and multiplication. This means that they form a subalgebra of the
domain semiring. *}

lemma dom_add_closed: "d(d(x)+d(y)) = d(x)+d(y)"
  by (metis d5 domain_invol)

lemma dom_mult_closed: "d(d(x)\<cdot>d(y)) = d(x)\<cdot>d(y)"
  by (metis d2 domain_export)

lemma dom_lb: "d(x)\<cdot>d(y) \<le> d(x)"
  by (metis domain_1 domain_export domain_invol)

lemma dom_glb: "d(x) \<le> d(y)\<cdot>d(z) \<longleftrightarrow> (d(x) \<le> d(y) \<and> d(x) \<le> d(z))"
    by (metis add_comm d3 distr dom_llp domain_export mult_assoc mult_onel add_ub  dom_lb eq_iff mult_isor  order_trans)

text {* We have already shown that domain elements form a semilattice
under multiplication, and they form a semilattice under addition by
definition of dioids. We now show that the absorption laws hold. *}

lemma domain_absorption_1: "d(x)\<cdot>(d(x)+d(y)) = d(x)"
  by (metis add_comm' d1_eq d3 distl domain_export mult_oner)

lemma domain_absorption_2: "d(x)+(d(x)\<cdot>d(y)) = d(x)"
  by (metis d1_eq distl domain_absorption_1 domain_export)

text {* This proves that domain elements form a lattice. It follows
immediately from the semiring distributivity law that domain elements
form a distributive lattice. In every lattice, one of the
distributivity laws suffices for that. We now show the other
distributivity law explicitly. *}

lemma domain_distributivity: "d(x)+(d(y)\<cdot>d(z)) = (d(x)+d(y))\<cdot>(d(x)+d(z))"
proof -
  have "d(x)+(d(y)\<cdot>d(z)) \<le> (d(x)+d(y))\<cdot>(d(x)+d(z))"
    by (smt dom_lb add_comm add_iso dom_el_comm  d5 dom_glb domain_export)
  thus ?thesis
    by (smt add_assoc' d1_eq distl distr dom_el_comm domain_absorption_2 domain_export order_refl)
qed

text {* This should probably be made explicit with a sublocale statement *}

text {* The next statements have to do with simulation. They must be copied to range. *}

(* lemma domain_bisimulation:"d(x\<cdot>d(y)\<cdot>d(z)) = d(x\<cdot>d(y))\<cdot>d(x\<cdot>d(z))"
nitpick [timeout=200] --found 8-element counterexample *)

lemma domain_simulation: "d(x\<cdot>d(y)\<cdot>d(z)) \<le> d(x\<cdot>d(y))\<cdot>d(x\<cdot>d(z))"
  by (metis dom_glb dom_subid domain_1 domain_iso mult_assoc mult_isol mult_isor mult_onel)

lemma domain_simulation_var: "d(x\<cdot>d(y))\<cdot>d(x\<cdot>d(y)\<cdot>d(z)) = d(x\<cdot>d(y)\<cdot>d(z))"
  by (metis d1_eq domain_export mult_assoc)

text {* Finally we relate domain elements with the order the meet semilattice way *}


lemma domain_order: "d(x) \<le> d(y) \<longleftrightarrow> d(x) = d(x)\<cdot>d(y)"
  by (metis dom_glb domain_export eq_iff)

end

section {* Antidomain Semirings *}

text {* In this setting, domain can be defined *}

class antidomain_semiring = semiring_one_zero + plus_ord + a_op +
  assumes a1: "a(x)\<cdot>x = 0"
  and a2: "a(x\<cdot>y)+a(x\<cdot>a(a(y))) = a(x\<cdot>a(a(y)))"
  and a3: "a(a(x))+a(x) = 1"

begin

text {* Definition of domain. *}

definition (in antidomain_semiring)
  antidomain_semiring_domain :: "'a \<Rightarrow> 'a" ("d")
  where "d(x) = a(a(x))"

text {* Again, every antidomain semiring is a dioid *}

subclass dioid
proof
  fix x y z :: 'a
  show "x+x = x"
    by (metis a1 a2 a3 add_comm' add_zerol distl mult_oner)
  show "z\<cdot>x \<le> z\<cdot>(x+y)"
    by (metis a2 a3 add_assoc' add_comm' distl leq_def mult_oner)
qed

lemma a_fixed_point: "\<forall>x.(a(x) = x \<longrightarrow> (\<forall>y.(y = 0)))"
  by (metis a1 a3 add_idem annir mult_onel)

lemma a_subid: "a(x) \<le> 1"
  by (metis a3 add_comm add_ub)

text {* The next lemma shows that antidomain elements are greatest left annihilators *}

lemma a_gla: "a(x)\<cdot>y = 0 \<longleftrightarrow> a(x) \<le> a(y)"

proof -
(* proof takes quite long 
have "a(x)\<cdot>y = 0 \<longrightarrow> a(x) \<le> a(y)"
by (metis a1 a2 a3 add_zerol distl eq_iff mult_onel mult_oner subdistr)
*)
 have "a(x)\<cdot>y = 0 \<longrightarrow> a(x)\<cdot>d(y) = 0"
   by (metis a1 a2 a3 add_comm add_zerol antidomain_semiring_domain_def leq_def mult_onel mult_oner order_prop)
  hence "a(x)\<cdot>y = 0 \<longrightarrow> a(x) \<le> a(y)"
    by (metis a3 a_subid add_zerol antidomain_semiring_domain_def distl mult_isor mult_onel mult_oner)
  thus ?thesis
    by (metis a1 a3 add_lub distr eq_iff leq_def mult_onel mult_oner order_prop)
qed

lemma a2_eq: "a(x\<cdot>y) = a(x\<cdot>d(y))"
  by (metis a1 a3 a_gla add_zerol antidomain_semiring_domain_def distr mult_assoc mult_onel a2 add_comm leq_def)

lemma a_closure:  "d(a(x)) = a(x)"
  by (metis a2_eq antidomain_semiring_domain_def mult_onel)

lemma a_subdist: "a(x+y) \<le> a(x)"
  by (metis a_gla add_zerol eq_iff leq_def subdistl)

lemma a_idem: "a(x)\<cdot>a(x) = a(x)"
  by (metis a1 a3 add_zerol distr mult_onel)

lemma a_1: "a(x) = 1 \<longrightarrow> x = 0"
  by (metis a1 mult_onel)

lemma a_3: "a(x)\<cdot>a(y)\<cdot>d(x+y) = 0"
  by (metis a2_eq a3 a_gla add_idem antidomain_semiring_domain_def distl distr less_le mult_assoc mult_onel order_prop strict_leq_def)

lemma a_add: "a(x)\<cdot>a(y) = a(x+y)"
proof -
  have  "a(x)\<cdot>a(y) = a(x)\<cdot>a(y)\<cdot>a(x+y)"
    by (metis a3 add_comm mult_assoc antidomain_semiring_domain_def mult_oner distl a_3  add_zerol)
  hence   "a(x)\<cdot>a(y) \<le> a(x+y)"
    by (metis a_subid mult_isor mult_onel order_trans)
  thus ?thesis
    by (metis a_idem a_subdist add_comm order_trans mult_isol mult_isor eq_iff)
qed

lemma a_export: "a(a(x)\<cdot>y) = d(x)+a(y)"
proof -
  have "a(a(x)\<cdot>y) = (a(a(x)\<cdot>y)\<cdot>d(y))+(a(a(x)\<cdot>y)\<cdot>a(y))"
    by (metis a3 add_comm antidomain_semiring_domain_def distl mult_oner)
  hence "a(a(x)\<cdot>y) \<le> (a(a(x)\<cdot>y)\<cdot>d(y))+a(y)"
    by (metis a_add a_subdist add_comm add_iso eq_iff order_trans)
  hence "a(a(x)\<cdot>y) \<le> (a(a(x)\<cdot>y)\<cdot>(a(x)+d(x))\<cdot>d(y))+a(y)"
    by (metis a3 add_comm antidomain_semiring_domain_def mult_oner)
  hence one: "a(a(x)\<cdot>y) \<le> (a(a(x)\<cdot>y)\<cdot>a(x)\<cdot>d(y))+(a(a(x)\<cdot>y)\<cdot>d(x)\<cdot>d(y))+a(y)"
    by (metis add_comm distl distr mult_assoc)
  have two: "(a(a(x)\<cdot>y)\<cdot>a(x)\<cdot>d(y)) = 0"
    by (metis a1 a2_eq mult_assoc)
  from one two have three:"a(a(x)\<cdot>y) \<le> (a(a(x)\<cdot>y)\<cdot>d(x)\<cdot>d(y))+a(y)"
    by (metis add_zerol)
  have four: "\<dots> \<le> d(x)+a(y)"
    by (metis a_add a_subdist add_assoc add_comm add_ub antidomain_semiring_domain_def leq_def)
  from three four have "a(a(x)\<cdot>y) \<le> d(x)+a(y)"
    by (metis order_trans)
  thus ?thesis 
    by (metis a1 a_gla a_add add_comm annir antidomain_semiring_domain_def add_lub mult_assoc eq_iff)
qed

end

sublocale antidomain_semiring < domain_semiring
"op +" "op \<le>" "op <" "op \<cdot>" "(1\<Colon>'a)" "(0\<Colon>'a)" "d"

proof
  fix x y :: 'a
  have  "x = d(x)\<cdot>x"
    by (metis a1 a3 add_comm add_zerol antidomain_semiring_domain_def distr mult_onel)
  thus "x+d(x)\<cdot>x = d(x)\<cdot>x"
    by (metis add_idem)
  show  "d(x\<cdot>y) = d(x\<cdot>d(y))"
    by (metis a2_eq antidomain_semiring_domain_def)
  show "d(x)+1 = 1"
    by (metis a_subid antidomain_semiring_domain_def leq_def)
  show  "d(0) = 0"
    by (metis a1 a3 a_export antidomain_semiring_domain_def mult_oner)
  show  "d(x+y) = d(x)+d(y)"
    by (metis a_add a_export antidomain_semiring_domain_def)
qed

text {* together with a-closure it now follows that antidomain
elements form distributive lattices *}

context antidomain_semiring
begin

lemma a_zero: "a(0) = 1"
  by (metis a3 add_zerol d4 antidomain_semiring_domain_def)

lemma a_one: "a(1) = 0"
  by (metis a1 mult_oner)

lemma a_comp_1: "d(x)\<cdot>a(x) = 0"
  by (metis a1 antidomain_semiring_domain_def)

lemma a_comp_2: "a(x)\<cdot>d(x) = 0"
  by (metis a1 dom_weakly_local)

text {* By the previous two lemmas it is now clear that antidomain algebras form a Boolean subalgebra *}


text {* perhaps we should make this explict with a sublocale statement
*}

lemma a_2_var: "a(x)\<cdot>d(y) = 0 \<longleftrightarrow> a(x) \<le> a(y)"
  by (metis a_gla dom_weakly_local)

lemma a_antitone: "x \<le> y \<longrightarrow> a(y) \<le> a(x)"
  by (metis a_subdist leq_def)

lemma a_de_morgan: "a(a(x)\<cdot>a(y)) = d(x+y)"
  by (metis a_add antidomain_semiring_domain_def)

lemma a_de_morgan_var_1: "a(a(x)\<cdot>a(y)) = d(x)+d(y)"
  by (metis a_add a_export antidomain_semiring_domain_def)

lemma a_de_morgan_var_2: "a(a(x)+a(y)) = d(x)\<cdot>d(y)"
 by (metis a_add antidomain_semiring_domain_def)

lemma a_de_morgan_var_3: "a(d(x)+d(y)) =a(x)\<cdot>a(y)"
  by (metis a_add a_closure antidomain_semiring_domain_def)

lemma a_de_morgan_var_4: "a(d(x)\<cdot>d(y))=a(x)+a(y)"
  by (metis a_closure a_export antidomain_semiring_domain_def)

lemma a_comm: "a(x)\<cdot>a(y) = a(y)\<cdot>a(x)"
  by (metis a_add add_comm)

lemma a_4: "a(x) \<le> a(x\<cdot>y)"
  by (metis a1 a_gla annir mult_assoc)

lemma a_5: "a(d(x)) = a(x)"
  by (metis a_closure antidomain_semiring_domain_def)

lemma a_6: "a(d(x)\<cdot>y) = a(x)+a(y)"
  by (metis a_closure a_export antidomain_semiring_domain_def)

lemma a_7: "d(x)\<cdot>a(d(y)+d(z)) = d(x)\<cdot>a(y)\<cdot>a(z)"
  by (metis a_5 a_add d5 mult_assoc)

text {* The following two lemmas give the Galois connection of Heyting
algebras *}

lemma d_a_galois1: "d(x)\<cdot>a(y) \<le> d(z) \<longleftrightarrow> d(x) \<le> d(z)+d(y)"
  by (metis a_add a_gla add_assoc add_comm d5 antidomain_semiring_domain_def)

lemma d_a_galois2: "d(x)\<cdot>d(y) \<le> d(z) \<longleftrightarrow> d(x) \<le> d(z)+a(y)"
  by (metis a_closure d_a_galois1 antidomain_semiring_domain_def)

lemma d_cancellation_1: "d(x) \<le> d(y)+(d(x)\<cdot>a(y))"
  by (metis a1 a_add a_export a_gla antidomain_semiring_domain_def mult_assoc)

lemma d_cancellation_2: "(d(z)+d(y))\<cdot>a(y) \<le> d(z)"
  by (metis a_3 a_add a_export a_gla add_assoc' add_comm' antidomain_semiring_domain_def)

text {* The next lemmas explicitly show that antidomain elements are closed under addition and multiplication. *}



lemma a_d_add_closure: "d(a(x)+a(y))=a(x)+a(y)"
  by (metis a_6 a_closure)

lemma a_d_mult_closure: "d(a(x)\<cdot>a(y))=a(x)\<cdot>a(y)"
  by (metis a_add a_closure)

lemma d_a_zero: "d(x)\<cdot>a(y) = 0 \<longleftrightarrow> d(x) \<le> d(y)"
  by (metis a_gla antidomain_semiring_domain_def)

lemma d_d_zero: "d(x)\<cdot>d(y) = 0 \<longleftrightarrow> d(x) \<le> a(y)"
  by (metis a_2_var antidomain_semiring_domain_def)

lemma d_6: "d(x)+d(y) = d(x)+a(x)\<cdot>d(y)"
  by (metis a1 a_add a_export add_zerol' antidomain_semiring_domain_def distl)

lemma d_7: "a(x)+a(y) = a(x)+d(x)\<cdot>a(y)"
proof -
  have "a(x)+a(y) =  a(x)\<cdot>a(x)+a(x)\<cdot>a(y)+d(x)\<cdot>a(x)+d(x)\<cdot>a(y)"
    by (metis a3 add_comm' antidomain_semiring_domain_def mult_onel distl distr add_assoc)
  thus ?thesis
    by (metis a_add a_gla a_subid add_comm' add_idem add_zerol' antidomain_semiring_domain_def domain_subid domain_absorption_2 add_assoc a_closure) 
qed

lemma kat_1: "d(x)\<cdot>y \<le> y\<cdot>d(z) \<longrightarrow> y\<cdot>a(z) \<le> a(x)\<cdot>y"
proof
  assume hyp: "d(x)\<cdot>y \<le> y\<cdot>d(z)"
  hence  "d(x)\<cdot>y\<cdot>a(z)+a(x)\<cdot>y\<cdot>a(z) \<le> a(x)\<cdot>y\<cdot>a(z)"
    by (metis mult_isor add_iso add_comm a_comp_1 annil mult_assoc add_zerol)
  hence "d(x)\<cdot>y\<cdot>a(z)+a(x)\<cdot>y\<cdot>a(z)  \<le> a(x)\<cdot>y"
    by (metis a_subid mult_isol mult_oner order_trans)
  thus "y\<cdot>a(z)  \<le> a(x)\<cdot>y"
    by (metis a1 a_export a_zero distr mult_onel)
qed

lemma kat_2:  "y\<cdot>a(z) \<le> a(x)\<cdot>y \<longrightarrow> d(x)\<cdot>y\<cdot>a(z) = 0"
  by (metis mult_isol mult_assoc a_comp_1 annir min_zero eq_iff)

lemma kat_3: "d(x)\<cdot>y\<cdot>a(z) = 0 \<longrightarrow> d(x)\<cdot>y = d(x)\<cdot>y\<cdot>d(z)"
  by (metis a3 antidomain_semiring_domain_def mult_oner distl add_zeror)

lemma kat_4: "d(x)\<cdot>y = d(x)\<cdot>y\<cdot>d(z) \<longrightarrow> d(x)\<cdot>y \<le> y\<cdot>d(z)"
  by (metis dom_subid mult_isor mult_onel)

lemma kat_1_equiv: "d(x)\<cdot>y \<le> y\<cdot>d(z) \<longleftrightarrow> y\<cdot>a(z) \<le> a(x)\<cdot>y"
  by (metis kat_1 kat_2 kat_3 kat_4)

lemma kat_2_equiv:  "y\<cdot>a(z) \<le> a(x)\<cdot>y \<longleftrightarrow> d(x)\<cdot>y\<cdot>a(z) = 0"
  by (metis kat_1_equiv kat_2 kat_3 kat_4)

lemma kat_3_equiv: "d(x)\<cdot>y\<cdot>a(z) = 0 \<longleftrightarrow> d(x)\<cdot>y = d(x)\<cdot>y\<cdot>d(z)"
  by (metis kat_1_equiv kat_2_equiv kat_3 kat_4)

lemma kat_4_equiv: "d(x)\<cdot>y = d(x)\<cdot>y\<cdot>d(z) \<longleftrightarrow> d(x)\<cdot>y \<le> y\<cdot>d(z)"
  by (metis kat_1_equiv kat_2_equiv kat_3_equiv kat_4)

lemma kat_1_equiv_opp: "y\<cdot>d(x) \<le> d(z)\<cdot>y \<longleftrightarrow> a(z)\<cdot>y \<le> y\<cdot>a(x)"
  by (metis a_closure antidomain_semiring_domain_def kat_1_equiv)

lemma kat_2_equiv_opp:  "a(z)\<cdot>y \<le> y\<cdot>a(x) \<longleftrightarrow> a(z)\<cdot>y\<cdot>d(x) = 0"
  by (metis a_closure antidomain_semiring_domain_def kat_1_equiv_opp kat_2_equiv)

lemma kat_3_equiv_opp: "a(z)\<cdot>y\<cdot>d(x) = 0 \<longleftrightarrow> y\<cdot>d(x) = d(z)\<cdot>y\<cdot>d(x)"
  by (metis a_one add_comm' annil domain_one kat_1_equiv kat_1_equiv_opp leq_def mult_assoc mult_oner order_refl)

lemma kat_4_equiv_opp: "y\<cdot>d(x) = d(z)\<cdot>y\<cdot>d(x) \<longleftrightarrow> y\<cdot>d(x) \<le> d(z)\<cdot>y"
  by (metis a_closure antidomain_semiring_domain_def kat_2_equiv kat_3_equiv_opp)

end

section{* Antidomain Kleene Algebras *}

class antidomain_kleene_algebra = antidomain_semiring + kleene_algebra

begin

lemma fdom_star: "d(x\<^sup>\<star>) = 1"
  by (metis a_add a_zero annir antidomain_semiring_domain_def dom_weakly_local mult_onel star_unfoldl_eq)

end

section{* Forward Diamond *}

text {* In this section we define a forward diamond operator over an
antidomain semiring *}

class fdiamond_semiring = antidomain_semiring + fdiamond_op +
  assumes fdiamond_def: "(\<bar>x\<rangle>y)  =  d(x\<cdot>y)"  


(* context antidomain_semiring
begin

definition fdiamond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("( \<bar>  _ \<rangle> _)" 90)
  where fdiamond_def: "(\<bar>x\<rangle>y)  =  d(x\<cdot>y)"  
*)
begin

lemma fdia_simp: "\<bar>x\<rangle>p = \<bar>x\<rangle>d(p)"
  by (metis d2 fdiamond_def) 

lemma fdia_simp_2:  "\<bar>x\<rangle>p =d(\<bar>x\<rangle>p)"
  by (metis domain_invol fdiamond_def)

lemma fdia_dom: "d(x) =\<bar>x\<rangle>1"
  by (metis fdiamond_def mult_oner)

lemma fdia_add1: "\<bar>x\<rangle>(y+z) = (\<bar>x\<rangle>y)+(\<bar>x\<rangle>z)"
  by (metis a_add a_export antidomain_semiring_domain_def fdiamond_def distl)

lemma fdia_add2: "\<bar>x+y\<rangle>z = (\<bar>x\<rangle>z)+(\<bar>y\<rangle>z)"
  by (metis a_add a_export antidomain_semiring_domain_def fdiamond_def distr)

lemma fdia_mult: "\<bar>x\<cdot>y\<rangle>z = \<bar>x\<rangle>(\<bar>y\<rangle>z)"
  by (metis a2_eq antidomain_semiring_domain_def fdiamond_def mult_assoc)

lemma fdia_one: "\<bar>1\<rangle>x = d(x)"
  by (metis antidomain_semiring_domain_def fdiamond_def mult_onel)

lemma fdia_zero: "\<bar>x\<rangle>0 = 0"
  by  (metis a_one a_zero annil antidomain_semiring_domain_def fdiamond_def)

lemma fdemodalisation1: "d(z)\<cdot>(\<bar>x\<rangle>y) = 0 \<longleftrightarrow> d(z)\<cdot>x\<cdot>d(y) = 0"
  by (metis dom_weakly_local fdiamond_def mult_assoc)

lemma fdemodalisation2: "\<bar>x\<rangle>y \<le> d(z) \<longleftrightarrow> a(z)\<cdot>x\<cdot>d(y) = 0"
  by (metis a2_eq a_gla fdiamond_def kat_1_equiv mult_assoc mult_onel mult_oner)

lemma fdemodalisation3: "\<bar>x\<rangle>y \<le> d(z) \<longleftrightarrow> x\<cdot>d(y) \<le> d(z)\<cdot>x"
  by (metis fdemodalisation2 kat_1_equiv_opp kat_2_equiv_opp)

lemma fdia_iso: "d(x) \<le> d(y) \<longrightarrow> \<bar>z\<rangle>x \<le> \<bar>z\<rangle>y"
  by (metis d2 d5 fdia_add1 fdiamond_def leq_def)

lemma dia_iso_var: "x \<le> y \<longrightarrow> \<bar>x\<rangle>p \<le> \<bar>y\<rangle>p"
  by (metis a_add a_export antidomain_semiring_domain_def distr fdiamond_def leq_def)

lemma fdia_zero_var: "\<bar>0\<rangle>x = 0"
  by (metis a_one a_zero annir antidomain_semiring_domain_def fdiamond_def)

lemma fdia_subdist_1: "\<bar>x\<rangle>p \<le> \<bar>x\<rangle>(p+q)"
  by (metis fdia_add1 add_lub order_refl)

lemma fdia_subdist_2: "\<bar>x\<rangle>(d(p)\<cdot>d(q)) \<le> \<bar>x\<rangle>d(p)"
  by (metis a2_eq a_add a_d_add_closure a_subdist antidomain_semiring_domain_def fdia_iso fdiamond_def)

lemma fdia_subdist: "\<bar>x\<rangle>(d(y)\<cdot>d(z)) \<le> (\<bar>x\<rangle>d(y))\<cdot>\<bar>x\<rangle>d(z)" 
  by (metis fdia_subdist_2 dom_el_comm dom_glb fdia_simp_2)

lemma dia_diff_var: "\<bar>x\<rangle>d(p) \<le> (\<bar>x\<rangle>(d(p)\<cdot>a(q)))+\<bar>x\<rangle>d(q)"
  by (metis fdia_simp antidomain_semiring_domain_def a1 a_add a_closure a_gla add_comm' fdia_iso mult_assoc fdia_add1)

lemma dia_diff: "(\<bar>x\<rangle>p)\<cdot>a(\<bar>x\<rangle>q) \<le> \<bar>x\<rangle>(d(p)\<cdot>a(q))"
  by (metis dia_diff_var fdia_add1 fdia_simp d5 d_a_galois1 fdiamond_def domain_invol)

lemma fdia_export_1:  "d(y)\<cdot>\<bar>x\<rangle>p = \<bar>d(y)\<cdot>x\<rangle>p"
  by (metis domain_export fdia_mult fdia_simp fdiamond_def)

lemma fdia_export_2: "a(y)\<cdot>\<bar>x\<rangle>p = \<bar>a(y)\<cdot>x\<rangle>p"
  by (metis a_closure fdiamond_def domain_export mult_assoc)

lemma fdia_split: "\<bar>x\<rangle>y = d(z)\<cdot>(\<bar>x\<rangle>y)+a(z)\<cdot>(\<bar>x\<rangle>y)"
    by (smt mult_onel a3 antidomain_semiring_domain_def distr)

end

section {* Forward Box *}

class fmodal_semiring = fdiamond_semiring + fbox_op +
  assumes fbox_def:  "\<bar>x]y = a(x\<cdot>a(y))"

(*
definition 
  fbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("( \<bar>  _ ] _)" 90)
  where  "(\<bar>x]y) = a(x\<cdot>a(y))"
*)

begin

text {* the next lemmas establish the De Morgan duality between boxes
and diamonds *}

lemma fbox_fdia: "\<bar>x]y = a(\<bar>x\<rangle>a(y))"
  by (metis a_5 fdiamond_def fbox_def) 

lemma fdia_fbox: "\<bar>x\<rangle>y = a(\<bar>x]a(y))"
  by (metis antidomain_semiring_domain_def fdia_mult fdia_one fbox_fdia mult_onel mult_oner)

lemma fbox_fdia_de_morgan_1: "a(\<bar>x]y) = \<bar>x\<rangle>a(y)"
  by (metis antidomain_semiring_domain_def fbox_def fdiamond_def)

lemma fdia_fbox_de_morgan_2: "a(\<bar>x\<rangle>y) = \<bar>x]a(y)"
  by (metis a2_eq a_closure antidomain_semiring_domain_def fbox_def fdiamond_def)

lemma fbox_simp: "\<bar>x]p = \<bar>x]d(p)"
by (metis fbox_fdia a_5)

lemma fbox_simp_2:  "\<bar>x]p =d(\<bar>x]p)"
by (metis a_closure fbox_fdia) 

text {* I use the following set of hypothesis for dualising statements. All box statements can then be obtained from the dual diamond statement *}

(*
sledgehammer (fdia_simp fdia_simp_2 fbox_simp fbox_simp_2 a_closure a_5 dom_add_closed dom_mult_closed a_antitone a_de_morgan_var_1 a_de_morgan_var_2 a_de_morgan_var_3 a_de_morgan_var_4 fdia_fbox fbox_fdia a_one a_zero fbox_fdia_de_morgan_1 fdia_fbox_de_morgan_2  antidomain_semiring_domain_def **dual_statement*** )
*)

lemma fbox_dom: "a(x) =\<bar>x]0"
by (metis a_5 a_zero fbox_fdia fdia_dom)

lemma fbox_add1: "\<bar>x](d(y)\<cdot>d(z)) = (\<bar>x]y)\<cdot>(\<bar>x]z)"
by  (smt fdia_simp fdia_simp_2 fbox_simp fbox_simp_2 a_closure a_5 dom_add_closed dom_mult_closed a_antitone a_de_morgan_var_1 a_de_morgan_var_2 a_de_morgan_var_3 a_de_morgan_var_4 fdia_fbox fbox_fdia a_one a_zero fdia_add1)

text {* Interestingly sledgehammer couldn't do this one\<dots> *}

lemma fbox_add2: "\<bar>x+y]z = (\<bar>x]z)\<cdot>(\<bar>y]z)"
by (metis a_de_morgan_var_3 fbox_fdia fdia_add2 fdia_simp_2)

lemma fbox_mult: "\<bar>x\<cdot>y]z = \<bar>x](\<bar>y]z)"
by (metis fbox_fdia fbox_fdia_de_morgan_1 fdia_mult)

lemma fbox_one: "\<bar>1]x = d(x)"
by (metis a_closure fbox_fdia_de_morgan_1 fbox_simp_2 fdia_fbox fdia_one)

lemma fbox_one_1: "\<bar>x]1 = 1"
by (metis a_one a_zero fbox_fdia fdia_zero)

lemma fbox_demodalisation3: "d(y) \<le> \<bar>x]d(z) \<longleftrightarrow> d(y)\<cdot>x \<le> x\<cdot>d(z)"
  by (metis a_gla antidomain_semiring_domain_def fbox_def kat_2_equiv_opp mult_assoc)

text {* Duality did not work here. *}

lemma fbox_iso: "d(x) \<le> d(y) \<longrightarrow> \<bar>z]x \<le> \<bar>z]y"
by (metis a_5 a_antitone a_closure fbox_fdia fdia_iso)

lemma fbox_antitone_var: "x \<le> y \<longrightarrow> \<bar>y]p \<le> \<bar>x]p"
by (metis a_antitone dia_iso_var fbox_fdia)

lemma fbox_subdist_1: "\<bar>x](d(p)\<cdot>d(q)) \<le> \<bar>x]d(p)"
by (metis a_antitone a_de_morgan_var_4 fbox_fdia fbox_simp fdia_subdist_1)

lemma fbox_subdist_2: "\<bar>x]d(p) \<le>\<bar>x](d(p)+d(q))"
by (metis a_antitone a_closure a_de_morgan_var_3 fbox_fdia fbox_simp fdia_subdist_2)

lemma fbox_subdist: "(\<bar>x]d(y))+\<bar>x]d(z) \<le> \<bar>x](d(y)+d(z))"
by (smt a_antitone a_closure a_de_morgan_var_3 a_de_morgan_var_4 fbox_fdia fbox_simp fdia_simp_2 fdia_subdist)

lemma fbox_diff_var: "(\<bar>x](d(p)+a(q)))\<cdot>(\<bar>x]d(q)) \<le> \<bar>x]d(p)" 
by   (smt a_antitone  a_de_morgan_var_3 a_de_morgan_var_4  fbox_fdia fbox_fdia_de_morgan_1
 fdia_fbox_de_morgan_2 antidomain_semiring_domain_def dia_diff_var)

lemma fbox_diff: "\<bar>x](d(p)+a(q)) \<le> (\<bar>x]p)+a(\<bar>x]q)"
by (smt a_antitone a_de_morgan_var_4 fbox_fdia fbox_fdia_de_morgan_1 fdia_fbox_de_morgan_2 antidomain_semiring_domain_def dia_diff)

end

class  fmodal_kleene_algebra = fmodal_semiring + kleene_algebra

begin

lemma a_star: "a(x\<^sup>\<star>) = 0"
  by (metis a_gla a_subdist mult_oner star_plus_one)

lemma dom_star: "d(x\<^sup>\<star>) = 1"
  by (metis a_star a_zero antidomain_semiring_domain_def)

lemma fdia_star_unfold: "(\<bar>1\<rangle>z)+\<bar>x\<rangle>(\<bar>x\<^sup>\<star>\<rangle>z) = \<bar>x\<^sup>\<star>\<rangle>z"
  by (metis fdia_mult fdia_add2 star_unfoldl_eq)

lemma fbox_star_unfold: "(\<bar>1]z)\<cdot>\<bar>x](\<bar>x\<^sup>\<star>]z) = \<bar>x\<^sup>\<star>]z"
by  (smt fdia_simp fdia_simp_2 fbox_simp fbox_simp_2 a_closure a_5 dom_add_closed dom_mult_closed a_antitone a_de_morgan_var_1 a_de_morgan_var_2 a_de_morgan_var_3 a_de_morgan_var_4 fdia_fbox fbox_fdia a_one a_zero fbox_fdia_de_morgan_1 fdia_fbox_de_morgan_2  antidomain_semiring_domain_def fdia_star_unfold )

lemma fdia_star_unfold_var: "d(z)+\<bar>x\<rangle>(\<bar>x\<^sup>\<star>\<rangle>z) = \<bar>x\<^sup>\<star>\<rangle>z"
by (metis fdia_one fdia_star_unfold)

lemma fbox_star_unfold_var: "d(z)\<cdot>\<bar>x](\<bar>x\<^sup>\<star>]z) = \<bar>x\<^sup>\<star>]z"
  by (metis a_closure a_de_morgan_var_2 antidomain_semiring_domain_def fbox_fdia_de_morgan_1 fbox_simp_2 fdia_star_unfold_var)

lemma fdia_star_unfold_var_2: "d(z)+\<bar>x\<rangle>(\<bar>x\<^sup>\<star>\<rangle>d(z)) = \<bar>x\<^sup>\<star>\<rangle>d(z)"
  by (metis d2 fdia_star_unfold_var fdiamond_def)

lemma fbox_star_unfold_var_2: "d(z)\<cdot>\<bar>x](\<bar>x\<^sup>\<star>]d(z)) = \<bar>x\<^sup>\<star>]d(z)"
  by (metis a_closure a_de_morgan_var_2 antidomain_semiring_domain_def fbox_fdia_de_morgan_1 fbox_simp_2 fdia_star_unfold_var_2)

lemma fdia_star_unfoldr: "(\<bar>1\<rangle>z)+(\<bar>x\<^sup>\<star>\<rangle>(\<bar>x\<rangle>z)) = \<bar>x\<^sup>\<star>\<rangle>z"
  by (metis fdia_mult fdia_one fdia_star_unfold_var star_slide_var)

lemma fbox_star_unfoldr: "(\<bar>1]z)\<cdot>(\<bar>x\<^sup>\<star>](\<bar>x]z)) = \<bar>x\<^sup>\<star>]z"
by   (smt fdia_simp fdia_simp_2 fbox_simp fbox_simp_2 a_closure a_5 dom_add_closed dom_mult_closed a_antitone a_de_morgan_var_1 a_de_morgan_var_2 a_de_morgan_var_3 a_de_morgan_var_4 fdia_fbox fbox_fdia a_one a_zero fbox_fdia_de_morgan_1 fdia_fbox_de_morgan_2  antidomain_semiring_domain_def fdia_star_unfoldr)

lemma fdia_star_unfoldr_var: "d(z)+(\<bar>x\<^sup>\<star>\<rangle>(\<bar>x\<rangle>z)) = \<bar>x\<^sup>\<star>\<rangle>z"
  by (metis fdia_mult fdia_star_unfold_var star_slide_var)

lemma fbox_star_unfoldr_var: "d(z)\<cdot>(\<bar>x\<^sup>\<star>](\<bar>x]z)) = \<bar>x\<^sup>\<star>]z"
  by (metis a_closure a_de_morgan_var_2 antidomain_semiring_domain_def fbox_fdia_de_morgan_1 fbox_simp_2 fdia_star_unfoldr_var)

lemma fdia_star_induct_var: "\<bar>x\<rangle>d(y) \<le> d(y) \<longrightarrow> \<bar>x\<^sup>\<star>\<rangle>d(y) \<le> d(y)"
  by (metis d2 fdemodalisation3 fdiamond_def star_sim1)

lemma fbox_star_induct_var: "d(y) \<le> \<bar>x]d(y) \<longrightarrow> d(y) \<le> \<bar>x\<^sup>\<star>]d(y)"
by (metis a_antitone a_closure antidomain_semiring_domain_def fbox_fdia_de_morgan_1 fbox_simp_2 fdia_star_induct_var)

lemma fdia_star_induct: "d(z)+(\<bar>x\<rangle>d(y)) \<le> d(y) \<longrightarrow> \<bar>x\<^sup>\<star>\<rangle>d(z) \<le> d(y)"
  by (smt add_lub fdia_star_induct_var d2 fdia_iso fdiamond_def order_trans)

lemma fbox_star_induct: "d(y) \<le> d(z)\<cdot>\<bar>x]d(y) \<longrightarrow>  d(y) \<le> \<bar>x\<^sup>\<star>]d(z)"
by  (smt fdia_simp fdia_simp_2 fbox_simp fbox_simp_2 a_closure a_5 dom_add_closed dom_mult_closed a_antitone a_de_morgan_var_1 a_de_morgan_var_2 a_de_morgan_var_3 a_de_morgan_var_4 fdia_fbox fbox_fdia a_one a_zero fbox_fdia_de_morgan_1 fdia_fbox_de_morgan_2  antidomain_semiring_domain_def fdia_star_induct)

lemma fdia_star_induct_eq: "d(z)+(\<bar>x\<rangle>d(y)) = d(y) \<longrightarrow> \<bar>x\<^sup>\<star>\<rangle>d(z) \<le> d(y)"
  by (metis fdia_star_induct order_refl)

lemma fbox_star_induct_eq: "d(z)\<cdot>(\<bar>x]d(y)) = d(y) \<longrightarrow> d(y) \<le> \<bar>x\<^sup>\<star>]d(z)"
by   (smt fdia_simp fdia_simp_2 fbox_simp fbox_simp_2 a_closure a_5 dom_add_closed dom_mult_closed a_antitone a_de_morgan_var_1 a_de_morgan_var_2 a_de_morgan_var_3 a_de_morgan_var_4 fdia_fbox fbox_fdia a_one a_zero fbox_fdia_de_morgan_1 fdia_fbox_de_morgan_2  antidomain_semiring_domain_def fdia_star_induct_eq)

lemma fbox_export_1: "a(p)+\<bar>x]d(q) = \<bar>d(p)\<cdot>x]d(q)"
  by (metis a_6 a_closure antidomain_semiring_domain_def fbox_fdia fdiamond_def mult_assoc)

lemma fbox_export_2: "d(p)+\<bar>x]d(q) = \<bar>a(p)\<cdot>x]d(q)"
  by (metis a_closure a_export antidomain_semiring_domain_def fbox_fdia fdiamond_def mult_assoc)

lemma fdia_test: "\<bar>d(x)\<rangle>d(y) = d(x)\<cdot>d(y)"
  by (metis d2 domain_export fdiamond_def)

lemma fbox_test: "\<bar>d(x)]d(y) = a(x)+d(y)"
  by (metis fbox_export_1 fbox_mult fbox_one fbox_simp)

(*
lemma fbox_test_var: "a(p)\<cdot>\<bar>a(p)]a(q) = a(p)\<cdot>a(q)"
proof -
  have "a(p)\<cdot>\<bar>a(p)]a(q) = a(p)\<cdot>\<bar>d(a(p))]d(a(q))"
    by (metis a_closure)
  also have " \<dots> = a(p)\<cdot>(a(d(a(p)))+d(a(q)))"
by (metis a_closure a_export antidomain_semiring_domain_def fbox_def)
 also have " \<dots> = a(p)\<cdot>(d(p)+a(q))"
by (metis a_closure antidomain_semiring_domain_def)
 also have " \<dots> = a(p)\<cdot>d(p)+a(p)\<cdot>a(q)"
by (metis distl)
also have "\<dots> = 0+a(p)\<cdot>a(q)"
thus ?thesis 
  by (metis a_export fbox_dom fbox_mult antidomain_semiring_domain_def mult_compl_intro pre_def)
*)
end

end

(*

lemma a_a2_0: "a(x)\<cdot>a(a(x)) = 0"
  by (metis a_comp_2 antidomain_semiring_domain_def)



lemma d_restrict: "(d(x)\<cdot>y \<le> z) = (d(x)\<cdot>y \<le> d(x)\<cdot>z)"
  by (metis mult_isol dom_el_idemp mult_assoc dom_subid mult_isor mult_onel order_trans)
*)

