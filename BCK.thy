header {* Experiments with the axioms of Boffa,  Conway,  Krob and Salomaa *}

(* possible title: on the fine-structure of regular algebras *)

theory Boffa_Conway_Krob
  imports Dioid

begin

text {* We analyse some syntactic arguments from papers of Boffa,
Conway, Krob, Salomaa and Kozen.

First we follow two papers of Boffa which, to a large extent, are
calculational.  *}

(**************************************************************************)

text {* We first introduce the system called $S$ in Boffa's paper. It
is derived from Salomaa and based on semirings. We also introduce a
variant based on dioids. *}

text {* By these definitions, every dioid-based Salomaa algebra is a
semiring-based one. We also prove the converse direction, that is,
idempotency is derivable in the semiring-based setting. So we can use
dioids as the basis of our axiomatisation. *}

class test = mult_op + one 

begin

primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
  where
  "power x 0 = 1" |
  "power x (Suc n) = x\<cdot> (power x n)"

value "power x 1"

lemma "power x 0 = 1"
by auto

lemma "power x 1 = x\<cdot>1"
by (simp add: power.simps)

end

class salomaa_s = semiring_one_zero + star_op + plus_ord +
  assumes S11: "(1+x)\<^sup>\<star> = x\<^sup>\<star>"
  and S12: "x\<^sup>\<star> = 1+x\<^sup>\<star>\<cdot>x"

class salomaa_d = salomaa_s + dioid_one_zero 

sublocale salomaa_s \<subseteq> salomaa_d
proof
  fix x  :: 'a
  show "x + x = x"
    by (metis S11 S12 add_comm' add_zerol annil distl mult_oner)
qed

text {* To compare with later axiomatisations we point out that Conway's starstar axiom does not hold in this setting, *}

(*
lemma starstar: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
nitpick --- 5-element counterexample
*)

text {* The next set of axioms is a fragment of Conway's classical
axioms, but without the powerstar schema. Again we give a
semiring-based and a dioid-based version and show that they are
equivalent. *}

class conway_s = semiring_one_zero + star_op + plus_ord +
  assumes C11: "(x+y)\<^sup>\<star>=(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
  and C12: "(x\<cdot>y)\<^sup>\<star> = 1+x\<cdot>((y\<cdot>x)\<^sup>\<star>)\<cdot>y"
  and C13: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>" 

class conway = conway_s + dioid_one_zero 

sublocale conway_s \<subseteq> conway
proof
  fix x :: 'a
  show "x+x = x"
    by (metis C12 C13 add_comm' add_zerol annir distl mult_oner)
qed

text {* Hence again we can use either one of the axiomatisations. *}

text {* Next we show that axiom C13 is irredundant. *}

class test_conway_d = dioid_one_zero + star_op +
  assumes "(x+y)\<^sup>\<star>=(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
  and "(x\<cdot>y)\<^sup>\<star> = 1+x\<cdot>((y\<cdot>x)\<^sup>\<star>)\<cdot>y"

begin

(*
lemma  "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>" 
nitpick --- 3-element counterexample
*)

end

(************************************************************************)

text {* After these preparations we turn to the hierarchy of
axiomatisations that are complete for the equational theory of regular
events. It is as follows.

First, Krob has proved a conjecture of Conway that Conway's classical
axioms plus a set of so-called group identities is complete for this
theory.

Second, Boffa has shown that Conway's classical axioms plus a
universal Horn identity (R) imply the group identities.

He has then shown that also Conway's powerstar axiom can be
eliminated. This axiomatisation is based on dioids and uses the
additional axioms C11, C12 and R. 

Third, Boffa has shown that Conway's classical axioms augmented by a
universal Horn formula imply the classical axioms augmented by R. This
solves another conjecture of Conway. We will prove this in a modular
way.

Fourth, Boffa has shown a similar way that Salomaa's axioms augmented
by a universal Horn formula imply Conway's classical axioms plus
R. This solves a conjecture by Salomaa. This needs to be done.

Fifth, Boffa has shown that Salomaa's axioms augmented by Arden's rule
imply the axiom systems in (3) and (4). This needs to be done.

Sixth, in his second paper, Boffa presents a second axiomatisation
based on dioid and shows that it implies his first one. He then shows
that Kozen's axioms (left and right variants) imply these axioms.

It follows that all systems mentioned are complete.

We will now refine Boffa's picture by proving implications and finding
counterexamples.

*}

text {* First we introduce Conway's classical axioms with group
identities [tbd] and Boffa's first axiom set and show that the latter
imply the former [tbd]. 

We know that, for Conway algebras, the semiring-based and the
dioid-based variants are the same. Here we use the dioid-based one,
even without axiom C13 and then show that this axiom can be derived.

*}

class boffa1 = dioid_one_zero + star_op +
  assumes C11: "(x+y)\<^sup>\<star>=(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
  and C12: "(x\<cdot>y)\<^sup>\<star> = 1+x\<cdot>((y\<cdot>x)\<^sup>\<star>)\<cdot>y"
  and R: "x\<cdot>x = x \<longrightarrow> x\<^sup>\<star> = 1+x"

begin

text {* We first show that every Boffa-1 algebra is a Conway algebra,
that is, axiom C13 is derivable. *}

subclass conway
proof
  fix x y :: 'a
  show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis C11)
  show " (x \<cdot> y)\<^sup>\<star> = (1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
    by (metis C12)
  show "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
    by (metis C11 C12 R add_idem mult_assoc mult_onel mult_oner)
qed

text {* Next we show that Conway's classical axioms plus the group
identities are derivable in Boffa-1 algebras. *}

(* [...] *)

text {* Because of that theorem we know that Boffa-1 algebras are
complete for the equational theory of regular events. Therefore, we
could show that all equations in our Kleene algebra file hold already
in Boffa-1 algebras. For technical reasons we will do that for Boffa-2
algebras. *}

end

text {* We now introduce Boffa's second axiom set and relate it to the
first one. *}

class boffa2 = dioid_one_zero + star_op +
  assumes B1: "1+x \<le> x\<^sup>\<star>"
  and B2: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  and B3: "1+x \<le> y \<and> y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"

text {* Every Boffa-1 algebra is a Boffa-2 algebra. *}

sublocale boffa1 \<subseteq> boffa2
proof
  fix x y :: 'a
  show "(1\<Colon>'a) + x \<le> x\<^sup>\<star>"
    by (smt C12 add_comm add_ub distl distr leq_def mult_onel mult_oner)
  show "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis C11 C13 `(1\<Colon>'a) + x \<le> x\<^sup>\<star>` add_comm add_lub leq_def mult_oner opp_mult_def)
  show "(1\<Colon>'a) + x \<le> y \<and> y \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis C11 C12 R add_lub leq_def mult_oner subdistl)
qed

text {* This result is new. *}

context boffa2

begin

text {* We will now show the converse direction, namely that the
axioms of Boffa-2 algebras imply those of Boffa-1 algebras. 

But before that we derive the equations of our Kleene algebra file in
the setting of Boffa-2 algebras. That this is possible is the
justified by the completeness result in which these laws are used. *}

(***********************************************************************)

lemma star_ref: "1 \<le> x\<^sup>\<star>"
  by (metis B1 add_lub)

lemma star_plus_one: "x\<^sup>\<star> = 1+x\<^sup>\<star>"
  by (metis leq_def star_ref)

lemma star_trans: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis B2 order_refl)

lemma star_trans_eq: "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B2)
 
lemma star_1l: "x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis B1 B2 add_lub mult_double_iso star_trans)

lemma star_one: "1\<^sup>\<star> = 1"
  by (metis B3 add_idem antisym mult_oner order_refl star_ref)

lemma star_subdist:  "x\<^sup>\<star> \<le> (x+y)\<^sup>\<star>"
  by (metis B1 B2 B3 add_lub star_ref)

lemma star_iso: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis leq_def star_subdist)

lemma star2: "(1+x)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B1 B2 B3 add_comm leq_def star_plus_one star_subdist)

lemma star_unfoldl: "1+x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_lub star_1l star_ref)

lemma star_unfoldr: "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  by (metis B1 B2 add_lub mult_double_iso star_trans)

lemma star_ext: "x \<le> x\<^sup>\<star>"
  by (metis B1 add_lub)

lemma star_1r: "x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  by (metis add_comm add_ub order_trans star_unfoldr)

lemma star_unfoldl_eq: "1+x\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
proof -
  have "(1+x\<cdot>x\<^sup>\<star>)\<cdot>(1+x\<cdot>x\<^sup>\<star>) = 1+x\<cdot>x\<^sup>\<star>"
    by (smt B2 add_assoc add_comm distl distr leq_def mult_assoc mult_onel star_1l star_plus_one)
  thus ?thesis
    by (smt B1 B3 antisym_conv distl iso_subdist mult_isol mult_oner star_plus_one star_subdist star_unfoldl)
qed

lemma star_unfoldr_eq: "1+x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
proof -
  have "(1+x\<^sup>\<star>\<cdot>x)\<cdot>(1+x\<^sup>\<star>\<cdot>x) = 1+x\<^sup>\<star>\<cdot>x"
    by (smt B2 add_comm add_ub distl distr leq_def mult_assoc mult_onel mult_oner star_1r)
  thus ?thesis
    by (smt add_assoc add_ub distr mult_onel star_plus_one le_neq_trans less_le_not_le star_unfoldr B3)
qed

lemma star_prod_unfold: "(x\<cdot>y)\<^sup>\<star> = 1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y"
proof -
  have "\<forall>x y .(1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y = (1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y)\<cdot>(1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y))"
    by (smt B2 add_assoc distl distr mult_assoc mult_onel mult_oner star_one star_unfoldl_eq)
  hence one:  "\<forall>x y. ((x\<cdot>y)\<^sup>\<star> \<le> 1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y)"
    by (metis B3 le_neq_trans less_le_not_le mult_oner star2 star_ext subdistl 
      distr mult_assoc star_iso star_unfoldr_eq subdistl)
  hence two: "\<forall> x y. (1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y \<le> (x\<cdot>y)\<^sup>\<star>)"
sorry
(*    by (smt add_comm add_iso distr leq_def subdistl distl mult_assoc mult_oner star_unfoldl_eq star_unfoldr_eq)
*)
  thus ?thesis using one and two by (metis antisym)
qed

lemma star_slide1: "(x\<cdot>y)\<^sup>\<star>\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  by (smt distl distr eq_refl mult_assoc mult_onel mult_oner star_prod_unfold)

lemma star_slide_var1: "x\<^sup>\<star>\<cdot>x \<le> x\<cdot>x\<^sup>\<star>"
  by (metis mult_onel mult_oner star_slide1)

lemma star_slide: "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  by (smt add_comm mult_assoc star_unfoldr_eq star_slide1 mult_isor add_iso mult_isol distl mult_oner distr mult_onel star_unfoldl_eq eq_iff star_slide1)

lemma star_rtc1: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis B1 B2 add_lub eq_refl)

lemma star_rtc1_eq: "1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B1 B2 leq_def)

lemma star_subdist_var_1: "x \<le> (x+y)\<^sup>\<star>"
  by (metis add_lub star_ext)

lemma star_subdist_var_2: "x\<cdot>y \<le> (x+y)\<^sup>\<star>"
  by (metis B2 add_comm mult_double_iso star_subdist_var_1)

lemma star_subdist_var_3: "x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<le> (x+y)\<^sup>\<star>"
  by (metis B2 add_comm mult_double_iso star_subdist)

lemma R_lemma: " x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = (1\<Colon>'a) + x"
  by (smt B3 add_assoc add_idem antisym distl distr mult_onel mult_oner order_refl star2 star_subdist_var_2)

lemma star_denest_var_0: "(x+y)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
proof -
  have "(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
    by (metis star_trans_eq star_slide mult_assoc)
  hence "((x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
    by (smt star_plus_one R_lemma iso_subdist leq_def mult_assoc mult_isol mult_oner order_trans)
  hence "(x+y)\<^sup>\<star> \<le> (x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
    by (smt add_lub leq_def mult_double_iso mult_onel mult_oner star_ext star_iso star_ref star_slide subdistl)
  thus ?thesis 
    by (metis B2 add_lub R_lemma mult_double_iso star_ext star_iso star_plus_one antisym)
qed

lemma star_denest: "(x+y)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
  by (metis B2 add_comm mult_assoc star2 star_denest_var_0 star_slide star_unfoldl_eq)

lemma star_sum_var: "(x+y)\<^sup>\<star>  = (x\<^sup>\<star>+y\<^sup>\<star>)\<^sup>\<star>"
  by (metis mult_onel star2 star_denest star_one)

lemma star_denest_var: "(x+y)\<^sup>\<star> = x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest_var_0 star_slide)

lemma star_denest_var_2: "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var)

lemma star_denest_var_3: "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<cdot>(y\<^sup>\<star>\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis B2 add_comm mult_assoc star_denest star_denest_var_2)

lemma star_denest_var_4:  "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = (y\<^sup>\<star>\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm star_denest)

lemma star_denest_var_5: "x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star> = y\<^sup>\<star>\<cdot>(x\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm' star_denest_var)

lemma star_denest_var_6: "(x+y)\<^sup>\<star> = x\<^sup>\<star>\<cdot>y\<^sup>\<star>\<cdot>(x+y)\<^sup>\<star>"
  by (metis mult_assoc star_denest star_denest_var_3)

lemma star_denest_var_7: "(x+y)\<^sup>\<star> = (x+y)\<^sup>\<star>\<cdot>x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis star_denest star_denest_var star_denest_var_3 star_denest_var_5 star_slide)

lemma star_denest_var_8: "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<cdot>y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var_6)

lemma star_denest_var_9: " (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<star>\<cdot>x\<^sup>\<star>\<cdot>y\<^sup>\<star>"
  by (metis star_denest star_denest_var_7)

lemma star_slide_var: "x\<^sup>\<star>\<cdot>x = x\<cdot>x\<^sup>\<star>"
  by (smt distl distr mult_assoc mult_onel mult_oner star_unfoldl_eq star_unfoldr_eq)

lemma star_sum_unfold: "(x+y)\<^sup>\<star> = x\<^sup>\<star>+x\<^sup>\<star>\<cdot>y\<cdot>(x+y)\<^sup>\<star>"
  by (metis distl mult_assoc mult_oner star_denest_var star_unfoldl_eq)

lemma troeger: "x\<^sup>\<star>\<cdot>(y\<cdot>((x+y)\<^sup>\<star>\<cdot>z)+z) = (x+y)\<^sup>\<star>\<cdot>z"
  by (smt add_comm distl distr mult_assoc star_sum_unfold)

lemma dbw_lemma: "x\<^sup>\<star>\<cdot>y\<cdot>z\<^sup>\<star> = x\<^sup>\<star>\<cdot>y+x\<^sup>\<star>\<cdot>x\<cdot>y\<cdot>z\<cdot>z\<^sup>\<star>+y\<cdot>z\<^sup>\<star>"
  by (smt add_assoc add_comm distl distr mult_assoc mult_onel mult_oner star_slide_var star_unfoldl_eq add_idem)


lemma meyer_1: "x\<^sup>\<star> = (1+x)\<cdot>(x\<cdot>x)\<^sup>\<star>"
proof -
  have "(1+x)\<cdot>(x\<cdot>x)\<^sup>\<star>\<cdot>(1+x)\<cdot>(x\<cdot>x)\<^sup>\<star> = (1+x)\<cdot>(x\<cdot>x)\<^sup>\<star>"
    by (smt distr mult_assoc mult_onel add_assoc distl  B2 star_slide R_lemma add_comm add_idem leq_def star_denest_var star_subdist_var_2 star_unfoldl_eq add_idem)
  hence  "x\<^sup>\<star> \<le> (1+x)\<cdot>(x\<cdot>x)\<^sup>\<star>"
    by (smt distl leq_def mult_oner star_plus_one B3 mult_assoc)
  thus ?thesis
    by (metis B2 add_idem star_iso star_subdist_var_2 star_denest B1 mult_double_iso antisym) 
qed

lemma star_zero: "0\<^sup>\<star> = 1"
  by (metis add_zeror star2 star_one)

(*************************************************************************)

text {* Having proved all these identities we now return to our more
structural considerations and show that every Boffa-2 algebra is a
Boffa-1 algebra, hence these two axiomatisations are equivalent. *}

subclass boffa1
proof
  fix x y :: 'a
  show "(x+y)\<^sup>\<star> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<star>\<cdot>x\<^sup>\<star>"
    by (metis star_denest_var_0)
  show "(x\<cdot>y)\<^sup>\<star> = 1+x\<cdot>(y\<cdot>x)\<^sup>\<star>\<cdot>y"
    by (metis star_prod_unfold)
  show "x\<cdot>x = x \<longrightarrow> x\<^sup>\<star> = 1+x"
    by (metis R_lemma)
qed

end

(*********************************************************************)

text {* We now study the expanded class of Conway axioms from Boffa's
first paper. In fact, Boffa includes Conway's powerstar axiom which we
disregard, hence obtain a somewhat stronger retult. *}

class conway_oner = conway +
  assumes arden_varr: "x = x\<cdot>y \<longrightarrow> x = x\<cdot>y\<^sup>\<star>"

begin

text {* We now show that the axioms of Boffa_1 (and Boffa_2) algebra
become derivable. *}

subclass  boffa1
proof 
  fix x y :: 'a 
  show  "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis C11)
  show   "(x \<cdot> y)\<^sup>\<star> = (1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
    by (metis C12 mult_assoc)
  show "x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = (1\<Colon>'a) + x"
    by (metis C12 arden_varr)
qed

end

class conway_onel = conway +
  assumes arden_varl: "x = y\<cdot>x \<longrightarrow> x = y\<^sup>\<star>\<cdot>x"

begin

text {* We now show that the axioms of Boffa_1 (and Boffa_2) algebra
become derivable. *}

subclass  boffa1
proof 
  fix x y :: 'a 
  show  "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis C11)
  show   "(x \<cdot> y)\<^sup>\<star> = (1\<Colon>'a) + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
    by (metis C12 mult_assoc)
  show "x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = (1\<Colon>'a) + x"
    by (metis C12 arden_varl mult_assoc)
qed

text {* Hence these axiomatisations are also complete *}

end

(***************************************************************************)

text {* Next we show that weak variants of Kozen's axioms are complete *}

class left_kozen = dioid_one_zero + star_op +
  assumes k1l: "1+x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and k2l: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"

begin

subclass boffa2
proof
  fix x y :: 'a
  show "1+x \<le> x\<^sup>\<star>"
    by (smt add_lub distl k1l leq_def mult_oner)
  show "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis add_lub antisym k1l k2l mult_isol mult_oner)
  show "1+x \<le> y \<and> y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis add_lub distr k2l mult_oner order_prop order_trans subdistl)
qed

text {* Next we show that left Kozen algebras and left Conway algebras
are equivalent. *}

subclass conway_onel
proof
  fix x y :: 'a
  show "x = y \<cdot> x \<longrightarrow> x = y\<^sup>\<star> \<cdot> x"
    by (metis antisym k2l mult_onel order_refl star_plus_one subdistr)
qed

end

sublocale conway_onel \<subseteq> left_kozen 
proof
  fix x y :: 'a
  show "(1\<Colon>'a) + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis order_refl star_unfoldl_eq)
  show "x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
    by (smt add_comm arden_varl distr eq_refl leq_def mult_onel star2)
qed

text {* another new result: left Conway's and left Kozen's algebras are the same. *}

text {* Now we prove the same results for right Kozen algebras *}

class right_kozen = dioid_one_zero + star_op 
+
  assumes k1r: "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  and k2r: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"

begin

subclass boffa2
proof
  fix x y :: 'a
  show "1+x \<le> x\<^sup>\<star>"
    by (smt add_lub distr k1r leq_def mult_onel)
  show "x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis add_lub antisym k1r k2r mult_isor mult_onel)
  show "1+x \<le> y \<and> y\<cdot>y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis add_lub distl k2r mult_onel order_prop order_trans subdistr)
qed


text {* Next we show that right Kozen algebras and right Conway algebras
are equivalent. *}

subclass conway_oner
proof
  fix x y :: 'a
  show "x = x \<cdot> y \<longrightarrow> x = x\<cdot>y\<^sup>\<star>"
    by (metis antisym k2r mult_oner order_refl star_plus_one subdistl)
qed

end

sublocale conway_oner \<subseteq> right_kozen 
proof
  fix x y :: 'a
  show "(1\<Colon>'a) + x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
    by (metis order_refl star_unfoldr_eq)
  show "y \<cdot> x \<le> y \<longrightarrow> y\<cdot> x\<^sup>\<star> \<le> y"
    by (smt add_comm arden_varr distl eq_refl leq_def mult_oner star2)
qed

text {* another new result: right Conway's and right Kozen's algebras are the same. *}

(****************************************************************************)

text {* Next we consider the relationship between Boffa's axioms and simulation rules *}

context boffa2

begin 

(*
lemma k2l_lemma: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
nitpick --- no proof no refutation

lemma arden_var_lemma: "x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>y = y"
nitpick --- no proof no refutation

hence we neither know whether Boffa's axioms imply Kozen's nor
Conway's axioms (extended).

lemma star_sim_one: "x\<cdot>y \<le> y\<cdot>z \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y\<cdot>z\<^sup>\<star>"
nitpick --- no proof no refutation

lemma star_sim_one: "y\<cdot>x \<le> z\<cdot>y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> z\<^sup>\<star>\<cdot>y"
nitpick --- no proof no refutation

lemma star_sim_three: "x\<cdot>y = y\<cdot>z \<longrightarrow> x\<^sup>\<star>\<cdot>y = y\<cdot>z\<^sup>\<star>"
nitpick --- no proof no refutation

*)

(*************************************************************************)

end

class left_kozen_eq = dioid_one_zero + star_op +
  assumes k1l_new: "1+x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and k2l_eq: "x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>y = y"

sublocale left_kozen \<subseteq> left_kozen_eq
proof
fix x y :: 'a
show "(1\<Colon>'a) + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
by (metis order_refl star_unfoldl_eq)
show  "x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> y = y"
by (metis arden_varl)
qed

context left_kozen_eq

begin

(*
lemma " x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = (1\<Colon>'a) + x"
nitpick --- 3-element counterexample

lemma "x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
nitpick --- 3-element counterexample
*)

text {* This means that completeness of this variant cannot be shown via Boffa algebras. Question: Is it complete? *}

text {* Similar results follow for the right variant by duality *}

end

(***********************************************************************)

class left_kozen_sim = dioid_one_zero + star_op +
  assumes k1l_newer: "1+x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and k2l_sim: "x\<cdot>y \<le> y\<cdot>z \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y\<cdot>z\<^sup>\<star>"

begin

(*
lemma "1\<^sup>\<star> = 1"
nitpick --- 3-element counterexample

lemma  "x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
nitpick --- 3-element counterexample

lemma " x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = (1\<Colon>'a) + x"
nitpick --- 3-element counterexample
*)

(* hence for this variant (and its dual we can't establish
completeness via Boffa's alrebras *)

end

(*************************************************************************)

class conway_two_l = conway + star_op +
assumes name_x:  "x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"

sublocale conway_onel \<subseteq> conway_two_l
proof
fix x y :: 'a
show  "x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
by (metis k2l)
qed

context conway_two_l

begin

subclass conway_onel
proof
fix x y :: 'a
show "x = y \<cdot> x \<longrightarrow> x = y\<^sup>\<star> \<cdot> x"
proof -
have "1 \<le> y\<^sup>\<star>"
by (metis C12 mult_oner order_prop)
hence "x \<le> y\<^sup>\<star>\<cdot>x"
  by (metis mult_isor mult_onel)
thus ?thesis
by (metis antisym name_x order_refl)
qed
qed

lemma k2_var: "z+x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<le> y"
by (metis add_lub k2l leq_def subdistl)

end


text {* so these two variants of conway algebra are the same. The same
holds for the right variant. *}

(************************************************************************)

class conway_sim_l = conway + star_op +
assumes name_xx:  "x\<cdot>y \<le> y\<cdot>z \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y\<cdot>z\<^sup>\<star>"

sublocale conway_two_l \<subseteq> conway_sim_l
proof
fix x y z :: 'a
show  "x \<cdot> y \<le> y \<cdot> z \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y \<cdot> z\<^sup>\<star>"
by (smt add_lub mult_assoc mult_isol mult_oner star_1l star_plus_one subdistl
distr order_prop k2_var mult_assoc)
qed

context conway_sim_l

begin

subclass conway_two_l
proof
fix x y :: 'a
show "x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
by (metis  mult_oner name_xx C12 C13 add_zeror annir)
qed

end

text {* so these two variants of conway algebra are the same. The same
holds for the right variant. This has been conjectured by Conway. *}

(***********************************************************************)

class conway_sim = conway + star_op +
assumes name_xxx:  "x\<cdot>y = y\<cdot>z \<longrightarrow> x\<^sup>\<star>\<cdot>y = y\<cdot>z\<^sup>\<star>"

begin

(*
lemma "x \<cdot> y \<le> y \<cdot> z \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y \<cdot> z\<^sup>\<star>"
nitpick --- no proof no refutation
*)

end


(*

check which of these i have done:

build boffa from kozen's axioms I guess this will be too weak

to be done: define conway one from kozens axioms and relate to conway one

add kozens implications to conway and compare 

add simulation rules to both bases and relate with kozen and conway

ad eq simulation and test conway's conjecture

do salomaa stuff

prove group equations and powerstar a la Boffa

test above conjectures in presence of powerstar

*)





end





