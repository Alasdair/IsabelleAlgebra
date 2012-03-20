header {* Concurrent Semirings *}

theory Concurrent_Semiring
  imports Signatures
begin

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]] 
  
text {* This file contains a formalisation of concurrent semirings and
its independence/aggregation model, following the development in the paper 

Tony Hoare et al.,. Concurrent Kleene and its Foundations, Journal of
Logic and Algebraic Programming (2011), doi:10.1016/j.jlap.2011.04.05

The main result is that certain independence/aggregations algebras
form a model of concurrent semigroups, monoids and semirings.
*}

(**************************************************************************)

section {* Ordered Semirings and Monoids *}

text {* We first define semigroups, monoids and ordered variants of
these classes. We used a predefined operation of multiplication which
has been defined in the Signature class included above. *}

class semigroup = mult_op +
  assumes mult_assoc: "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"

class monoid = semigroup + one +
  assumes mult_onel: "1\<cdot>x = x"
  and mult_oner: "x\<cdot>1 = x"

class ordered_semigroup = semigroup + order +
  assumes mult_isor: "x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y"
  and  mult_isol: "x \<le> y \<longrightarrow> x\<cdot>z \<le> y\<cdot>z"

class ordered_monoid = ordered_semigroup + monoid

(**************************************************************************)

section {* Ordered Bisemigroups and Bimonoids *}

text {* A bisemigroup is defined as a structure $(S,\<cdot>,\<otimes>)$ such that
$(S,\<cdot>)$ is a semigroup and $(S,\<otimes>)$ is a commutative semigroup. *}

class bisemigroup = semigroup + c_mult_op +
  assumes c_mult_assoc: "(x\<otimes>y)\<otimes>z = x\<otimes>(y\<otimes>z)"
  assumes c_mult_comm: "x\<otimes>y = y\<otimes>x"

text {* Of course, in an ordered bisemigroup, $\<otimes>$ should also be
isotone. *}

class ordered_bisemigroup = ordered_semigroup + bisemigroup +
  assumes c_mult_isor: "x \<le> y \<longrightarrow> z\<otimes>x \<le> z\<otimes>y"

begin

lemma c_mult_isol: "x \<le> y \<longrightarrow> x\<otimes>z \<le> y\<otimes>z"
  by (metis c_mult_comm c_mult_isor)

text {* The next statements show that in an ordered semigroup that
satisfies the exchange law, the small exchange laws and the
multiplication inclusion law are independent. *}

(*
lemma mult_incl_indep: "(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>y)\<otimes>(x\<cdot>z) \<longrightarrow> x\<cdot>y \<le> x\<otimes>y"
nitpick -- two element counterexample found 
*)

(*
lemma small_exchange1_indep: "(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>y)\<otimes>(x\<cdot>z) \<longrightarrow> (x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z)"
nitpick -- two element counterexample found
*)

(*
lemma small_exchange2_indep: "(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>y)\<otimes>(x\<cdot>z) \<longrightarrow> x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z"
nitpick -- two element counterexample found 
*)

end

text {* We first define bimonoids as structures $(S,\<cdot>,\<otimes>,1,e)$ as
bisemirings with two different units: $1$ for $cdot$ and $e$ for
$\<otimes>$. In concurrent monoids, they will be the same. *}

class bimonoid = bisemigroup + monoid +
  fixes unit :: "'a" ("e")
  assumes c_mult_unitl: "e\<otimes>x = x"
  and c_mult_unitr: "x\<otimes>e = x"

class ordered_bimonoid = ordered_bisemigroup + bimonoid 

(***********************************************************************)

section {* Concurrent Semigroups and Monoids *}

class concurrent_semigroup = ordered_bisemigroup +
  assumes mult_incl: "x\<cdot>y \<le> x\<otimes>y"
  assumes small_exchange1: "(x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z)"
  assumes small_exchange2: "x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z"
  assumes exchange: "(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>y)\<otimes>(x\<cdot>z)"

class concurrent_monoid = ordered_bimonoid +
  assumes exchange: "(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>y)\<otimes>(x\<cdot>z)"
  assumes one_eq_unit: "1 = e"

begin

text {* The following statement shows that every concurrent monoid is
a concurrent semigroup. In particular, this means that the
multiplication inclusion axiom and the two small exchange axioms of
concurrent semirings are redundant (derivable) in concurrent monoids.
*}

subclass concurrent_semigroup
proof 
  fix w x y z
  show "x\<cdot>y \<le> x\<otimes>y"
    by (metis c_mult_unitl c_mult_unitr exchange mult_onel mult_oner one_eq_unit)
  show "(x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z)"
    by (metis c_mult_unitl exchange mult_oner one_eq_unit)
  show "x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z"
    by (metis c_mult_unitr exchange mult_onel one_eq_unit)
  show "(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>y)\<otimes>(x\<cdot>z)"
    by (metis exchange)
qed

text {* The assumption of one singe unit is essential for this
result. Without it, Nitpick finds two-element counterexamples for
multiplication implication and the two small exchange laws. *}

end

(*************************************************************************)

text {* Related to concurrent monoids we now prove the Eckmann-Hilton
theorem that if two sets are equipped with binary operations $\<cdot>$ and
$\<otimes>$ and a single unit $1$, and if they satisfy an equational version
of the exchange law, then $\<cdot>$ and $\<otimes>$ coincide and are commutative.

In fact we can assume two different units and then show that they must
be the same.  *}

class eckmann_hilton_structure = mult_op + c_mult_op + one + 
  fixes unit :: "'a" ("1'")
  assumes eh_mult_oner: "x\<cdot>1 = x"
  and eh_mult_onel: "1\<cdot>x = x"
  and eh_c_mult_oner: "1'\<otimes>x = x"
  and eh_c_mult_onel: "x\<otimes>1' = x"
  and eq_exchange: "(w\<otimes>x)\<cdot>(y\<otimes>z) = (w\<cdot>y)\<otimes>(x\<cdot>z)"

begin

lemma one_mult: "x\<cdot>y = x\<otimes>y"
  by (metis eh_c_mult_onel eh_c_mult_oner eh_mult_onel eh_mult_oner eq_exchange)

lemma mult_comm: "x\<cdot>y = y\<cdot>x"
  by (metis eh_mult_onel eh_mult_oner eq_exchange one_mult)

lemma c_mult_comm: "x\<otimes>y = y\<otimes>x"
  by (metis mult_comm one_mult)

lemma one_equal: "1 = 1'"
  by (metis eh_c_mult_onel eh_mult_onel one_mult)

(*
lemma (in concurrent_monoid) "x\<cdot>y = x\<otimes>y"
nitpick -- 3-element counterexample found
*)

(*
lemma (in concurrent_monoid) "x\<cdot>y = y\<cdot>x"
nitpick -- 3-element counterexample found
*)

end

(****************************************************************************)

section {* Concurrent Semirings *}

text {* To simplify some proofs we introduce a class that combines the
definition of the plus operation with that of the order. *}

class plus_ord = plus + ord +
  assumes leq_def: "x \<le> y \<longleftrightarrow> x+y = y"
  and strict_leq_def: "x < y \<longleftrightarrow> x \<le>  y \<and>  \<not>  (y \<le>  x)"

text {* We can then defined bisemirings (with two different
multiplicative units) as expansions of bimonoids. *}

class bisemiring = bimonoid + plus_ord + zero +
  assumes add_assoc: "(x+y)+z = x+(y+z)"
  assumes add_comm: "x+y = y+x"
  assumes add_zerol: "0+x = x"
  assumes mult_distl: "x\<cdot>(y+z) = x\<cdot>y+x\<cdot>z"
  assumes mult_distr: "(x+y)\<cdot>z = x\<cdot>z+y\<cdot>z"
  assumes c_mult_distl: "x\<otimes>(y+z) = x\<otimes>y+x\<otimes>z"
  assumes mult_annil: "0\<cdot>x = 0"
  assumes mult_annir: "x\<cdot>0 = 0"
  assumes c_mult_annil: "0\<otimes>x = 0"

begin

text {* Next we prove some simple lemmas. *}

lemma add_zeror: "x+0 = x"
  by (metis add_comm add_zerol)

lemma c_mult_distr: "(x+y)\<otimes>z = x\<otimes>z+y\<otimes>z"
  by (metis c_mult_comm c_mult_distl)

lemma c_mult_annir: "x\<otimes>0 = 0"
  by (metis c_mult_annil c_mult_comm)

end

text {* Since (additively) idempotent semirings are known as
dioids---they carry two monoid structures---the name \emph{trioid}
lends itself for idempotent bisemirings. *}

class trioid = bisemiring +
  assumes add_idem: "x+x = x"

begin 

text {* The next statement shows that every trioid is an ordered
bimonoid. The link is provided by the definition of the order $x\<le>y$
iff $x+y=y$ in the above plus-ord class *}

subclass ordered_bimonoid
proof
  fix x y z
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (metis strict_leq_def)
  show "x \<le> x"
    by (metis add_idem leq_def)
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    by (metis add_assoc leq_def)
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
    by (metis add_comm leq_def)
  show "x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y"
    by (metis leq_def mult_distl)
  show "x \<le> y \<longrightarrow> x\<cdot>z \<le> y\<cdot>z"
    by (metis leq_def mult_distr)
  show "x \<le> y \<longrightarrow> z\<otimes>x \<le> z\<otimes>y"
    by (metis c_mult_comm c_mult_distr leq_def)
qed

end

class concurrent_semiring = concurrent_monoid + trioid

(************************************************************************)


section {* Aggregation, Independence  and Concurrent Semigroups *}

text {* We now introduce the independence model of concurrent
semigroups. It consists of an aggregation algebra $(A,\<oplus>)$ together with
a familiy of independence relations which are assumed to be
bilinear. 

Here we are only interested in two independence relations $R$ and $S$
with the additional properties that $R\<subseteq>S$ and $S$ is symmetric.  *}

class aggregation_semigroup =
  fixes agg_comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 90) 
  assumes agg_assoc: "(x\<oplus>y)\<oplus>z = x\<oplus>(y\<oplus>z)"
  assumes agg_comm: "x\<oplus>y = y\<oplus>x"

class independence_algebra_base = aggregation_semigroup +
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes S :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes R_linearl: "(R (x\<oplus>y) z) \<longleftrightarrow> (R x z) \<and> (R y z)"
  assumes R_linearr: "(R x (y\<oplus>z)) \<longleftrightarrow> (R x y) \<and> (R x z)"
  assumes S_linearl: "(S (x\<oplus>y) z) \<longleftrightarrow> (S x z) \<and> (S y z)"
  assumes S_linearr: "(S x (y\<oplus>z)) \<longleftrightarrow> (S x y) \<and> (S x z)"
  assumes S_symm: "(S x y) \<longrightarrow> (S y x)"

class independence_algebra_1 = independence_algebra_base +
  assumes R_sub_S: "(R x y) \<longrightarrow> (S x y)" 

begin

text {* The first set of lemmas captures some simple algebraic
properties of independence relations. Essentially they say that
aggregates behave like sets with respect to independence. 

They are not needed for linking the model with concurrent
semigroups. *}

lemma indep_assoc_1: "R ((w\<oplus>x)\<oplus>y) z = R (w\<oplus>(x\<oplus>y)) z"
  by (metis R_linearl)

lemma indep_assoc_2: "R w ((x\<oplus>y)\<oplus>z) = R w (x\<oplus>(y\<oplus>z))"
  by (metis R_linearr)

lemma indep_comm_1: "R (x\<oplus>y) z = R (y\<oplus>x) z"
  by (metis R_linearl)

lemma indep_comm_2: "R x (y\<oplus>z) = R x (z\<oplus>y)"
  by (metis R_linearr)

lemma indep_idem_1: "R (x\<oplus>x) y = R x y"
  by (metis R_linearl)
lemma indep_idem_2: "R x (y\<oplus>y) = R x y"
  by (metis R_linearr)

text {* The next set of lemmas is important for linking aggregation
algebras with concurrent semigroups, monoids and semirings. *}

lemma R_agg_assoc: "R (x\<oplus>y) z \<and> R x y \<longleftrightarrow> R x (y\<oplus>z) \<and> R y z"
  by (metis R_linearl R_linearr)

lemma S_agg_assoc: "S (x\<oplus>y) z \<and> S x y \<longleftrightarrow> S x (y\<oplus>z) \<and> S y z"
  by (metis S_linearl S_linearr)

lemma indep_small_exchange_1: "R (x\<oplus>y) z \<and> S x y \<longrightarrow> S x (y\<oplus>z) \<and> R y z"
  by (metis R_linearl R_sub_S S_linearr)

lemma indep_small_exchange_2: "R x (y\<oplus>z)  \<and> S y z \<longrightarrow> S (x\<oplus>y) z \<and> R x y"
  by (metis R_linearr R_sub_S S_linearl)

lemma indep_exchange: "R (w\<oplus>x) (y\<oplus>z) \<and> S w x \<and> S y z \<longrightarrow> R w y \<and> R x z \<and> S (w\<oplus>y) (x\<oplus>z)"
  by (metis S_symm R_linearl R_linearr R_sub_S S_linearr) 

lemma indep_exchange_var: "R (w\<oplus>x) (y\<oplus>z) \<and> S w x \<and> S y z \<longrightarrow> R w z \<and> R x y \<and> S (w\<oplus>z) (x\<oplus>y)"
  by (metis R_linearr S_symm indep_exchange)

end

text{* We now define complex products for $R$ and $S$ in the obvious
way. 

These lift the operations on the aggregation algebra to the set level.
*}

class independence_semigroup = independence_algebra_1 + 
  fixes R_prd :: "'a set \<Rightarrow> 'a set => 'a set"
  fixes S_prd :: "'a set \<Rightarrow> 'a set => 'a set"
  assumes R_prd: "R_prd X Y = {x\<oplus>y | x y. x\<in>X \<and> y\<in>Y \<and> R x y}" 
  assumes S_prd:"S_prd X Y = {x\<oplus>y | x y. x\<in>X \<and> y\<in>Y \<and> S x y}"

begin

text {* The next two lemmas provide elimination rules for the complex
products. They blast away the set structure and provide first-order
reasoning (with Sledgehammer). *}

lemma R_prd_elim: "x\<in>R_prd X Y = (\<exists>y z.(y\<in>X \<and> z\<in>Y \<and> x=y\<oplus>z \<and> R y z))"
  by (simp add:R_prd, auto)

lemma S_prd_elim: "x\<in>S_prd X Y = (\<exists>y z.(y\<in>X \<and> z\<in>Y \<and> x=y\<oplus>z \<and> S y z))"
  by (simp add:S_prd, auto)

end

text {* We now show that independence algebras are models of
concurrent semigroups. *}

interpretation concurrent_semigroup 
  R_prd S_prd "op \<subseteq>" "op \<subset>"
proof 
  fix w x y z
  show "R_prd (R_prd x y) z = R_prd x (R_prd y z)"
    by (simp add:set_eq_iff R_prd_elim, smt agg_assoc R_agg_assoc)
  show "S_prd (S_prd x y) z = S_prd x (S_prd y z)"
    by (simp add:set_eq_iff S_prd_elim, smt agg_assoc S_agg_assoc)
  show "S_prd x y = S_prd y x"
    by (metis set_eq_iff S_prd_elim S_symm agg_comm)
  show "x \<subseteq> y \<longrightarrow> R_prd z x \<subseteq> R_prd z y"
    by (simp add:subset_eq, auto, simp add:R_prd_elim, auto)
  show "x \<subseteq> y \<longrightarrow> R_prd x z \<subseteq> R_prd y z"
    by (simp add:subset_eq, auto, simp add:R_prd_elim, auto)
  show  "x \<subseteq> y \<longrightarrow> S_prd z x \<subseteq> S_prd z y"
    by (simp add:subset_eq, auto, simp add:S_prd_elim, auto)
  show "R_prd x y \<subseteq> S_prd x y"
    by (metis R_prd_elim R_sub_S S_prd_elim subsetI)
  show "R_prd (S_prd x y) z \<subseteq> S_prd x (R_prd y z)"
    by (simp add:subset_eq, auto, simp add:R_prd_elim S_prd_elim, metis agg_assoc indep_small_exchange_1)
  show  "R_prd x (S_prd y z) \<subseteq> S_prd (R_prd x y) z"
    by (simp add:subset_eq, auto, simp add:R_prd_elim S_prd_elim, metis agg_assoc indep_small_exchange_2)
  show "R_prd (S_prd w x) (S_prd y z) \<subseteq> S_prd (R_prd w y) (R_prd x z)"
    by (simp add:subset_eq, auto, simp add:R_prd_elim S_prd_elim, smt agg_assoc agg_comm indep_exchange)
qed

(**************************************************************************)

section {* Aggregation, Independence  and Concurrent Monoids *}

text {* We now define monoidal independence algebras, by adding a unit
to the aggregation semigroup and requiring strictness of the
independence relations *}

class aggregation_monoid = aggregation_semigroup +
  fixes u :: "'a" 
  assumes agg_unitl: "u\<oplus>x = x"
  assumes agg_unitr: "x\<oplus>u = x"

class independence_algebra_2 = independence_algebra_1 + aggregation_monoid +
  assumes R_strictl: "R u x"
  assumes R_strictr: "R x u" 
  assumes S_strictl: "S u x"
  assumes S_strictr: "S x u"

class independence_monoid = independence_algebra_2 +
  fixes U :: "'a set"
  assumes U_unit: "U = {u}"

text {* We now show that the resulting independence algebras form
models of concurrent monoids. *}

interpretation independence_algebra_2: concurrent_monoid
  R_prd S_prd U U "op \<subseteq>" "op \<subset>"
proof
  fix w x y z
 show  "R_prd U x = x"
   by (simp add:set_eq_iff R_prd_elim, metis R_strictl U_unit agg_unitl singleton_iff)
 show "R_prd x U = x"
   by (simp add:set_eq_iff R_prd_elim, metis R_strictr U_unit agg_unitr singleton_iff)
 show "S_prd U x = x"
   by (simp add:set_eq_iff S_prd_elim, metis S_strictl U_unit agg_unitl singleton_iff)
 show "S_prd x U = x"
   by (simp add:set_eq_iff S_prd_elim, metis S_strictr U_unit agg_unitr singleton_iff)
 show "R_prd (S_prd w x) (S_prd y z) \<subseteq> S_prd (R_prd w y) (R_prd x z)"
    by (simp add:subset_eq, auto, simp add:R_prd_elim S_prd_elim, smt agg_assoc agg_comm indep_exchange)
 show "U = U" by auto
qed

(*******************************************************************************)

section {* Aggregation, Independence  and Concurrent Semirings *}

text {* Finally, we show that independence algebras are models of
concurrent semirings. Here, addition is interpreted as set union. *}

interpretation concurrent_semiring R_prd S_prd U U "op \<subseteq>" "op \<subset>" "op \<union>" "{}"
proof
  fix x y z
  show "(x \<subseteq> y) = (x \<union> y = y)"
    by (metis Un_absorb2 Un_commute Un_upper1)
  show "(x \<subset> y) = (x \<subseteq> y \<and> \<not> y \<subseteq> x)"
    by (metis less_fun_def)
  show "x \<union> y \<union> z = x \<union> (y \<union> z)"
    by (metis Un_commute Un_left_commute)
  show "x \<union> y = y \<union> x"
    by (metis Un_commute)
  show "{} \<union> x = x"
    by (metis Un_empty_left)
  show "\<And>x y z. R_prd x (y \<union> z) = R_prd x y \<union> R_prd x z"
    by (simp add:set_eq_iff R_prd_elim, auto)
  show "\<And>x y z. R_prd (x \<union> y) z = R_prd x z \<union> R_prd y z"
    by (simp add:set_eq_iff R_prd_elim, auto)
  show "\<And>x y z. S_prd x (y \<union> z) = S_prd x y \<union> S_prd x z"
    by (simp add:set_eq_iff S_prd_elim, auto)
  show "\<And>x. R_prd {} x = {}"
    by (simp add:set_eq_iff R_prd_elim)
  show "\<And>x. R_prd x {} = {}"
    by (simp add:set_eq_iff R_prd_elim)
  show "\<And>x. S_prd {} x = {}"
    by (simp add:set_eq_iff S_prd_elim)
  show " x \<union> x = x"
    by (metis Un_absorb)
qed

(***************************************************************************)

section {* Dual Concurrent Semigroups *}

text {* We now prove some dual results for structures in which the
order in the exchange laws is reversed. *}

class dual_concurrent_semigroup = ordered_bisemigroup +
  assumes dual_mult_incl: "x\<otimes>y \<le> x\<cdot>y"
  assumes dual_small_exchange1: "x\<otimes>(y\<cdot>z) \<le> (x\<otimes>y)\<cdot>z"
  assumes dual_small_exchange2: "(x\<cdot>y)\<otimes>z \<le> x\<cdot>(y\<otimes>z)"
  assumes dual_exchange: "(w\<cdot>y)\<otimes>(x\<cdot>z) \<le> (w\<otimes>x)\<cdot>(y\<otimes>z)"

class dual_independence_algebra_1 = aggregation_semigroup +
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes S :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes R_linearl: "(R (x\<oplus>y) z) \<longleftrightarrow> (R x z) \<and> (R y z)"
  assumes R_linearr: "(R x (y\<oplus>z)) \<longleftrightarrow> (R x y) \<and> (R x z)"
  assumes S_linearl: "(S (x\<oplus>y) z) \<longleftrightarrow> (S x z) \<and> (S y z)"
  assumes S_linearr: "(S x (y\<oplus>z)) \<longleftrightarrow> (S x y) \<and> (S x z)"
  assumes S_symm: "(S x y) \<longrightarrow> (S y x)"
  assumes S_sub_R: "(S x y) \<longrightarrow> (R x y)" 

begin

text {* The following lemmas are duals of the above ones. *}

lemma indep_assoc_1_d: "R ((w\<oplus>x)\<oplus>y) z = R (w\<oplus>(x\<oplus>y)) z"
  by (metis R_linearl)

lemma indep_assoc_2_d: "R w ((x\<oplus>y)\<oplus>z) = R w (x\<oplus>(y\<oplus>z))"
  by (metis R_linearr)

lemma indep_comm_1_d: "R (x\<oplus>y) z = R (y\<oplus>x) z"
  by (metis R_linearl)

lemma indep_comm_2_d: "R x (y\<oplus>z) = R x (z\<oplus>y)"
  by (metis R_linearr)

lemma indep_idem_1_d: "R (x\<oplus>x) y = R x y"
  by (metis R_linearl)
lemma indep_idem_2_d: "R x (y\<oplus>y) = R x y"
  by (metis R_linearr)

lemma R_agg_assoc_d: "R (x\<oplus>y) z \<and> R x y \<longleftrightarrow> R x (y\<oplus>z) \<and> R y z"
  by (metis R_linearl R_linearr)

lemma S_agg_assoc_d: "S (x\<oplus>y) z \<and> S x y \<longleftrightarrow> S x (y\<oplus>z) \<and> S y z"
  by (metis S_linearl S_linearr)

lemma indep_small_exchange_1_d: "S x (y\<oplus>z) \<and> R y z \<longrightarrow> R (x\<oplus>y) z \<and> S x y"
  by (metis R_linearl S_sub_R S_linearr)

lemma indep_small_exchange_2_d: "S (x\<oplus>y) z \<and> R x y \<longrightarrow> R x (y\<oplus>z)  \<and> S y z"
  by (metis R_linearr S_sub_R S_linearl)

lemma indep_exchange_d: "R w y \<and> R x z \<and> S (w\<oplus>y) (x\<oplus>z) \<longrightarrow> R (w\<oplus>x) (y\<oplus>z) \<and> S w x \<and> S y z"
  by (metis S_symm R_linearl R_linearr S_sub_R S_linearr) 

lemma indep_exchange_var_d: "R w z \<and> R x y \<and> S (w\<oplus>z) (x\<oplus>y) \<longrightarrow> R (w\<oplus>x) (y\<oplus>z) \<and> S w x \<and> S y z"
  by (metis R_linearr S_symm indep_exchange_d)

end

text{* We now again define complex products for $R$ and $S$.
*}

class dual_independence_semigroup = dual_independence_algebra_1 + 
  fixes R_prd :: "'a set \<Rightarrow> 'a set => 'a set"
  fixes S_prd :: "'a set \<Rightarrow> 'a set => 'a set"
  assumes R_prd: "R_prd X Y = {x\<oplus>y | x y. x\<in>X \<and> y\<in>Y \<and> R x y}" 
  assumes S_prd:"S_prd X Y = {x\<oplus>y | x y. x\<in>X \<and> y\<in>Y \<and> S x y}"

begin

lemma R_prd_elim_d: "x\<in>R_prd X Y = (\<exists>y z.(y\<in>X \<and> z\<in>Y \<and> x=y\<oplus>z \<and> R y z))"
  by (simp add:R_prd, auto)

lemma S_prd_elim_d: "x\<in>S_prd X Y = (\<exists>y z.(y\<in>X \<and> z\<in>Y \<and> x=y\<oplus>z \<and> S y z))"
  by (simp add:S_prd, auto)

end

text {* We now show that dual independence algebras are models of
dual concurrent semigroups. *}

(*
sublocale dual_independence_semigroup \<subseteq> dual_concurrent_semigroup 
  R_prd S_prd "op \<subseteq>" "op \<subset>"
proof 
  fix w x y z
  show "dual_independence_semigroup_class.R_prd
        (dual_independence_semigroup_class.R_prd x y) z =
       dual_independence_semigroup_class.R_prd x
        (dual_independence_semigroup_class.R_prd y z)"
    by (simp add:set_eq_iff R_prd_elim_d, smt agg_assoc R_agg_assoc_d)
  show "dual_independence_semigroup_class.S_prd
        (dual_independence_semigroup_class.S_prd x y) z =
       dual_independence_semigroup_class.S_prd x
        (dual_independence_semigroup_class.S_prd y z)"
    by (simp add:set_eq_iff S_prd_elim_d, smt agg_assoc S_agg_assoc_d)
  show "dual_independence_semigroup_class.S_prd x y =
          dual_independence_semigroup_class.S_prd y x"
    by (metis set_eq_iff S_prd_elim_d S_symm agg_comm)
  show "x \<subseteq> y \<longrightarrow>
       dual_independence_semigroup_class.R_prd z x
       \<subseteq> dual_independence_semigroup_class.R_prd z y"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d, auto)
  show "x \<subseteq> y \<longrightarrow>
       dual_independence_semigroup_class.R_prd x z
       \<subseteq> dual_independence_semigroup_class.R_prd y z"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d, auto)
  show  "x \<subseteq> y \<longrightarrow>
       dual_independence_semigroup_class.S_prd z x
       \<subseteq> dual_independence_semigroup_class.S_prd z y"
    by (simp add:subset_eq, auto, simp add:S_prd_elim_d, auto)
  show "dual_independence_semigroup_class.S_prd x y
          \<subseteq> dual_independence_semigroup_class.R_prd x y"
    by (metis R_prd_elim_d S_sub_R S_prd_elim_d subsetI)
  show "dual_independence_semigroup_class.S_prd x
        (dual_independence_semigroup_class.R_prd y z)
       \<subseteq> dual_independence_semigroup_class.R_prd
          (dual_independence_semigroup_class.S_prd x y) z"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d S_prd_elim_d, metis agg_assoc indep_small_exchange_1_d)
  show  "dual_independence_semigroup_class.S_prd
        (dual_independence_semigroup_class.R_prd x y) z
       \<subseteq> dual_independence_semigroup_class.R_prd x
          (dual_independence_semigroup_class.S_prd y z)"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d S_prd_elim_d, metis agg_assoc indep_small_exchange_2_d)
  show "dual_independence_semigroup_class.S_prd
        (dual_independence_semigroup_class.R_prd w y)
        (dual_independence_semigroup_class.R_prd x z)
       \<subseteq> dual_independence_semigroup_class.R_prd
          (dual_independence_semigroup_class.S_prd w x)
          (dual_independence_semigroup_class.S_prd y z)"
apply (simp add:subset_eq, auto)
apply (simp add:R_prd_elim_d S_prd_elim_d)
apply (smt agg_assoc agg_comm indep_exchange_d)

    by (simp add:subset_eq, auto, simp add:R_prd_elim_d S_prd_elim_d, smt agg_assoc agg_comm indep_exchange_d)
qed
*)


interpretation dual_concurrent_semigroup 
  R_prd S_prd "op \<subseteq>" "op \<subset>"
proof 
  fix w x y z
  show "R_prd (R_prd x y) z = R_prd x (R_prd y z)"
    by (simp add:set_eq_iff R_prd_elim_d, smt agg_assoc R_agg_assoc_d)
  show "S_prd (S_prd x y) z = S_prd x (S_prd y z)"
    by (simp add:set_eq_iff S_prd_elim_d, smt agg_assoc S_agg_assoc_d)
  show "S_prd x y = S_prd y x"
    by (metis set_eq_iff S_prd_elim_d S_symm agg_comm)
  show "x \<subseteq> y \<longrightarrow> R_prd z x \<subseteq> R_prd z y"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d, auto)
  show "x \<subseteq> y \<longrightarrow> R_prd x z \<subseteq> R_prd y z"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d, auto)
  show  "x \<subseteq> y \<longrightarrow> S_prd z x \<subseteq> S_prd z y"
    by (simp add:subset_eq, auto, simp add:S_prd_elim_d, auto)
  show "S_prd x y \<subseteq> R_prd x y"
    by (metis R_prd_elim_d S_sub_R S_prd_elim_d subsetI)
  show "S_prd x (R_prd y z) \<subseteq> R_prd (S_prd x y) z"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d S_prd_elim_d, metis agg_assoc indep_small_exchange_1_d)
  show  "S_prd (R_prd x y) z \<subseteq> R_prd x (S_prd y z)"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d S_prd_elim_d, metis agg_assoc indep_small_exchange_2_d)
  show "S_prd (R_prd w y) (R_prd x z) \<subseteq> R_prd (S_prd w x) (S_prd y z)"
    by (simp add:subset_eq, auto, simp add:R_prd_elim_d S_prd_elim_d, smt agg_assoc agg_comm indep_exchange_d)
qed

end
