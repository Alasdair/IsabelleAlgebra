header {* Dioids *}

theory Dioid
  imports Signatures
begin

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]


(**************************************************************************)

section {* Join Semilattices *}

text {* We first define a class that combines addition and the definition of order in semilattices. This class makes some of the definitions below more slick. *}

class plus_ord = plus + ord +
  assumes leq_def: "x \<le> y \<longleftrightarrow> x+y = y"
  and strict_leq_def: "x < y \<longleftrightarrow> x \<le>  y \<and>  \<not>  (y \<le>  x)"

text {* Join semilattices are defined equationally and then linked
with Isabelle's class for orderings. We should merge this to Tjark's
class that integrates order and plus to simplify the subclass
proofs. *}

class join_semilattice = plus_ord +
  assumes add_assoc: "(x+y)+z = x+(y+z)"
  and add_comm: "x+y = y+x"
  and add_idem: "x+x = x"
begin

subclass order
proof
  fix x y z :: 'a
  show "x \<le> x"
    by (metis add_idem leq_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis add_comm leq_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis add_assoc leq_def)
  show  "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
    by (metis strict_leq_def)
qed

text {* We can now show some basic order-based properties of semilattices *}

lemma add_iso: "x \<le> y \<longrightarrow> x+z \<le> y+z"
  by (metis add_assoc add_comm add_idem leq_def max_def)

text {* We do this proof by smt because it is slightly faster than metis. Isar proof was even faster, but the output was not useful *}

lemma add_ub: "x \<le> x+y"
  by (metis add_assoc add_idem leq_def)

lemma add_lub: "x+y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
  by (metis add_comm add_iso add_ub leq_def)

lemma leq_symm_intro: "\<lbrakk>x \<le>  y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
  by (metis eq_iff)

text {* the next lemma links the above definition of order as $x\leq y\leftrightarrow x+y=y$ with a perhaps more conventional one *}

lemma order_prop: "(x \<le> y) \<longleftrightarrow> (\<exists>z.(x+z = y))"
  by (metis leq_def add_ub)

end

(************************************************************************)

text{* Next a least element is added to the join semilattice *}

class join_semilattice_with_zero = join_semilattice + zero +
  assumes add_zerol': "0+x = x"
begin

lemma add_zeror: "x+0 = x"
  by (metis add_comm add_zerol')

lemma min_zero: "0 \<le> x"
  by (metis add_zerol' leq_def)

lemma no_trivial_inverse: "\<forall>x.(x \<noteq> 0 \<longrightarrow>\<not>(\<exists>y.(x+y = 0)))"
  by (metis add_assoc add_zerol' add_zeror add_idem)

end

(***************************************************************************)

section {* Near Semirings *}

text {*

Near semirings, also called seminearrings, are generalisations of near
rings to the semiring case. They have been studied, for instance, in
Pilz's book on near rings. According to his definition, a near
semiring consists of an additive and a multiplicative semigroup that
interact via a single distributivity law (left or right). The additive
semigroup is not required to be commutative. The definition is
influenced by the set of partial transformations on semigroups. We
only consider near semirings in which addition is commutative, but
call them near semirings for brevity

*}

class near_semiring = plus + mult_op +
  assumes mult_assoc: "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
  and add_assoc': "(x+y)+z = x+(y+z)"
  and add_comm': "x+y = y+x"
  and distr: "(x+y)\<cdot>z = x\<cdot>z+y\<cdot>z"

text {* 
A near dioid is then a (commutative) near semiring in which addition is idempotent. This generalises the notion of (additively) idempotent semiring by dropping on distributivity law.  Near dioids are a starting point of process algebras.
*}

class near_dioid = near_semiring + plus_ord +
  assumes idem: "x+x = x"
begin

text {* When addition is idempotent, the additive (commutative) semigroup is a semilattice, hence near dioids are ordered by the semilattice order. *}


subclass join_semilattice
proof
  fix x y z :: 'a
  show "(x+y)+z = x+(y+z)"
    by (metis add_assoc')
  show "x+y = y+x"
    by (metis add_comm')
  show  "x+x = x"
    by (metis idem)
qed

text {* It follows that multiplication is right-isotone, but not necessarily left-isotone *}

lemma mult_isor: "x \<le> y \<longrightarrow> x\<cdot>z \<le> y\<cdot>z"
  by (metis distr leq_def)

lemma subdistr: "x\<cdot>z \<le> (x+y)\<cdot>z"
  by (metis add_ub mult_isor)

(*
lemma mult_isol: "x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y"
    nitpick  -- "3-element counterexample"
*)


text {* The following lemmas are essentially about predioids (see below). It shows that left isotonicity is equivalent to left subdistributivities *}

lemma iso_subdist: "(\<forall>x.\<forall>y.\<forall>z.(x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y)) \<longleftrightarrow> (\<forall>x.\<forall>y.\<forall>z.(z\<cdot>x \<le> z\<cdot>(x+y)))"
  by (metis add_ub leq_def)

(*
lemma iso_subdist_var: "(x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y) \<longleftrightarrow> (z\<cdot>x \<le> z\<cdot>(x+y))"
    nitpick -- "3-element counterexample"
*)

lemma subdist_var: "(\<forall>x.\<forall>y.\<forall>z.(z\<cdot>x \<le> z\<cdot>(x+y))) \<longleftrightarrow> (\<forall>x.\<forall>y.\<forall>z.(z\<cdot>x+z\<cdot>y \<le> z\<cdot>(x+y)))"
  by (metis add_comm' add_lub)

end

text {* We now make multiplication in near dioids left-isotone, which
is equivalent to the following left subdistributivity property (see
above for the proof). The corresponding structures are important for
probabilistic Kleene algebras and game algebras. We are not aware that
these structures have a special name, so we baptise them "predioids".

We do not explicitly defined presemirings since we have no application
for them.  *}

class pre_dioid = near_dioid +
  assumes subdistl: "z\<cdot>x \<le> z\<cdot>(x+y)"

begin

lemma mult_isol: "x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y"
  by (metis leq_def subdistl)

lemma mult_double_iso: "w \<le> x \<and> y \<le> z \<longrightarrow> w\<cdot>y \<le> x\<cdot>z"
  by (metis distr order_prop order_trans subdistl) 

end

(*************************************************************************)

text{* By adding a left distributivity law we can now obtain semirings and  dioids, which are idempotent semirings, from near semirings and near dioids *}

class semiring = near_semiring +
  assumes  distl: "x\<cdot>(y+z) = x\<cdot>y+x\<cdot>z"

class dioid = semiring + pre_dioid

(*************************************************************************)

section{* Adding a Multiplicative Unit *}

text {* In our applications, multiplicative units are important for
defining a str operation of finite iteration. We do not introduce left
and right units separately since we have no application for this *}

class near_semiring_one = near_semiring + one +
  assumes mult_onel: "1\<cdot>x = x"
  and mult_oner: "x\<cdot>1 = x"

class near_dioid_one = near_semiring_one + plus_ord +
  assumes idemo: "1+1 = 1"

begin

subclass near_dioid
proof
  fix x y :: 'a
  show "x+x = x"
    by (metis distr idemo mult_onel)
qed

end

(*****************************************************************************)

class pre_dioid_one = near_semiring_one + pre_dioid

begin

subclass near_dioid_one
proof
  fix x y :: 'a
  show "1+1 =1"
    by (metis idem)
qed

end

(*****************************************************************************)

class semiring_one = near_semiring_one + semiring

class dioid_one = semiring_one + near_dioid
begin

subclass pre_dioid_one
proof
  fix x y z :: 'a
 show  "z \<cdot> x \<le> z \<cdot> (x + y)"
   by (metis add_ub distl)
qed

end

(****************************************************************************)

section {* Adding Additive Units *}

text {* We add left and right additive units separately. We call them
left and right units because of their annihilation properties. We need
predominantly left units in applications, so we define this case
separately and then turn the left unit into a left and right unit.

Semirings and dioids with right additive units can be obtained from
those with a left unit by duality. *}


class near_semiring_one_zerol = near_semiring_one + zero +
  assumes add_zerol: "0+x = x"
  and annir: "0\<cdot>x = 0"

class near_dioid_one_zerol = near_semiring_one_zerol + near_dioid

class pre_dioid_one_zerol = near_semiring_one_zerol + pre_dioid
begin

subclass near_dioid_one_zerol .. 

end

(******************************************************************************)

class semiring_one_zerol = near_semiring_one_zerol + semiring

class dioid_one_zerol = semiring_one_zerol + near_dioid
begin

subclass pre_dioid_one_zerol
proof
  fix x y z :: 'a
  show "z \<cdot> x \<le> z \<cdot> (x + y)"
    by (metis distl order_prop)
qed

subclass join_semilattice_with_zero
proof
  fix x y z :: 'a
  show "0+x = x"
    by (metis add_zerol)
qed

end

(*****************************************************************************)

class semiring_one_zero = semiring_one_zerol +
  assumes annil: "x\<cdot>0 = 0"

class dioid_one_zero = dioid_one_zerol + semiring_one_zero

section{* Duality by Opposition *}

text {* This section needs to be reworked. We should restrict our
attention to semirings and dioids. We can then show the duality for
left and right zeros and that the dual of every semiring with all
units and zeros is again a semiring *}

definition (in mult_op) opp_mult (infixl "\<odot>" 80)
  where "x \<odot> y \<equiv> y \<cdot> x"

lemma (in semiring_one_zero) dual_semiring_one_zero:
  "class.semiring_one_zero (op +) (op \<odot>) 1 0" 
proof
  fix  x y z :: 'a
  show  "x\<odot>y\<odot>z = x\<odot>(y\<odot>z)"
    by (metis mult_assoc opp_mult_def)
  show "(x+y)+z = x+(y+z)"
    by (metis add_assoc')
  show "x+y = y+x"
    by (metis add_comm')
  show "(x+y)\<odot>z = x\<odot>z+y\<odot>z"
    by (metis distl opp_mult_def)
  show "1\<odot>x = x"
    by (metis mult_oner opp_mult_def)
  show "x\<odot>1 = x"
    by (metis mult_onel opp_mult_def)
  show "0+x = x"
    by (metis add_zerol)
  show "0\<odot>x = 0"
    by (metis annil opp_mult_def)
  show "x\<odot>(y+z) = x\<odot>y+x\<odot>z"
    by (metis distr opp_mult_def)
  show "x\<odot>0 = 0"
    by (metis annir opp_mult_def)
qed

(*
class opp_mult = mult +
  fixes   opp_mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>`" 80)
  assumes opp_mult_def: "x \<cdot>` y = y \<cdot> x"

class dual_semiring_one_zero = semiring_one_zero + opp_mult

sublocale dual_semiring_one_zero < semiring_one_zero "op +" "op \<cdot>`" "1" "0"
  proof
     fix x y z
     show "x \<cdot>` y \<cdot>` z = x \<cdot>` (y \<cdot>` z)"
       by (metis opp_mult_def mult_assoc)
     show "x + y + z = x + (y + z)"
       by (metis add_assoc')
     show "x + y = y + x"
       by (metis add_comm')
     show "(x + y) \<cdot>` z = x \<cdot>` z + y \<cdot>` z"
       by (metis opp_mult_def distl)
     show "(1\<Colon>'a) \<cdot>` x = x"
       by (metis opp_mult_def mult_oner)
     show "x \<cdot>` (1\<Colon>'a) = x"
       by (metis opp_mult_def mult_onel)
     show "(0\<Colon>'a) + x = x"
       by (metis add_zerol)
     show "(0\<Colon>'a) \<cdot>` x = (0\<Colon>'a)"
       by (metis annil opp_mult_def)
     show "x \<cdot>` (y + z) = x \<cdot>` y + x \<cdot>` z"
       by (metis opp_mult_def distr)
     show "x \<cdot>` (0\<Colon>'a) = (0\<Colon>'a)"
       by (metis annir opp_mult_def)
  qed

class dual_dioid_one_zero = dioid_one_zerol + dual_semiring_one_zero

sublocale dual_dioid_one_zero < dioid_one_zero "op +" "op \<cdot>`" "op \<le>" "op <" "1" "0"
  proof
     fix x y z
     show "x + x = x"
       by (metis add_idem)
     show "(x \<le> y) = (x + y = y)"
       by (metis leq_def')
     show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
       by (metis strict_leq_def')
  qed

*)

end
