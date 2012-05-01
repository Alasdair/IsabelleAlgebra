theory Quantale
  imports Signatures Lattice Main Dioid StarContinuousKA
begin

class quantale = complete_lattice +
  fixes qmult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 80)
  assumes qmult_assoc: "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  and inf_distl: "x \<odot> \<Sigma> Y = \<Sigma> ((\<lambda>y. x\<odot>y) ` Y)"
  and inf_distr: "\<Sigma> Y \<odot> x = \<Sigma> ((\<lambda>y. y\<odot>x) ` Y)"

begin

  lemma bot_zeror: "x \<odot> \<bottom> = \<bottom>"
  proof -
    have "x \<odot> \<Sigma> {} = \<Sigma> ((\<lambda>y. x\<odot>y) ` {})" using inf_distl .
    thus ?thesis by simp
  qed

  lemma bot_zerol: "\<bottom> \<odot> x = \<bottom>"
  proof -
    have "\<Sigma> {} \<odot> x = \<Sigma> ((\<lambda>y. y\<odot>x) ` {})" using inf_distr .
    thus ?thesis by simp
  qed

  lemma qdistl1: "x \<odot> (y + z) = (x \<odot> y) + (x \<odot> z)"
  proof -
    have "x \<odot> \<Sigma> {y,z} = \<Sigma> ((\<lambda>y. x\<odot>y) ` {y,z})" using inf_distl .
    thus ?thesis by (simp add: plus_def)
  qed

  lemma qdistr1: "(y + z) \<odot> x = (y \<odot> x) + (z \<odot> x)"
  proof -
    have "\<Sigma> {y,z} \<odot> x = \<Sigma> ((\<lambda>y. y\<odot>x) ` {y,z})" using inf_distr .
    thus ?thesis by (simp add: plus_def)
  qed

end

sublocale quantale \<subseteq> dioid
  where mult = qmult
proof
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)" using qmult_assoc .
  show "x + y + z = x + (y + z)" using add_assoc .
  show "x + y = y + x" using add_comm .
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z" using qdistr1 .
  show "(x \<le> y) = (x + y = y)" using leq_def .
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" using less_le_not_le .
  show "x + x = x" using add_idem .
  show "z \<odot> x \<le> z \<odot> (x + y)" by (metis insertCI lub_least plus_def qdistl1)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z" using qdistl1 .
qed

class unital_quantale = quantale +
  fixes unit :: 'a
  assumes qunitl: "unit \<odot> x = x"
  and qunitr: "x \<odot> unit = x"

sublocale unital_quantale \<subseteq> dioid_one_zero
  where zero = bot and mult = qmult and one = unit
proof
  fix x :: 'a
  show "unit \<odot> x = x" using qunitl .
  show "x \<odot> unit = x" using qunitr .
  show "\<bottom> + x = x" by simp
  show "\<bottom> \<odot> x = \<bottom>" using bot_zerol .
  show "x \<odot> \<bottom> = \<bottom>" using bot_zeror .
qed


class commutative_quantale = quantale +
  assumes qmult_comm: "x \<odot> y = y \<odot> x"

class idempotent_quantale = quantale +
  assumes qmult_idem: "x \<odot> x = x"

class involutive_quantale = quantale + involution_op +
  assumes invol_ax: "(x \<odot> y)\<^sup>\<circ> = y\<^sup>\<circ> \<odot> x\<^sup>\<circ>"
  and invol_join_preserve: "(sum xs)\<^sup>\<circ> = sum (map (\<lambda>x. x\<^sup>\<circ>) xs)"

class frame = quantale +
  assumes mult_is_meet: "x \<odot> y = x \<cdot> y"
