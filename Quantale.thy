theory Quantale
  imports Signatures Lattice Main
begin

primrec (in complete_join_semilattice) sum :: "'a list \<Rightarrow> 'a" where
  "sum [] = \<bottom>"
| "sum (x # xs) = x + sum xs"

class quantale = complete_lattice + odot_op +
  assumes qmult_assoc: "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  and inf_distl: "x \<odot> sum ys = sum (map (\<lambda>y. x \<odot> y) ys)"
  and inf_distr: "sum ys \<odot> x = sum (map (\<lambda>y. y \<odot> x) ys)"
begin
  lemma bot_zeror: "x \<odot> \<bottom> = \<bottom>"
  proof -
    have "x \<odot> sum [] = sum (map (\<lambda>y. x \<odot> y) [])" by (metis inf_distl)
    thus ?thesis by (simp add: sum_def)
  qed

  lemma bot_zerol: "\<bottom> \<odot> x = \<bottom>"
  proof -
    have "sum [] \<odot> x = sum (map (\<lambda>y. y \<odot> x) [])" by (metis inf_distr)
    thus ?thesis by (simp add: sum_def)
  qed

  lemma qdistl1: "x \<odot> (y + z) = (x \<odot> y) + (x \<odot> z)"
  proof -
    have "x \<odot> sum [y,z] = sum (map (\<lambda>y. x \<odot> y) [y,z])" by (metis inf_distl)
    thus ?thesis by (simp add: sum_def)
  qed

  lemma qdistr1: "(y + z) \<odot> x = (y \<odot> x) + (z \<odot> x)"
  proof -
    have "sum [y,z] \<odot> x = sum (map (\<lambda>y. y \<odot> x) [y,z])" by (metis inf_distr)
    thus ?thesis by (simp add: sum_def)
  qed
end

class commutative_quantale = quantale +
  assumes qmult_comm: "x \<odot> y = y \<odot> x"

class idempotent_quantale = quantale +
  assumes qmult_idem: "x \<odot> x = x"

class involutive_quantale = quantale + involution_op +
  assumes invol_ax: "(x \<odot> y)\<^sup>\<circ> = y\<^sup>\<circ> \<odot> x\<^sup>\<circ>"
  and invol_join_preserve: "(sum xs)\<^sup>\<circ> = sum (map (\<lambda>x. x\<^sup>\<circ>) xs)"

class frame = quantale +
  assumes mult_is_meet: "x \<odot> y = x \<cdot> y"
