theory Boolean_Algebra_Extras
  imports Lattice
begin

record 'a huntington_algebra = "'a partial_object" +
  hor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+\<index>" 70)
  hnot :: "'a \<Rightarrow> 'a" ("!\<index>")

no_notation
  Groups.plus_class.plus (infixl "+" 65) and
  Groups.one_class.one ("1") and
  Groups.zero_class.zero ("0")

locale huntington_algebra = fixes A (structure)
  assumes hor_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x + y \<in> carrier A"
  and hnot_closed: "x \<in> carrier A \<Longrightarrow> !x \<in> carrier A"
  and huntington: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = !(!x + y) + !(!x + !y)"
  and comm: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x + y = y + x"
  and assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
  and carrier_non_empty: "carrier A \<noteq> {}"

begin

  (* Following Allan L. Mann's 'A complete proof of the Robbins conjecture' *)

  lemma or_left_cong: "x = z \<Longrightarrow> x + y = z + y" by auto

  lemma or_right_cong: "y = z \<Longrightarrow> x + y = x + z" by auto

  lemma not_cong: "x = y \<Longrightarrow> !x = !y" by auto

  lemma H1: assumes xc: "x \<in> carrier A" shows "x + !x = !x + !(!x)"
  proof -
    have nxc: "!x \<in> carrier A" and nnxc: "!(!x) \<in> carrier A"
      by (metis assms hnot_closed)+
    have "x + !x = !(!x + !(!x)) + !(!x + !(!(!x))) + (!(!(!x) + !(!x)) + !(!(!x) + !(!(!x))))"
      by (subst huntington[OF nxc nnxc], subst huntington[OF xc nnxc], simp)
    also have "... = !(!(!x) + !x) + !(!(!x) + !(!x)) + (!(!(!(!x)) + !x) + !(!(!(!x)) + !(!x)))"
      by (smt assoc comm hnot_closed hor_closed nxc)
    also have "... = !x + !(!x)"
      by (rule sym, subst huntington[OF nnxc nxc], subst huntington[OF nxc nxc], simp)
    finally show ?thesis .
  qed

  lemma double_neg: assumes xc: "x \<in> carrier A" shows "!(!x) = x"
  proof -
    have nxc: "!x \<in> carrier A" and nnxc: "!(!x) \<in> carrier A"
      by (metis assms hnot_closed)+
    have "!(!x) = !(!(!(!x)) + !x) + !(!(!(!x)) + !(!x))"
      by (subst huntington[OF nnxc nxc], simp)
    also have "... = !(!(!(!x)) + !x) + !(!x + x)"
      by (rule or_right_cong, rule not_cong, metis H1 assms comm hnot_closed)
    also have "... = !(!x + !x) + !(!x + x)"
      by (smt H1 comm hnot_closed hor_closed huntington nxc)
    also have "... = x"
      by (metis assms comm hnot_closed hor_closed huntington)
    finally show ?thesis .
  qed

  lemma H2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !x = !y \<Longrightarrow> x = y" by (metis double_neg)

  definition hand :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 80) where
    "x \<cdot> y = !(!x + !y)"

  lemma hand_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier A"
    by (metis hand_def hnot_closed hor_closed)

  lemma de_morgan1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !(x + y) = !x \<cdot> !y"
    by (metis double_neg hand_def)

  lemma de_morgan2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !(x \<cdot> y) = !x + !y"
    by (metis double_neg hand_def hnot_closed hor_closed)

  lemma hor_as_hand: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x + y = !(!x \<cdot> !y)"
    by (metis (lifting) de_morgan2 double_neg hnot_closed)

  lemma hunt_var: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = x\<cdot>y + x\<cdot>!y"
    by (metis (lifting) hand_def hnot_closed huntington)

  lemma hand_comm: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>y = y\<cdot>x"
    by (metis (lifting) comm hand_def hnot_closed)

  lemma hand_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
    by (smt assoc de_morgan2 hand_def hnot_closed)

  lemma and_right_cong: "y = z \<Longrightarrow> x\<cdot>y = x\<cdot>z" by auto

  lemma and_left_cong: "x = y \<Longrightarrow> x\<cdot>z = y\<cdot>z" by auto

  definition one_f :: "'a \<Rightarrow> 'a" where
    "one_f x \<equiv> x + !x"

  lemma one_f_const:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "one_f x = one_f y"
  proof -
    have nxc: "!x \<in> carrier A" and nyc: "!y \<in> carrier A"
      by (metis hnot_closed xc yc)+
    have "one_f x = x + !x"
      by (simp add: one_f_def)
    also have "... = ! (! x + ! y) + ! (! x + ! (! y)) + (! (! (! x) + ! y) + ! (! (! x) + ! (! y)))"
      by (subst huntington[OF nxc nyc], subst huntington[OF xc nyc], simp)
    also have "... = ! (! y + ! x) + ! (! y + ! (! x)) + (! (! (! y) + ! x) + ! (! (! y) + ! (! x)))"
      by (smt assoc comm hnot_closed hor_closed nxc nyc)
    also have "... = y + !y"
      by (rule sym, subst huntington[OF nyc nxc], subst huntington[OF yc nxc], simp)
    also have "... = one_f y"
      by (simp add: one_f_def)
    finally show ?thesis .
  qed

  definition hone :: "'a" ("1") where
    "1 \<equiv> THE x. x \<in> (one_f ` carrier A)"

  lemma one_prop: "x \<in> carrier A \<Longrightarrow> x + !x = 1"
    by (simp add: hone_def, rule the1I2, auto, (metis one_f_def one_f_const)+)

  lemma one_closed: "1 \<in> carrier A"
    apply (simp add: hone_def)
    apply (rule the1I2)
    apply auto
    apply (metis carrier_non_empty empty_is_image ex_in_conv)
    apply (metis one_f_const)
    by (metis hnot_closed hor_closed one_f_def)

  definition hzero :: "'a" ("0") where
    "0 = !1"

  lemma zero_closed: "0 \<in> carrier A"
    by (metis hnot_closed hzero_def one_closed)

  lemma or_zero:
    assumes xc: "x \<in> carrier A"
    shows "x + 0 = x"
  proof -
    have "!1 = 0"
      by (metis hzero_def)
    also have "... = ! (! 0 + 0) + ! (! 0 + ! 0)"
      by (subst huntington[OF zero_closed zero_closed], simp)
    also have "... = 0 + !(!0 + !0)"
      by (metis (lifting) double_neg hzero_def one_closed one_prop)
    also have "... = !1 + !(1 + 1)"
      by (metis hzero_def double_neg one_closed)
    finally have eq1: "!1 = !1 + !(1 + 1)" .

    hence eq2: "1 = 1 + !(1 + 1)"
      by (smt assoc double_neg hnot_closed hor_closed hzero_def one_prop zero_closed)

    hence eq3: "1 = 1 + 1"
      by (metis assoc hnot_closed hor_closed one_closed one_prop)

    from eq1 and eq3 have eq4: "0 = 0 + 0"
      by (metis hzero_def)

    have "x + 0 = ! (! x + x) + ! (! x + ! x) + 0"
      by (subst huntington[OF xc xc], simp)
    also have "... = !(!x + !x) + 0 + 0"
      by (smt assms comm hnot_closed hor_closed hzero_def one_prop)
    also have "... = !(!x + !x) + 0"
      by (metis assms assoc eq4 hand_closed hand_def zero_closed)
    also have "... = !(!x + !x) + !(!x + x)"
      by (metis assms comm hnot_closed hzero_def one_prop)
    also have "... = x"
      by (metis assms double_neg hand_def hunt_var)
    finally show ?thesis .
  qed

  lemma and_one: "x \<in> carrier A \<Longrightarrow> x\<cdot>1 = x"
    by (metis double_neg hand_def hnot_closed hzero_def or_zero)

  lemma and_zero: "x \<in> carrier A \<Longrightarrow> x\<cdot>0 = 0"
    by (smt H1 assoc de_morgan2 hand_def hnot_closed hor_closed hunt_var hzero_def one_prop)

  lemma or_one: "x \<in> carrier A \<Longrightarrow> x + 1 = 1"
    by (smt and_zero hand_def hnot_closed hor_as_hand hzero_def one_closed one_prop)

  lemma or_idem: "x \<in> carrier A \<Longrightarrow> x + x = x"
    by (smt double_neg hand_closed hnot_closed hor_as_hand huntington hzero_def one_prop or_zero)

  lemma and_idem: "x \<in> carrier A \<Longrightarrow> x\<cdot>x = x"
    by (metis double_neg hand_def hnot_closed or_idem)

  definition HBA :: "'a ord" where
    "HBA = \<lparr>carrier = carrier A, le = (\<lambda>x y. x + y = y)\<rparr>"

  lemma HBA_ord: "order HBA"
    by (default, simp_all add: HBA_def, (metis or_idem assoc comm)+)

  lemma HBA_carrier [simp]: "carrier HBA = carrier A"
    by (simp add: HBA_def)

  lemma HBA_lub: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> order.is_lub HBA (x + y) {x, y}"
    apply (simp add: order.is_lub_simp[OF HBA_ord], safe)
    apply (simp_all add: HBA_def)
    apply (metis hor_closed)
    apply (metis assoc or_idem)
    apply (metis assoc comm or_idem)
    by (metis assoc)

  lemma glb1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> y + x = x"
    by (smt and_idem assoc de_morgan2 hand_closed hand_def hnot_closed huntington)

  lemma glb2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> y + y = y"
    by (smt and_idem assoc de_morgan2 hand_closed hand_comm hand_def hnot_closed huntington)

  lemma absorb1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>(x + y) = x"
    by (smt comm double_neg glb1 hand_closed hand_def hnot_closed)

  lemma HBA_glb: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> order.is_glb HBA (x \<cdot> y) {x, y}"
    apply (simp add: order.is_glb_simp[OF HBA_ord], safe)
    apply (simp_all add: HBA_def)
    apply (metis hand_closed)
    apply (metis glb1)
    apply (metis glb2)
    by (smt H2 de_morgan1 de_morgan2 glb1 hand_assoc hand_closed hand_comm hnot_closed)

  lemma HBA_js: "join_semilattice HBA"
    apply default
    prefer 4
    apply (rule_tac x = "x + y" in bexI)
    apply simp
    apply (metis HBA_lub)
    apply (simp_all add: HBA_def)
    apply (metis hor_closed)
    apply (metis or_idem)
    apply (metis assoc)
    by (metis comm)

  lemma HBA_ms: "meet_semilattice HBA"
    apply default
    prefer 4
    apply (rule_tac x = "x \<cdot> y" in bexI)
    apply simp
    apply (metis HBA_glb)
    apply (simp_all add: HBA_def)
    apply (metis hand_closed)
    apply (metis or_idem)
    apply (metis assoc)
    by (metis comm)

  lemma HBA_lattice: "lattice HBA"
    by (simp add: lattice_def, metis HBA_ms HBA_js)

  lemma HBA_join [simp]: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion>\<^bsub>HBA\<^esub> y = x + y"
    apply (simp add: order.join_def[OF HBA_ord] order.lub_def[OF HBA_ord])
    apply (rule the1I2)
    apply auto
    apply (metis HBA_lub)
    apply (metis HBA_ord order.is_lub_unique)
    by (metis HBA_lub HBA_ord order.is_lub_unique)

  lemma HBA_meet [simp]: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter>\<^bsub>HBA\<^esub> y = x\<cdot>y"
    apply (simp add: order.meet_def[OF HBA_ord] order.glb_def[OF HBA_ord])
    apply (rule the1I2)
    apply auto
    apply (metis HBA_glb)
    apply (metis HBA_ord order.is_glb_unique)
    by (metis (lifting) HBA_glb HBA_ord order.is_glb_unique)

  lemma HBA_bounded: "bounded_lattice HBA"
    apply (simp add: bounded_lattice_def bounded_lattice_axioms_def)
    apply safe
    apply (rule HBA_lattice)
    apply (rule_tac x = 0 in bexI)
    apply (metis comm or_zero zero_closed)
    apply (metis zero_closed)
    apply (rule_tac x = 1 in bexI)
    apply (metis and_one hand_comm one_closed)
    by (metis one_closed)

  lemma HBA_top [simp]: "bounded_lattice.top HBA = 1"
    apply (simp add: bounded_lattice.top_def[OF HBA_bounded])
    apply (rule the1I2)
    apply (simp_all add: HBA_def)
    apply (metis and_one comm glb2 one_closed)
    by (metis double_neg hnot_closed one_prop)

  lemma HBA_bot [simp]: "bounded_lattice.bot HBA = 0"
    apply (simp add: bounded_lattice.bot_def[OF HBA_bounded])
    apply (rule the1I2)
    apply (simp_all add: HBA_def)
    apply (metis (lifting) comm or_zero zero_closed)
    by (metis or_zero zero_closed)

  lemma HBA_complemented: "complemented_lattice HBA"
    apply (simp add: complemented_lattice_def complemented_lattice_axioms_def)
    apply safe
    apply (metis HBA_bounded)
    apply (rule_tac x = "!x" in exI)
    apply (subgoal_tac "!x \<in> carrier A")
    apply simp
    apply (metis hand_def hzero_def one_prop)
    by (metis hnot_closed)

  lemma distl:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "x\<cdot>(y + z) = x\<cdot>y + x\<cdot>z"
  proof -
    have c1: "x\<cdot>y \<in> carrier A"
      by (metis hand_closed xc yc)
    have c2: "x\<cdot>(y + z)\<cdot>!y \<in> carrier A"
      by (metis hand_closed hnot_closed hor_closed xc yc zc)

    have "x\<cdot>(y + z) = x\<cdot>(y + z)\<cdot>y + x\<cdot>(y + z)\<cdot>!y"
      by (smt comm hand_closed hnot_closed hor_closed hunt_var xc yc zc)
    also have "... = x\<cdot>y + x\<cdot>(y + z)\<cdot>!y"
      apply (rule or_left_cong)
      by (smt double_neg glb1 hand_assoc hand_closed hnot_closed hor_as_hand xc yc zc)
    also have "... = (x\<cdot>y\<cdot>z + x\<cdot>y\<cdot>!z) + (x\<cdot>(y + z)\<cdot>!y\<cdot>z + x\<cdot>(y + z)\<cdot>!y\<cdot>!z)"
      by (subst hunt_var[OF c1 zc], subst hunt_var[OF c2 zc], simp)
    also have "... = (x\<cdot>y\<cdot>z + x\<cdot>y\<cdot>!z) + (x\<cdot>!y\<cdot>z + x\<cdot>(y + z)\<cdot>!y\<cdot>!z)"
      apply (rule or_right_cong, rule or_left_cong)
      by (smt absorb1 comm hand_assoc hand_closed hand_comm hnot_closed hor_closed xc yc zc)
    also have "... = (x\<cdot>y\<cdot>z + x\<cdot>y\<cdot>!z) + (x\<cdot>!y\<cdot>z + x\<cdot>(y + z)\<cdot>!(y+z))"
      by (smt de_morgan1 hand_assoc hand_closed hnot_closed hor_closed xc yc zc)
    also have "... = (x\<cdot>y\<cdot>z + x\<cdot>y\<cdot>!z) + (x\<cdot>!y\<cdot>z + x\<cdot>0)"
      by (smt hand_assoc hand_def hnot_closed hor_closed hzero_def one_prop xc yc zc)
    also have "... = (x\<cdot>y\<cdot>z + x\<cdot>y\<cdot>!z) + (x\<cdot>!y\<cdot>z + 0)"
      by (metis and_zero xc)
    also have "... = x\<cdot>y\<cdot>z + x\<cdot>y\<cdot>!z + x\<cdot>!y\<cdot>z"
      by (metis hand_closed hnot_closed or_zero xc yc zc)
    also have "... = x\<cdot>y\<cdot>z + x\<cdot>y\<cdot>!z + x\<cdot>y\<cdot>z + x\<cdot>!y\<cdot>z"
      by (metis (no_types) c1 comm glb1 hand_closed hunt_var zc)
    also have "... = x\<cdot>y + x\<cdot>z"
      by (smt assoc hand_assoc hand_closed hand_comm hnot_closed hunt_var xc yc zc)
    finally show ?thesis .
  qed

  lemma distr:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "(x + y)\<cdot>z = x\<cdot>z + y\<cdot>z"
    by (metis distl hand_comm hor_closed xc yc zc)

  lemma HBA_distributive: "distributive_lattice HBA"
    apply (simp add: distributive_lattice_def distributive_lattice_axioms_def)
    apply safe
    apply (metis HBA_lattice)
    apply (subgoal_tac "y + z \<in> carrier A" "x\<cdot>y \<in> carrier A" "x\<cdot>z \<in> carrier A")
    apply simp
    apply (metis distl)
    apply (metis hand_closed)+
    apply (metis hor_closed)
    apply (subgoal_tac "y\<cdot>z \<in> carrier A" "x + y \<in> carrier A" "x + z \<in> carrier A")
    apply simp
    apply (smt and_idem assoc comm distl distr glb1 glb2 hand_closed hand_def hor_as_hand)
    apply (metis hor_closed)+
    by (metis hand_closed)

  lemma HBA_ba: "boolean_algebra HBA"
    by (simp add: boolean_algebra_def, metis HBA_complemented HBA_distributive)

end

lemma huntington_induces_ba:
  assumes hunt: "huntington_algebra \<lparr>carrier = A, hor = p, hnot = n\<rparr>"
  shows "boolean_algebra \<lparr>carrier = A, le = (\<lambda>x y. p x y = y)\<rparr>"
proof -
  let ?H = "\<lparr>carrier = A, hor = p, hnot = n\<rparr>"

  have "boolean_algebra (huntington_algebra.HBA ?H)"
    by (metis assms huntington_algebra.HBA_ba)

  moreover have "\<lparr>carrier = A, le = (\<lambda>x y. p x y = y)\<rparr> = huntington_algebra.HBA ?H"
    by (simp add: huntington_algebra.HBA_def[OF hunt])

  ultimately show ?thesis by auto
qed

notation
  Groups.plus_class.plus (infixl "+" 65) and
  Groups.one_class.one ("1") and
  Groups.zero_class.zero ("0")

no_notation
  huntington_algebra.hor (infixl "+\<index>" 70) and
  huntington_algebra.hnot ("!\<index>")

datatype 'a bexpr = BLeaf 'a
                  | BOr "'a bexpr" "'a bexpr" (infixl ":+:" 70)
                  | BNot "'a bexpr"
                  | BAnd "'a bexpr" "'a bexpr" (infixl ":\<cdot>:" 70)
                  | BOne
                  | BZero

primrec bexpr_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a bexpr \<Rightarrow> 'b bexpr" where
  "bexpr_map f (BLeaf x) = BLeaf (f x)"
| "bexpr_map f (BOr x y) = BOr (bexpr_map f x) (bexpr_map f y)"
| "bexpr_map f (BNot x) = BNot (bexpr_map f x)"
| "bexpr_map f (BAnd x y) = BAnd (bexpr_map f x) (bexpr_map f y)"
| "bexpr_map f BOne = BOne"
| "bexpr_map f BZero = BZero"

primrec bexpr_leaves :: "'a bexpr \<Rightarrow> 'a set" where
  "bexpr_leaves (BLeaf x) = {x}"
| "bexpr_leaves (BOr x y) = bexpr_leaves x \<union> bexpr_leaves y"
| "bexpr_leaves (BNot x) = bexpr_leaves x"
| "bexpr_leaves (BAnd x y) = bexpr_leaves x \<union> bexpr_leaves y"
| "bexpr_leaves BOne = {}"
| "bexpr_leaves BZero = {}"

inductive hunt_con :: "'a bexpr \<Rightarrow> 'a bexpr \<Rightarrow> bool" where
  refl [intro]: "hunt_con x x"
| sym [sym]: "hunt_con x y \<Longrightarrow> hunt_con y x"
| trans [trans]: "\<lbrakk>hunt_con x y; hunt_con y z\<rbrakk> \<Longrightarrow> hunt_con x z"
| or_compat: "hunt_con x1 x2 \<Longrightarrow> hunt_con y1 y2 \<Longrightarrow> hunt_con (BOr x1 y1) (BOr x2 y2)"
| not_compat: "hunt_con x y \<Longrightarrow> hunt_con (BNot x) (BNot y)"
| and_compat: "hunt_con x1 x2 \<Longrightarrow> hunt_con y1 y2 \<Longrightarrow> hunt_con (BAnd x1 y1) (BAnd x2 y2)"
| huntington: "hunt_con (BNot (BNot x :+: y) :+: BNot (BNot x :+: BNot y)) x"
| comm: "hunt_con (x :+: y) (y :+: x)"
| assoc: "hunt_con ((x :+: y) :+: z) (x :+: (y :+: z))"
| one: "hunt_con (x :+: BNot x) BOne"
| zero: "hunt_con (BNot BOne) BZero"
| meet: "hunt_con (x :\<cdot>: y) (BNot (BNot x :+: BNot y))"

quotient_type 'a bterm = "'a bexpr" / "hunt_con"
  apply (simp add: equivp_def, auto)
  apply (subgoal_tac "\<forall>z. hunt_con x z = hunt_con y z")
  apply auto
  by (metis hunt_con.sym hunt_con.trans)+

lift_definition bt_or :: "'a bterm \<Rightarrow> 'a bterm \<Rightarrow> 'a bterm" is BOr
  by (rule hunt_con.or_compat, assumption+)

lift_definition bt_not :: "'a bterm \<Rightarrow> 'a bterm" is BNot
  by (rule hunt_con.not_compat, assumption)

lift_definition bt_and :: "'a bterm \<Rightarrow> 'a bterm \<Rightarrow> 'a bterm" is BAnd
  by (rule hunt_con.and_compat, assumption+)

lift_definition bt_one :: "'a bterm" is BOne
  by (rule hunt_con.refl)

lift_definition bt_zero :: "'a bterm" is BZero
  by (rule hunt_con.refl)

definition free_ba where "free_ba \<equiv> \<lparr>carrier = UNIV, le = (\<lambda>x y. bt_or x y = y)\<rparr>"

lemma free_ba_hunt: "huntington_algebra \<lparr>carrier = UNIV, hor = bt_or, hnot = bt_not\<rparr>"
proof (default, simp_all)
  fix x y z :: "'b bterm"
  show "x = bt_or (bt_not (bt_or (bt_not x) y)) (bt_not (bt_or (bt_not x) (bt_not y)))"
    by (rule HOL.sym, transfer, rule hunt_con.huntington)
  show "bt_or x y = bt_or y x"
    by (transfer, rule hunt_con.comm)
  show "bt_or (bt_or x y) z = bt_or x (bt_or y z)"
    by (transfer, rule hunt_con.assoc)
qed

abbreviation BTH where "BTH \<equiv> \<lparr>carrier = UNIV, hor = bt_or, hnot = bt_not\<rparr>"

lemma bt_hone [simp]: "huntington_algebra.hone BTH = bt_one"
proof -
  have "bt_or bt_one (bt_not bt_one) = bt_one"
    by (transfer, metis one)
  thus ?thesis
    by (simp add: huntington_algebra.one_prop[symmetric, OF free_ba_hunt])
qed

lemma bt_hzero [simp]: "huntington_algebra.hzero BTH = bt_zero"
proof -
  have "bt_not bt_one = bt_zero"
    by (transfer, metis zero)
  thus ?thesis
    by (simp add: huntington_algebra.hzero_def[OF free_ba_hunt])
qed

interpretation hba: huntington_algebra "BTH"
  where "hor BTH x y = bt_or x y"
  and "hnot BTH x = bt_not x"
  and "huntington_algebra.hand BTH x y = bt_and x y"
  and "huntington_algebra.hone BTH = bt_one"
  and "huntington_algebra.hzero BTH = bt_zero"
  and "x \<in> carrier BTH = True"
  apply (simp_all add: free_ba_hunt)
  apply (simp add: huntington_algebra.hand_def[OF free_ba_hunt])
  apply transfer
  apply (metis hunt_con.sym meet)
  done

theorem free_ba: "boolean_algebra free_ba"
proof (simp add: free_ba_def)
  from free_ba_hunt
  show "boolean_algebra \<lparr>carrier = UNIV, le = \<lambda>x y. bt_or x y = y\<rparr>"
    by (rule huntington_induces_ba)
qed

lemma free_ba_ord: "order free_ba"
  apply (insert free_ba)
  apply (simp add: boolean_algebra_def distributive_lattice_def)
  apply (simp add: lattice_def join_semilattice_def)
  by auto

lemma [simp]: "carrier free_ba = UNIV"
  by (simp add: free_ba_def)

lemma [simp]: "x \<squnion>\<^bsub>free_ba\<^esub> y = bt_or x y"
  apply (simp add: order.join_def[OF free_ba_ord] order.lub_simp[OF free_ba_ord])
  apply (simp add: free_ba_def)
  apply (rule the1I2)
  apply auto
  apply (smt hba.assoc hba.comm hba.or_idem)
  apply (metis hba.comm)
  by (metis (full_types) hba.assoc hba.comm hba.or_idem)

lemma [simp]: "x \<sqinter>\<^bsub>free_ba\<^esub> y = bt_and x y"
  apply (simp add: order.meet_def[OF free_ba_ord] order.glb_simp[OF free_ba_ord])
  apply (simp add: free_ba_def)
  apply (rule the1I2)
  apply auto
  apply (rule_tac x = "bt_and x y" in exI)
  apply (metis hba.absorb1 hba.distl hba.glb2 hba.hand_comm)
  apply (metis hba.comm)
  by (smt hba.absorb1 hba.distr hba.glb2 hba.hand_comm)

lemma free_ba_bl: "bounded_lattice free_ba"
  apply (insert free_ba)
  apply (simp add: boolean_algebra_def complemented_lattice_def)
  apply auto
  done

lemma [simp]: "bounded_lattice.top free_ba = bt_one"
  apply (simp add: bounded_lattice.top_def[OF free_ba_bl])
  apply (simp add: free_ba_def)
  apply (rule the1I2)
  apply auto
  apply (metis hba.or_one)
  apply (metis hba.comm)
  by (metis hba.comm hba.or_one)

lemma [simp]: "bounded_lattice.bot free_ba = bt_zero"
  apply (simp add: bounded_lattice.bot_def[OF free_ba_bl])
  apply (simp add: free_ba_def)
  apply (rule the1I2)
  apply auto
  apply (metis hba.comm hba.or_zero)
  apply (metis hba.or_zero)
  by (metis hba.or_zero)

interpretation ba: join_semilattice free_ba
  where "x \<squnion>\<^bsub>free_ba\<^esub> y = bt_or x y"
  and "x \<sqinter>\<^bsub>free_ba\<^esub> y = bt_and x y"
  and "carrier free_ba = UNIV"
  and "bounded_lattice.top free_ba = bt_one"
  and "bounded_lattice.bot free_ba = bt_zero"
  by (insert free_ba, simp_all add: boolean_algebra_def distributive_lattice_def lattice_def, auto)

interpretation ba: meet_semilattice free_ba
  where "x \<squnion>\<^bsub>free_ba\<^esub> y = bt_or x y"
  and "x \<sqinter>\<^bsub>free_ba\<^esub> y = bt_and x y"
  and "carrier free_ba = UNIV"
  and "bounded_lattice.top free_ba = bt_one"
  and "bounded_lattice.bot free_ba = bt_zero"
  by (insert free_ba, simp_all add: boolean_algebra_def distributive_lattice_def lattice_def, auto)

interpretation ba: boolean_algebra free_ba
  where "x \<squnion>\<^bsub>free_ba\<^esub> y = bt_or x y"
  and "x \<sqinter>\<^bsub>free_ba\<^esub> y = bt_and x y"
  and "carrier free_ba = UNIV"
  and "bounded_lattice.top free_ba = bt_one"
  and "bounded_lattice.bot free_ba = bt_zero"
  by (insert free_ba, simp_all)

end
