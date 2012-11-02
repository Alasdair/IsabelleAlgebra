theory Dioid
  imports Lattice
begin

(* +------------------------------------------------------------------------+ *)
subsection {* Dioids *}
(* +------------------------------------------------------------------------+ *)

record 'a dioid = "'a partial_object" +
  plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+\<index>" 70)
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<index>" 80)
  one :: "'a" ("1\<index>")
  zero :: "'a" ("0\<index>")

locale dioid = fixes A (structure)
  assumes add_closed: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x + y \<in> carrier A"
  and mult_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> carrier A"
  and one_closed: "(1::'a) \<in> carrier A"
  and zero_closed: "(0::'a) \<in> carrier A"
  and mult_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
  and add_assoc: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
  and add_comm: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x + y = y + x"
  and add_idem: "(x::'a) \<in> carrier A \<Longrightarrow> x + x = x"
  and distl: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>(y + z) = x\<cdot>y + x\<cdot>z"
  and distr: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x + y)\<cdot>z = x\<cdot>z + y\<cdot>z"
  and mult_onel: "(x::'a) \<in> carrier A \<Longrightarrow> 1\<cdot>x = x"
  and mult_oner: "(x::'a) \<in> carrier A \<Longrightarrow> x\<cdot>1 = x"
  and add_zerol: "(x::'a) \<in> carrier A \<Longrightarrow> 0 + x = x"
  and mult_zerol: "(x::'a) \<in> carrier A \<Longrightarrow> 0\<cdot>x = 0"
  and mult_zeror: "(x::'a) \<in> carrier A \<Longrightarrow> x\<cdot>0 = 0"

begin

  definition nat_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
    "x \<sqsubseteq> y \<equiv> x + y = y"

  abbreviation natural :: "'a ord" where
    "natural \<equiv> \<lparr>carrier = carrier A, le = nat_order\<rparr>"

  lemma natural: "order natural"
    by (default, auto simp add: nat_order_def, (metis add_idem add_assoc add_comm)+)

end

sublocale dioid \<subseteq> order "\<lparr>carrier = carrier A, le = nat_order\<rparr>" using natural .

sublocale dioid \<subseteq> join_semilattice "\<lparr>carrier = carrier A, le = nat_order\<rparr>"
  apply (default, auto simp add: order.is_lub_simp[OF natural])
  by (smt add_assoc add_closed add_comm add_idem nat_order_def)

context dioid
begin

  lemma add_zeror: "x \<in> carrier A \<Longrightarrow> x + 0 = x"
    by (metis add_comm add_zerol zero_closed)

  lemma add_lub: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z  \<longleftrightarrow> x + y \<sqsubseteq> z"
    by (metis add_assoc add_closed add_comm add_idem nat_order_def)

  lemma add_iso: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> z + x \<sqsubseteq> z + y"
    by (metis add_assoc add_closed add_comm add_idem nat_order_def)

  lemma mult_isol: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> z\<cdot>x \<sqsubseteq> z\<cdot>y"
    by (metis distl nat_order_def)

  lemma mult_isor: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> x\<cdot>z \<sqsubseteq> y\<cdot>z"
    by (metis distr nat_order_def)

  lemma mult_double_iso: "\<lbrakk>w \<in> carrier A; x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> w \<sqsubseteq> x \<and> y \<sqsubseteq> z \<longrightarrow> w\<cdot>y \<sqsubseteq> x\<cdot>z"
    by (smt add_assoc distl distr add_idem nat_order_def mult_closed)

  lemma subdistl: "\<lbrakk>x \<in>  carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z\<cdot>x \<sqsubseteq> z\<cdot>(x + y)"
    by (metis add_assoc add_closed add_idem nat_order_def mult_double_iso)

  lemma zero_min: "x \<in> carrier A \<Longrightarrow> 0 \<sqsubseteq> x"
    by (metis (lifting) add_zerol nat_order_def)

  lemma no_trivial_inverse: "\<forall>x\<in>carrier A.(x \<noteq> 0 \<longrightarrow> \<not>(\<exists>y\<in>carrier A.(x+y = 0)))"
    by (metis add_lub add_zeror nat_order_def zero_min)

  lemmas nat_antisym = order_antisym[simplified]
    and nat_refl = order_refl[simplified]
    and nat_trans = order_trans[simplified]

end

(* +------------------------------------------------------------------------+ *)
subsection {* Free Dioid *}
(* +------------------------------------------------------------------------+ *)

datatype 'a dioid_term = DioidAtom 'a
                       | DioidPlus "'a dioid_term" "'a dioid_term"
                       | DioidMult "'a dioid_term" "'a dioid_term"
                       | DioidOne
                       | DioidZero

primrec (in dioid) term_unfold :: "'a dioid_term \<Rightarrow> 'a" where
  "term_unfold (DioidAtom x) = x"
| "term_unfold (DioidPlus x y) = (term_unfold x) + (term_unfold y)"
| "term_unfold (DioidMult x y) = (term_unfold x) \<cdot> (term_unfold y)"
| "term_unfold DioidOne = 1"
| "term_unfold DioidZero = 0"

lemma (in dioid) term_fold_atom: "x \<in> carrier A \<Longrightarrow> x = term_unfold (DioidAtom x)"
  by (rule term_unfold.simps(1)[symmetric])

primrec (in dioid) term_atoms :: "'a dioid_term \<Rightarrow> 'a set" where
  "term_atoms (DioidAtom x) = {x}"
| "term_atoms (DioidPlus x y) = (term_atoms x) \<union> (term_atoms y)"
| "term_atoms (DioidMult x y) = (term_atoms x) \<union> (term_atoms y)"
| "term_atoms DioidOne = {}"
| "term_atoms DioidZero = {}"

lemma (in dioid) term_closure: "term_atoms x \<subseteq> carrier A \<Longrightarrow> term_unfold x \<in> carrier A"
  by (induct x, simp_all add: add_closed mult_closed one_closed zero_closed)

primrec dioid_term_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dioid_term \<Rightarrow> 'b dioid_term" where
  "dioid_term_map f (DioidAtom x) = DioidAtom (f x)"
| "dioid_term_map f (DioidPlus x y) = DioidPlus (dioid_term_map f x) (dioid_term_map f y)"
| "dioid_term_map f (DioidMult x y) = DioidMult (dioid_term_map f x) (dioid_term_map f y)"
| "dioid_term_map f DioidOne = DioidOne"
| "dioid_term_map f DioidZero = DioidZero"

inductive dioid_con :: "'a dioid_term \<Rightarrow> 'a dioid_term \<Rightarrow> bool" where
  refl [intro]: "dioid_con x x"
| sym [sym]: "dioid_con x y \<Longrightarrow> dioid_con y x"
| trans [trans]: "dioid_con x y \<Longrightarrow> dioid_con y z \<Longrightarrow> dioid_con x z"
| add_lift: "dioid_con x1 x2 \<Longrightarrow> dioid_con y1 y2 \<Longrightarrow> dioid_con (DioidPlus x1 y1) (DioidPlus x2 y2)"
| mult_lift: "dioid_con x1 x2 \<Longrightarrow> dioid_con y1 y2 \<Longrightarrow> dioid_con (DioidMult x1 y1) (DioidMult x2 y2)"
| mult_assoc: "dioid_con (DioidMult (DioidMult x y) z) (DioidMult x (DioidMult y z))"
| add_assoc: "dioid_con (DioidPlus (DioidPlus x y) z) (DioidPlus x (DioidPlus y z))"
| add_comm: "dioid_con (DioidPlus x y) (DioidPlus y x)"
| add_idem: "dioid_con (DioidPlus x x) x"
| distl: "dioid_con (DioidMult x (DioidPlus y z)) (DioidPlus (DioidMult x y) (DioidMult x z))"
| distr: "dioid_con (DioidMult (DioidPlus x y) z) (DioidPlus (DioidMult x z) (DioidMult y z))"
| mult_onel: "dioid_con (DioidMult DioidOne x) x"
| mult_oner: "dioid_con (DioidMult x DioidOne) x"
| add_zerol: "dioid_con (DioidPlus DioidZero x) x"
| mult_zerol: "dioid_con (DioidMult DioidZero x) DioidZero"
| mult_zeror: "dioid_con (DioidMult x DioidZero) DioidZero"

quotient_type 'a dioid_expr = "'a dioid_term" / dioid_con
  by (metis (lifting) dioid_con.refl dioid_con.sym dioid_con.trans equivpI reflpI sympI transpI)

lift_definition term_mult :: "'a dioid_expr \<Rightarrow> 'a dioid_expr \<Rightarrow> 'a dioid_expr" is DioidMult
  by (rule mult_lift, assumption+)

lift_definition term_plus :: "'a dioid_expr \<Rightarrow> 'a dioid_expr \<Rightarrow> 'a dioid_expr" is DioidPlus
  by (rule add_lift, assumption+)

lift_definition term_one :: "'a dioid_expr" is DioidOne
  by (rule dioid_con.refl)

lift_definition term_zero :: "'a dioid_expr" is DioidZero
  by (rule dioid_con.refl)

definition free_dioid :: "'a dioid_expr dioid" where
  "free_dioid = \<lparr>carrier = UNIV, plus = term_plus, mult = term_mult, one = term_one, zero = term_zero\<rparr>"

lemma "dioid free_dioid"
proof (unfold_locales, simp_all add: free_dioid_def)
  fix x y z
  show "term_mult (term_mult x y) z = term_mult x (term_mult y z)"
    by (transfer, rule dioid_con.mult_assoc)
  show "term_plus (term_plus x y) z = term_plus x (term_plus y z)"
    by (transfer, rule dioid_con.add_assoc)
  show "term_plus x y = term_plus y x"
    by (transfer, rule dioid_con.add_comm)
  show "term_plus x x = x"
    by (transfer, rule dioid_con.add_idem)
  show "term_mult x (term_plus y z) = term_plus (term_mult x y) (term_mult x z)"
    by (transfer, rule dioid_con.distl)
  show "term_mult (term_plus x y) z = term_plus (term_mult x z) (term_mult y z)"
    by (transfer, rule dioid_con.distr)
  show "term_mult term_one x = x"
    by (transfer, rule dioid_con.mult_onel)
  show "term_mult x term_one = x"
    by (transfer, rule dioid_con.mult_oner)
  show "term_plus term_zero x = x"
    by (transfer, rule dioid_con.add_zerol)
  show "term_mult term_zero x = term_zero"
    by (transfer, rule dioid_con.mult_zerol)
  show "term_mult x term_zero = term_zero"
    by (transfer, rule dioid_con.mult_zeror)
qed

ML {*

fun term_fold_tac fold_atom folds closure leaves =
  Subgoal.FOCUS (fn {context, prems, ...} =>
  let
    val witnesses = Locale.get_witnesses context
    val subst_thm = hd (witnesses RL [fold_atom])
    val subst_thms = prems RL [subst_thm]
    val folds = witnesses RL folds
    val to_leaves_thm = hd (witnesses RL [closure])
  in
    DETERM
      (Method.insert_tac subst_thms 1
      THEN REPEAT (etac @{thm ssubst} 1)
      THEN asm_full_simp_tac (HOL_basic_ss addsimps folds) 1)
    THEN (if leaves then rtac to_leaves_thm 1 else all_tac)
  end)

val dioid_term_fold_tac =
  term_fold_tac @{thm dioid.term_fold_atom} @{thms dioid.term_unfold.simps[symmetric]} @{thm dioid.term_closure}

*}

method_setup dioid_closure = {*
Scan.succeed (fn ctxt =>
  let
    val witnesses = Locale.get_witnesses ctxt
    val unfolds = witnesses RL @{thms dioid.term_atoms.simps}
  in
    METHOD (fn _ =>
      dioid_term_fold_tac true ctxt 1
      THEN asm_full_simp_tac (@{simpset} addsimps unfolds) 1)
  end)
*}

lemma (in dioid) "\<lbrakk>y\<cdot>y \<in> carrier A; x \<in> carrier A\<rbrakk> \<Longrightarrow> x + x + y\<cdot>y \<in> carrier A"
  by dioid_closure

end
