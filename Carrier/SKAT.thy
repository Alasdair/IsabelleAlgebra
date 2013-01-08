theory SKAT
  imports SKAT_Term
begin

(* +------------------------------------------------------------------------+ *)
subsection {* Schematic Kleene Algebra Expressions *}
(* +------------------------------------------------------------------------+ *)

datatype 'a skat_expr = SKLeaf nat "'a trm"
                      | SKPlus "'a skat_expr" "'a skat_expr" (infixl ":\<oplus>:" 70)
                      | SKMult "'a skat_expr" "'a skat_expr" (infixl ":\<odot>:" 80)
                      | SKStar "'a skat_expr"
                      | SKBool "'a pred bexpr"
                      | SKOne
                      | SKZero

primrec reads :: "'a::ranked_alphabet skat_expr \<Rightarrow> nat set" where
  "reads (SKLeaf x s) = FV s"
| "reads (SKPlus x y) = reads x \<union> reads y"
| "reads (SKMult x y) = reads x \<union> reads y"
| "reads (SKStar x) = reads x"
| "reads (SKBool p) = \<Union> (pred_vars ` bexpr_leaves p)"
| "reads SKOne = {}"
| "reads SKZero = {}"

primrec writes :: "'a::ranked_alphabet skat_expr \<Rightarrow> nat set" where
  "writes (SKLeaf x s) = {x}"
| "writes (SKPlus x y) = writes x \<union> writes y"
| "writes (SKMult x y) = writes x \<union> writes y"
| "writes (SKStar x) = writes x"
| "writes (SKBool p) = {}"
| "writes SKOne = {}"
| "writes SKZero = {}"

primrec touches :: "'a::ranked_alphabet skat_expr \<Rightarrow> nat set" where
  "touches (SKLeaf x s) = {x} \<union> FV s"
| "touches (SKPlus x y) = touches x \<union> touches y"
| "touches (SKMult x y) = touches x \<union> touches y"
| "touches (SKStar x) = touches x"
| "touches (SKBool p) = \<Union> (pred_vars ` bexpr_leaves p)"
| "touches SKOne = {}"
| "touches SKZero = {}"

lemma touches_rw: "touches t = writes t \<union> reads t"
  by (induct t, auto)

(* +------------------------------------------------------------------------+ *)
subsection {* Quotient Type *}
(* +------------------------------------------------------------------------+ *)

inductive skat_con :: "'a::ranked_alphabet skat_expr \<Rightarrow> 'a skat_expr \<Rightarrow> bool"
  where
  (* Basic equivalence conditions *)
  refl [intro]: "skat_con x x"
| sym [sym]: "skat_con x y \<Longrightarrow> skat_con y x"
| trans [trans]: "skat_con x y \<Longrightarrow> skat_con y z \<Longrightarrow> skat_con x z"

  (* Compatability conditions *)
| add_compat: "skat_con x1 x2 \<Longrightarrow> skat_con y1 y2 \<Longrightarrow> skat_con (SKPlus x1 y1) (SKPlus x2 y2)"
| mult_compat: "skat_con x1 x2 \<Longrightarrow> skat_con y1 y2 \<Longrightarrow> skat_con (SKMult x1 y1) (SKMult x2 y2)"
| star_compat: "skat_con x y \<Longrightarrow> skat_con (SKStar x) (SKStar y)"
| skat_not_compat: "skat_con (SKBool x) (SKBool y) \<Longrightarrow> skat_con (SKBool (BNot x)) (SKBool (BNot y))"

  (* Dioid laws for kexprs *)
| mult_assoc: "skat_con (SKMult (SKMult x y) z) (SKMult x (SKMult y z))"
| add_assoc: "skat_con (SKPlus (SKPlus x y) z) (SKPlus x (SKPlus y z))"
| add_comm: "skat_con (SKPlus x y) (SKPlus y x)"
| add_idem: "skat_con (SKPlus x x) x"
| distl: "skat_con (SKMult x (SKPlus y z)) (SKPlus (SKMult x y) (SKMult x z))"
| distr: "skat_con (SKMult (SKPlus x y) z) (SKPlus (SKMult x z) (SKMult y z))"
| mult_onel: "skat_con (SKMult SKOne x) x"
| mult_oner: "skat_con (SKMult x SKOne) x"
| add_zerol: "skat_con (SKPlus SKZero x) x"
| mult_zerol: "skat_con (SKMult SKZero x) SKZero"
| mult_zeror: "skat_con (SKMult x SKZero) SKZero"

  (* Kleene Algebra rules *)
| star_unfoldl: "skat_con (SKPlus (SKPlus SKOne (SKMult x (SKStar x))) (SKStar x)) (SKStar x)"
| star_unfoldr: "skat_con (SKPlus (SKPlus SKOne (SKMult (SKStar x) x)) (SKStar x)) (SKStar x)"
| star_inductl: "skat_con (SKPlus (SKPlus z (SKMult x y)) y) y \<Longrightarrow> skat_con (SKPlus (SKMult (SKStar x) z) y) y"
| star_inductr: "skat_con (SKPlus (SKPlus z (SKMult y x)) y) y \<Longrightarrow> skat_con (SKPlus (SKMult z (SKStar x)) y) y"

  (* Boolean Algebra rules *)
| test_ba: "hunt_con x y \<Longrightarrow> skat_con (SKBool x) (SKBool y)"
| test_zero: "skat_con SKZero (SKBool BZero)"
| test_one: "skat_con SKOne (SKBool BOne)"
| test_plus: "skat_con (SKBool (BAnd x y)) (SKMult (SKBool x) (SKBool y))"
| test_mult: "skat_con (SKBool (BOr x y)) (SKPlus (SKBool x) (SKBool y))"

| assign1: "\<lbrakk>x \<noteq> y; y \<notin> FV s\<rbrakk> \<Longrightarrow> skat_con (SKLeaf x s :\<odot>: SKLeaf y t) (SKLeaf y (t[x|s]) :\<odot>: SKLeaf x s)"
| assign2: "\<lbrakk>x \<noteq> y; x \<notin> FV s\<rbrakk> \<Longrightarrow> skat_con (SKLeaf x s :\<odot>: SKLeaf y t) (SKLeaf x s :\<odot>: SKLeaf y (t[x|s]))"
| assign3: "skat_con (SKLeaf x s :\<odot>: SKLeaf x t) (SKLeaf x (t[x|s]))"
| assign4: "skat_con (SKBool (bexpr_map (pred_subst x t) \<phi>) :\<odot>: SKLeaf x t) (SKLeaf x t :\<odot>: SKBool \<phi>)"

lemma skat_con_eq: "x = y \<Longrightarrow> skat_con x y" by (simp add: skat_con.refl)

quotient_type 'a skat = "'a::ranked_alphabet skat_expr" / skat_con
proof (auto simp add: equivp_def)
  fix x y assume "skat_con x y"
  thus "skat_con x = skat_con y"
    apply (subgoal_tac "\<forall>z. skat_con x z = skat_con y z")
    apply auto
    by (metis skat_con.sym skat_con.trans)+
qed

(* +------------------------------------------------------------------------+ *)
subsection {* Lifting Definitions *}
(* +------------------------------------------------------------------------+ *)

lift_definition skat_assign :: "nat \<Rightarrow> 'a::ranked_alphabet trm \<Rightarrow> 'a skat"
  (infix ":=" 100) is SKLeaf
  by (rule skat_con.refl)

lift_definition skat_mult :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat" (infixl "\<cdot>" 80) is SKMult
  by (rule mult_compat, assumption+)

lift_definition skat_plus :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat" (infixl "+" 70) is SKPlus
  by (rule add_compat, assumption+)

no_notation
  dioid.plus (infixl "+\<index>" 70) and
  dioid.mult (infixl "\<cdot>\<index>" 80)

lift_definition skat_one :: "'a::ranked_alphabet skat" ("\<one>") is SKOne
  by (rule skat_con.refl)

lift_definition skat_zero :: "'a::ranked_alphabet skat" ("\<zero>") is SKZero
  by (rule skat_con.refl)

no_notation
  dioid.one ("\<one>\<index>") and
  dioid.zero ("\<zero>\<index>")

lift_definition skat_star :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat" ("_\<^sup>\<star>" [101] 100) is SKStar
  by (rule star_compat, assumption)

no_notation
  kleene_algebra.star ("_\<^sup>\<star>\<index>" [101] 100)

definition skat_star1 :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat" ("_\<^sup>+" [101] 100) where
  "skat_star1 x = x\<cdot>x\<^sup>\<star>"

lift_definition test :: "'a::ranked_alphabet pred bterm \<Rightarrow> 'a skat" is SKBool
  by (rule skat_con.test_ba, assumption)

lift_definition pred_expr :: "'a::ranked_alphabet pred bexpr \<Rightarrow> 'a skat" is SKBool
  by (metis skat_con.refl)

lift_definition skat_bexpr_not :: "'a::ranked_alphabet pred bexpr \<Rightarrow> 'a skat" is "SKBool \<circ> BNot"
  by auto

definition skat_not :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat" ("!") where
  "!x \<equiv> if (\<exists>P. x = abs_skat (SKBool P)) then skat_bexpr_not (SOME P. x = abs_skat (SKBool P)) else undefined"

lift_definition pred :: "'a::ranked_alphabet pred \<Rightarrow> 'a skat" is "SKBool \<circ> BLeaf" by auto

lemma pred_to_expr: "pred \<phi> = pred_expr (BLeaf \<phi>)"
  by (simp add: pred_def pred_expr_def)

primrec test_unfold :: "'a::ranked_alphabet pred bexpr \<Rightarrow> 'a skat" where
  "test_unfold (BLeaf x) = pred x"
| "test_unfold (BOr x y) = test_unfold x + test_unfold y"
| "test_unfold (BAnd x y) = test_unfold x \<cdot> test_unfold y"
| "test_unfold (BNot x) = !(test_unfold x)"
| "test_unfold BOne = \<one>"
| "test_unfold BZero = \<zero>"

lemma not_test_unfold: "!(test_unfold x) = test_unfold (BNot x)" by simp

lemma pred_expr_not: "!(pred_expr p) = pred_expr (BNot p)"
  apply (simp add: skat_not_def)
  apply auto
  defer
  apply (metis map_fun_apply pred_expr_def)
  apply (rule someI2)
  apply auto
proof -
  fix P x assume "pred_expr p = abs_skat (SKBool x)"
  thus "skat_bexpr_not x = pred_expr (BNot p)"
    apply transfer
    apply simp
    by (metis skat_con.sym skat_not_compat)
qed

lemma pred_expr_unfold: "test_unfold p = pred_expr p"
  apply (induct p)
  apply (metis pred_to_expr test_unfold.simps(1))
proof simp_all
  fix p1 p2
  show "pred_expr p1 + pred_expr p2 = pred_expr (p1 :+: p2)"
    by (transfer, metis (lifting) skat_con.sym test_mult)
  show "!(pred_expr p1) = pred_expr (BNot p1)"
    by (metis pred_expr_not)
  show "pred_expr p1 \<cdot> pred_expr p2 = pred_expr (p1 :\<cdot>: p2)"
    by (transfer, metis skat_con.sym test_plus)
  show "\<one> = pred_expr BOne"
    by (transfer, metis test_one)
  show "\<zero> = pred_expr BZero"
    by (transfer, metis test_zero)
qed

primrec skat_unfold :: "'a::ranked_alphabet skat_expr \<Rightarrow> 'a skat" ("\<lfloor>_\<rfloor>" [111] 110) where
  "skat_unfold (SKLeaf x y) = x := y"
| "skat_unfold (SKPlus x y) = skat_unfold x + skat_unfold y"
| "skat_unfold (SKMult x y) = skat_unfold x \<cdot> skat_unfold y"
| "skat_unfold (SKBool p) = test_unfold p"
| "skat_unfold SKOne = \<one>"
| "skat_unfold SKZero = \<zero>"
| "skat_unfold (SKStar x) = (skat_unfold x)\<^sup>\<star>"

primrec atoms :: "'a::ranked_alphabet skat_expr \<Rightarrow> 'a skat_expr set" where
  "atoms (SKLeaf x y) = {SKLeaf x y}"
| "atoms (SKPlus x y) = atoms x \<union> atoms y"
| "atoms (SKMult x y) = atoms x \<union> atoms y"
| "atoms (SKBool p) = SKBool ` BLeaf ` bexpr_leaves p"
| "atoms SKOne = {}"
| "atoms SKZero = {}"
| "atoms (SKStar x) = atoms x"

lemma FV_null [simp]: "FV null = {}"
  by (simp add: null_def)

lemma read_atoms: "a \<in> atoms s \<Longrightarrow> reads a \<subseteq> reads s"
  by (induct s, auto)

lemma write_atoms: "a \<in> atoms s \<Longrightarrow> writes a \<subseteq> writes s"
  by (induct s, auto)

lemma touch_atoms: "a \<in> atoms s \<Longrightarrow> touches a \<subseteq> touches s"
  by (induct s, auto)

lemma unfold_is_abs: "\<lfloor>y\<rfloor> = abs_skat y"
proof (induct y, simp_all)
  fix x s show "x := s = abs_skat (SKLeaf x s)"
    by (transfer, metis skat_con.refl)
next
  fix s t show "abs_skat s + abs_skat t = abs_skat (s :\<oplus>: t)"
    by (transfer, metis skat_con.refl)
next
  fix s t show "abs_skat s \<cdot> abs_skat t = abs_skat (s :\<odot>: t)"
    by (transfer, metis skat_con.refl)
next
  fix s show "abs_skat s\<^sup>\<star> = abs_skat (SKStar s)"
    by (transfer, metis skat_con.refl)
next
  fix a
  have "pred_expr a = abs_skat (SKBool a)"
    by (transfer, metis skat_con.refl)
  thus "test_unfold a = abs_skat (SKBool a)"
    by (subst pred_expr_unfold)
next
  show "\<one> = abs_skat SKOne"
    by (transfer, metis skat_con.refl)
next
  show "\<zero> = abs_skat SKZero"
    by (transfer, metis skat_con.refl)
qed

lemma unfold_exists: "\<exists>t. \<lfloor>t\<rfloor> = s"
  by (metis Quotient3_abs_rep Quotient3_skat unfold_is_abs)

lemma unfold_transfer: "\<lfloor>x\<rfloor> = \<lfloor>y\<rfloor> \<longleftrightarrow> skat_con x y"
  by (simp add: unfold_is_abs, transfer, simp)

(* +------------------------------------------------------------------------+ *)
subsection {* Assignment Rules *}
(* +------------------------------------------------------------------------+ *)

lemma skat_assign1: "\<lbrakk>x \<noteq> y; y \<notin> FV s\<rbrakk> \<Longrightarrow> (x := s \<cdot> y := t) = (y := t[x|s] \<cdot> x := s)"
  by (transfer, rule skat_con.assign1)

lemma skat_assign1_var: "\<lbrakk>x \<noteq> y; y \<notin> FV s; t' = t[x|s]\<rbrakk> \<Longrightarrow> (x := s \<cdot> y := t) = (y := t' \<cdot> x := s)"
  by (metis skat_assign1)

lemma skat_assign2: "\<lbrakk>x \<noteq> y; x \<notin> FV s\<rbrakk> \<Longrightarrow> (x := s \<cdot> y := t) = (x := s \<cdot> y := t[x|s])"
  by (transfer, rule skat_con.assign2)

lemma skat_assign2_var: "\<lbrakk>x \<noteq> y; x \<notin> FV s; t' = t[x|s]\<rbrakk> \<Longrightarrow> (x := s \<cdot> y := t) = (x := s \<cdot> y := t')"
  by (metis skat_assign2)

lemma skat_assign3: "(x := s \<cdot> x := t) = (x := t[x|s])"
  by (transfer, rule skat_con.assign3)

lemma skat_assign4: "(pred (\<phi>[x|t]) \<cdot> x := t) = (x := t \<cdot> pred \<phi>)"
  by (transfer, metis assign4 bexpr_map.simps(1) o_apply)

lemma skat_assign4_var: "\<psi> = \<phi>[x|t] \<Longrightarrow> (pred \<psi> \<cdot> x := t) = (x := t \<cdot> pred \<phi>)"
  by (erule ssubst, rule skat_assign4)

lemma skat_assign_comm: "\<lbrakk>x \<noteq> y; x \<notin> FV t; y \<notin> FV s\<rbrakk> \<Longrightarrow> (x := s \<cdot> y := t) = (y := t \<cdot> x := s)"
  by (insert skat_assign1[of x y s t], simp)

lemma skat_pred_comm: "x \<notin> pred_vars \<phi> \<Longrightarrow> pred \<phi> \<cdot> x := s = x := s \<cdot> pred \<phi>"
  by (metis no_pred_vars skat_assign4)

lemma skat_null_zero: "(x := s \<cdot> x := null) = (x := null)"
proof -
  have "(x := s \<cdot> x := null) = (x := null[x|s])"
    by (rule skat_assign3)
  also have "... = x := null"
    by (simp add: null_def)
  finally show ?thesis .
qed

lemma skat_null_comm: "(x := null \<cdot> y := null) = (y := null \<cdot> x := null)"
  by (metis FV_null empty_iff skat_assign_comm)

(* +------------------------------------------------------------------------+ *)
subsection {* Interpretations *}
(* +------------------------------------------------------------------------+ *)

definition test_set :: "'a::ranked_alphabet skat set" where
  "test_set \<equiv> test ` UNIV"

definition tests :: "'a::ranked_alphabet skat ord" where
  "tests \<equiv> \<lparr>carrier = test_set, le = (\<lambda>x y. skat_plus x y = y)\<rparr>"

definition free_kat :: "'a::ranked_alphabet skat test_algebra" where
  "free_kat = \<lparr>carrier = UNIV, plus = skat_plus, mult = skat_mult, one = skat_one, zero = skat_zero, star = skat_star, test_algebra.test = tests\<rparr>"

definition skat_order :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
  "x \<sqsubseteq> y \<equiv> x + y = y"

lemma free_kat_dioid: "dioid free_kat"
proof (unfold_locales, simp_all add: free_kat_def)
  fix x y z
  show "skat_mult (skat_mult x y) z = skat_mult x (skat_mult y z)"
    by (transfer, rule skat_con.mult_assoc)
  show "skat_plus (skat_plus x y) z = skat_plus x (skat_plus y z)"
    by (transfer, rule skat_con.add_assoc)
  show "skat_plus x y = skat_plus y x"
    by (transfer, rule skat_con.add_comm)
  show "skat_plus x x = x"
    by (transfer, rule skat_con.add_idem)
  show "skat_mult x (skat_plus y z) = skat_plus (skat_mult x y) (skat_mult x z)"
    by (transfer, rule skat_con.distl)
  show "skat_mult (skat_plus x y) z = skat_plus (skat_mult x z) (skat_mult y z)"
    by (transfer, rule skat_con.distr)
  show "skat_mult skat_one x = x"
    by (transfer, rule skat_con.mult_onel)
  show "skat_mult x skat_one = x"
    by (transfer, rule skat_con.mult_oner)
  show "skat_plus skat_zero x = x"
    by (transfer, rule skat_con.add_zerol)
  show "skat_mult skat_zero x = skat_zero"
    by (transfer, rule skat_con.mult_zerol)
  show "skat_mult x skat_zero = skat_zero"
    by (transfer, rule skat_con.mult_zeror)
qed

interpretation skd: dioid free_kat
  where "dioid.plus free_kat x y = skat_plus x y"
  and "dioid.zero free_kat = \<zero>"
  and "dioid.mult free_kat x y = x \<cdot> y"
  and "dioid.one free_kat = \<one>"
  and "x \<in> carrier free_kat = True"
  and "dioid.nat_order free_kat x y = (x \<sqsubseteq> y)"
  apply (simp add: free_kat_dioid)
  apply (simp_all add: dioid.nat_order_def[OF free_kat_dioid] skat_order_def)
  by (simp_all add: free_kat_def)

lemma free_kat_ka: "kleene_algebra free_kat"
  apply unfold_locales
  apply (simp_all add: dioid.nat_order_def[OF free_kat_dioid])
proof (simp_all add: free_kat_def)
  fix x y z
  show "\<one> + x \<cdot> skat_star x + skat_star x = skat_star x"
    by (transfer, rule skat_con.star_unfoldl)
  show "\<one> + skat_star x \<cdot> x + skat_star x = skat_star x"
    by (transfer, rule skat_con.star_unfoldr)
  show "z + x \<cdot> y + y = y \<longrightarrow> skat_star x \<cdot> z + y = y"
    by (transfer, metis skat_con.star_inductl)
  show "z + y \<cdot> x + y = y \<longrightarrow> z \<cdot> skat_star x + y = y"
    by (transfer, metis skat_con.star_inductr)
qed

(* PR4 *)

interpretation ska: kleene_algebra free_kat
  where "dioid.plus free_kat x y = x + y"
  and "dioid.zero free_kat = \<zero>"
  and "dioid.mult free_kat x y = x\<cdot>y"
  and "dioid.one free_kat = \<one>"
  and "kleene_algebra.star free_kat x = x\<^sup>\<star>"
  and "dioid.nat_order free_kat x y = (x \<sqsubseteq> y)"
  apply (simp add: free_kat_ka)
  apply (simp_all add: dioid.nat_order_def[OF free_kat_dioid] skat_order_def)
  by (simp_all add: free_kat_def)

lemma test_closed_set: "test z \<in> test_set"
  by (simp add: test_set_def)

lemma test_closed: "test z \<in> carrier tests"
  by (simp add: tests_def, rule test_closed_set)

lemma test_to_pred_expr: "test = pred_expr \<circ> rep_bterm"
  by (metis SKAT.test_def map_fun_def o_id pred_expr_def)

lemma pred_expr_test: "pred_expr p = test (abs_bterm p)"
  by (simp add: pred_expr_def, transfer, rule skat_con.refl)

lemma pred_expr_closed: "pred_expr x \<in> carrier tests"
  by (metis pred_expr_test test_closed)

lemma not_closed: "x \<in> carrier tests \<Longrightarrow> !x \<in> carrier tests"
proof (simp add: tests_def)
  assume "x \<in> test_set"
  then obtain x' where "x = pred_expr x'"
    by (auto simp add: test_set_def test_to_pred_expr o_def)
  have "!(pred_expr x') = pred_expr (BNot x')"
    by (metis pred_expr_not)
  hence "!(pred_expr x') \<in> test_set"
    by (metis pred_expr_test test_closed_set)
  from `x = pred_expr x'` and this show "!x \<in> test_set"
    by auto
qed

lemma test_ex: "x \<in> test_set \<Longrightarrow> \<exists>y. x = test y"
  by (simp add: test_set_def image_iff)

lemma pred_test: "pred p = test (abs_bterm (BLeaf p))"
  by (simp add: pred_def, transfer, rule skat_con.refl)

lemma pred_closed: "pred p \<in> carrier tests"
  by (simp add: pred_test, rule test_closed)

(* Transfer concepts from skat to the embedded algebra *)

lemma one_to_test: "\<one> = test (bt_one)"
  by (transfer, rule test_one)

lemma test_one_closed: "\<one> \<in> carrier tests"
  by (metis one_to_test test_closed)

lemma zero_to_test: "\<zero> = test (bt_zero)"
  by (transfer, rule test_zero)

lemma test_zero_closed: "\<zero> \<in> carrier tests"
  by (metis test_closed zero_to_test)

lemma mult_to_test: "test x \<cdot> test y = test (bt_and x y)"
  by (transfer, metis skat_con.sym test_plus)

lemma test_mult_closed:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "x \<cdot> y \<in> carrier tests"
proof -
  from xc yc obtain x' and y' where "x = test x'" and "y = test y'"
    by (simp add: tests_def, metis test_ex)
  moreover have "test x' \<cdot> test y' \<in> carrier tests"
    by (simp add: mult_to_test, rule test_closed)
  ultimately show "x \<cdot> y \<in> carrier tests"
    by auto
qed

lemma plus_to_test: "test x + test y = test (bt_or x y)"
  by (transfer, metis skat_con.sym test_mult)

lemma test_plus_closed:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "x + y \<in> carrier tests"
proof -
  from xc yc obtain x' and y' where "x = test x'" and "y = test y'"
    by (simp add: tests_def, metis test_ex)
  moreover have "test x' + test y' \<in> carrier tests"
    by (simp add: plus_to_test, rule test_closed)
  ultimately show "x + y \<in> carrier tests"
    by auto
qed

lemma not_to_not: "!(test x) = test (bt_not x)"
  by (metis (full_types) Quotient3_abs_rep Quotient3_bterm bt_not_def map_fun_apply pred_expr_test pred_expr_unfold test_unfold.simps(4))

lemma test_eq: "x = y \<Longrightarrow> test x = test y" by auto

(* The tests algebra is an partial order *)

lemma tests_ord: "order tests"
  apply (unfold_locales, simp_all add: tests_def)
  apply (metis skd.add_idem)
  apply (metis skd.add_assoc)
  by (metis skd.add_comm)

lemmas or_to_plus = plus_to_test[symmetric]

lemma tests_lub:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "order.is_lub tests (x + y) {x, y}"
proof (simp add: order.is_lub_simp[OF tests_ord], simp_all add: tests_def, safe)
  from xc and yc obtain x' and y' where x'_def: "x = test x'" and y'_def: "y = test y'"
    by (simp add: tests_def, metis test_ex)

  show "x \<in> test_set" and "y \<in> test_set"
    by (insert xc yc, simp_all add: tests_def)

  show "skat_plus x y \<in> test_set"
    by (simp add: x'_def y'_def plus_to_test, rule test_closed_set)

  show "skat_plus x (skat_plus x y) = skat_plus x y"
    by (metis skd.add_assoc skd.add_idem)

  show "skat_plus y (skat_plus x y) = skat_plus x y"
    by (metis skd.add_assoc skd.add_comm skd.add_idem)

  fix w :: "'a skat"
  assume "w \<in> test_set" and xw: "skat_plus x w = w" and yw: "skat_plus y w = w"
  then obtain w' where w'_def: "w = test w'" by (metis test_ex)
  from xw have "skat_plus (test x') w = w"
    by (metis x'_def)
  from w'_def and this have "skat_plus (test x') (test w') = (test w')"
    by simp
  from this[symmetric] show "skat_plus (skat_plus x y) w = w"
    apply (simp add: plus_to_test x'_def y'_def w'_def)
    by (metis or_to_plus skd.add_assoc w'_def x'_def xw y'_def yw)
qed

lemma "test x + test y = test y \<Longrightarrow> test y \<cdot> test x = test x"
  apply (simp add: plus_to_test mult_to_test)
  by (metis UNIV_I ba.absorb2 ba.meet_comm mult_to_test)

lemma test_meet_leq1:
  assumes xc: "x \<in> carrier tests"
  and yc: "y \<in> carrier tests"
  shows "x + y = y \<longleftrightarrow> y \<cdot> x = x"
proof -
  have "\<forall>x y. test x + test y = test y \<longrightarrow> test y \<cdot> test x = test x"
    apply (simp add: plus_to_test mult_to_test)
    by (metis UNIV_I ba.absorb2 ba.meet_comm mult_to_test)

  moreover have "\<forall>x y. test y \<cdot> test x = test x \<longrightarrow> test x + test y = test y"
    apply (simp add: plus_to_test mult_to_test)
    by (metis UNIV_I ba.absorb1 ba.join_comm or_to_plus)

  ultimately show ?thesis using xc yc
    by (simp add: tests_def test_set_def, auto)
qed

lemma test_meet_leq:
  "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> (x \<sqsubseteq>\<^bsub>tests\<^esub> y) = (y \<cdot> x = x)"
  by (simp add: tests_def test_meet_leq1)

lemma tests_glb:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "order.is_glb tests (x \<cdot> y) {x, y}"
  apply (simp add: order.is_glb_simp[OF tests_ord])
  apply (insert xc yc, subgoal_tac "x \<cdot> y \<in> carrier tests")
  apply (simp add: test_meet_leq)
  apply (simp add: tests_def)
  defer
  apply (metis test_mult_closed)
proof safe
  from xc and yc obtain x' and y' where x'_def: "x = test x'" and y'_def: "y = test y'"
    by (simp add: tests_def, metis test_ex)

  show "x \<cdot> (x \<cdot> y) = x \<cdot> y"
    apply (simp add: x'_def y'_def mult_to_test, rule test_eq)
    by (metis UNIV_I ba.meet_assoc ba.meet_idem)

  show "y \<cdot> (x \<cdot> y) = x \<cdot> y"
    apply (simp add: x'_def y'_def mult_to_test, rule test_eq)
    by (metis UNIV_I ba.meet_assoc ba.meet_comm ba.meet_idem)

  fix w :: "'a skat"
  assume "w \<in> test_set" and xw: "x \<cdot> w = w" and yw: "y \<cdot> w = w"
  then obtain w' where w'_def: "w = test w'" by (metis test_ex)
  from xw have "(test x') \<cdot> w = w"
    by (metis x'_def)
  from w'_def and this have "(test x') \<cdot> (test w') = (test w')"
    by simp
  from this[symmetric] show "(x \<cdot> y) \<cdot> w = w"
    apply (simp add: mult_to_test x'_def y'_def w'_def)
    by (metis UNIV_I ba.meet_assoc mult_to_test w'_def y'_def yw)
qed

lemma tests_js: "join_semilattice tests"
proof (simp add: join_semilattice_def join_semilattice_axioms_def, safe)
  show "order tests" using tests_ord .

  fix x y :: "'a skat" assume "x \<in> carrier tests" and "y \<in> carrier tests"
  thus "\<exists>z\<in>carrier tests. order.is_lub tests z {x, y}"
    apply (intro bexI) by (rule tests_lub, assumption+, metis test_plus_closed)
qed

lemma tests_join [simp]: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> x \<squnion>\<^bsub>tests\<^esub> y = x + y"
  by (metis tests_ord order.join_def order.lub_is_lub tests_lub)

lemma tests_ms: "meet_semilattice tests"
proof (simp add: meet_semilattice_def meet_semilattice_axioms_def, safe)
  show "order tests" using tests_ord .

  fix x y :: "'a skat" assume "x \<in> carrier tests" and "y \<in> carrier tests"
  thus "\<exists>z\<in>carrier tests. order.is_glb tests z {x, y}"
    apply (intro bexI) by (rule tests_glb, assumption+, metis test_mult_closed)
qed

lemma tests_meet [simp]: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> x \<sqinter>\<^bsub>tests\<^esub> y = x \<cdot> y"
  by (metis tests_ord order.meet_def order.glb_is_glb tests_glb)

lemma tests_lattice: "lattice tests"
  unfolding lattice_def by (metis tests_js tests_ms)

lemma tests_bounded: "bounded_lattice tests"
  apply (simp add: bounded_lattice_def bounded_lattice_axioms_def, safe)
  apply (metis tests_lattice)
  apply (rule_tac x = "\<zero>::'a::ranked_alphabet skat" in bexI)
  apply (metis skd.add_zerol)
  apply (metis test_zero_closed)
  apply (rule_tac x = "\<one>::'a::ranked_alphabet skat" in bexI)
  apply (metis skd.mult_onel)
  apply (metis test_one_closed)
  done

lemma test_top_is_one [simp]: "bounded_lattice.top tests = \<one>"
  by (metis bounded_lattice.top_closed bounded_lattice.top_greatest skd.mult_oner test_meet_leq test_one_closed tests_bounded)

lemma test_bot_is_zero [simp]: "bounded_lattice.bot tests = \<zero>"
  by (metis bounded_lattice.bot_closed bounded_lattice.bot_least skd.mult_zerol test_meet_leq test_zero_closed tests_bounded)

lemma tests_distributive: "distributive_lattice tests"
proof (simp add: distributive_lattice_def distributive_lattice_axioms_def, safe)
  show "lattice tests"
    by (metis tests_lattice)

  fix x y z :: "'a skat"
  assume xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests" and zc: "z \<in> carrier tests"
  thus "(x \<sqinter>\<^bsub>tests\<^esub> (y + z)) = (x \<cdot> y \<squnion>\<^bsub>tests\<^esub> x \<cdot> z)"
    by (metis skd.distl test_mult_closed test_plus_closed tests_join tests_meet)
  from xc yc zc show "x \<squnion>\<^bsub>tests\<^esub> (y \<cdot> z) = (x + y) \<sqinter>\<^bsub>tests\<^esub> (x + z)"
    apply (subgoal_tac "y \<cdot> z \<in> carrier tests" "x + y \<in> carrier tests" "x + z \<in> carrier tests")
    defer
    apply (metis test_plus_closed test_mult_closed)+
    apply simp
  proof -
    from xc yc zc obtain x' y' z' where "x = test x'" and "y = test y'" and "z = test z'"
      by (simp add: tests_def, metis test_ex)
    thus "x + y \<cdot> z = (x + y) \<cdot> (x + z)"
      apply (simp add: plus_to_test mult_to_test)
      apply (rule test_eq)
      by (metis UNIV_I ba.dist2)
  qed
qed

lemma tests_complemented: "complemented_lattice tests"
proof (simp add: complemented_lattice_def complemented_lattice_axioms_def, safe)
  show "bounded_lattice tests"
    by (metis tests_bounded)

  fix x assume xc: "x \<in> carrier tests"
  thus "\<exists>y. y \<in> carrier tests \<and> x \<squnion>\<^bsub>tests\<^esub> y = \<one> \<and> x \<sqinter>\<^bsub>tests\<^esub> y = \<zero>"
    apply (rule_tac x = "!x" in exI)
    apply (subgoal_tac "!x \<in> carrier tests", safe)
    apply simp_all
    prefer 3
    apply (metis not_closed)
  proof -
    assume "!x \<in> carrier tests"
    from xc obtain x' where "x = test x'"
      by (simp add: tests_def, metis test_ex)
    thus "x + !x = \<one>"
      apply (simp add: not_to_not plus_to_test one_to_test)
      apply (rule test_eq)
      by (transfer, rule hunt_con.one)
    from `x = test x'` show "x \<cdot> !x = \<zero>"
      apply (simp add: not_to_not mult_to_test zero_to_test)
      apply (rule test_eq)
      apply transfer
      by (metis hunt_con.trans meet Boolean_Algebra_Extras.not_compat one zero)
  qed
qed

lemma tests_ba: "boolean_algebra tests"
  by (simp add: boolean_algebra_def, metis tests_complemented tests_distributive)

lemma free_kat': "kat' free_kat"
proof (simp add: kat'_def, safe)
  show "kleene_algebra free_kat"
    by (rule free_kat_ka)
  show "\<And>x. x \<in> KAT.tests free_kat \<Longrightarrow> x \<in> carrier free_kat"
    by (simp add: free_kat_def)
  have "\<forall>x y. x \<sqsubseteq>\<^bsub>test_algebra.test free_kat\<^esub> y = dioid.nat_order free_kat x y"
    by (simp add: dioid.nat_order_def[OF free_kat_dioid], simp add: free_kat_def tests_def)
  thus "op \<sqsubseteq>\<^bsub>test_algebra.test free_kat\<^esub> = dioid.nat_order free_kat"
    by auto
  show "boolean_algebra (test_algebra.test free_kat)"
    by (simp add: free_kat_def tests_ba)
qed

lemma free_kat: "kat free_kat"
  by (simp add: kat_def kat_axioms_def, rule conjI, rule free_kat', simp add: free_kat_def)

declare pred_expr_not [simp]

lemma kat_comp_simp [simp]: "x \<in> carrier tests \<Longrightarrow> KAT.kat.complement free_kat x = !x"
  apply (subst KAT.kat.complement_def[OF free_kat])
  apply (rule the1I2)
  apply auto
  apply (simp_all add: free_kat_def)
  apply (rule_tac x = "!x" in exI)
  apply auto
  apply (metis not_closed)
  prefer 3
  apply (metis (lifting) boolean_algebra.compl_uniq test_bot_is_zero test_top_is_one tests_ba tests_join tests_meet)
proof -
  fix y :: "'a skat" assume "x \<in> carrier tests" and "y \<in> carrier tests"
  then obtain x' and y' where
    x'_def[simp]: "x = pred_expr x'" and y'_def[simp]: "y = pred_expr y'"
    by (auto simp add: tests_def test_set_def test_to_pred_expr o_def)
  show a: "x + !x = \<one>"
  proof (simp, transfer)
    fix x
    show "skat_con (SKBool x :\<oplus>: SKBool (BNot x)) SKOne"
      by (smt one skat_con.sym skat_con.trans test_ba test_mult test_one)
  qed
  show b: "x \<cdot> ! x = \<zero>"
  proof (simp, transfer)
    fix x
    have "skat_con (SKBool (x :\<cdot>: BNot x)) SKZero"
      by (metis hunt_con.trans meet not_compat one skat_con.sym skat_con.trans test_ba test_zero zero)
    thus "skat_con (SKBool x :\<odot>: SKBool (BNot x)) SKZero"
      by (smt skat_con.sym skat_con.trans test_plus)
  qed
  assume "x + y = \<one>" and "x \<cdot> y = \<zero>"
  from this and a b show "y = !x"
    by (smt x'_def y'_def boolean_algebra.compl_uniq pred_expr_closed pred_expr_not test_bot_is_zero test_top_is_one tests_ba tests_join tests_meet)
qed

interpretation skt: kat free_kat
  where "dioid.plus free_kat x y = x + y"
  and "dioid.zero free_kat = \<zero>"
  and "dioid.mult free_kat x y = x\<cdot>y"
  and "dioid.one free_kat = \<one>"
  and "kleene_algebra.star free_kat x = x\<^sup>\<star>"
  and "dioid.nat_order free_kat x y = (x \<sqsubseteq> y)"
  and "KAT.tests free_kat = carrier tests"
  apply (simp add: free_kat)
  apply (simp_all add: dioid.nat_order_def[OF free_kat_dioid] skat_order_def)
  apply (simp_all add: free_kat_def)
  done

(* Interpretation statement can't import BA rules properly *)

lemma complement_one: "p \<in> carrier tests \<Longrightarrow> p + !p = \<one>"
  by (metis kat_comp_simp skt.complement1)

lemma complement_zero: "p \<in> carrier tests \<Longrightarrow> p \<cdot> !p = \<zero>"
  by (metis kat_comp_simp skt.complement2)

lemma test_under_one: "p \<in> carrier tests \<Longrightarrow> p \<sqsubseteq> \<one>"
  by (metis skt.test_under_one)

lemma test_double_compl: "p \<in> carrier tests \<Longrightarrow> p = !(!p)"
  by (metis kat_comp_simp not_closed skt.test_double_compl)

lemma de_morgan1: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> !p \<cdot> !q = !(p + q)"
  by (smt kat_comp_simp skt.de_morgan1 test_plus_closed)

lemma test_meet_def: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p \<cdot> q = !(!p + !q)"
  by (metis (lifting) de_morgan1 not_closed test_double_compl)

lemma de_morgan2: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> !p + !q = !(p \<cdot> q)"
  by (smt not_closed test_double_compl test_meet_def test_plus_closed)

lemma test_compl_anti: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p \<sqsubseteq> q \<longleftrightarrow> !q \<sqsubseteq> !p"
  by (metis kat_comp_simp skt.test_compl_anti)

lemma test_join_def: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p + q = !(!p \<cdot> !q)"
  by (metis (lifting) de_morgan2 not_closed test_double_compl)

lemma ba_3: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p = (p \<cdot> q) + (p \<cdot> !q)"
  by (metis (lifting) complement_one skd.distl skd.mult_oner)

lemma ba_5: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> (p + q) \<cdot> !p = q \<cdot> !p"
  by (metis (lifting) complement_zero skd.add_zerol skd.distr)

lemma compl_1: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> !p = !(p + q) + !(p + !q)"
  by (metis (lifting) ba_3 de_morgan1 not_closed)

lemma ba_1: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests; r \<in> carrier tests\<rbrakk> \<Longrightarrow> p + q + !q = r + !r"
  by (metis (lifting) complement_one skat_order_def skd.add_assoc test_under_one)

lemma ba_2: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p + p = p + !(q + !q)"
  by (metis complement_one kat_comp_simp skd.add_idem skd.add_zeror skt.test_not_one test_one_closed)

lemma ba_4: "\<lbrakk>p \<in> carrier tests; q \<in> carrier tests\<rbrakk> \<Longrightarrow> p = (p + !q) \<cdot> (p + q)"
  by (metis complement_zero not_closed skd.add_zeror skt.test_dist2 skt.test_mult_comm)

lemma shunting:
  assumes pc: "p \<in> carrier tests" and qc: "q \<in> carrier tests" and rc: "r \<in> carrier tests"
  shows "p \<cdot> q \<sqsubseteq> r \<longleftrightarrow> q \<sqsubseteq> !p + r"
  by (metis kat_comp_simp pc qc rc skt.shunting)

lemma kat1:
  assumes bt: "b \<in> carrier tests" and ct: "c \<in> carrier tests"
  shows "b\<cdot>p = p\<cdot>c \<longleftrightarrow> b\<cdot>p\<cdot>!c + !b\<cdot>p\<cdot>c = \<zero>"
proof
  assume "b\<cdot>p = p\<cdot>c"
  hence "b\<cdot>p\<cdot>!c + !b\<cdot>p\<cdot>c = p\<cdot>c\<cdot>!c + !b\<cdot>b\<cdot>p"
    by (metis skd.mult_assoc)
  also have "... = \<zero>"
    by (metis bt complement_zero ct not_closed skd.add_zerol skd.mult_assoc skd.mult_zerol skd.mult_zeror test_double_compl)
  finally show "b\<cdot>p\<cdot>!c + !b\<cdot>p\<cdot>c = \<zero>" .
next
  assume asm: "b\<cdot>p\<cdot>!c + !b\<cdot>p\<cdot>c = \<zero>"
  have "b\<cdot>p = b\<cdot>p\<cdot>c + b\<cdot>p\<cdot>!c"
    by (metis (lifting) complement_one ct skd.distl skd.mult_oner)
  also have "... = b\<cdot>p\<cdot>c"
    by (metis (lifting) asm skd.add_assoc skd.add_idem skd.add_zeror)
  also have "... = !b\<cdot>p\<cdot>c + b\<cdot>p\<cdot>c"
    by (metis asm calculation complement_zero ct skd.add_zerol skd.mult_assoc skd.mult_zeror)
  also have "... = p\<cdot>c"
    by (metis bt complement_one skd.add_comm skd.distr skd.mult_onel)
  finally show "b\<cdot>p = p\<cdot>c" .
qed

lemma kat2:
  assumes bt: "b \<in> carrier tests" and ct: "c \<in> carrier tests"
  shows "!b\<cdot>p = p\<cdot>!c \<longleftrightarrow> b\<cdot>p\<cdot>!c + !b\<cdot>p\<cdot>c = \<zero>"
proof
  assume asm: "!b\<cdot>p = p\<cdot>!c"
  hence "b\<cdot>p\<cdot>!c + !b\<cdot>p\<cdot>c = b\<cdot>!b\<cdot>p + p\<cdot>!c\<cdot>c"
    by (metis skd.mult_assoc)
  also have "... = \<zero>"
    by (smt asm bt ct kat1 not_closed skd.add_comm skd.mult_assoc test_double_compl)
  finally show "b\<cdot>p\<cdot>!c + !b\<cdot>p\<cdot>c = \<zero>" .
next
  assume asm: "b\<cdot>p\<cdot>!c + !b\<cdot>p\<cdot>c = \<zero>"
  have "!b\<cdot>p = !b\<cdot>p\<cdot>c + !b\<cdot>p\<cdot>!c"
    by (metis (lifting) complement_one ct skd.distl skd.mult_oner)
  also have a: "... = !b\<cdot>p\<cdot>!c"
    by (smt asm skd.add_assoc skd.add_comm skd.add_idem skd.add_zeror)
  also have "... = !b\<cdot>p\<cdot>!c + b\<cdot>p\<cdot>!c"
    by (metis a asm skat_order_def skd.add_comm skd.add_lub skd.add_zerol skd.nat_refl)
  also have "... = p\<cdot>!c"
    by (metis bt complement_one skd.add_comm skd.distr skd.mult_onel)
  finally show "!b\<cdot>p = p\<cdot>!c" .
qed

lemma kat3:
  assumes bt: "b \<in> carrier tests" and ct: "c \<in> carrier tests"
  shows "b\<cdot>p = p\<cdot>c \<longleftrightarrow> !b\<cdot>p = p\<cdot>!c"
  by (simp add: kat2[OF bt ct] kat1[OF bt ct])

locale kat_homomorphism =
  fixes f :: "'a::ranked_alphabet skat_expr \<Rightarrow> 'b::ranked_alphabet skat"
  assumes homo_plus: "f (x :\<oplus>: y) = f x + f y"
  and homo_test_plus: "f (SKBool (P :+: Q)) = f (SKBool P) + f (SKBool Q)"
  and homo_mult: "f (x :\<odot>: y) = f x \<cdot> f y"
  and homo_test_mult: "f (SKBool (P :\<cdot>: Q)) = f (SKBool P) \<cdot> f (SKBool Q)"
  and homo_star: "f (SKStar x) = (f x)\<^sup>\<star>"
  and homo_one: "f SKOne = \<one>"
  and homo_test_one: "f (SKBool BOne) = \<one>"
  and homo_zero: "f SKZero = \<zero>"
  and homo_test_zero: "f (SKBool BZero) = \<zero>"
  and homo_not: "f (SKBool (BNot P)) = !(f (SKBool P))"
  and homo_tests: " f (SKBool P) \<in> carrier tests"

lemma skat_unfold_homo: "kat_homomorphism skat_unfold"
  by (default, simp_all, metis pred_expr_closed pred_expr_unfold)

lemma metatheorem:
  assumes f_homo: "kat_homomorphism f"
  and g_homo: "kat_homomorphism g"
  and atomic: "\<And>a. a \<in> atoms p \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
  shows "f p \<cdot> x = x \<cdot> g p"
  using atomic
proof (induct p)
  fix X s assume "\<And>a. a \<in> atoms (SKLeaf X s) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
  thus "f (SKLeaf X s) \<cdot> x = x \<cdot> g (SKLeaf X s)" by simp
next
  fix p q
  assume "(\<And>a. a \<in> atoms p \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f p \<cdot> x = x \<cdot> g p"
  and "(\<And>a. a \<in> atoms q \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f q \<cdot> x = x \<cdot> g q"
  and "\<And>a. a \<in> atoms (p :\<oplus>: q) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
  thus "f (p :\<oplus>: q) \<cdot> x = x \<cdot> g (p :\<oplus>: q)"
    by (auto simp add: kat_homomorphism.homo_plus f_homo g_homo skd.distl skd.distr)
next
  fix p q
  assume "(\<And>a. a \<in> atoms p \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f p \<cdot> x = x \<cdot> g p"
  and "(\<And>a. a \<in> atoms q \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f q \<cdot> x = x \<cdot> g q"
  and "\<And>a. a \<in> atoms (p :\<odot>: q) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
  thus "f (p :\<odot>: q) \<cdot> x = x \<cdot> g (p :\<odot>: q)"
    by (auto simp add: kat_homomorphism.homo_mult f_homo g_homo, metis skd.mult_assoc)
next
  fix p assume "(\<And>a. a \<in> atoms p \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f p \<cdot> x = x \<cdot> g p"
  and "\<And>a. a \<in> atoms (SKStar p) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
  thus "f (SKStar p) \<cdot> x = x \<cdot> g (SKStar p)"
    by (auto simp add: kat_homomorphism.homo_star f_homo g_homo intro: ska.star_sim[symmetric])
next
  fix P
  assume "\<And>a. a \<in> atoms (SKBool P) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
  thus "f (SKBool P) \<cdot> x = x \<cdot> g (SKBool P)"
  proof (induct P)
    fix l
    assume "\<And>a. a \<in> atoms (SKBool (BLeaf l)) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
    thus "f (SKBool (BLeaf l)) \<cdot> x = x \<cdot> g (SKBool (BLeaf l))" by simp
  next
    fix P Q
    assume "(\<And>a. a \<in> atoms (SKBool P) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f (SKBool P) \<cdot> x = x \<cdot> g (SKBool P)"
    and "(\<And>a. a \<in> atoms (SKBool Q) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f (SKBool Q) \<cdot> x = x \<cdot> g (SKBool Q)"
    and "\<And>a. a \<in> atoms (SKBool (P :+: Q)) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
    moreover hence "\<And>a. a \<in> (atoms (SKBool P) \<union> atoms (SKBool Q)) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a" by auto
    ultimately show "f (SKBool (P :+: Q)) \<cdot> x = x \<cdot> g (SKBool (P :+: Q))"
      by (simp add: f_homo g_homo kat_homomorphism.homo_test_plus skd.distl skd.distr)
  next
    fix P Q
    assume "(\<And>a. a \<in> atoms (SKBool P) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f (SKBool P) \<cdot> x = x \<cdot> g (SKBool P)"
    and "(\<And>a. a \<in> atoms (SKBool Q) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f (SKBool Q) \<cdot> x = x \<cdot> g (SKBool Q)"
    and "\<And>a. a \<in> atoms (SKBool (P :\<cdot>: Q)) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
    moreover hence "\<And>a. a \<in> (atoms (SKBool P) \<union> atoms (SKBool Q)) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a" by auto
    ultimately show "f (SKBool (P :\<cdot>: Q)) \<cdot> x = x \<cdot> g (SKBool (P :\<cdot>: Q))"
      by (simp add: f_homo g_homo kat_homomorphism.homo_test_mult, metis skd.mult_assoc)
  next
    fix P
    assume ind_hyp: "(\<And>a. a \<in> atoms (SKBool P) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a) \<Longrightarrow> f (SKBool P) \<cdot> x = x \<cdot> g (SKBool P)"
    and "\<And>a. a \<in> atoms (SKBool (BNot P)) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
    hence "\<And>a. a \<in> atoms (SKBool P) \<Longrightarrow> f a \<cdot> x = x \<cdot> g a"
      by simp
    from this and ind_hyp have "f (SKBool P) \<cdot> x = x \<cdot> g (SKBool P)"
      by simp
    moreover have "f (SKBool P) \<in> carrier tests" and "g (SKBool P) \<in> carrier tests"
      by (metis f_homo g_homo kat_homomorphism.homo_tests)+
    ultimately show "f (SKBool (BNot P)) \<cdot> x = x \<cdot> g (SKBool (BNot P))"
      by (simp add: f_homo g_homo kat_homomorphism.homo_not kat3[symmetric])
  next
    show "f (SKBool BOne) \<cdot> x = x \<cdot> g (SKBool BOne)"
      by (metis f_homo g_homo kat_homomorphism.homo_test_one skd.mult_onel skd.mult_oner)
  next
    show "f (SKBool BZero) \<cdot> x = x \<cdot> g (SKBool BZero)"
      by (metis f_homo g_homo kat_homomorphism.homo_test_zero skd.mult_zerol skd.mult_zeror)
  qed
next
  show "f SKOne \<cdot> x = x \<cdot> g SKOne"
    by (metis f_homo g_homo kat_homomorphism.homo_one skd.mult_onel skd.mult_oner)
next
  show "f SKZero \<cdot> x = x \<cdot> g SKZero"
    by (metis f_homo g_homo kat_homomorphism.homo_zero skd.mult_zerol skd.mult_zeror)
qed

lemmas skat_comm = metatheorem[OF skat_unfold_homo skat_unfold_homo]

lemma atoms_oneof: "a \<in> atoms p \<Longrightarrow> (\<exists>X s. a = SKLeaf X s) \<or> (\<exists>P. a = SKBool (BLeaf P))"
  by (induct p, auto)

lemma no_touch_comm:
  assumes no_touch: "touches s \<inter> touches t = {}"
  shows "\<lfloor>s\<rfloor> \<cdot> \<lfloor>t\<rfloor> = \<lfloor>t\<rfloor> \<cdot> \<lfloor>s\<rfloor>"
proof (rule skat_comm, rule skat_comm[symmetric])
  fix sa ta assume asm1: "sa \<in> atoms s" and asm2: "ta \<in> atoms t"
  let ?opts = "((\<exists>x s. sa = SKLeaf x s) \<or> (\<exists>P. sa = SKBool (BLeaf P)))
             \<and> ((\<exists>x s. ta = SKLeaf x s) \<or> (\<exists>P. ta = SKBool (BLeaf P)))"

  have "\<lbrakk>touches sa \<inter> touches ta = {}; ?opts\<rbrakk> \<Longrightarrow> \<lfloor>ta\<rfloor> \<cdot> \<lfloor>sa\<rfloor> = \<lfloor>sa\<rfloor> \<cdot> \<lfloor>ta\<rfloor>"
    apply (auto intro: skat_assign_comm skat_pred_comm)
    apply (rule HOL.sym)
    apply (auto intro: skat_pred_comm)
    by (metis skt.test_mult_comm pred_closed)

  moreover have "touches sa \<inter> touches ta = {}"
    by (insert no_touch asm1 asm2 touch_atoms, blast)

  moreover have "?opts"
    by (metis asm1 asm2 atoms_oneof)

  ultimately show "\<lfloor>ta\<rfloor> \<cdot> \<lfloor>sa\<rfloor> = \<lfloor>sa\<rfloor> \<cdot> \<lfloor>ta\<rfloor>" by auto
qed

fun eliminate :: "nat \<Rightarrow> 'a::ranked_alphabet skat_expr => 'a skat_expr" where
  "eliminate x (SKLeaf y s) = (if x = y then SKOne else (SKLeaf y s))"
| "eliminate x (SKBool p) = (SKBool p)"
| "eliminate x (s :\<odot>: t) = eliminate x s :\<odot>: eliminate x t"
| "eliminate x (s :\<oplus>: t) = eliminate x s :\<oplus>: eliminate x t"
| "eliminate x (SKStar s) = SKStar (eliminate x s)"
| "eliminate x SKOne = SKOne"
| "eliminate x SKZero = SKZero"

lemma eliminate_homo: "\<And>X. kat_homomorphism (\<lambda>s. \<lfloor>eliminate X s\<rfloor>)"
  by (default, simp_all, metis pred_expr_closed pred_expr_unfold)

lemma non_output_infinite: "\<not> finite (- output_vars TYPE('a::ranked_alphabet))"
  by (smt finite_compl infinite_UNIV_nat output_finite)

lemma inf_inj_image: "\<lbrakk>inj f; \<not> finite X\<rbrakk> \<Longrightarrow> \<not> finite (f ` X)"
  by (metis (lifting) finite_imageD injD inj_onI)

lemma not_read_elim [intro!]: "x \<notin> reads s \<Longrightarrow> x \<notin> touches (eliminate x s)"
  by (induct s, auto)

lemma eliminate_comm:
  "x \<notin> reads s \<Longrightarrow> \<lfloor>eliminate x s\<rfloor> \<cdot> x := null = x := null \<cdot> \<lfloor>eliminate x s\<rfloor>"
proof -
  assume no_read: "x \<notin> reads s"
  have "\<lfloor>eliminate x s\<rfloor> \<cdot> \<lfloor>SKLeaf x null\<rfloor> = \<lfloor>SKLeaf x null\<rfloor> \<cdot> \<lfloor>eliminate x s\<rfloor>"
    by (rule no_touch_comm, simp, rule not_read_elim, simp add: no_read)
  thus ?thesis
    by simp
qed

lemma eliminate_variables:
  assumes no_reads: "x \<notin> reads p"
  shows "\<lfloor>p\<rfloor> \<cdot> x := null = \<lfloor>eliminate x p\<rfloor> \<cdot> x := null"
proof -
  have "(\<And>a. a \<in> atoms p \<Longrightarrow> \<lfloor>a\<rfloor> \<cdot> x := null = x := null \<cdot> \<lfloor>eliminate x a\<rfloor>)"
  proof -
    fix a assume asm: "a \<in> atoms p"
    hence "(\<exists>x s. a = SKLeaf x s) \<or> (\<exists>P. a = SKBool (BLeaf P))"
      by (metis atoms_oneof)
    moreover from asm have "x \<notin> reads a"
      by (metis disjoint_iff_not_equal no_reads read_atoms set_rev_mp)
    ultimately show "\<lfloor>a\<rfloor> \<cdot> x := null = x := null \<cdot> \<lfloor>eliminate x a\<rfloor>"
      apply auto
      apply (metis skat_null_zero skd.mult_oner)
      apply (metis FV_null empty_iff skat_assign_comm)
      by (metis skat_pred_comm)
  qed
  with metatheorem[OF skat_unfold_homo eliminate_homo[of x] this]
  show ?thesis
    by (metis eliminate_comm no_reads)
qed

fun halt :: "nat list \<Rightarrow> 'a::ranked_alphabet skat" where
  "halt (x#xs) = x := null \<cdot> halt xs"
| "halt [] = \<one>"

lemma halt_snoc: "halt (x#xs) = halt xs \<cdot> x := null"
  apply (induct xs, auto)
  by (metis skd.mult_onel skd.mult_oner, metis (lifting) skat_null_comm skd.mult_assoc)

lemma halt_first: "halt (x#xs) = x := null \<cdot> halt (x#xs)"
  by (metis (lifting) halt.simps(1) skat_null_zero skd.mult_assoc)

lemma halt_append: "halt (xs @ ys) = halt xs \<cdot> halt ys"
  by (induct xs, auto, (metis skd.mult_onel skd.mult_assoc)+)

lemma halt_set: "x \<in> set xs \<Longrightarrow> halt xs = x := null \<cdot> halt xs"
proof -
  assume "x \<in> set xs"
  then obtain ys and zs where xs_split: "xs = ys @ x#zs"
    by (metis (lifting) split_list_first)
  hence "halt xs = halt (ys @ x#zs)"
    by metis
  also have "... = halt ys \<cdot> halt (x#zs)"
    by (metis halt_append)
  also have "... = halt ys \<cdot> x := null \<cdot> halt (x#zs)"
    by (metis halt_first skd.mult_assoc)
  also have "... = x := null \<cdot> halt ys \<cdot> halt (x#zs)"
    by (metis halt.simps(1) halt_snoc)
  also have "... = x := null \<cdot> halt xs"
    by (metis append_Cons halt.simps(1) halt_append xs_split)
  finally show ?thesis .
qed

lemma eliminate_variables_halt:
  assumes x_in_xs: "x \<in> set xs"
  and no_reads: "x \<notin> reads p"
  and non_output: "x \<notin> output_vars TYPE('a::ranked_alphabet) "
  shows "\<lfloor>p\<rfloor> \<cdot> (halt xs :: 'a skat) = \<lfloor>eliminate x p\<rfloor> \<cdot> halt xs"
proof -
  have "\<lfloor>p\<rfloor> \<cdot> halt xs = \<lfloor>p\<rfloor> \<cdot> x := null \<cdot> halt xs"
    by (metis halt_set skd.mult_assoc x_in_xs)
  also have "... = \<lfloor>eliminate x p\<rfloor> \<cdot> x := null \<cdot> halt xs"
    by (metis eliminate_variables no_reads)
  also have "... = \<lfloor>eliminate x p\<rfloor> \<cdot> halt xs"
    by (metis halt_set skd.mult_assoc x_in_xs)
  finally show ?thesis .
qed

lemma skat_comm_pred_con:
  fixes x y :: "'a::ranked_alphabet pred bexpr"
  shows "skat_con (SKBool x :\<odot>: SKBool y) (SKBool y :\<odot>: SKBool x)"
proof -
  have "pred_expr x \<in> carrier tests" and "pred_expr y \<in> carrier tests"
    by (metis pred_expr_closed)+
  hence "pred_expr x \<cdot> pred_expr y = pred_expr y \<cdot> pred_expr x"
    by (metis skt.test_mult_comm)
  thus ?thesis
    by (transfer fixing: x y)
qed

lemma skat_comm_assign_pred_con:
  fixes P :: "'a::ranked_alphabet pred bexpr"
  assumes xP: "x \<notin> reads (SKBool P)"
  shows "skat_con (SKBool P :\<odot>: SKLeaf x s) (SKLeaf x s :\<odot>: SKBool P)"
proof (auto simp add: unfold_transfer[symmetric] pred_expr_unfold, insert xP, induct P)
  fix P :: "'a pred" assume "x \<notin> reads (SKBool (BLeaf P))"
  thus "pred_expr (BLeaf P) \<cdot> x := s = x := s \<cdot> pred_expr (BLeaf P)"
    by (simp add: pred_to_expr[symmetric], metis skat_pred_comm)
next
  fix P1 P2 :: "'a pred bexpr"
  assume ind_hyp1: "x \<notin> reads (SKBool P1) \<Longrightarrow> pred_expr P1 \<cdot> x := s = x := s \<cdot> pred_expr P1"
  and ind_hyp2: "x \<notin> reads (SKBool P2) \<Longrightarrow> pred_expr P2 \<cdot> x := s = x := s \<cdot> pred_expr P2"
  and "x \<notin> reads (SKBool (P1 :+: P2))"
  hence "x \<notin> reads (SKBool P1)" and "x \<notin> reads (SKBool P2)"
    by auto
  thus "pred_expr (P1 :+: P2) \<cdot> x := s = x := s \<cdot> pred_expr (P1 :+: P2)"
    by (smt ind_hyp1 ind_hyp2 pred_expr_unfold skd.distl skd.distr test_unfold.simps(2))
next
  fix P :: "'a pred bexpr"
  assume ind_hyp: "x \<notin> reads (SKBool P) \<Longrightarrow> pred_expr P \<cdot> x := s = x := s \<cdot> pred_expr P"
  and "x \<notin> reads (SKBool (BNot P))"
  hence "x \<notin> reads (SKBool P)"
    by auto
  from ind_hyp[OF this] show "pred_expr (BNot P) \<cdot> x := s = x := s \<cdot> pred_expr (BNot P)"
    apply (simp add: pred_expr_unfold[symmetric])
    apply (subst kat3[symmetric])
    apply (metis pred_expr_closed pred_expr_unfold)
    by auto
next
  fix P1 P2 :: "'a pred bexpr"
  assume ind_hyp1: "x \<notin> reads (SKBool P1) \<Longrightarrow> pred_expr P1 \<cdot> x := s = x := s \<cdot> pred_expr P1"
  and ind_hyp2: "x \<notin> reads (SKBool P2) \<Longrightarrow> pred_expr P2 \<cdot> x := s = x := s \<cdot> pred_expr P2"
  and "x \<notin> reads (SKBool (P1 :\<cdot>: P2))"
  hence "x \<notin> reads (SKBool P1)" and "x \<notin> reads (SKBool P2)"
    by auto
  thus "pred_expr (P1 :\<cdot>: P2) \<cdot> x := s = x := s \<cdot> pred_expr (P1 :\<cdot>: P2)"
    by (smt ind_hyp1 ind_hyp2 pred_expr_unfold skd.mult_assoc test_unfold.simps(3))
next
  show "pred_expr bexpr.BOne \<cdot> x := s = x := s \<cdot> pred_expr bexpr.BOne"
    by (metis pred_expr_unfold skd.mult_onel skd.mult_oner test_unfold.simps(5))
next
  show "pred_expr bexpr.BZero \<cdot> x := s = x := s \<cdot> pred_expr bexpr.BZero"
    by (metis pred_expr_unfold skd.mult_zerol skd.mult_zeror test_unfold.simps(6))
qed

lemma skat_comm_assign_con:
  "\<lbrakk>x \<noteq> y; x \<notin> FV t; y \<notin> FV s\<rbrakk> \<Longrightarrow> skat_con (SKLeaf x s :\<odot>: SKLeaf y t) (SKLeaf y t :\<odot>: SKLeaf x s)"
  by (auto simp add: unfold_transfer[symmetric] intro: skat_assign_comm)

lemma skat_comm_no_touch_con:
  "touches t \<inter> touches s = {} \<Longrightarrow> skat_con (s :\<odot>: t) (t :\<odot>: s)"
  by (auto simp add: unfold_transfer[symmetric] intro: no_touch_comm)

lemma skat_comm_con:
  assumes atoms_comm: "\<And>xa ya. \<lbrakk>xa \<in> atoms x; ya \<in> atoms y\<rbrakk> \<Longrightarrow> skat_con (xa :\<odot>: ya) (ya :\<odot>: xa)"
  shows "skat_con (x :\<odot>: y) (y :\<odot>: x)"
  apply (simp add: unfold_transfer[symmetric])
  apply (rule skat_comm)
  apply (rule HOL.sym)
  apply (rule skat_comm)
  apply (rule HOL.sym)
  by (auto simp only: skat_unfold.simps[symmetric] unfold_transfer intro: atoms_comm)

lemma skat_fold_tac_simp:
  "skat_unfold (SKBool (p :\<cdot>: q)) = skat_unfold (SKBool p :\<odot>: SKBool q)"
  by simp

lemma eliminate_variables_con:
  assumes x_in_xs: "x \<in> set xs" and nr: "x \<notin> reads (s::'a skat_expr)" and xo: "x \<notin> output_vars TYPE('a::ranked_alphabet)"
  shows "\<lfloor>s\<rfloor> \<cdot> halt xs = \<lfloor>eliminate x s\<rfloor> \<cdot> halt xs"
  by (metis eliminate_variables_halt nr x_in_xs xo)

ML {*

fun nat_cterm 0 = @{cterm "0::nat"}
  | nat_cterm n = Thm.apply @{cterm Suc} (nat_cterm (n - 1))

structure SkatSimpRules = Named_Thms
  (val name = @{binding "skat_simp"}
   val description = "SKAT simplification rules")

fun skat_fold_tac ctxt n =
  REPEAT (EqSubst.eqsubst_tac ctxt [0] @{thms test_unfold.simps[symmetric]} n)
  THEN REPEAT (EqSubst.eqsubst_tac ctxt [0] @{thms skat_unfold.simps[symmetric]} n)

fun skat_apply_fold_tac ctrm =
  Subgoal.FOCUS (fn {context, ...} =>
    rtac @{thm HOL.trans} 1
    THEN rtac (Drule.instantiate' [SOME (ctyp_of_term ctrm)] [SOME ctrm] @{thm arg_cong}) 1
    THEN simp_tac (Simplifier.context context empty_ss addsimps SkatSimpRules.get context) 1
    THEN skat_fold_tac context 1
    THEN simp_tac HOL_basic_ss 1)

(* The Transfer package doesn't export this, so we copy it over here *)
fun gen_frees_tac keepers ctxt = SUBGOAL (fn (t, i) =>
  let
    val vs = rev (Term.add_frees t [])
    val vs' = filter_out (member (op =) keepers) vs
  in
    Induct.arbitrary_tac ctxt 0 vs' i
  end)

fun skat_transfer_tac ctxt n =
  let
    fun transfer1 ctxt n =
      skat_fold_tac ctxt n
      THEN CHANGED (simp_tac (HOL_basic_ss addsimps @{thms skat_fold_tac_simp unfold_transfer}) n)
    fun transfer2 ctxt =
      gen_frees_tac [] ctxt THEN' Transfer.transfer_tac true ctxt
  in
    simp_tac (HOL_basic_ss addsimps SkatSimpRules.get ctxt) n
    THEN (transfer1 ctxt n ORELSE transfer2 ctxt n)
  end

fun comm_rules_tac n =
  rtac @{thm skat_comm_pred_con} n
  ORELSE rtac @{thm skat_comm_assign_pred_con} n
  ORELSE rtac @{thm skat_comm_assign_pred_con[symmetric]} n
  ORELSE rtac @{thm skat_comm_assign_con} n
  ORELSE rtac @{thm skat_comm_no_touch_con} n

fun skat_comm_tac solver = Subgoal.FOCUS_PARAMS (fn {context, ...} =>
  DETERM (skat_transfer_tac context 1
    THEN rtac @{thm skat_comm_con} 1
    THEN full_simp_tac (HOL_basic_ss addsimps @{thms atoms.simps}) 1
    THEN safe_tac context
    THEN ALLGOALS (asm_full_simp_tac (HOL_basic_ss addsimps @{thms triv_forall_equality}))
    THEN ALLGOALS (comm_rules_tac))
  THEN ALLGOALS (solver context))

fun all_tac_solver _ _ = all_tac

fun simp_solver ctxt n = REPEAT (CHANGED
  (asm_full_simp_tac (simpset_of ctxt) n ))

fun eliminate_variable_tac v = Subgoal.FOCUS (fn {context, ...} =>
  asm_full_simp_tac (HOL_basic_ss addsimps SkatSimpRules.get context) 1
  THEN skat_fold_tac context 1
  THEN DETERM (EqSubst.eqsubst_tac context [0] [Drule.instantiate' [] [SOME (nat_cterm v)] @{thm eliminate_variables_con}] 1)
  THEN asm_full_simp_tac (simpset_of context) 1
  THEN asm_full_simp_tac (simpset_of context) 1
  THEN TRY (simp_tac (simpset_of context) 1)
  THEN asm_full_simp_tac (simpset_of context addsimps AlphabetRules.get context) 1
  THEN asm_full_simp_tac (simpset_of context addsimps @{thms skd.mult_oner skd.mult_onel}) 1)

*}

setup {* SkatSimpRules.setup *}

method_setup skat_fold = {*
Scan.succeed (fn ctxt => SIMPLE_METHOD (CHANGED (skat_fold_tac ctxt 1)))
*}

method_setup skat_comm' = {*
Scan.succeed (fn ctxt => SIMPLE_METHOD' (skat_comm_tac all_tac_solver ctxt))
*}

method_setup skat_comm = {*
Scan.succeed (fn ctxt => SIMPLE_METHOD' (skat_comm_tac simp_solver ctxt))
*}

method_setup skat_simp = {*
Scan.succeed (fn ctxt =>
  asm_full_simp_tac (simpset_of ctxt addsimps SkatSimpRules.get ctxt) 1
  |> SIMPLE_METHOD)
*}

method_setup skat_reduce = {*
Scan.succeed (fn ctxt =>
  simp_tac (HOL_basic_ss addsimps SkatSimpRules.get ctxt) 1
  |> SIMPLE_METHOD)
*}

method_setup eliminate_variable = {*
Scan.lift Parse.nat >>
  (fn v => fn ctxt => SIMPLE_METHOD (eliminate_variable_tac v ctxt 1))
*}

definition while :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat" ("WHILE _ DO _ WEND" [64,64] 63) where
  "WHILE b DO p WEND = (b\<cdot>p)\<^sup>\<star>\<cdot>!b"

definition if_then_else :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat"
  ("IF _ THEN _ ELSE _ ENDIF" [64,64,64] 63) where
  "IF b THEN p ELSE q ENDIF \<equiv> b\<cdot>p + (!b)\<cdot>q"

notation
  SKAT.skat_mult (infixl ";" 64)

definition biconditional ::
  "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat" (infixl "iff" 65)
where
  "x iff y = !x\<cdot>!y + x\<cdot>y"

declare biconditional_def [skat_simp]

lemma bicon_conj1: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> (x iff y)\<cdot>y = x\<cdot>y"
  apply (simp add: biconditional_def skd.distr[simplified])
  by (smt complement_zero de_morgan1 not_closed skd.add_comm skd.add_idem skd.add_zeror skd.mult_assoc test_double_compl)

lemma bicon_conj2: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> y\<cdot>(x iff y) = x\<cdot>y"
  by (smt biconditional_def complement_zero de_morgan1 de_morgan2 not_closed skd.add_zerol skd.distl skd.mult_assoc skt.test_meet_idem skt.test_mult_comm)

lemma bicon_zero: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> (x iff y)\<cdot>(!x\<cdot>y) = \<zero>"
  by (smt bicon_conj1 complement_zero not_closed skd.mult_assoc skd.mult_zeror skt.test_mult_comm)

lemma bicon_comm: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> x iff y = y iff x"
  by (metis (lifting) biconditional_def not_closed skt.test_mult_comm)

lemma bicon_refl: "x \<in> carrier tests \<Longrightarrow> \<one> = x iff x"
  by (simp add: biconditional_def) (metis complement_one not_closed skd.add_comm skt.test_meet_idem)

lemma bicon_not: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> x iff y = !x iff !y"
  by (metis (lifting) biconditional_def skd.add_comm test_double_compl)

lemma skat_not_assign: "!(pred (\<phi>[x|t])); x := t = x := t; !(pred \<phi>)"
  by (simp add: pred_to_expr, transfer, metis (no_types) assign4 bexpr_map.simps(1) bexpr_map.simps(3))

lemma skat_iff_assign: "pred (\<phi>[x|t]) iff pred (\<psi>[x|t]); x := t = x := t; pred \<phi> iff pred \<psi>"
  by (simp add: biconditional_def skd.distl skd.distr) (metis (no_types) skat_assign4 skat_not_assign skd.mult_assoc)

lemma skat_iff_assign_var:
  "\<lbrakk>\<phi>' = \<phi>[x|t]; \<psi>' = \<psi>[x|t]\<rbrakk> \<Longrightarrow> pred \<phi>' iff pred \<psi>'; x := t = x := t; pred \<phi> iff pred \<psi>"
  by (metis skat_iff_assign)

lemma skat_iff_left_assign_var:
  "\<lbrakk>\<phi>' = \<phi>[x|t]; \<psi> = \<psi>[x|t]\<rbrakk> \<Longrightarrow> pred \<phi>' iff pred \<psi>; x := t = x := t; pred \<phi> iff pred \<psi>"
  by (subst skat_iff_assign_var, auto)

lemma eq_pred:
  assumes x_FV: "x \<notin> FV s" and x_not_y: "x \<noteq> y"
  shows "x := s ; y := s = x := s ; y := s ; (pred (Pred p [Var x]) iff pred (Pred p [Var y]))"
proof -
  have "x := s; y := s = pred (Pred p [s]) iff pred (Pred p [s]); x := s; y := s"
    by (subst bicon_refl[symmetric]) (auto simp add: pred_closed skd.mult_onel)
  also have "... = x := s; pred (Pred p [s]) iff pred (Pred p [Var x]); y := s"
    by (subst skat_iff_assign_var, auto, metis assms no_FV)
  also have "... = x := s; y := s; pred (Pred p [Var y]) iff pred (Pred p [Var x])"
    apply (simp add: skd.mult_assoc)
    apply (rule arg_cong) back
    apply (subst skat_iff_left_assign_var[of "Pred p [s]" _ _ "Pred p [Var y]"])
    apply simp
    apply simp
    apply (metis x_not_y)
    by auto
  also have "... = x := s; y := s; pred (Pred p [Var x]) iff pred (Pred p [Var y])"
    by (subst bicon_comm) (auto simp add: pred_closed)
  finally show ?thesis .
qed

end
