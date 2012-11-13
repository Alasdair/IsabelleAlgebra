theory Ranked_Alphabet
  imports KAT Boolean_Algebra_Extras
begin

(* +------------------------------------------------------------------------+ *)
subsection {* Ranked Alphabets *}
(* +------------------------------------------------------------------------+ *)

class ranked_alphabet =
  fixes arity :: "'a \<Rightarrow> nat"
  and funs :: "'a set"
  and rels :: "'a set"
  and NULL :: 'a
  and output_vars :: "'a itself \<Rightarrow> nat set"
  assumes symbols_finite: "finite UNIV"
  and funs_rels_disjoint: "funs \<inter> rels = {}"
  and funs_rels_union: "funs \<union> rels = UNIV"
  and funs_exist: "funs \<noteq> {}"
  and rels_exist: "rels \<noteq> {}"
  and NULL_fun: "NULL \<in> funs"
  and NULL_arity: "arity NULL = 0"

text {* A ranked alphabet consists of a set of disjoint function and
relation symbols. Each symbol in the alphabet has an associated
arity. The set @{const funs} contains all the function symbols, while
@{const rels} contains all the relation symbols. The @{const arity}
function returns the arity of a symbol.

Ranked alphabets are formalised as a typeclass, so a concrete alphabet
is simply a type which supports the above functions and the typeclass
laws. This avoids having to parameterise defintions with alphabets,
which allows things to stay at the type level. *}

(* +------------------------------------------------------------------------+ *)
subsection {* Terms *}
(* +------------------------------------------------------------------------+ *)

datatype 'a trm = App 'a "'a trm list" | Var nat

fun trm_vars :: "'a trm \<Rightarrow> nat set" where
  "trm_vars (App f xs) = \<Union> (set (map trm_vars xs))"
| "trm_vars (Var v) = {v}"

fun trm_subst :: "nat set \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" where
  "trm_subst v s (Var v') = (if v' \<in> v then s else Var v')"
| "trm_subst v s (App f xs) = App f (map (trm_subst v s) xs)"

inductive_set trms :: "'a::ranked_alphabet trm set" where
  var: "Var n \<in> trms"
| func: "\<lbrakk>f \<in> funs; arity f = n; xs \<in> lists trms; length xs = n\<rbrakk> \<Longrightarrow> App f xs \<in> trms"

lemma trm_subterms: "App f xs \<in> trms \<Longrightarrow> xs \<in> lists trms"
  by (metis trm.simps(1) trm.simps(4) trms.simps)

lemma trm_subterms_var: "App f xs \<in> trms \<Longrightarrow> set xs \<subseteq> trms"
  by (metis in_lists_conv_set subset_code(1) trm_subterms)

lemma map_in_lists: "map f xs \<in> lists X \<longleftrightarrow> f ` set xs \<subseteq> X"
  by (metis in_lists_conv_set in_mono set_map subsetI)

lemma trm_subst_wf: "\<lbrakk>s \<in> trms; x \<in> trms\<rbrakk> \<Longrightarrow> trm_subst v s x \<in> trms"
proof (rule trms.induct[of x "\<lambda>x. trm_subst v s x \<in> trms"], safe)
  fix n assume "s \<in> trms" and "x \<in> trms" thus "trm_subst v s (Var n) \<in> trms"
    by (metis trm_subst.simps(1) trms.var)
next
  fix f :: "'a::ranked_alphabet" and xs :: "'a trm list"
  assume s_trm: "s \<in> trms" and x_trm: "x \<in> trms" and f_fun: "f \<in> funs"
  and xs_len: "length xs = arity f"
  and ind_hyp: "\<forall>x\<in>set xs. x \<in> trms \<inter> {x. trm_subst v s x \<in> trms}"
  show "trm_subst v s (App f xs) \<in> trms"
  proof (simp, rule trms.func[of _ "length xs"])
    show "f \<in> funs" using f_fun .
    show "arity f = length xs" by (simp add: xs_len)
    show "map (trm_subst v s) xs \<in> lists trms"
      by (simp add: map_in_lists image_def, auto, metis Int_Collect ind_hyp)
    show "length (map (trm_subst v s) xs) = length xs"
      by (metis length_map)
  qed
qed

lemma trms_const: "\<lbrakk>f \<in> funs; arity f = 0\<rbrakk> \<Longrightarrow> App f [] \<in> trms"
  by (rule trms.func, simp_all add: lists_def)

(* +------------------------------------------------------------------------+ *)
subsection {* n-tuples *}
(* +------------------------------------------------------------------------+ *)

text {* Given a set, generate all posible $n$-tuples of a specific
length. Here we represent an $n$-tuple as a list. *}

fun ntuples :: "'a set \<Rightarrow> nat \<Rightarrow> ('a list) set" ("_\<^bsup>_\<^esup>") where
  "X\<^bsup>0\<^esup> = {[]}"
| "X\<^bsup>Suc n\<^esup> = {x. \<exists>y\<in>X. \<exists>ys\<in>X\<^bsup>n\<^esup>. x = y#ys}"

lemma ntuples1: "set xs \<subseteq> X \<longleftrightarrow> xs \<in> X\<^bsup>length xs\<^esup>" by (induct xs, simp_all)

lemma ntuples2: "\<lbrakk>set xs \<subseteq> X; length xs = n\<rbrakk> \<Longrightarrow> xs \<in> X\<^bsup>n\<^esup>" by (metis ntuples1)

lemma ntuples3: "xs \<in> X\<^bsup>length xs\<^esup> \<Longrightarrow> set xs \<subseteq> X"
  by (induct xs, simp_all)

lemma ntuples4: "xs \<in> X\<^bsup>n\<^esup> \<Longrightarrow> length xs = n"
  apply (induct X n arbitrary: xs rule: ntuples.induct)
  by (simp_all, metis Suc_length_conv)

lemma ntuples5 [iff]: "xs \<in> X\<^bsup>n\<^esup> \<longleftrightarrow> (set xs \<subseteq> X \<and> length xs = n)"
  by (metis ntuples1 ntuples4)

lemma ntuples6: "(x \<in> X \<and> xs \<in> X\<^bsup>n\<^esup>) \<longleftrightarrow> x#xs \<in> X\<^bsup>Suc n\<^esup>" by simp

lemma ntuples7: "n \<noteq> 0 \<longleftrightarrow> [] \<notin> X\<^bsup>n\<^esup>"
  by (induct n, simp_all)

lemma ntuples_set: "X\<^bsup>n\<^esup> = {xs. set xs \<subseteq> X \<and> length xs = n}" by auto

type_synonym 'a relation = "('a list) set"

(* +------------------------------------------------------------------------+ *)
subsection {* Interpretation and term evaluation *}
(* +------------------------------------------------------------------------+ *)

record ('a, 'b) interp = "'b partial_object" +
  mf :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b"
  mr :: "'a \<Rightarrow> 'b relation"

locale valid_interp =
  fixes D :: "('a::ranked_alphabet, 'b) interp"
  assumes fun_meaning: "f \<in> funs \<Longrightarrow> mf D f : (carrier D)\<^bsup>arity f\<^esup> \<rightarrow> carrier D"
  and rel_meaning: "P \<in> rels \<Longrightarrow> mr D P \<subseteq> (carrier D)\<^bsup>arity P\<^esup>"

type_synonym 'a mem = "nat \<Rightarrow> 'a"

fun eval_trm :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'a trm \<Rightarrow> 'b" where
  "eval_trm D mem (Var n) = mem n"
| "eval_trm D mem (App f xs) = mf D f (map (eval_trm D mem) xs)"

lemma eval_trm_closed:
  assumes valid_ip: "valid_interp D"
  and valid_mem: "\<forall>n. mem n \<in> carrier D"
  and trms: "x \<in> trms" shows "eval_trm D mem x \<in> carrier D"
  using trms
proof (induct x)
  fix n
  show "eval_trm D mem (Var n) \<in> carrier D"
    by (simp add: eval_trm.simps, metis valid_mem)
next
  fix f :: "'b::ranked_alphabet" and n xs
  assume f_funs: "f \<in> funs" and f_arity: "arity f = n"
  and xs_eval: "xs \<in> lists (trms \<inter> {x. eval_trm D mem x \<in> carrier D})"
  and xs_len: "length xs = n"

  have "xs \<in> lists {x. eval_trm D mem x \<in> carrier D}"
    by (metis (lifting) xs_eval IntD2 lists_Int_eq)
  hence "set xs \<subseteq> {x. eval_trm D mem x \<in> carrier D}"
    by (metis lists_eq_set mem_Collect_eq)

  hence "map (eval_trm D mem) xs \<in> carrier D\<^bsup>length xs\<^esup>"
    by (induct xs, simp_all add: map_def)

  hence "mf D f (map (eval_trm D mem) xs) \<in> carrier D"
    apply (rule typed_application)
    apply (simp add: xs_len f_arity[symmetric])
    by (rule valid_interp.fun_meaning[OF valid_ip f_funs])

  thus "eval_trm D mem (App f xs) \<in> carrier D"
    by (simp add: eval_trm.simps(1))
qed

typedef (open) 'a wf_trm = "trms::'a::ranked_alphabet trm set"
  by (rule_tac x = "Var 0" in exI, rule trms.var)

definition var :: "nat \<Rightarrow> 'a::ranked_alphabet wf_trm" where
  "var i \<equiv> Abs_wf_trm (Var i)"

lemma Rep_var [simp]: "Rep_wf_trm (var n) = Var n"
  by (metis Abs_wf_trm_inverse trms.var var_def)

lemma Abs_var [simp]: "Abs_wf_trm (Var n) = var n"
  by (metis var_def)

definition null :: "'a::ranked_alphabet wf_trm" where
  "null \<equiv> Abs_wf_trm (App NULL [])"

definition wf_trm_vars :: "'a::ranked_alphabet wf_trm \<Rightarrow> nat set" where
  "wf_trm_vars x = trm_vars (Rep_wf_trm x)"

definition eval_wf_trm :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'a wf_trm \<Rightarrow> 'b" where
  "eval_wf_trm D mem x \<equiv> eval_trm D mem (Rep_wf_trm x)"

lemma eval_wf_trm_closed:
  assumes valid_ip: "valid_interp D"
  and valid_mem: "\<forall>n. mem n \<in> carrier D"
  shows "eval_wf_trm D mem x \<in> carrier D"
  by (metis Rep_wf_trm eval_trm_closed eval_wf_trm_def valid_ip valid_mem)

definition wf_trm_subst :: "nat set \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a wf_trm \<Rightarrow> 'a wf_trm" where
  "wf_trm_subst v s x \<equiv> Abs_wf_trm (trm_subst v (Rep_wf_trm s) (Rep_wf_trm x))"

abbreviation wf_trm_subst_notation :: "'a::ranked_alphabet wf_trm \<Rightarrow> nat set \<Rightarrow> 'a wf_trm \<Rightarrow> 'a wf_trm"
  ("_[_|_]" [100,100,100] 101) where
  "s[x|t] \<equiv> wf_trm_subst x t s"

(* +------------------------------------------------------------------------+ *)
subsection {* Predicates *}
(* +------------------------------------------------------------------------+ *)

datatype 'a pred = Pred 'a "'a wf_trm list"

inductive_set preds :: "'a::ranked_alphabet pred set" where
  "\<lbrakk>P \<in> rels; arity P = length xs\<rbrakk> \<Longrightarrow> Pred P xs \<in> preds"

primrec eval_pred :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "eval_pred D mem (Pred P xs) \<longleftrightarrow> map (eval_wf_trm D mem) xs \<in> mr D P"

primrec pred_subst :: "nat set \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a pred \<Rightarrow> 'a pred" where
  "pred_subst v s (Pred P xs) = Pred P (map (wf_trm_subst v s) xs)"

typedef (open) 'a wf_pred = "preds::'a::ranked_alphabet pred set"
  by (metis Ex_list_of_length equals0I preds.intros rels_exist)

definition eval_wf_pred :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a wf_pred \<Rightarrow> bool" where
  "eval_wf_pred D mem P \<equiv> eval_pred D mem (Rep_wf_pred P)"

definition
  wf_pred_subst :: "nat set \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a wf_pred \<Rightarrow> 'a wf_pred"
  where
  "wf_pred_subst v s \<equiv> Abs_wf_pred \<circ> pred_subst v s \<circ> Rep_wf_pred"

abbreviation
  wf_pred_subst_notation :: "'a::ranked_alphabet wf_pred \<Rightarrow> nat set \<Rightarrow> 'a wf_trm \<Rightarrow> 'a wf_pred"
  ("_[_|_]" [100,100,100] 101) where
  "s[x|t] \<equiv> wf_pred_subst x t s"

(* Simple while programs *)

datatype 'a prog = If "'a wf_pred" "'a prog" "'a prog"
                 | While "'a wf_pred" "'a prog"
                 | Seq "'a prog list"
                 | Assign nat "'a wf_trm"

fun eval_prog :: "nat \<Rightarrow> ('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a prog \<Rightarrow> 'b mem option" where
  "eval_prog 0 _ _ _ = None"
| "eval_prog (Suc n) D mem (If P x y) =
     (if eval_wf_pred D mem P
     then eval_prog n D mem x
     else eval_prog n D mem y)"
| "eval_prog (Suc n) D mem (While P x) =
     (if eval_wf_pred D mem P
     then case eval_prog n D mem x of
       Some mem' \<Rightarrow> eval_prog n D mem' (While P x)
     | None \<Rightarrow> None
     else Some mem)"
| "eval_prog (Suc n) D mem (Seq (x#xs)) =
     (case eval_prog n D mem x of
       Some mem' \<Rightarrow> eval_prog n D mem (Seq xs)
     | None \<Rightarrow> None)"
| "eval_prog (Suc n) D mem (Seq []) = Some mem"
| "eval_prog (Suc n) D mem (Assign m x) =
     (Some (\<lambda>v. if v = m then eval_wf_trm D mem x else mem v))"

definition terminates :: "'a::ranked_alphabet prog \<Rightarrow> bool" where
  "terminates prgm \<equiv> \<exists>steps. \<forall>D mem. valid_interp D \<longrightarrow> eval_prog steps D mem prgm \<noteq> None"

definition tprogs :: "'a::ranked_alphabet prog set" where
  "tprogs \<equiv> {prgm. terminates TYPE('b) prgm}"

(* +------------------------------------------------------------------------+ *)
subsection {* Schematic Kleene Algebra Expressions *}
(* +------------------------------------------------------------------------+ *)

datatype 'a skat_expr = SKLeaf "nat set" "'a wf_trm"
                      | SKPlus "'a skat_expr" "'a skat_expr" (infixl ":\<oplus>:" 70)
                      | SKMult "'a skat_expr" "'a skat_expr" (infixl ":\<odot>:" 80)
                      | SKStar "'a skat_expr"
                      | SKBool "'a wf_pred bexpr"
                      | SKOne
                      | SKZero

(* Free variables *)

fun FV' :: "'a trm \<Rightarrow> nat set" where
  "FV' (Var v) = {v}"
| "FV' (App f xs) = foldr op \<union> (map FV' xs) {}"

definition FV :: "'a::ranked_alphabet wf_trm \<Rightarrow> nat set" where
  "FV \<equiv> FV' \<circ> Rep_wf_trm"

lemma app_FV': "v \<inter> FV' (App f xs) = {} \<Longrightarrow> \<forall>x\<in>set xs. v \<inter> FV' x = {}"
  by (erule contrapos_pp, simp, induct xs, auto)

lemma no_FV' [simp]: "v \<inter> FV' s = {} \<Longrightarrow> trm_subst v t s = s"
proof (induct s)
  fix f xs
  assume asm: "\<forall>x\<in>set xs. v \<inter> FV' x = {} \<longrightarrow> trm_subst v t x = x"
    and "v \<inter> FV' (App f xs) = {}"
  hence "\<forall>x\<in>set xs. v \<inter> FV' x = {}"
    by (metis app_FV')
  thus "trm_subst v t (App f xs) = App f xs"
    by (metis (lifting) asm map_idI trm_subst.simps(2))
next
  fix v' assume "v \<inter> FV' (Var v') = {}"
  thus "trm_subst v t (Var v') = Var v'" by simp
next
  show "\<forall>x\<in>set []. v \<inter> FV' x = {} \<longrightarrow> trm_subst v t x = x" by simp
next
  fix x xs
  assume "v \<inter> FV' x = {} \<Longrightarrow> trm_subst v t x = x"
    and "\<forall>y\<in>set xs. v \<inter> FV' y = {} \<longrightarrow> trm_subst v t y = y"
  thus "\<forall>y\<in>set (x # xs). v \<inter> FV' y = {} \<longrightarrow> trm_subst v t y = y"
    by auto
qed

lemma no_FV [simp]: "v \<inter> FV s = {} \<Longrightarrow> s[v|t] = s"
  by (induct s, metis FV_def Rep_wf_trm_inverse no_FV' o_apply wf_trm_subst_def)

primrec pred_vars :: "'a::ranked_alphabet pred \<Rightarrow> nat set" where
  "pred_vars (Pred P xs) = \<Union> (set (map FV xs))"

definition wf_pred_vars :: "'a::ranked_alphabet wf_pred \<Rightarrow> nat set" where
  "wf_pred_vars P = pred_vars (Rep_wf_pred P)"

primrec touches :: "'a::ranked_alphabet skat_expr \<Rightarrow> nat set" where
  "touches (SKLeaf X s) = X \<union> FV s"
| "touches (SKPlus x y) = touches x \<union> touches y"
| "touches (SKMult x y) = touches x \<union> touches y"
| "touches (SKStar x) = touches x"
| "touches (SKBool p) = \<Union> (wf_pred_vars ` bexpr_leaves p)"
| "touches SKOne = {}"
| "touches SKZero = {}"

primrec modifies :: "'a::ranked_alphabet skat_expr \<Rightarrow> nat set" where
  "modifies (SKLeaf X s) = X"
| "modifies (SKPlus x y) = modifies x \<union> modifies y"
| "modifies (SKMult x y) = modifies x \<union> modifies y"
| "modifies (SKStar x) = modifies x"
| "modifies (SKBool p) = {}"
| "modifies SKOne = {}"
| "modifies SKZero = {}"

lemma modify_subset_touch: "modifies x \<subseteq> touches x"
  by (induct x, auto)

fun SKNot :: "'a skat_expr \<Rightarrow> 'a skat_expr" where
  "SKNot (SKBool x) = (SKBool (BNot x))"
| "SKNot x = undefined"

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
| test_plus: "skat_con (SKBool (BMult x y)) (SKMult (SKBool x) (SKBool y))"
| test_mult: "skat_con (SKBool (BPlus x y)) (SKPlus (SKBool x) (SKBool y))"

| assign1: "y \<inter> FV s = {} \<Longrightarrow> skat_con (SKLeaf x s :\<odot>: SKLeaf y t) (SKLeaf y (t[x|s]) :\<odot>: SKLeaf x s)"
| assign2: "x \<inter> FV s = {} \<Longrightarrow> skat_con (SKLeaf x s :\<odot>: SKLeaf y t) (SKLeaf x s :\<odot>: SKLeaf y (t[x|s]))"
| assign3: "skat_con (SKLeaf x s :\<odot>: SKLeaf x t) (SKLeaf x (t[x|s]))"
| assign4: "skat_con (SKBool (bexpr_map (wf_pred_subst x t) \<phi>) :\<odot>: SKLeaf x t) (SKLeaf x t :\<odot>: SKBool \<phi>)"
| assign5: "X \<inter> FV s = {} \<Longrightarrow> skat_con (SKLeaf (X \<union> Y) s) (SKLeaf X s :\<odot>: SKLeaf Y s)"
| assign6: "skat_con SKOne (SKLeaf {} s)"

lemma skat_con_eq: "x = y \<Longrightarrow> skat_con x y" by (simp add: skat_con.refl)

quotient_type 'a skat = "'a::ranked_alphabet skat_expr" / skat_con
proof (auto simp add: equivp_def)
  fix x y assume "skat_con x y"
  thus "skat_con x = skat_con y"
    apply (subgoal_tac "\<forall>z. skat_con x z = skat_con y z")
    apply auto
    by (metis skat_con.sym skat_con.trans)+
qed

lift_definition skat_set_assign :: "nat set \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a skat" (infix "::=" 100) is SKLeaf
  by (rule skat_con.refl)

definition skat_assign :: "nat \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a skat" (infix ":=" 100) where
  "x := s \<equiv> {x} ::= s"

definition halt :: "'a::ranked_alphabet skat" where
  "halt = (- output_vars TYPE('a)) ::= null"

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

lift_definition test :: "'a::ranked_alphabet wf_pred bterm \<Rightarrow> 'a skat" is SKBool
  by (rule skat_con.test_ba, assumption)

lift_definition pred_expr :: "'a::ranked_alphabet wf_pred bexpr \<Rightarrow> 'a skat" is SKBool
  by (metis skat_con.refl)

lift_definition skat_not :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat" ("!") is SKNot
  by (smt equivp_def equivp_symp fun_relE mult_compat one skat_con.mult_oner skat_con.mult_zerol skat_con.mult_zeror skat_con.refl skat_con.sym skat_con.trans skat_equivp test_ba test_one test_plus test_zero)

lift_definition pred :: "'a::ranked_alphabet wf_pred \<Rightarrow> 'a skat" is "SKBool \<circ> BLeaf" by auto

lemma skat_set_assign1: "Y \<inter> FV s = {} \<Longrightarrow> (X ::= s \<cdot> Y ::= t) = (Y ::= t[X|s] \<cdot> X ::= s)"
  by (transfer, rule assign1, assumption)

lemma skat_set_assign1_var: "\<lbrakk>u = t[X|s]; Y \<inter> FV s = {}\<rbrakk> \<Longrightarrow> (X ::= s \<cdot> Y ::= t) = (Y ::= u \<cdot> X ::= s)"
  by (erule ssubst, rule skat_set_assign1, assumption)

lemma skat_assign1: "y \<notin> FV s \<Longrightarrow> (x := s \<cdot> y := t) = (y := t[{x}|s] \<cdot> x := s)"
  by (simp add: skat_assign_def, rule skat_set_assign1, blast)

lemma skat_set_assign2: "X \<inter> FV s = {} \<Longrightarrow> (X ::= s \<cdot> Y ::= t) = (X ::= s \<cdot> Y ::= t[X|s])"
  by (transfer, rule assign2, assumption)

lemma skat_assign2: "x \<notin> FV s \<Longrightarrow> (x := s \<cdot> y := t) = (x := s \<cdot> y := t[{x}|s])"
  by (simp add: skat_assign_def, rule skat_set_assign2, blast)

lemma skat_set_assign3: "(X ::= s \<cdot> X ::= t) = (X ::= t[X|s])"
  by (transfer, rule assign3)

lemma skat_assign3: "(x := s \<cdot> x := t) = (x := t[{x}|s])"
  by (simp add: skat_assign_def, rule skat_set_assign3)

lemma pred_to_expr: "pred \<phi> = pred_expr (BLeaf \<phi>)"
  by (simp add: pred_def pred_expr_def)

lemma skat_set_assign4_expr: "(pred_expr (bexpr_map (\<lambda>\<psi>. \<psi>[X|t]) \<phi>) \<cdot> X ::= t) = (X ::= t \<cdot> pred_expr \<phi>)"
  by (transfer, rule assign4)

lemma skat_set_assign4_expr_var: "\<psi> = bexpr_map (\<lambda>\<gamma>. \<gamma>[X|t]) \<phi> \<Longrightarrow> pred_expr \<psi> \<cdot> X ::= t = X ::= t \<cdot> pred_expr \<phi>"
  by (erule ssubst, rule skat_set_assign4_expr)

lemma skat_set_assign4: "(pred (\<phi>[X|t]) \<cdot> X ::= t) = (X ::= t \<cdot> pred \<phi>)"
  apply (simp add: pred_to_expr)
  by (metis bexpr_map.simps(1) skat_set_assign4_expr)

lemma skat_set_assign4_var: "\<psi> = \<phi>[X|t] \<Longrightarrow> pred \<psi> \<cdot> X ::= t = X ::= t \<cdot> pred \<phi>"
  by (erule ssubst, rule skat_set_assign4)

lemma skat_assign4: "(pred (\<phi>[{x}|t]) \<cdot> x := t) = (x := t \<cdot> pred \<phi>)"
  by (simp add: skat_assign_def, rule skat_set_assign4)

lemma skat_assign4_var: "\<psi> = \<phi>[{x}|t] \<Longrightarrow> (pred \<psi> \<cdot> x := t) = (x := t \<cdot> pred \<phi>)"
  by (erule ssubst, rule skat_assign4)

lemma skat_set_assign_comm: "\<lbrakk>X \<inter> FV t = {}; Y \<inter> FV s = {}\<rbrakk> \<Longrightarrow> (X ::= s \<cdot> Y ::= t) = (Y ::= t \<cdot> X ::= s)"
  by (metis no_FV skat_set_assign1)

lemma skat_assign_comm: "\<lbrakk>x \<notin> FV t; y \<notin> FV s\<rbrakk> \<Longrightarrow> (x := s \<cdot> y := t) = (y := t \<cdot> x := s)"
  by (insert skat_assign1[of y s x t], simp)

lemma skat_set_assign5: "X \<inter> FV s = {} \<Longrightarrow> ((X \<union> Y) ::= s) = (X ::= s \<cdot> Y ::= s)"
  by (transfer, rule assign5, assumption)

lemma skat_set_assign5_var: "\<lbrakk>Z = X \<union> Y; X \<inter> FV s = {}\<rbrakk> \<Longrightarrow> Z ::= s = X ::= s \<cdot> Y ::= s"
  by (erule ssubst, rule skat_set_assign5)

lemma FV_null [simp]: "FV null = {}"
  apply (simp add: null_def FV_def)
  apply (subst Abs_wf_trm_inverse)
  apply (metis NULL_arity NULL_fun trms_const)
  by simp

lemma null_Rep [simp]: "Rep_wf_trm null = App NULL []"
  apply (simp add: null_def, subst Abs_wf_trm_inverse)
  apply (metis NULL_arity NULL_fun trms_const)
  by auto

lemma null_Abs [simp]: "Abs_wf_trm (App NULL []) = null"
  by (metis Ranked_Alphabet.null_def)

lemma skat_null_zero: "(x := s \<cdot> x := null) = (x := null)"
proof -
  have "(x := s \<cdot> x := null) = (x := null[{x}|s])"
    by (rule skat_assign3)
  also have "... = x := null"
    by (simp add: wf_trm_subst_def)
  finally show ?thesis .
qed

lemma skat_null_comm: "(x := null \<cdot> y := null) = (y := null \<cdot> x := null)"
  by (rule skat_assign_comm, simp_all)

lemma skat_halt: "x \<notin> output_vars TYPE('a::ranked_alphabet) \<Longrightarrow> (halt::'a skat) = x := null \<cdot> halt"
  apply (simp add: halt_def skat_assign_def)
  apply (subst skat_set_assign5_var[of _ "{x}" "- output_vars TYPE('a)"])
  apply (metis Compl_iff insert_absorb insert_is_Un)
  apply (simp add: FV_def)
  by (metis Compl_iff insert_absorb insert_is_Un)

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

lemma skat_not_closed: "x \<in> test_set \<Longrightarrow> !x \<in> test_set"
proof -
  assume "x \<in> test_set"
  then obtain x' where "x = test x'"
    by (metis image_iff test_set_def)
  have "!(test x') = test (bt_not x')"
    by (transfer, metis SKNot.simps(1) skat_con.refl)
  hence "!(test x') \<in> test_set"
    by (simp, metis rangeI test_set_def)
  from `x = test x'` and this show "!x \<in> test_set"
    by auto
qed

lemma test_ex: "x \<in> test_set \<Longrightarrow> \<exists>y. x = test y"
  by (simp add: test_set_def image_iff)

lemma test_closed: "test z \<in> test_set"
  by (simp add: test_set_def)

lemma test_closed_var: "test z \<in> carrier tests"
  by (simp add: tests_def, rule test_closed)

lemma pred_test: "pred p = test (abs_bterm (BLeaf p))"
  apply (simp add: pred_def)
  apply transfer
  by (metis skat_con.refl)

lemma pred_expr_test: "pred_expr p = test (abs_bterm p)"
  by (transfer, auto)

lemma pred_closed: "pred p \<in> carrier tests"
  by (simp add: pred_test, rule test_closed_var)

lemma pred_expr_closed: "pred_expr p \<in> carrier tests"
  by (simp add: pred_expr_test, rule test_closed_var)

(* Transfer concepts from skat to the embedded algebra *)

lemma one_to_test: "\<one> = test (bt_one)"
  by (transfer, rule test_one)

lemma test_one_closed: "\<one> \<in> carrier tests"
  by (metis one_to_test test_closed_var)

lemma zero_to_test: "\<zero> = test (bt_zero)"
  by (transfer, rule test_zero)

lemma test_zero_closed: "\<zero> \<in> carrier tests"
  by (metis test_closed_var zero_to_test)

lemma mult_to_test: "test x \<cdot> test y = test (bt_and x y)"
  by (transfer, metis skat_con.sym test_plus)

lemma test_mult_closed:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "x \<cdot> y \<in> carrier tests"
proof -
  from xc yc obtain x' and y' where "x = test x'" and "y = test y'"
    by (simp add: tests_def, metis test_ex)
  moreover have "test x' \<cdot> test y' \<in> carrier tests"
    by (simp add: mult_to_test, rule test_closed_var)
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
    by (simp add: plus_to_test, rule test_closed_var)
  ultimately show "x + y \<in> carrier tests"
    by auto
qed

lemma not_to_not: "!(test x) = test (bt_not x)"
  by (transfer, metis SKNot.simps(1) skat_con.refl)

lemma not_closed: assumes xc: "x \<in> carrier tests" shows "!x \<in> carrier tests"
proof -
  from xc obtain x' where "x = test x'"
    by (simp add: tests_def, metis test_ex)
  thus "!x \<in> carrier tests"
    by (simp add: not_to_not, metis test_closed_var)
qed

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
    by (simp add: x'_def y'_def plus_to_test, rule test_closed)

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
      by (metis hunt_con.trans meet not_compat one zero)
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
    x'_def[simp]: "x = test x'" and y'_def[simp]: "y = test y'"
    by (simp add: tests_def, metis test_ex)
  show "x + !x = \<one>"
  proof (simp, transfer)
    fix x
    have "skat_con (SKBool (x :+: BNot x)) SKOne"
      by (smt one skat_con.sym skat_con.trans test_ba test_mult test_one)
    thus "skat_con (SKBool x :\<oplus>: SKNot (SKBool x)) SKOne"
      by (simp, smt skat_con.sym skat_con.trans test_mult)
  qed
  show "x \<cdot> ! x = \<zero>"
  proof (simp, transfer)
    fix x
    have "skat_con (SKBool (x :\<cdot>: BNot x)) SKZero"
      by (metis hunt_con.trans meet not_compat one skat_con.sym skat_con.trans test_ba test_zero zero)
    thus "skat_con (SKBool x :\<odot>: SKNot (SKBool x)) SKZero"
      by (simp, smt skat_con.sym skat_con.trans test_plus)
  qed
  assume "x + y = \<one>" and "x \<cdot> y = \<zero>"
  thus "y = !x"
    apply simp
    apply transfer
    apply simp
    by (metis (hide_lams, no_types) mult_compat skat_con.mult_oner skat_con.mult_zeror skat_con.sym skat_con.trans test_mult test_plus)
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

lemma complement_one: "p \<in> carrier tests \<Longrightarrow> p + !p = \<one>"
  by (metis kat_comp_simp skt.complement1)

lemma complement_zero: "p \<in> carrier tests \<Longrightarrow> p \<cdot> !p = \<zero>"
  by (metis kat_comp_simp skt.complement2)

primrec test_unfold :: "'a::ranked_alphabet wf_pred bexpr \<Rightarrow> 'a skat" where
  "test_unfold (BLeaf x) = pred x"
| "test_unfold (BOr x y) = test_unfold x + test_unfold y"
| "test_unfold (BAnd x y) = test_unfold x \<cdot> test_unfold y"
| "test_unfold (BNot x) = !(test_unfold x)"
| "test_unfold BOne = \<one>"
| "test_unfold BZero = \<zero>"

lemma not_test_unfold: "!(test_unfold x) = test_unfold (BNot x)" by simp

primrec skat_unfold :: "'a::ranked_alphabet skat_expr \<Rightarrow> 'a skat" where
  "skat_unfold (SKLeaf x y) = x ::= y"
| "skat_unfold (SKPlus x y) = skat_unfold x + skat_unfold y"
| "skat_unfold (SKMult x y) = skat_unfold x \<cdot> skat_unfold y"
| "skat_unfold (SKBool p) = test_unfold p"
| "skat_unfold SKOne = \<one>"
| "skat_unfold SKZero = \<zero>"
| "skat_unfold (SKStar x) = (skat_unfold x)\<^sup>\<star>"

lemma pred_expr_unfold: "test_unfold p = pred_expr p"
  apply (induct p)
  apply (metis pred_to_expr test_unfold.simps(1))
proof simp_all
  fix p1 p2
  show "pred_expr p1 + pred_expr p2 = pred_expr (p1 :+: p2)"
    by (transfer, metis (lifting) skat_con.sym test_mult)
  show "!(pred_expr p1) = pred_expr (BNot p1)"
    by (transfer, auto)
  show "pred_expr p1 \<cdot> pred_expr p2 = pred_expr (p1 :\<cdot>: p2)"
    by (transfer, metis skat_con.sym test_plus)
  show "\<one> = pred_expr BOne"
    by (transfer, metis test_one)
  show "\<zero> = pred_expr BZero"
    by (transfer, metis test_zero)
qed

lemma pred_subst_id: "X \<inter> pred_vars y = {} \<Longrightarrow> y = pred_subst X s y"
proof (induct y, simp, simp add: wf_trm_subst_def)
  fix ys :: "'a wf_trm list"
  assume "X \<inter> (\<Union>y\<in>set ys. FV y) = {}"
  thus "ys = map (wf_trm_subst X s) ys"
    apply (induction ys, simp_all) (* This takes a while... *)
    by (metis Int_Un_distrib Int_commute Un_commute Un_empty_left Un_left_absorb no_FV)
qed

lemma pred_comm: "X \<inter> wf_pred_vars p = {} \<Longrightarrow> pred p \<cdot> X ::= s = X ::= s \<cdot> pred p"
  apply (induct p)
  apply (simp add: wf_pred_vars_def)
  apply (subgoal_tac "X \<inter> pred_vars y = {}")
  apply (rule skat_set_assign4_var)
  apply (simp add: wf_pred_subst_def)
  apply (subst Abs_wf_pred_inverse)
  apply assumption
  apply (metis (lifting) pred_subst_id)
  apply (subst Abs_wf_pred_inverse[symmetric])
  by assumption+

lemma pred_expr_comm:
  "X \<inter> (\<Union>x\<in>bexpr_leaves p. wf_pred_vars x) = {} \<Longrightarrow> pred_expr p \<cdot> X ::= s = X ::= s \<cdot> pred_expr p"
  apply (rule_tac skat_set_assign4_expr_var)
  apply (induct p, simp_all)
  defer
  apply (smt inf_sup_distrib1 sup_bot_left sup_commute sup_idem sup_left_commute)
  apply (metis (lifting) Int_Un_distrib2 Int_commute sup_eq_bot_iff)
proof -
  fix p :: "'a wf_pred" assume "X \<inter> wf_pred_vars p = {}"
  thus "p = p[X|s]"
    apply (induct p)
    apply (simp add: wf_pred_vars_def)
    apply (subgoal_tac "X \<inter> pred_vars y = {}")
    apply (metis Abs_wf_pred_inverse o_apply pred_subst_id wf_pred_subst_def)
    by (metis (lifting) Abs_wf_pred_inverse)
qed

theorem no_modify_commute_test:
  assumes no_modification: "modifies x \<inter> touches (SKBool y) = {}"
  shows "skat_unfold (x :\<odot>: SKBool y) = skat_unfold (SKBool y :\<odot>: x)"
proof -
  from no_modification show ?thesis
    apply (induct x, simp_all)
    apply (simp add: pred_expr_unfold)
    apply (metis pred_expr_comm)
    apply (smt inf_sup_distrib2 skd.distl skd.distr sup_eq_bot_iff)
    apply (smt inf_sup_distrib2 skd.mult_assoc sup_eq_bot_iff)
    apply (rule skd.nat_antisym[simplified])
    apply (rule ska.star_inductl[rule_format,simplified])
    apply (smt ska.star_1l ska.star_plus_one skat_order_def skd.add_assoc skd.distl skd.mult_assoc skd.mult_oner)
    apply (rule ska.star_inductr[rule_format,simplified])
    apply (subst skd.mult_assoc[simplified])
    apply (subgoal_tac "test_unfold y \<cdot> skat_unfold xa = skat_unfold xa \<cdot> test_unfold y")
    apply (rotate_tac 3)
    apply (erule ssubst)
    apply (subst skd.mult_assoc[symmetric,simplified])
    apply (rule ska.add_lub_r1[simplified])
    apply (metis ska.star_ref skd.mult_isor skd.mult_onel)
    apply (smt ska.star_1l ska.star_slide_var1 skd.mult_isor skd.nat_trans)
    apply simp
    apply (simp add: pred_expr_unfold)
    apply (subst tests_meet[symmetric])
    prefer 3
    apply (subst tests_meet[symmetric])
    prefer 3
    apply (subst meet_semilattice.meet_comm[OF tests_ms], simp)
    apply (rule pred_expr_closed)+
    apply (metis skd.mult_onel skd.mult_oner)
    apply (metis skd.mult_zerol skd.mult_zeror)
    done
qed

theorem no_interact_commute1_fold:
  assumes no_interaction: "(X \<union> FV s) \<inter> touches y = {}"
  shows "skat_unfold (SKLeaf X s :\<odot>: y) = skat_unfold (y :\<odot>: SKLeaf X s)"
proof -
  let ?U = "skat_unfold"
  from no_interaction show ?thesis
  proof (induct y, simp_all)
    fix Y and t :: "'a wf_trm" assume asm: "(X \<union> FV s) \<inter> (Y \<union> FV t) = {}"
    show "X ::= s \<cdot> Y ::= t = Y ::= t \<cdot> X ::= s"
      by (rule skat_set_assign_comm, insert asm, blast+)
  next
    fix t u
    assume ind_hyp1:
      "(X \<union> FV s) \<inter> touches t = {} \<Longrightarrow> X ::= s \<cdot> ?U t = ?U t \<cdot> X ::= s"
    and ind_hyp2:
      "(X \<union> FV s) \<inter> touches u = {} \<Longrightarrow> X ::= s \<cdot> ?U u = ?U u \<cdot> X ::= s"
    and ni: "(X \<union> FV s) \<inter> (touches t \<union> touches u) = {}"
    have "X ::= s \<cdot> (?U t + ?U u) = (X ::= s \<cdot> ?U t) + (X ::= s \<cdot> ?U u)"
      by (metis skd.distl)
    also have "... = (?U t \<cdot> X ::= s) + (?U u \<cdot> X ::= s)"
      by (insert ni, subst ind_hyp1[simplified], blast, subst ind_hyp2[simplified], auto)
    also have "... = (?U t + ?U u) \<cdot> X ::= s"
      by (metis skd.distr)
    finally show "X ::= s \<cdot> (?U t + ?U u) = (?U t + ?U u) \<cdot> X ::= s" .
  next
    fix t u
    assume ind_hyp1:
      "(X \<union> FV s) \<inter> touches t = {} \<Longrightarrow> X ::= s \<cdot> ?U t = ?U t \<cdot> X ::= s"
    and ind_hyp2:
      "(X \<union> FV s) \<inter> touches u = {} \<Longrightarrow> X ::= s \<cdot> ?U u = ?U u \<cdot> X ::= s"
    and ni: "(X \<union> FV s) \<inter> (touches t \<union> touches u) = {}"
    show "X ::= s \<cdot> (?U t \<cdot> ?U u) = (?U t \<cdot> ?U u) \<cdot> X ::= s"
      apply (subst skd.mult_assoc[symmetric, simplified])
      apply (insert ni, subst ind_hyp1, blast)
      apply (subst skd.mult_assoc[simplified])
      apply (subst ind_hyp2, auto)
      by (simp add: skd.mult_assoc[simplified])
  next
    fix t
    assume ind_hyp: "X ::= s \<cdot> ?U t = ?U t \<cdot> X ::= s"
    and ni: "(X \<union> FV s) \<inter> touches t = {}"
    have "X ::= s \<cdot> ?U t\<^sup>\<star> \<sqsubseteq> ?U t\<^sup>\<star> \<cdot> X ::= s"
      apply (rule ska.star_inductr[rule_format,simplified])
      by (metis ind_hyp ska.star_unfoldr skd.add_lub skd.mult_assoc skd.mult_isor skd.mult_onel)
    moreover have "?U t\<^sup>\<star> \<cdot> X ::= s \<sqsubseteq> X ::= s \<cdot> ?U t\<^sup>\<star>"
      apply (rule ska.star_inductl[rule_format,simplified])
      by (smt ind_hyp ska.star_unfoldl_eq skd.distl skd.mult_assoc skd.mult_oner skd.nat_refl)
    ultimately show "X ::= s \<cdot> ?U t\<^sup>\<star> = ?U t\<^sup>\<star> \<cdot> X ::= s"
      by (metis skd.nat_antisym)
  next
    fix p :: "'a wf_pred bexpr"
    assume "(X \<union> FV s) \<inter> (\<Union>x\<in>bexpr_leaves p. wf_pred_vars x) = {}"
    thus "X ::= s \<cdot> test_unfold p = test_unfold p \<cdot> X ::= s"
      apply (simp only: pred_expr_unfold)
      by (metis (lifting) Int_Un_distrib2 pred_expr_comm sup_eq_bot_iff)
  next
    show "X ::= s \<cdot> \<one> = \<one> \<cdot> X ::= s"
      by (metis skd.mult_onel skd.mult_oner)
  next
    show "X ::= s \<cdot> \<zero> = \<zero> \<cdot> X ::= s"
      by (metis skd.mult_zerol skd.mult_zeror)
  qed
qed

lemma no_interact_commute_fold:
  assumes no_interaction: "touches x \<inter> touches y = {}"
  shows "skat_unfold x \<cdot> skat_unfold y = skat_unfold y \<cdot> skat_unfold x"
proof -
  from no_interaction show ?thesis
    apply (induct x)
    apply (metis no_interact_commute1_fold skat_unfold.simps(3) touches.simps(1))
    apply (smt UnI1 UnI2 disjoint_iff_not_equal skat_unfold.simps(2) skd.distl skd.distr touches.simps(2))
    apply (smt UnI1 UnI2 disjoint_iff_not_equal skat_unfold.simps(3) skd.mult_assoc touches.simps(3))
    defer
    defer
    apply (metis skat_unfold.simps(5) skd.mult_onel skd.mult_oner)
    apply (metis skat_unfold.simps(6) skd.mult_zerol skd.mult_zeror)
    apply (rule skd.nat_antisym[simplified])
    apply simp
    apply (rule ska.star_inductl[rule_format,simplified])
    apply (subst skd.mult_assoc[symmetric,simplified])
    apply simp
    apply (subst skd.mult_assoc[simplified])
    apply (rule ska.add_lub_r1[simplified])
    apply (metis (lifting) ska.star_plus_one skat_order_def skd.distl skd.mult_oner)
    apply (metis (lifting) ska.star_1l skd.mult_isol)
    apply simp
    apply (rule ska.star_inductr[rule_format,simplified])
    apply (subst skd.mult_assoc[simplified])
    apply (subgoal_tac "skat_unfold y \<cdot> skat_unfold x = skat_unfold x \<cdot> skat_unfold y")
    apply (rotate_tac 2)
    apply (erule ssubst)
    apply (subst skd.mult_assoc[simplified,symmetric])
    apply (rule ska.add_lub_r1[simplified])
    apply (metis ska.star_ref skd.mult_isor skd.mult_onel)
    apply (metis (lifting) ska.star_ext ska.star_invol ska.star_trans_eq skd.mult_double_iso skd.mult_isor)
    apply auto
    apply (insert no_modify_commute_test[of y] modify_subset_touch[of y])
    by (smt Un_commute Union_image_eq inf_commute inf_sup_distrib2 le_iff_sup skat_unfold.simps(3) skat_unfold.simps(4) sup_bot_left touches.simps(5))
qed

lemma no_interact_commute_fold_var:
  "touches x \<inter> touches y = {} \<Longrightarrow> skat_unfold (x :\<odot>: y) = skat_unfold (y :\<odot>: x)"
  by (simp, erule no_interact_commute_fold)

lemma assign_commute_fold:
  assumes no_interference: "X \<inter> FV t = {} \<and> Y \<inter> FV s = {}"
  shows "skat_unfold (SKLeaf X s :\<odot>: SKLeaf Y t) = skat_unfold (SKLeaf Y t :\<odot>: SKLeaf X s)"
  by (smt no_interference skat_set_assign_comm skat_unfold.simps(1) skat_unfold.simps(3))

lemma skat_comm_tac1:
  "skat_unfold (SKBool (p :\<cdot>: q)) = skat_unfold (SKBool p :\<odot>: SKBool q)"
  by simp

ML {*

fun skat_fold_tac ctxt n =
  REPEAT (EqSubst.eqsubst_tac ctxt [0] @{thms test_unfold.simps[symmetric]} n)
  THEN (REPEAT (EqSubst.eqsubst_tac ctxt [0] @{thms skat_unfold.simps[symmetric]} n))

structure SkatAlphabetRules = Named_Thms
  (val name = @{binding "skat_alphabet"}
   val description = "SKAT alphabet rules")

structure SkatSimpRules = Named_Thms
  (val name = @{binding "skat_simp"}
   val description = "SKAT simplification rules")

fun skat_std_commuter ctxt n =
  DETERM (skat_fold_tac ctxt n
    THEN simp_tac (HOL_basic_ss addsimps @{thms skat_comm_tac1}) n)
  THEN (resolve_tac @{thms no_modify_commute_test no_modify_commute_test[symmetric]} n
    ORELSE rtac @{thm assign_commute_fold} n
    ORELSE rtac @{thm no_interact_commute_fold_var} n)

fun skat_ni_commuter ctxt n =
  DETERM (skat_fold_tac ctxt n
    THEN simp_tac (HOL_basic_ss addsimps @{thms skat_comm_tac1}) n)
  THEN rtac @{thm no_interact_commute_fold_var} n

fun wf_trm_abs_inverse_tac ctxt =
  EqSubst.eqsubst_tac ctxt [0] @{thms Abs_wf_trm_inverse} 1
  THEN REPEAT
    (CHANGED (asm_full_simp_tac (simpset_of ctxt addsimps SkatAlphabetRules.get ctxt) 1)
    ORELSE resolve_tac @{thms trms.intros} 1)

fun wf_pred_abs_inverse_tac ctxt =
  EqSubst.eqsubst_tac ctxt [0] @{thms Abs_wf_pred_inverse} 1
  THEN REPEAT
    (CHANGED (asm_full_simp_tac
      (simpset_of ctxt addsimps @{thms FV_def} addsimps SkatAlphabetRules.get ctxt) 1)
    ORELSE resolve_tac @{thms preds.intros} 1
    ORELSE rtac @{thm conjI} 1)

val touch_simp_tac =
  Subgoal.FOCUS (fn {context, ...} =>
    REPEAT (wf_trm_abs_inverse_tac context)
    THEN REPEAT (wf_pred_abs_inverse_tac context))

fun skat_comm_tac' commuter ctxt n =
  asm_full_simp_tac (HOL_basic_ss addsimps SkatSimpRules.get ctxt) n
  THEN DETERM (commuter ctxt n)
  THEN asm_full_simp_tac (simpset_of ctxt addsimps @{thms FV_def wf_pred_vars_def}) n
  THEN TRY (touch_simp_tac ctxt n)

val skat_comm_tac = skat_comm_tac' skat_std_commuter
*}

method_setup skat_comm = {*
Scan.succeed (fn ctxt => SIMPLE_METHOD (skat_comm_tac ctxt 1))
*}

method_setup skat_simp = {*
Scan.succeed (fn ctxt =>
  asm_full_simp_tac (simpset_of ctxt addsimps SkatSimpRules.get ctxt) 1
  THEN TRY (touch_simp_tac ctxt 1)
  |> SIMPLE_METHOD)
*}

method_setup skat_reduce = {*
Scan.succeed (fn ctxt =>
  SIMPLE_METHOD (simp_tac (HOL_basic_ss addsimps SkatSimpRules.get ctxt) 1))
*}

setup {* SkatAlphabetRules.setup *}
setup {* SkatSimpRules.setup *}

declare skat_assign_def [skat_simp]

lemma "X \<inter> FV s = {} \<Longrightarrow> (X ::= s)\<^sup>+ = X ::= s"
proof -
  assume "X \<inter> FV s = {}"
  hence "X ::= s + X ::= s \<cdot> X ::= s \<sqsubseteq> X ::= s"
    by (metis Un_absorb skat_set_assign5 skd.add_idem skd.nat_refl)
  hence "X ::= s \<cdot> (X ::= s)\<^sup>\<star> \<sqsubseteq> X ::= s"
    by (rule ska.star_inductr[rule_format,simplified])
  hence "(X ::= s)\<^sup>+ \<sqsubseteq> X ::= s"
    by (metis skat_star1_def)
  moreover have "X ::= s \<sqsubseteq> (X ::= s)\<^sup>+"
    by (metis ska.star_ref skat_star1_def skd.mult_isol skd.mult_oner)
  ultimately show ?thesis
    by (metis skd.nat_antisym)
qed

lemma skat_star_elim:
  assumes "X \<inter> touches t = {}"
  shows "(X ::= s \<cdot> skat_unfold t)\<^sup>\<star> \<cdot> X ::= null = (skat_unfold t)\<^sup>\<star> \<cdot> X ::= null"
  apply (subst ska.star_elim[symmetric,simplified])
  apply (metis FV_null inf_bot_right no_FV skat_set_assign3)
  apply skat_comm
  apply (metis assms inf_commute)
  apply (metis FV_null inf_bot_right no_FV skat_set_assign3)
  by auto

lemma unfold_is_abs: "skat_unfold y = abs_skat y"
proof (induct y, simp_all)
  fix X s show "X ::= s = abs_skat (SKLeaf X s)"
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

lemma unfold_exists: "\<exists>t. skat_unfold t = s"
  by (metis Quotient3_abs_rep Quotient3_skat unfold_is_abs)

definition P where "P X s \<equiv> X ::= s"

declare P_def [skat_simp]

ML {*
fun inst_thm ctrm thm = Drule.instantiate' [SOME (ctyp_of_term ctrm)] [SOME ctrm] thm

fun skat_apply_fold_tac ctrm =
  Subgoal.FOCUS (fn {context, ...} =>
    rtac @{thm HOL.trans} 1
    THEN rtac (inst_thm ctrm @{thm arg_cong}) 1
    THEN simp_tac (Simplifier.context context empty_ss addsimps SkatSimpRules.get context) 1
    THEN skat_fold_tac context 1
    THEN simp_tac HOL_basic_ss 1)
*}

definition seq :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "seq xs \<equiv> foldl op \<cdot> \<one> xs"

definition SEQ :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "SEQ \<equiv> seq"

definition qes :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "qes xs \<equiv> seq (rev xs)"

definition QES :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "QES \<equiv> qes"

lemma seq_to_qes: "seq xs = qes (rev xs)"
  by (simp add: qes_def)

ML {*
fun seq_select_tac s ctxt n =
  simp_tac (HOL_basic_ss addsimps @{thms SEQ_def[symmetric]}) n
  THEN EqSubst.eqsubst_tac ctxt [s] @{thms SEQ_def} n

fun seq_deselect_tac n =
  simp_tac (HOL_basic_ss addsimps @{thms SEQ_def QES_def}) n

fun qes_select_tac s ctxt n =
  simp_tac (HOL_basic_ss addsimps @{thms QES_def[symmetric]}) n
  THEN EqSubst.eqsubst_tac ctxt [s] @{thms QES_def} n

fun qes_deselect_tac n =
  simp_tac (HOL_basic_ss addsimps @{thms QES_def}) n

fun seq_reverse_tac s ctxt n =
  seq_select_tac s ctxt n
  THEN simp_tac (HOL_basic_ss addsimps @{thms seq_to_qes rev.simps append.simps}) n
  THEN seq_deselect_tac n

fun qes_reverse_tac s ctxt n =
  qes_select_tac s ctxt n
  THEN simp_tac (HOL_basic_ss addsimps @{thms qes_def rev.simps append.simps}) n
  THEN qes_deselect_tac n

*}

method_setup seq_select = {*
Scan.lift (Scan.optional Parse.nat 0) >>
  (fn s => fn ctxt => SIMPLE_METHOD (seq_select_tac s ctxt 1))
*}

method_setup seq_deselect = {*
Scan.succeed (fn _ => SIMPLE_METHOD (seq_deselect_tac 1))
*}

method_setup qes_select = {*
Scan.lift (Scan.optional Parse.nat 0) >>
  (fn s => fn ctxt => SIMPLE_METHOD (qes_select_tac s ctxt 1))
*}

method_setup qes_deselect = {*
Scan.succeed (fn _ => SIMPLE_METHOD (qes_deselect_tac 1))
*}

method_setup seq_rev = {*
Scan.lift (Scan.optional Parse.nat 0) >>
  (fn s => fn ctxt => seq_reverse_tac s ctxt |> SIMPLE_METHOD')
*}

method_setup qes_rev = {*
Scan.lift (Scan.optional Parse.nat 0) >>
  (fn s => fn ctxt => qes_reverse_tac s ctxt |> SIMPLE_METHOD')
*}

lemmas mult_oner = skd.mult_oner[simplified]
  and mult_onel = skd.mult_onel[simplified]

declare mult_oner [skat_simp]
  and mult_onel [skat_simp]
  and seq_def [skat_simp]
  and qes_def [skat_simp]
  and foldl.simps [skat_simp]
  and rev.simps [skat_simp]
  and append.simps [skat_simp]

lemma seq_singleton [simp]: "seq [x] = x" by skat_reduce
lemma qes_singleton [simp]: "qes [x] = x" by skat_reduce

lemma foldl_step: "foldl op \<cdot> \<one> (x#xs) = x \<cdot> foldl op \<cdot> \<one> xs"
  by (induct xs arbitrary: x, auto, skat_reduce, metis skd.mult_assoc)

lemma foldl_is_foldr: "foldl op \<cdot> \<one> xs = foldr op \<cdot> xs \<one>"
  by (induct xs, auto, metis foldl_Cons foldl_step)

lemma seq_foldr: "seq xs = foldr op \<cdot> xs \<one>"
  by (simp add: seq_def foldl_is_foldr)

lemma seq_mult: "seq (xs @ ys) = seq xs \<cdot> seq ys"
  apply (induct xs)
  apply (simp add: seq_foldr)
  apply (metis skd.mult_onel)
  apply (simp add: seq_foldr)
  by (metis skd.mult_assoc)

lemma seq_cut: "seq xs = seq (take n xs) \<cdot> seq (drop n xs)"
  by (subst seq_mult[symmetric], simp)

lemma seq_zip: "seq xs = qes (rev (take n xs)) \<cdot> seq (drop n xs)"
  by (metis seq_cut seq_to_qes)

ML {*

fun nat_cterm 0 = @{cterm "0::nat"}
  | nat_cterm n = Thm.apply @{cterm Suc} (nat_cterm (n - 1))

*}

method_setup cut = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat >>
  (fn (s, c) => fn ctxt =>
    let
      val ct = nat_cterm c
    in
      seq_select_tac s ctxt 1
      THEN EqSubst.eqsubst_tac ctxt [0] [Drule.instantiate' [] [NONE, SOME ct] @{thm seq_cut}] 1
      THEN simp_tac (HOL_basic_ss addsimps @{thms Nat.nat.cases take.simps drop.simps}) 1
      THEN seq_deselect_tac 1
      |> SIMPLE_METHOD
    end)
*}

ML {*
fun zip_tac s c ctxt n =
  let
    val ct = nat_cterm c
  in
    seq_select_tac s ctxt n
    THEN EqSubst.eqsubst_tac ctxt [0] [Drule.instantiate' [] [NONE, SOME ct] @{thm seq_zip}] n
    THEN simp_tac (HOL_basic_ss addsimps @{thms rev.simps append.simps Nat.nat.cases take.simps drop.simps}) n
  end
*}

method_setup zip = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat >>
  (fn (s, c) => fn ctxt => SIMPLE_METHOD (zip_tac s c ctxt 1))
*}

lemma zip_right: "qes (x#xs) \<cdot> seq ys = qes xs \<cdot> seq (x#ys)"
  by (metis (no_types) foldl_step qes_def rev.simps(2) seq_def seq_mult seq_singleton skd.mult_assoc)

lemmas zip_left = zip_right[symmetric]

lemma zip_comm: "x\<cdot>y = y\<cdot>x \<Longrightarrow> qes (x#xs) \<cdot> seq (y#ys) = qes (y#xs) \<cdot> seq (x#ys)"
  by (metis (no_types) qes_def rev.simps(2) seq_mult seq_singleton skd.mult_assoc zip_left)

lemma unzip: "qes xs \<cdot> seq ys = seq (rev xs @ ys)"
  by (metis qes_def seq_mult)

ML {*
fun unzip_tac ctxt n =
  EqSubst.eqsubst_tac ctxt [0] @{thms unzip} n
  THEN simp_tac (HOL_basic_ss addsimps @{thms rev.simps append.simps}) n
*}

method_setup unzip = {*
Scan.succeed (fn ctxt => unzip_tac ctxt |> SIMPLE_METHOD')
*}

method_setup commr = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat >>
  (fn (s, c) => fn ctxt =>
    zip_tac s c ctxt 1
    THEN (CHANGED (REPEAT (EVERY
      [ EqSubst.eqsubst_tac ctxt [0] @{thms zip_comm} 1
      , skat_comm_tac ctxt 1
      , EqSubst.eqsubst_tac ctxt [0] @{thms zip_left} 1
      ])))
    THEN unzip_tac ctxt 1
    THEN seq_deselect_tac 1
    |> SIMPLE_METHOD)
*}

method_setup comml = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat >>
  (fn (s, c) => fn ctxt =>
    zip_tac s (c - 1) ctxt 1
    THEN (CHANGED (REPEAT (EVERY
      [ EqSubst.eqsubst_tac ctxt [0] @{thms zip_comm} 1
      , skat_comm_tac ctxt 1
      , EqSubst.eqsubst_tac ctxt [0] @{thms zip_right} 1
      ])))
    THEN unzip_tac ctxt 1
    THEN seq_deselect_tac 1
    |> SIMPLE_METHOD)
*}

lemma seq_cong: "seq xs = seq ys \<Longrightarrow> seq (x#xs) = seq (x#ys)"
  by (skat_simp, metis Ranked_Alphabet.mult_onel foldl_Cons foldl_step)

lemma qes_cong: "qes xs = qes ys \<Longrightarrow> qes (x#xs) = qes (x#ys)"
  by skat_simp

method_setup cong = {*
Scan.succeed (fn ctxt =>
  REPEAT (rtac @{thm seq_cong} 1)
  THEN simp_tac (HOL_basic_ss addsimps @{thms seq_to_qes rev.simps append.simps}) 1
  THEN REPEAT (rtac @{thm qes_cong} 1)
  THEN simp_tac (HOL_basic_ss addsimps @{thms qes_def rev.simps append.simps}) 1
  |> CHANGED |> SIMPLE_METHOD)
*}

method_setup congl = {*
Scan.succeed (fn ctxt =>
  REPEAT (rtac @{thm seq_cong} 1) |> CHANGED |> SIMPLE_METHOD)
*}

method_setup congr = {*
Scan.succeed (fn ctxt =>
  simp_tac (HOL_basic_ss addsimps @{thms seq_to_qes rev.simps append.simps}) 1
  THEN (REPEAT (rtac @{thm qes_cong} 1))
  THEN simp_tac (HOL_basic_ss addsimps @{thms qes_def rev.simps append.simps}) 1
  |> CHANGED |> SIMPLE_METHOD)
*}

lemma seq_head_eq [intro]: "\<lbrakk>x = y; seq xs = seq ys\<rbrakk> \<Longrightarrow> seq (x#xs) = seq (y#ys)"
  by (metis seq_cong)

lemma seq_head_plus [intro]: "seq xs = seq ys + seq zs \<Longrightarrow> seq (x#xs) = seq (x#ys) + seq (x#zs)"
  by (metis append_Cons eq_Nil_appendI seq_mult skd.distl)

lemma seq_head_elim [simp,elim]: "x \<in> carrier tests \<Longrightarrow> seq (x#xs) + seq (!x#xs) = seq xs"
proof -
  assume "x \<in> carrier tests"
  hence "(x + !x) \<cdot> seq xs = seq xs"
    by (metis complement_one skd.mult_onel)
  hence "x \<cdot> seq xs + !x \<cdot> seq xs = seq xs"
    by (metis skd.distr)
  thus ?thesis
    by (metis append_Cons append_Nil seq_mult seq_singleton)
qed

lemma seq_head_elim_var [simp,elim]: "x \<in> carrier tests \<Longrightarrow> seq (!x#xs) + seq (x#xs) = seq xs"
  by (metis seq_head_elim skd.add_comm)

lemma zip_zero: "x\<cdot>y = \<zero> \<Longrightarrow> qes (x#xs) \<cdot> seq (y#ys) = \<zero>"
  by (metis fold_Cons_rev foldl_step seq_def skd.mult_assoc skd.mult_zerol skd.mult_zeror zip_left)

lemma zip_zero1: "x \<in> carrier tests \<Longrightarrow> qes (x#xs) \<cdot> seq (!x#ys) = \<zero>"
  by (metis complement_zero foldl_step seq_def skd.mult_assoc skd.mult_zerol skd.mult_zeror zip_left)

lemma zip_zero2: "x \<in> carrier tests \<Longrightarrow> qes (!x#xs) \<cdot> seq (x#ys) = \<zero>"
  by (metis not_closed skt.test_mult_comm zip_comm zip_zero1)

lemma zippify: "seq xs \<cdot> seq ys = qes (rev xs) \<cdot> seq ys"
  by (simp add: qes_def)

method_setup zero = {*
Scan.succeed (fn ctxt =>
  EqSubst.eqsubst_tac ctxt [0] @{thms zippify} 1
  THEN simp_tac (HOL_basic_ss addsimps @{thms rev.simps append.simps}) 1
  THEN EqSubst.eqsubst_tac ctxt [0] @{thms zip_zero1 zip_zero2} 1
  |> SIMPLE_METHOD)
*}

lemma seq_cons: "seq (x#xs) = x \<cdot> seq xs"
  by (metis foldl_step seq_def)

lemma qes_snoc: "qes (x#xs) = qes xs \<cdot> x"
  by (simp add: qes_def seq_mult)

lemma seq_empty [simp]: "seq [] = \<one>" by skat_reduce
lemma qes_empty [simp]: "qes [] = \<one>" by skat_reduce

inductive not_read :: "nat set \<Rightarrow> 'a::ranked_alphabet skat_expr \<Rightarrow> bool" where
  "X \<inter> FV s = {} \<Longrightarrow> not_read X (SKLeaf Y s)"
| "X \<inter> (\<Union>q\<in>bexpr_leaves p. wf_pred_vars q) = {} \<Longrightarrow> not_read X (SKBool p)"
| "\<lbrakk>not_read X s; not_read X t\<rbrakk> \<Longrightarrow> not_read X (s :\<odot>: t)"
| "\<lbrakk>not_read X s; not_read X t\<rbrakk> \<Longrightarrow> not_read X (s :\<oplus>: t)"
| "not_read X s \<Longrightarrow> not_read X (SKStar s)"
| "not_read X SKOne"
| "not_read X SKZero"

lemma not_read_leaf [simp]: "not_read X (SKLeaf Y s) = (X \<inter> FV s = {})"
  by (default, rule not_read.cases[of "X" "SKLeaf Y s"], simp_all add: not_read.intros(1))

lemma not_read_bool [simp]: "not_read X (SKBool p) = (X \<inter> (\<Union>q\<in>bexpr_leaves p. wf_pred_vars q) = {})"
  by (default, rule not_read.cases[of "X" "SKBool p"], simp_all add: not_read.intros(2))

lemma not_read_mult [simp]: "not_read X (s :\<odot>: t) = (not_read X s \<and> not_read X t)"
  by (default, rule not_read.cases[of "X" "s :\<odot>: t"], simp_all add: not_read.intros(3))

lemma not_read_plus [simp]: "not_read X (s :\<oplus>: t) = (not_read X s \<and> not_read X t)"
  by (default, rule not_read.cases[of "X" "s :\<oplus>: t"], simp_all add: not_read.intros(4))

lemma not_read_star [simp]: "not_read X (SKStar s) = not_read X s"
  by (default, rule not_read.cases[of "X" "SKStar s"], simp_all add: not_read.intros(5))

fun eliminate :: "nat set \<Rightarrow> 'a::ranked_alphabet skat_expr => 'a skat_expr" where
  "eliminate X (SKLeaf Y s) = SKLeaf (Y - X) s"
| "eliminate X (SKBool p) = (SKBool p)"
| "eliminate X (s :\<odot>: t) = eliminate X s :\<odot>: eliminate X t"
| "eliminate X (s :\<oplus>: t) = eliminate X s :\<oplus>: eliminate X t"
| "eliminate X (SKStar s) = SKStar (eliminate X s)"
| "eliminate X SKOne = SKOne"
| "eliminate X SKZero = SKZero"

lemma [simp]: "X \<inter> Y \<union> X = X" by blast

lemma not_read_elim [intro!]: "not_read X s \<Longrightarrow> touches (eliminate X s) \<inter> X = {}"
  by (induct s, auto)

lemma eliminate_comm:
  "not_read X s \<Longrightarrow> skat_unfold (eliminate X s) \<cdot> X ::= null = X ::= null \<cdot> skat_unfold (eliminate X s)"
  by (skat_comm, auto)

subsubsection {* Lemma 4.4 *}

text {* If the variables in a set $X$ are not read by a program $s$
then any assignments to a variable in $X$ can be eliminated from $s$
*}

theorem variable_elimination:
  "not_read X s \<Longrightarrow> skat_unfold s \<cdot> X ::= null = skat_unfold (eliminate X s) \<cdot> X ::= null"
proof (induct s, auto simp add: skd.distr[simplified])
  fix Y s assume asm: "X \<inter> FV s = {}"
  have "Y ::= s \<cdot> X ::= null = ((X \<inter> Y) \<union> (Y - X)) ::= s \<cdot> X ::= null"
    by (metis Un_Diff_Int inf_commute sup_commute)
  also have "... = (X \<inter> Y) ::= s \<cdot> (Y - X) ::= s \<cdot> X ::= null"
    by (subst skat_set_assign5, insert asm, auto)
  also have "... = (X \<inter> Y) ::= s \<cdot> X ::= null \<cdot> (Y - X) ::= s"
    by (smt FV_null Int_empty_right asm skat_set_assign_comm skd.mult_assoc)
  also have "... = (X \<inter> Y) ::= s \<cdot> ((X \<inter> Y) ::= null \<cdot> X ::= null) \<cdot> (Y - X) ::= s"
    by (subst skat_set_assign5[symmetric], insert asm, auto)
  also have "... = (X \<inter> Y) ::= null \<cdot> X ::= null \<cdot> (Y - X) ::= s"
    by (metis FV_null inf_bot_right no_FV skat_set_assign3 skd.mult_assoc)
  also have "... = X ::= null \<cdot> (Y - X) ::= s"
    by (metis FV_null Un_commute inf_bot_right skat_set_assign5 sup_inf_absorb)
  also have "... = (Y - X) ::= s \<cdot> X ::= null"
    by (metis FV_null asm inf_bot_right skat_set_assign_comm)
  finally show "Y ::= s \<cdot> X ::= null = (Y - X) ::= s \<cdot> X ::= null" .
next
  fix s t :: "'a skat_expr"
  assume "skat_unfold s \<cdot> X ::= null = skat_unfold (eliminate X s) \<cdot> X ::= null"
  and "skat_unfold t \<cdot> X ::= null = skat_unfold (eliminate X t) \<cdot> X ::= null"
  and "not_read X s" and "not_read X t"
  thus "skat_unfold s \<cdot> skat_unfold t \<cdot> X ::= null =
        skat_unfold (eliminate X s) \<cdot> skat_unfold (eliminate X t) \<cdot> X ::= null"
    by (metis (lifting) eliminate_comm skd.mult_assoc)
next
  fix s :: "'a skat_expr"
  assume "skat_unfold s \<cdot> X ::= null = skat_unfold (eliminate X s) \<cdot> X ::= null"
  and "not_read X s"
  thus "skat_unfold s\<^sup>\<star> \<cdot> X ::= null = skat_unfold (eliminate X s)\<^sup>\<star> \<cdot> X ::= null"
    by (metis eliminate_comm ska.star_sim)
qed

end
