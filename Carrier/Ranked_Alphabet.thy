theory Ranked_Alphabet
  imports KAT Boolean_Algebra_Extras
begin

(* +------------------------------------------------------------------------+ *)
subsection {* Ranked Alphabets *}
(* +------------------------------------------------------------------------+ *)

text {* A ranked alphabet consists of a set of disjoint function and
relation symbols. Each symbol in the alphabet has an associated
arity. The set @{const funs} contains all the function symbols, while
@{const rels} contains all the relation symbols. The @{const arity}
function returns the arity of a symbol.

Ranked alphabets are formalised as a typeclass, so a concrete alphabet
is simply a type which supports the above functions and the typeclass
laws. This avoids having to parameterise defintions with alphabets,
which allows things to stay at the type level. *}

class ranked_alphabet =
  fixes arity :: "'a \<Rightarrow> nat"
  and funs :: "'a set"
  and rels :: "'a set"
  assumes symbols_finite: "finite UNIV"
  and funs_rels_disjoint: "funs \<inter> rels = {}"
  and funs_rels_union: "funs \<union> rels = UNIV"
  and funs_exist: "funs \<noteq> {}"
  and rels_exist: "rels \<noteq> {}"

(* +------------------------------------------------------------------------+ *)
subsection {* Terms *}
(* +------------------------------------------------------------------------+ *)

datatype 'a trm = App 'a "'a trm list" | Var nat

fun trm_vars :: "'a trm \<Rightarrow> nat set" where
  "trm_vars (App f xs) = \<Union> (set (map trm_vars xs))"
| "trm_vars (Var v) = {v}"

fun trm_subst :: "nat \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" where
  "trm_subst v s (Var v') = (if v = v' then s else Var v')"
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

text {* Given a set, generate all posible $n$-tuples of a specific
length. Here we represent an $n$-tuple as a list. *}

fun ntuples :: "'a set \<Rightarrow> nat \<Rightarrow> ('a list) set" ("_\<^bsup>_\<^esup>") where
  "X\<^bsup>0\<^esup> = {[]}"
| "X\<^bsup>Suc n\<^esup> = {x. \<exists>y\<in>X. \<exists>ys\<in>X\<^bsup>n\<^esup>. x = y#ys}"

lemma ntuples1: "set xs \<subseteq> X \<longleftrightarrow> xs \<in> X\<^bsup>length xs\<^esup>" by (induct xs, simp_all)

lemma ntuples2: "\<lbrakk>set xs \<subseteq> X; length xs = n\<rbrakk> \<Longrightarrow> xs \<in> X\<^bsup>n\<^esup>" by (metis ntp1)

lemma lem: "(x \<in> X \<and> xs \<in> X\<^bsup>n\<^esup>) \<longleftrightarrow> x#xs \<in> X\<^bsup>Suc n\<^esup>" by simp

lemma "n \<noteq> 0 \<longleftrightarrow> [] \<notin> X\<^bsup>n\<^esup>"
  by (induct n, simp_all)

lemma ntp3: "xs \<in> X\<^bsup>length xs\<^esup> \<Longrightarrow> set xs \<subseteq> X"
  by (induct xs, simp_all)

lemma ntp4: "xs \<in> X\<^bsup>n\<^esup> \<Longrightarrow> length xs = n"
  apply (induct X n arbitrary: xs rule: ntuples.induct)
  by (simp_all, metis Suc_length_conv)

lemma ntp5 [iff]: "xs \<in> X\<^bsup>n\<^esup> \<longleftrightarrow> (set xs \<subseteq> X \<and> length xs = n)"
  by (metis ntp1 ntp4)

lemma ntuples_set: "X\<^bsup>n\<^esup> = {xs. set xs \<subseteq> X \<and> length xs = n}" by auto

type_synonym 'a relation = "('a list) set"

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

definition eval_wf_trm :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'a wf_trm \<Rightarrow> 'b" where
  "eval_wf_trm D mem x \<equiv> eval_trm D mem (Rep_wf_trm x)"

lemma eval_wf_trm_closed:
  assumes valid_ip: "valid_interp D"
  and valid_mem: "\<forall>n. mem n \<in> carrier D"
  shows "eval_wf_trm D mem x \<in> carrier D"
  by (metis Rep_wf_trm eval_trm_closed eval_wf_trm_def valid_ip valid_mem)

value Abs_wf_trm

definition wf_trm_subst :: "nat \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a wf_trm \<Rightarrow> 'a wf_trm" where
  "wf_trm_subst v s x \<equiv> Abs_wf_trm (trm_subst v (Rep_wf_trm s) (Rep_wf_trm x))"

abbreviation wf_trm_subst_notation :: "'a::ranked_alphabet wf_trm \<Rightarrow> nat \<Rightarrow> 'a wf_trm \<Rightarrow> 'a wf_trm"
  ("_[_|_]" [100,100,100] 101) where
  "s[x|t] \<equiv> wf_trm_subst x t s"

datatype 'a pred = Pred 'a "'a wf_trm list"

inductive_set preds :: "'a::ranked_alphabet pred set" where
  "\<lbrakk>P \<in> rels; arity P = length xs\<rbrakk> \<Longrightarrow> Pred P xs \<in> preds"

primrec eval_pred :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "eval_pred D mem (Pred P xs) \<longleftrightarrow> map (eval_wf_trm D mem) xs \<in> mr D P"

primrec pred_subst :: "nat \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a pred \<Rightarrow> 'a pred" where
  "pred_subst v s (Pred P xs) = Pred P (map (wf_trm_subst v s) xs)"

typedef (open) 'a wf_pred = "preds::'a::ranked_alphabet pred set"
  by (metis Ex_list_of_length equals0I preds.intros rels_exist)

definition eval_wf_pred :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a wf_pred \<Rightarrow> bool" where
  "eval_wf_pred D mem P \<equiv> eval_pred D mem (Rep_wf_pred P)"

definition
  wf_pred_subst :: "nat \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a wf_pred \<Rightarrow> 'a wf_pred"
  where
  "wf_pred_subst v s \<equiv> Abs_wf_pred \<circ> pred_subst v s \<circ> Rep_wf_pred"

abbreviation
  wf_pred_subst_notation :: "'a::ranked_alphabet wf_pred \<Rightarrow> nat \<Rightarrow> 'a wf_trm \<Rightarrow> 'a wf_pred"
  ("_[_|_]" [100,100,100] 101) where
  "s[x|t] \<equiv> wf_pred_subst x t s"

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

(*
typedef (open) ('a::ranked_alphabet, 'b) tprog = "tprogs TYPE('b) :: 'a::ranked_alphabet prog set"
  sorry
*)

(*
fun nat_interp_funs :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "nat_interp_funs 0 (x#xs) = x + nat_interp_funs 0 xs"
| "nat_interp_funs 0 [] = 0"
| "nat_interp_funs (Suc 0) (x#xs) = x * nat_interp_funs 1 xs"
| "nat_interp_funs (Suc 0) [] = 1"
| "nat_interp_funs (Suc (Suc 0)) (x#xs) = x - nat_interp_funs 2 xs"
| "nat_interp_funs (Suc (Suc 0)) [] = 0"
| "nat_interp_funs n _ = n - 4"

definition nat_interp_rels :: "nat \<Rightarrow> nat relation" where
  "nat_interp_rels n = (\<Union>n. lists {n})"

fun nat_arity :: "nat \<Rightarrow> nat" where
  "nat_arity 0 = 2"
| "nat_arity (Suc 0) = 2"
| "nat_arity (Suc (Suc 0)) = 2"
| "nat_arity (Suc (Suc (Suc 0))) = 2"
| "nat_arity n = 0"

value Abs_ranked_alphabet

definition nat_alphabet :: "ranked_alphabet" where
  "nat_alphabet = Abs_ranked_alphabet (RA \<nat> nat_arity (\<nat> \<inter> {3}) {3})"
*)

datatype 'a skat_expr = SKLeaf nat "'a wf_trm"
                      | SKPlus "'a skat_expr" "'a skat_expr" (infixl ":\<oplus>:" 70)
                      | SKMult "'a skat_expr" "'a skat_expr" (infixl ":\<odot>:" 80)
                      | SKStar "'a skat_expr"
                      | SKBool "'a wf_pred bexpr"
                      | SKOne
                      | SKZero

fun FV' :: "'a trm \<Rightarrow> nat set" where
  "FV' (Var v) = {v}"
| "FV' (App f xs) = foldr op \<union> (map FV' xs) {}"

definition FV :: "'a::ranked_alphabet wf_trm \<Rightarrow> nat set" where
  "FV \<equiv> FV' \<circ> Rep_wf_trm"

lemma app_FV': "v \<notin> FV' (App f xs) \<Longrightarrow> \<forall>x\<in>set xs. v \<notin> FV' x"
proof (erule contrapos_pp, auto)
  fix x assume "x \<in> set xs" and "v \<in> FV' x"
  thus "v \<in> foldr op \<union> (map FV' xs) {}"
    by (induct xs, simp_all, blast)
qed

lemma no_FV' [simp]: "v \<notin> FV' s \<Longrightarrow> trm_subst v t s = s"
proof (induct s)
  fix f xs
  assume asm: "\<forall>x\<in>set xs. v \<notin> FV' x \<longrightarrow> trm_subst v t x = x"
    and "v \<notin> FV' (App f xs)"
  hence "\<forall>x\<in>set xs. v \<notin> FV' x"
    by (metis app_FV')
  thus "trm_subst v t (App f xs) = App f xs"
    by (metis (lifting) asm map_idI trm_subst.simps(2))
next
  fix v' assume "v \<notin> FV' (Var v')"
  thus "trm_subst v t (Var v') = Var v'" by simp
next
  show "\<forall>x\<in>set []. v \<notin> FV' x \<longrightarrow> trm_subst v t x = x" by simp
next
  fix x xs
  assume "v \<notin> FV' x \<Longrightarrow> trm_subst v t x = x"
    and "\<forall>y\<in>set xs. v \<notin> FV' y \<longrightarrow> trm_subst v t y = y"
  thus "\<forall>y\<in>set (x # xs). v \<notin> FV' y \<longrightarrow> trm_subst v t y = y"
    by auto
qed

lemma no_FV [simp]: "v \<notin> FV s \<Longrightarrow> s[v|t] = s"
  by (induct s, metis FV_def Rep_wf_trm_inverse no_FV' o_apply wf_trm_subst_def)

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

| assign1: "y \<notin> FV s \<Longrightarrow> skat_con (SKLeaf x s :\<odot>: SKLeaf y t) (SKLeaf y (t[x|s]) :\<odot>: SKLeaf x s)"
| assign2: "x \<notin> FV s \<Longrightarrow> skat_con (SKLeaf x s :\<odot>: SKLeaf y t) (SKLeaf x s :\<odot>: SKLeaf y (t[x|s]))"
| assign3: "skat_con (SKLeaf x s :\<odot>: SKLeaf x t) (SKLeaf x (t[x|s]))"
| assign4: "skat_con (SKBool (BLeaf (\<phi>[x|t])) :\<odot>: SKLeaf x t) (SKLeaf x t :\<odot>: SKBool (BLeaf \<phi>))"

lemma skat_con_eq: "x = y \<Longrightarrow> skat_con x y" by (simp add: skat_con.refl)

quotient_type 'a skat = "'a::ranked_alphabet skat_expr" / skat_con
proof (auto simp add: equivp_def)
  fix x y assume "skat_con x y"
  thus "skat_con x = skat_con y"
    apply (subgoal_tac "\<forall>z. skat_con x z = skat_con y z")
    apply auto
    by (metis skat_con.sym skat_con.trans)+
qed

lift_definition skat_assign :: "nat \<Rightarrow> 'a::ranked_alphabet wf_trm \<Rightarrow> 'a skat" (infix ":=" 100) is SKLeaf
  by (rule skat_con.refl)

lift_definition skat_mult :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat" (infixl "\<odot>" 80) is SKMult
  by (rule mult_compat, assumption+)

lift_definition skat_plus :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat \<Rightarrow> 'a skat" (infixl "\<oplus>" 70) is SKPlus
  by (rule add_compat, assumption+)

lift_definition skat_one :: "'a::ranked_alphabet skat" ("\<one>") is SKOne
  by (rule skat_con.refl)

lift_definition skat_zero :: "'a::ranked_alphabet skat" ("\<zero>") is SKZero
  by (rule skat_con.refl)

lift_definition skat_star :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat" is SKStar
  by (rule star_compat, assumption)

lift_definition test :: "'a::ranked_alphabet wf_pred bterm \<Rightarrow> 'a skat" is SKBool
  by (rule skat_con.test_ba, assumption)

lift_definition skat_not :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat" ("!") is SKNot
  by (smt equivp_def equivp_symp fun_relE mult_compat one skat_con.mult_oner skat_con.mult_zerol skat_con.mult_zeror skat_con.refl skat_con.sym skat_con.trans skat_equivp test_ba test_one test_plus test_zero)

lift_definition pred :: "'a::ranked_alphabet wf_pred \<Rightarrow> 'a skat" is "SKBool \<circ> BLeaf" by auto

lemma skat_assign1: "y \<notin> FV s \<Longrightarrow> (x := s \<odot> y := t) = (y := t[x|s] \<odot> x := s)"
  by (transfer, rule assign1, assumption)

lemma skat_assign2: "x \<notin> FV s \<Longrightarrow> (x := s \<odot> y := t) = (x := s \<odot> y := t[x|s])"
  by (transfer, rule assign2, assumption)

lemma skat_assign3: "(x := s \<odot> x:= t) = (x := t[x|s])"
  by (transfer, rule assign3)

lemma skat_assign4: "(pred (\<phi>[x|t]) \<odot> x := t) = (x := t \<odot> pred \<phi>)"
  by (transfer, simp add: o_def, rule assign4)

lemma skat_assign_comm: "\<lbrakk>x \<notin> FV t; y \<notin> FV s\<rbrakk> \<Longrightarrow> (x := s \<odot> y := t) = (y := t \<odot> x := s)"
  by (insert skat_assign1[of y s x t], simp)

definition test_set :: "'a::ranked_alphabet skat set" where
  "test_set \<equiv> test ` UNIV"

definition tests :: "'a::ranked_alphabet skat ord" where
  "tests \<equiv> \<lparr>carrier = test_set, le = (\<lambda>x y. skat_plus x y = y)\<rparr>"

definition free_kat :: "'a::ranked_alphabet skat test_algebra" where
  "free_kat = \<lparr>carrier = UNIV, plus = skat_plus, mult = skat_mult, one = skat_one, zero = skat_zero, star = skat_star, test_algebra.test = tests\<rparr>"

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
  where "x +\<^bsub>free_kat\<^esub> y = skat_plus x y"
  and "0\<^bsub>free_kat\<^esub> = \<zero>"
  and "x \<cdot>\<^bsub>free_kat\<^esub> y = x \<odot> y"
  and "1\<^bsub>free_kat\<^esub> = \<one>"
  and "x \<in> carrier free_kat = True"
  by (simp add: free_kat_dioid, simp_all add: free_kat_def)

lemma free_kat_ka: "kleene_algebra free_kat"
  apply unfold_locales
  apply (simp_all add: dioid.nat_order_def[OF free_kat_dioid])
proof (simp_all add: free_kat_def)
  fix x y z
  show "\<one> \<oplus> x \<odot> skat_star x \<oplus> skat_star x = skat_star x"
    by (transfer, rule skat_con.star_unfoldl)
  show "\<one> \<oplus> skat_star x \<odot> x \<oplus> skat_star x = skat_star x"
    by (transfer, rule skat_con.star_unfoldr)
  show "z \<oplus> x \<odot> y \<oplus> y = y \<longrightarrow> skat_star x \<odot> z \<oplus> y = y"
    by (transfer, metis skat_con.star_inductl)
  show "z \<oplus> y \<odot> x \<oplus> y = y \<longrightarrow> z \<odot> skat_star x \<oplus> y = y"
    by (transfer, metis skat_con.star_inductr)
qed

interpretation ska: kleene_algebra free_kat
  where "x +\<^bsub>free_kat\<^esub> y = skat_plus x y"
  and "x \<in> carrier free_kat = True"
  and "x \<cdot>\<^bsub>free_kat\<^esub> y = skat_mult x y"
  and "x\<^sup>\<star>\<^bsub>free_kat\<^esub> = skat_star x"
  by (simp add: free_kat_ka, simp_all add: free_kat_def)

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

(* Transfer concepts from skat to the embedded algebra *)

lemma one_to_test: "\<one> = test (bt_one)"
  by (transfer, rule test_one)

lemma test_one_closed: "\<one> \<in> carrier tests"
  by (metis one_to_test test_closed_var)

lemma zero_to_test: "\<zero> = test (bt_zero)"
  by (transfer, rule test_zero)

lemma test_zero_closed: "\<zero> \<in> carrier tests"
  by (metis test_closed_var zero_to_test)

lemma mult_to_test: "test x \<odot> test y = test (bt_and x y)"
  by (transfer, metis skat_con.sym test_plus)

lemma test_mult_closed:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "x \<odot> y \<in> carrier tests"
proof -
  from xc yc obtain x' and y' where "x = test x'" and "y = test y'"
    by (simp add: tests_def, metis test_ex)
  moreover have "test x' \<odot> test y' \<in> carrier tests"
    by (simp add: mult_to_test, rule test_closed_var)
  ultimately show "x \<odot> y \<in> carrier tests"
    by auto
qed

lemma plus_to_test: "test x \<oplus> test y = test (bt_or x y)"
  by (transfer, metis skat_con.sym test_mult)

lemma test_plus_closed:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "x \<oplus> y \<in> carrier tests"
proof -
  from xc yc obtain x' and y' where "x = test x'" and "y = test y'"
    by (simp add: tests_def, metis test_ex)
  moreover have "test x' \<oplus> test y' \<in> carrier tests"
    by (simp add: plus_to_test, rule test_closed_var)
  ultimately show "x \<oplus> y \<in> carrier tests"
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

lemma ba_ord: "order free_ba" sorry

lemmas or_to_plus = plus_to_test[symmetric]

lemma tests_lub:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "order.is_lub tests (x \<oplus> y) {x, y}"
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

lemma "test x \<oplus> test y = test y \<Longrightarrow> test y \<odot> test x = test x"
  apply (simp add: plus_to_test mult_to_test)
  by (metis UNIV_I ba.absorb2 ba.meet_comm mult_to_test)

lemma test_meet_leq1:
  assumes xc: "x \<in> carrier tests"
  and yc: "y \<in> carrier tests"
  shows "x \<oplus> y = y \<longleftrightarrow> y \<odot> x = x"
proof -
  have "\<forall>x y. test x \<oplus> test y = test y \<longrightarrow> test y \<odot> test x = test x"
    apply (simp add: plus_to_test mult_to_test)
    by (metis UNIV_I ba.absorb2 ba.meet_comm mult_to_test)

  moreover have "\<forall>x y. test y \<odot> test x = test x \<longrightarrow> test x \<oplus> test y = test y"
    apply (simp add: plus_to_test mult_to_test)
    by (metis UNIV_I ba.absorb1 ba.join_comm or_to_plus)

  ultimately show ?thesis using xc yc
    by (simp add: tests_def test_set_def, auto)
qed

lemma test_meet_leq:
  "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> (x \<sqsubseteq>\<^bsub>tests\<^esub> y) = (y \<odot> x = x)"
  by (simp add: tests_def test_meet_leq1)

lemma tests_glb:
  assumes xc: "x \<in> carrier tests" and yc: "y \<in> carrier tests"
  shows "order.is_glb tests (x \<odot> y) {x, y}"
  apply (simp add: order.is_glb_simp[OF tests_ord])
  apply (insert xc yc, subgoal_tac "x \<odot> y \<in> carrier tests")
  apply (simp add: test_meet_leq)
  apply (simp add: tests_def)
  defer
  apply (metis test_mult_closed)
proof safe
  from xc and yc obtain x' and y' where x'_def: "x = test x'" and y'_def: "y = test y'"
    by (simp add: tests_def, metis test_ex)

  show "x \<odot> (x \<odot> y) = x \<odot> y"
    apply (simp add: x'_def y'_def mult_to_test, rule test_eq)
    by (metis UNIV_I ba.meet_assoc ba.meet_idem)

  show "y \<odot> (x \<odot> y) = x \<odot> y"
    apply (simp add: x'_def y'_def mult_to_test, rule test_eq)
    by (metis UNIV_I ba.meet_assoc ba.meet_comm ba.meet_idem)

  fix w :: "'a skat"
  assume "w \<in> test_set" and xw: "x \<odot> w = w" and yw: "y \<odot> w = w"
  then obtain w' where w'_def: "w = test w'" by (metis test_ex)
  from xw have "(test x') \<odot> w = w"
    by (metis x'_def)
  from w'_def and this have "(test x') \<odot> (test w') = (test w')"
    by simp
  from this[symmetric] show "(x \<odot> y) \<odot> w = w"
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

lemma tests_join [simp]: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> x \<squnion>\<^bsub>tests\<^esub> y = x \<oplus> y"
  by (metis tests_ord order.join_def order.lub_is_lub tests_lub)

lemma tests_ms: "meet_semilattice tests"
proof (simp add: meet_semilattice_def meet_semilattice_axioms_def, safe)
  show "order tests" using tests_ord .

  fix x y :: "'a skat" assume "x \<in> carrier tests" and "y \<in> carrier tests"
  thus "\<exists>z\<in>carrier tests. order.is_glb tests z {x, y}"
    apply (intro bexI) by (rule tests_glb, assumption+, metis test_mult_closed)
qed

lemma tests_meet [simp]: "\<lbrakk>x \<in> carrier tests; y \<in> carrier tests\<rbrakk> \<Longrightarrow> x \<sqinter>\<^bsub>tests\<^esub> y = x \<odot> y"
  by (metis tests_ord order.meet_def order.glb_is_glb tests_glb)

lemma tests_lattice: "lattice tests"
  unfolding lattice_def by (metis tests_js tests_ms)

lemma tests_bounded: "bounded_lattice tests"
  apply (simp add: bounded_lattice_def bounded_lattice_axioms_def, safe)
  apply (metis tests_lattice)
  apply (rule_tac x = \<zero> in bexI)
  apply (metis skd.add_zerol)
  apply (metis test_zero_closed)
  apply (rule_tac x = \<one> in bexI)
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
  thus "(x \<sqinter>\<^bsub>tests\<^esub> (y \<oplus> z)) = (x \<odot> y \<squnion>\<^bsub>tests\<^esub> x \<odot> z)"
    by (metis skd.distl test_mult_closed test_plus_closed tests_join tests_meet)
  from xc yc zc show "x \<squnion>\<^bsub>tests\<^esub> (y \<odot> z) = (x \<oplus> y) \<sqinter>\<^bsub>tests\<^esub> (x \<oplus> z)"
    apply (subgoal_tac "y \<odot> z \<in> carrier tests" "x \<oplus> y \<in> carrier tests" "x \<oplus> z \<in> carrier tests")
    defer
    apply (metis test_plus_closed test_mult_closed)+
    apply simp
  proof -
    from xc yc zc obtain x' y' z' where "x = test x'" and "y = test y'" and "z = test z'"
      by (simp add: tests_def, metis test_ex)
    thus "x \<oplus> y \<odot> z = (x \<oplus> y) \<odot> (x \<oplus> z)"
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
    thus "x \<oplus> !x = \<one>"
      apply (simp add: not_to_not plus_to_test one_to_test)
      apply (rule test_eq)
      by (transfer, rule hunt_con.one)
    from `x = test x'` show "x \<odot> !x = \<zero>"
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

value "pred"

typedef kzp = "{0::nat,1,2,3,4}" by auto

definition f_kzp :: "kzp" where "f_kzp \<equiv> Abs_kzp (1::nat)"
definition g_kzp :: "kzp" where "g_kzp \<equiv> Abs_kzp (2::nat)"
definition P_kzp :: "kzp" where "P_kzp \<equiv> Abs_kzp (0::nat)"
definition bot_kzp :: "kzp" where "bot_kzp \<equiv> Abs_kzp (3::nat)"
definition x_kzp :: "kzp" where "x_kzp \<equiv> Abs_kzp (4::nat)"

lemma kzp_UNIV: "UNIV = {P_kzp,f_kzp,g_kzp,bot_kzp,x_kzp}"
proof -
  have "type_definition Rep_kzp Abs_kzp kzp"
    by (metis type_definition_kzp)
  hence "Abs_kzp ` kzp = UNIV"
    by (metis type_definition.Abs_image)
  thus "UNIV = {P_kzp,f_kzp,g_kzp,bot_kzp,x_kzp}"
    by (smt P_kzp_def bot_kzp_def x_kzp_def f_kzp_def g_kzp_def image_empty image_insert kzp_def)
qed

instantiation kzp :: ranked_alphabet
begin

  fun arity_kzp' :: "nat \<Rightarrow> nat" where
    "arity_kzp' 0 = 1"
  | "arity_kzp' (Suc 0) = 1"
  | "arity_kzp' (Suc (Suc 0)) = 2"
  | "arity_kzp' _ = 0"

  definition arity_kzp :: "kzp \<Rightarrow> nat" where
    "arity_kzp k \<equiv> arity_kzp' (Rep_kzp k)"

  definition funs_kzp where "funs \<equiv> {f_kzp, g_kzp, bot_kzp, x_kzp}"

  definition rels_kzp where "rels \<equiv> {P_kzp}"

  instance proof
    show "finite (UNIV :: kzp set)" by (simp add: kzp_UNIV)

    show "(funs :: kzp set) \<inter> rels = {}"
      apply (simp add: funs_kzp_def rels_kzp_def P_kzp_def f_kzp_def g_kzp_def bot_kzp_def x_kzp_def)
      by (smt Abs_kzp_inverse insertI1 insertI2 kzp_def)

    show "(funs :: kzp set) \<union> rels = UNIV"
      by (simp add: funs_kzp_def rels_kzp_def kzp_UNIV)

    show "(funs :: kzp set) \<noteq> {}"
      by (simp add: funs_kzp_def)

    show "(rels :: kzp set) \<noteq> {}"
      by (simp add: rels_kzp_def)
  qed
end

definition f :: "kzp wf_trm \<Rightarrow> kzp wf_trm" where
  "f x \<equiv> Abs_wf_trm (App f_kzp [Rep_wf_trm x])"

definition g :: "kzp wf_trm \<Rightarrow> kzp wf_trm \<Rightarrow> kzp wf_trm" where
  "g x y \<equiv> Abs_wf_trm (App g_kzp [Rep_wf_trm x, Rep_wf_trm y])"

definition P :: "kzp wf_trm \<Rightarrow> kzp skat" where
  "P x \<equiv> pred (Abs_wf_pred (Pred P_kzp [x]))"

definition x :: "kzp wf_trm " where
  "x \<equiv> Abs_wf_trm (App x_kzp [])"

definition bot :: "kzp wf_trm" where
  "bot \<equiv> Abs_wf_trm (App bot_kzp [])"

definition var :: "nat \<Rightarrow> 'a::ranked_alphabet wf_trm" where
  "var i \<equiv> Abs_wf_trm (Var i)"

no_notation
  dioid.one ("1\<index>") and
  one_class.one ("1")

definition seq :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "seq xs = foldr op \<odot> xs \<one>"

lemma seq_mult: "seq (xs @ ys) = seq xs \<odot> seq ys"
  apply (induct xs)
  apply (simp add: seq_def)
  apply (metis skd.mult_onel)
  apply (simp add: seq_def)
  by (metis skd.mult_assoc)

lemma list_td_split: "take n xs @ drop n xs = xs"
  by (induct xs, simp_all)

lemma seq_split:
  assumes seq_take: "seq (take n xs) = seq (take n ys)"
  and seq_drop: "seq (drop n xs) = seq (drop n ys)"
  shows "seq xs = seq ys"
proof -
  have "seq (take n xs @ drop n xs) = seq (take n ys @ drop n ys)"
    by (simp only: seq_mult, metis seq_drop seq_take)
  thus ?thesis
    by simp
qed

lemma seq_append:
  "seq (take n xs) \<odot> seq (drop n xs) = seq (take m ys) \<odot> seq (drop m ys) \<Longrightarrow> seq xs = seq ys"
  by (simp add: seq_mult[symmetric])

definition kz19 :: "kzp skat list" where "kz19 \<equiv>
  [ 1 := x
  , 4 := f (var 1)
  , 1 := f (var 1)
  , 2 := g (var 1) (var 4)
  , 3 := g (var 1) (var 1)
  , skat_star (seq
    [ !(P (var 1))
    , 1 := f (var 1)
    , 2 := g (var 1) (var 4)
    , 3 := g (var 1) (var 1)
    ])
  , P (var 1)
  , 1 := f (var 3)
  , skat_star (seq
    [ seq
      [ !(P (var 4)) \<oplus> (P (var 4) \<odot> skat_star (!(P (var 2)) \<odot> 2 := f (var 2)))
      , P (var 2)
      , ! (P (var 3))
      , 4 := f (var 1)
      , 1 := f (var 1)
      ]
    , 2 := g (var 1) (var 4)
    , 3 := g (var 1) (var 1)
    , skat_star (seq
      [ !(P (var 1))
      , 1 := f (var 1)
      , 2 := g (var 1) (var 4)
      , 3 := g (var 1) (var 1)
      ])
    , P (var 1)
    , 1 := f (var 3)
    ])
  , P (var 4)
  , skat_star (!(P (var 2)) \<odot> 2 := f (var 2))
  , P (var 2)
  , P (var 3)
  , 0 := var 2
  ]"

definition kz21 where "kz21 \<equiv>
  [ 1 := x
  , 4 := f (var 1)
  , 1 := f (var 1)
  , 2 := g (var 1) (var 4)
  , 3 := g (var 1) (var 1)
  , skat_star (seq
    [ !(P (var 1))
    , 1 := f (var 1)
    , 2 := g (var 1) (var 4)
    , 3 := g (var 1) (var 1)
    ])
  , skat_star (seq
    [ P (var 1)
    , 1 := f (var 3)
    , seq
      [ !(P (var 4)) \<oplus> (P (var 4) \<odot> skat_star (!(P (var 2)) \<odot> 2 := f (var 2)))
      , P (var 2)
      , ! (P (var 3))
      , 4 := f (var 1)
      , 1 := f (var 1)
      ]
    , 2 := g (var 1) (var 4)
    , 3 := g (var 1) (var 1)
    , skat_star (seq
      [ !(P (var 1))
      , 1 := f (var 1)
      , 2 := g (var 1) (var 4)
      , 3 := g (var 1) (var 1)
      ])
    ])
  , P (var 1)
  , 1 := f (var 3)
  , P (var 4)
  , skat_star (!(P (var 2)) \<odot> 2 := f (var 2))
  , P (var 2)
  , P (var 3)
  , 0 := var 2
  ]"

definition kz22 :: "kzp skat list" where "kz22 \<equiv>
  [ 1 := x
  , 4 := f (var 1)
  , 1 := f (var 1)
  , 2 := g (var 1) (var 4)
  , 3 := g (var 1) (var 1)
  , skat_star (seq
    [ !(P (var 1))
    , 1 := f (var 1)
    , 2 := g (var 1) (var 4)
    , 3 := g (var 1) (var 1)
    ] \<oplus> seq
    [ P (var 1)
    , 1 := f (var 3)
    , !(P (var 4)) \<oplus> seq
      [ P (var 4)
      , skat_star (!(P (var 2)) \<odot> 2 := f (var 2))
      , P (var 2)
      , !(P (var 3))
      , 4 := f (var 1)
      , 1 := f (var 1)
      ]
    , 2 := g (var 1) (var 3)
    , 3 := g (var 1) (var 1)
    ])
  , P (var 1)
  , 1 := f (var 3)
  , P (var 4)
  , skat_star (!(P (var 2)) \<odot> 2 := f (var 2))
  , P (var 2)
  , P (var 3)
  , 0 := var 2
  ]"

definition kz47 where "kz47 \<equiv>
  [ 2 := f x
  , P (var 2)
  , 2 := g (var 2) (var 2)
  , skat_star (seq
    [ !(P (var 2))
    , 2 := f (f 2)
    , P (var 2)
    , 2 := g (var 2) (var 2)
    ])
  , P (var 2)
  , 0 := var 2
  ]"

lemma seq_singleton: "seq [q] = q"
  apply (simp add: seq_def)
  by (metis skd.mult_oner)

lemma slide_19_21:
  assumes xs_def: "xs = drop n ys"
  shows "seq xs \<odot> skat_star (seq ys) = skat_star (seq (xs @ take n ys)) \<odot> seq xs"
proof -
  have "seq xs \<odot> skat_star (seq (take n ys) \<odot> seq xs) = skat_star (seq xs \<odot> seq (take n ys)) \<odot> seq xs"
    by (simp add: ska.star_slide[simplified,symmetric])
  thus ?thesis
    by (metis append_take_drop_id assms seq_mult)
qed

lemma "seq kz19 = seq kz21"
  apply (simp add: kz19_def kz21_def)
  apply (rule seq_split[of 6], simp_all)
  apply (rule seq_split[of 3], simp_all)
  apply (rule seq_append[of 2 _ 1], simp)
  apply (simp only: seq_singleton)
  apply (rule HOL.trans)
  by (rule slide_19_21[of _ 4], simp_all)

lemma "seq kz21 = seq kz22"
  apply (simp add: kz21_def kz22_def)
  apply (rule seq_split[of 5], simp_all)

definition Aloop2p1 where "Aloop2p1 \<equiv>
  [ skat_not (P (var 4)) \<oplus> (P (var 4) \<odot> skat_star (skat_not (P (var 2)) \<odot> 2 := f (var 2)))
  , P (var 2)
  , !(P (var 3))
  , 4 := f (var 1)
  , 1 := f (var 1)
  ]"


end

  , skat_star (seq
    [])
  , P (var 4)
  , skat_star (!(P (var 2)) \<odot> (2 := f (var 2)))
  , P (var 2)
  , P (var 3)
  , 0 := var 2
  ]"
} *}

definition a :: "nat \<Rightarrow> kzp skat" where
  "a i \<equiv> pred (Abs_wf_pred (Pred P [var i]))"

definition b :: "nat \<Rightarrow> kzp skat" where
  "b i \<equiv> pred (Abs_wf_pred (Pred P [Abs_wf_trm (App f [Var i])]))"

definition c :: "nat \<Rightarrow> kzp skat" where
  "c i \<equiv> pred (Abs_wf_pred (Pred P [Abs_wf_trm (App f [App f [Var i]])]))"

definition p :: "nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "p i j \<equiv> i := Abs_wf_trm (App f [Var j])"

definition q :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "q i j k \<equiv> i := Abs_wf_trm (App g [Var j, Var k])"

definition r :: "nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "r i j \<equiv> i := Abs_wf_trm (App f [App f [Var j]])"

definition x :: "nat \<Rightarrow> kzp skat" where
  "x i \<equiv> i := Abs_wf_trm (App x_kzp [])"

definition s :: "nat \<Rightarrow> kzp skat" where
  "s i \<equiv> i := Abs_wf_trm (App f [App x_kzp []])"

definition t :: "nat \<Rightarrow> kzp skat" where
  "t i \<equiv> i := Abs_wf_trm (App g [App f [App x_kzp []], App f [App x_kzp []]])"

definition u :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kzp skat" where
  "u i j k \<equiv> i := Abs_wf_trm (App g [App f [App f [Var j]], App f [App f [Var k]]])"

definition z :: "nat \<Rightarrow> kzp skat" where
  "z i \<equiv> 0 := var i"

definition y :: "nat \<Rightarrow> kzp skat" where
  "y i \<equiv> i := Abs_wf_trm (App bot [])"

definition seq :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "seq xs \<equiv> foldr op \<odot> xs \<one>"

lemma seq_split: "seq (xs @ ys) = seq xs \<odot> seq ys"
  apply (induct xs)
  apply (simp add: seq_def)
  apply (metis skd.mult_onel)
  apply (simp add: seq_def)
  by (metis skd.mult_assoc)



abbreviation S6Ap1 :: "kzp skat" where
  "S6Ap1 \<equiv> seq [x 1, p 4 1, q 2 1 4, q 3 1 1, skat_star (seq [!(a 1), p 1 1, q 2 1 4, q 3 1 1]), a 1, p 1 3]"

abbreviation S6Ap21 :: "kzp skat" where
  "S6Ap21 \<equiv> !(a 4) \<oplus> a 4 \<odot> skat_star (!(a 2) \<odot> p 2 2) \<odot> a 2 \<odot> !(a 3) \<odot> p 4 1 \<odot> p 1 1"

abbreviation S6Ap22 :: "kzp skat" where
  "S6Ap22 \<equiv> !(a 1) \<odot> p 1 1 \<odot> q 2 1 4 \<odot> q 3 1 1"

abbreviation S6Ap2 :: "kzp skat" where
  "S6Ap2 \<equiv> skat_star (S6Ap21 \<odot> q 2 1 4 \<odot> q 3 1 1 \<odot> skat_star S6Ap22 \<odot> a 1 \<odot> p 1 3)"

abbreviation S6Ap3 :: "kzp skat" where
  "S6Ap3 \<equiv> a 4 \<odot> (!(a 2) \<odot> p 2 2) \<odot> a 2 \<odot> a 3 \<odot> z 2"

abbreviation S6A :: "kzp skat" where
  "S6A \<equiv> S6Ap1 \<odot> S6Ap2 \<odot> S6Ap3"

lemma "S6Ap1 = x 1 \<odot> p 4 1 \<odot> p 1 1 \<odot> q 3 1 1 \<odot> (!(a 1) \<odot> p 1 1 \<odot> q 2 1 4 "

done

skat_star ((!(a 4) \<oplus> a 4 \<odot> skat_star (!(a 2) \<odot> p 2 2) \<odot> a 2 \<odot> !(a 3) \<odot> p 4 1 \<odot> p 1 1) \<odot> q 2 1 4 \<odot> q 3 1 1 \<odot> skat_star (!(a 1) \<odot> p 1 1 \<odot> q 2 1 4 \<odot> q 3 1 1) \<odot> a 1 \<odot> p 1 3)"

done
          \<odot> a 4 \<odot> (!(a 2) \<odot> p 2 2) \<odot> a 2 \<odot> a 3 \<odot> z 2"

end
