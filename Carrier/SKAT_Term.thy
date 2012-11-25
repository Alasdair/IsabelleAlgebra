theory SKAT_Term
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

lemma no_pred_vars: "X \<inter> pred_vars \<phi> = {} \<Longrightarrow> pred_subst X t \<phi> = \<phi>"
proof (induct \<phi>, simp)
  fix xs :: "'a wf_trm list" assume "X \<inter> UNION (set xs) FV = {}"
  thus "map (wf_trm_subst X t) xs = xs"
    apply (induct xs, simp_all)
    by (metis Int_Un_distrib Un_commute Un_empty_left Un_left_absorb no_FV)
qed

definition wf_pred_vars :: "'a::ranked_alphabet wf_pred \<Rightarrow> nat set" where
  "wf_pred_vars P = pred_vars (Rep_wf_pred P)"

lemma no_wf_pred_vars [simp]: "X \<inter> wf_pred_vars \<phi> = {} \<Longrightarrow> wf_pred_subst X t \<phi> = \<phi>"
  apply (induct \<phi>)
  by (metis Abs_wf_pred_inverse Diff_Compl no_pred_vars o_eq_dest_lhs wf_pred_subst_def wf_pred_vars_def)

ML {*

structure AlphabetRules = Named_Thms
  (val name = @{binding "alphabet"}
   val description = "Alphabet rules")

fun wf_trm_abs_inverse_tac simpset ctxt =
  EqSubst.eqsubst_tac ctxt [0] @{thms Abs_wf_trm_inverse} 1
  THEN REPEAT
    (CHANGED (asm_full_simp_tac
      (simpset addsimps @{thms FV_def} addsimps AlphabetRules.get ctxt) 1)
    ORELSE resolve_tac @{thms trms.intros} 1)

fun wf_pred_abs_inverse_tac simpset ctxt =
  EqSubst.eqsubst_tac ctxt [0] @{thms Abs_wf_pred_inverse} 1
  THEN REPEAT
    (CHANGED (asm_full_simp_tac
      (simpset addsimps @{thms wf_pred_vars_def} addsimps AlphabetRules.get ctxt) 1)
    ORELSE resolve_tac @{thms preds.intros} 1
    ORELSE rtac @{thm conjI} 1)

fun wf_simp_tac simpset =
  Subgoal.FOCUS (fn {context, ...} =>
    REPEAT (wf_trm_abs_inverse_tac simpset context)
    THEN REPEAT (wf_pred_abs_inverse_tac simpset context))

*}

setup {* AlphabetRules.setup *}

method_setup wf_simp = {*
Scan.succeed (fn ctxt => SIMPLE_METHOD' (wf_simp_tac (simpset_of ctxt) ctxt))
*}

lemma trm_simple_induct': "\<lbrakk>\<And>f xs. (\<forall>x\<in>set xs. P x) \<Longrightarrow> P (App f xs); \<And>n. P (Var n)\<rbrakk> \<Longrightarrow> P s \<and> (\<forall>x\<in>set []. P x)"
  by (rule trm.induct[of "\<lambda>xs. (\<forall>x\<in>set xs. P x)" P], simp_all)

lemma trm_simple_induct: "\<lbrakk>\<And>n. P (Var n); \<And>f xs. (\<forall>x\<in>set xs. P x) \<Longrightarrow> P (App f xs)\<rbrakk> \<Longrightarrow> P s"
  by (metis trm_simple_induct')

lemma foldr_FV': "foldr op \<union> (map FV' xs) {} = \<Union> (FV' ` set xs)"
  by (induct xs, auto)

lemma eval_trm_eq_mem: "(\<forall>v\<in>FV' s. m1 v = m2 v) \<Longrightarrow> eval_trm D m1 s = eval_trm D m2 s"
proof (induct rule: trm_simple_induct, auto)
  fix f :: "'a" and xs :: "'a trm list"
  assume asm1: "\<forall>x\<in>set xs. (\<forall>v\<in>FV' x. m1 v = m2 v) \<longrightarrow> eval_trm D m1 x = eval_trm D m2 x"
  and asm2: "\<forall>v\<in>foldr op \<union> (map FV' xs) {}. m1 v = m2 v"
  have "foldr op \<union> (map FV' xs) {} = \<Union> (FV' ` set xs)"
    by (induct xs, auto)
  hence "\<forall>v\<in>\<Union>(FV' ` set xs). m1 v = m2 v"
    by (metis asm2)
  hence "\<forall>x\<in>set xs. (\<forall>v\<in>FV' x. m1 v = m2 v)"
    by (metis UnionI imageI)
  hence "\<forall>x\<in>set xs. eval_trm D m1 x = eval_trm D m2 x"
    by (metis asm1)
  hence "map (eval_trm D m1) xs = map (eval_trm D m2) xs"
    by (induct xs, auto)
  thus "mf D f (map (eval_trm D m1) xs) = mf D f (map (eval_trm D m2) xs)"
    by metis
qed

definition setMem :: "nat \<Rightarrow> 'a \<Rightarrow> 'a mem \<Rightarrow> 'a mem" where
  "setMem x s mem \<equiv> \<lambda>v. if v = x then s else mem v"

definition assign ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> nat \<Rightarrow> 'a trm \<Rightarrow> 'b mem \<Rightarrow> 'b mem"
  where
  "assign D x s mem = setMem x (eval_trm D mem s) mem"

lemma eval_assign1:
  assumes ys: "y \<notin> FV' s" and xy: "x \<noteq> y"
  shows "assign D y t (assign D x s mem) = assign D x s (assign D y (trm_subst {x} s t) mem)"
  apply (induct t rule: trm_simple_induct)
  apply (simp add: assign_def setMem_def)
  apply default
  apply default
  apply default
  apply (smt eval_trm_eq_mem ys)
  apply auto
  apply default
  apply (smt eval_trm.simps(1) eval_trm_eq_mem xy ys)
proof
  fix f ts v
  assume "\<forall>t\<in>set ts. assign D y t (assign D x s mem) =
                      assign D x s (assign D y (trm_subst {x} s t) mem)"
  hence "\<forall>t\<in>set ts. assign D y t (assign D x s mem) v =
                     assign D x s (assign D y (trm_subst {x} s t) mem) v"
    by auto
  thus "assign D y (App f ts) (assign D x s mem) v =
        assign D x s (assign D y (App f (map (trm_subst {x} s) ts)) mem) v"
    apply (simp add: assign_def setMem_def o_def)
    by (smt eval_trm_eq_mem map_eq_conv xy ys)
qed

lemma eval_assign2:
  assumes ys: "x \<notin> FV' s" and xy: "x \<noteq> y"
  shows "assign D y t (assign D x s mem) =
         assign D y (trm_subst {x} s t) (assign D x s mem)"
  apply (induct t rule: trm_simple_induct)
  apply (simp add: assign_def setMem_def)
  apply default
  apply default
  apply default
  apply (smt eval_trm_eq_mem ys)
  apply auto
proof
  fix f ts v
  assume "\<forall>t\<in>set ts. assign D y t (assign D x s mem) =
                      assign D y (trm_subst {x} s t) (assign D x s mem)"
  hence "\<forall>t\<in>set ts. assign D y t (assign D x s mem) v =
                     assign D y (trm_subst {x} s t) (assign D x s mem) v"
    by auto
  thus "assign D y (App f ts) (assign D x s mem) v =
        assign D y (App f (map (trm_subst {x} s) ts)) (assign D x s mem) v"
    apply (simp add: assign_def setMem_def o_def)
    by (smt eval_trm_eq_mem map_eq_conv xy ys)
qed

lemma eval_assign3: "assign D x t (assign D x s mem) = assign D x (trm_subst {x} s t) mem"
proof (induct t rule: trm_simple_induct, simp add: assign_def setMem_def, auto, default)
  fix f ts v
  assume "\<forall>t\<in>set ts. assign D x t (assign D x s mem) = assign D x (trm_subst {x} s t) mem"
  hence "\<forall>t\<in>set ts. assign D x t (assign D x s mem) v = assign D x (trm_subst {x} s t) mem v"
    by auto
  hence "v = x \<longrightarrow> map (eval_trm D (\<lambda>v. if v = x then eval_trm D mem s else mem v)) ts =
                  map (eval_trm D mem \<circ> trm_subst {x} s) ts"
    by (auto simp add: assign_def setMem_def)
  thus "assign D x (App f ts) (assign D x s mem) v = assign D x (App f (map (trm_subst {x} s) ts)) mem v"
    by (auto simp add: assign_def setMem_def o_def, smt map_eq_conv)
qed

end
