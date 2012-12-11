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
  assumes funs_rels_disjoint: "funs \<inter> rels = {}"
  and funs_rels_union: "funs \<union> rels = UNIV"
  and funs_exist: "funs \<noteq> {}"
  and rels_exist: "rels \<noteq> {}"
  and NULL_fun: "NULL \<in> funs"
  and NULL_arity: "arity NULL = 0"
  and output_exists: "\<exists>x. x \<in> output_vars TYPE('a)"
  and output_finite: "finite (output_vars TYPE('a))"

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

fun trm_subst :: "nat \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" where
  "trm_subst v s (Var v') = (if v' = v then s else Var v')"
| "trm_subst v s (App f xs) = App f (map (trm_subst v s) xs)"

inductive_set wf_trms :: "'a::ranked_alphabet trm set" where
  var: "Var n \<in> wf_trms"
| func: "\<lbrakk>f \<in> funs; arity f = n; xs \<in> lists wf_trms; length xs = n\<rbrakk> \<Longrightarrow> App f xs \<in> wf_trms"

lemma trm_subterms: "App f xs \<in> wf_trms \<Longrightarrow> xs \<in> lists wf_trms"
  by (metis (lifting) trm.simps(1) trm.simps(4) wf_trms.simps)

lemma trm_subterms_var: "App f xs \<in> wf_trms \<Longrightarrow> set xs \<subseteq> wf_trms"
  by (metis in_lists_conv_set subset_code(1) trm_subterms)

lemma map_in_lists: "map f xs \<in> lists X \<longleftrightarrow> f ` set xs \<subseteq> X"
  by (metis in_lists_conv_set in_mono set_map subsetI)

lemma trm_subst_wf: "\<lbrakk>s \<in> wf_trms; x \<in> wf_trms\<rbrakk> \<Longrightarrow> trm_subst v s x \<in> wf_trms"
proof (rule wf_trms.induct[of x "\<lambda>x. trm_subst v s x \<in> wf_trms"], safe)
  fix n assume "s \<in> wf_trms" and "x \<in> wf_trms" thus "trm_subst v s (Var n) \<in> wf_trms"
    by (metis trm_subst.simps(1) wf_trms.var)
next
  fix f :: "'a::ranked_alphabet" and xs :: "'a trm list"
  assume s_trm: "s \<in> wf_trms" and x_trm: "x \<in> wf_trms" and f_fun: "f \<in> funs"
  and xs_len: "length xs = arity f"
  and ind_hyp: "\<forall>x\<in>set xs. x \<in> wf_trms \<inter> {x. trm_subst v s x \<in> wf_trms}"
  show "trm_subst v s (App f xs) \<in> wf_trms"
  proof (simp, rule wf_trms.func[of _ "length xs"])
    show "f \<in> funs" using f_fun .
    show "arity f = length xs" by (simp add: xs_len)
    show "map (trm_subst v s) xs \<in> lists wf_trms"
      by (simp add: map_in_lists image_def, auto, metis Int_Collect ind_hyp)
    show "length (map (trm_subst v s) xs) = length xs"
      by (metis length_map)
  qed
qed

lemma wf_trms_const: "\<lbrakk>f \<in> funs; arity f = 0\<rbrakk> \<Longrightarrow> App f [] \<in> wf_trms"
  by (rule wf_trms.func, simp_all add: lists_def)

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

type_synonym 'a mem = "nat \<Rightarrow> 'a"

fun eval_trm :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'a trm \<Rightarrow> 'b" where
  "eval_trm D mem (Var n) = mem n"
| "eval_trm D mem (App f xs) = mf D f (map (eval_trm D mem) xs)"

definition null :: "'a::ranked_alphabet trm" where
  "null \<equiv> App NULL []"

abbreviation trm_subst_notation :: "'a::ranked_alphabet trm \<Rightarrow> nat \<Rightarrow> 'a trm \<Rightarrow> 'a trm"
  ("_[_|_]" [100,100,100] 101) where
  "s[x|t] \<equiv> trm_subst x t s"

(* +------------------------------------------------------------------------+ *)
subsection {* Predicates *}
(* +------------------------------------------------------------------------+ *)

datatype 'a pred = Pred 'a "'a trm list"

inductive_set wf_preds :: "'a::ranked_alphabet pred set" where
  "\<lbrakk>P \<in> rels; arity P = length xs\<rbrakk> \<Longrightarrow> Pred P xs \<in> wf_preds"

primrec eval_pred :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "eval_pred D mem (Pred P xs) \<longleftrightarrow> map (eval_trm D mem) xs \<in> mr D P"

primrec pred_subst :: "nat \<Rightarrow> 'a::ranked_alphabet trm \<Rightarrow> 'a pred \<Rightarrow> 'a pred" where
  "pred_subst v s (Pred P xs) = Pred P (map (trm_subst v s) xs)"

abbreviation
  pred_subst_notation :: "'a::ranked_alphabet pred \<Rightarrow> nat \<Rightarrow> 'a trm \<Rightarrow> 'a pred"
  ("_[_|_]" [100,100,100] 101) where
  "s[x|t] \<equiv> pred_subst x t s"

(* Simple while programs *)

datatype 'a prog = If "'a pred" "'a prog" "'a prog"
                 | While "'a pred" "'a prog"
                 | Seq "'a prog" "'a prog"
                 | Assign nat "'a trm"
                 | Skip

fun prog_preds :: "'a prog \<Rightarrow> 'a pred set" where
  "prog_preds (If P x y) = {P} \<union> prog_preds x \<union> prog_preds y"
| "prog_preds (While P x) = {P} \<union> prog_preds x"
| "prog_preds (Seq x y) = prog_preds x \<union> prog_preds y"
| "prog_preds (Assign _ _) = {}"
| "prog_preds Skip = {}"

fun prog_whiles :: "'a prog \<Rightarrow> 'a prog set" where
  "prog_whiles (If P x y) = prog_whiles x \<union> prog_whiles y"
| "prog_whiles (While P x) = {While P x} \<union> prog_whiles x"
| "prog_whiles (Seq x y) = prog_whiles x \<union> prog_whiles y"
| "prog_whiles (Assign _ _) = {}"
| "prog_whiles Skip = {}"

fun eval_prog :: "nat \<Rightarrow> ('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a prog \<Rightarrow> 'b mem option" where
  "eval_prog 0 _ _ _ = None"
| "eval_prog (Suc n) D mem (If P x y) =
     (if eval_pred D mem P
     then eval_prog n D mem x
     else eval_prog n D mem y)"
| "eval_prog (Suc n) D mem (While P x) =
     (if eval_pred D mem P
     then case eval_prog n D mem x of
       Some mem' \<Rightarrow> eval_prog n D mem' (While P x)
     | None \<Rightarrow> None
     else Some mem)"
| "eval_prog (Suc n) D mem (Seq x y) =
     (case eval_prog n D mem x of
       Some mem' \<Rightarrow> eval_prog n D mem' y
     | None \<Rightarrow> None)"
| "eval_prog (Suc n) D mem Skip = Some mem"
| "eval_prog (Suc n) D mem (Assign m x) =
     (Some (\<lambda>v. if v = m then eval_trm D mem x else mem v))"

(*
lemma min_terminates: "eval_prog n D mem pgm = Some r \<Longrightarrow> eval_prog (n + m) D mem pgm = Some r"
  sorry

definition terminates :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a prog \<Rightarrow> bool" where
  "terminates D prgm \<equiv> \<exists>steps. \<forall>mem. eval_prog steps D mem prgm \<noteq> None"

lemma Skip_terminates [intro!]: "terminates D Skip"
  by (simp add: terminates_def, rule_tac x = 1 in exI, auto)

lemma Assign_terminates [intro!]: "terminates D (Assign x s)"
  by (simp add: terminates_def, rule_tac x = 1 in exI, auto)

lemma If_terminates [intro]: "\<lbrakk>terminates D x; terminates D y\<rbrakk> \<Longrightarrow> terminates D (If P x y)"
proof (simp add: terminates_def)
  assume "\<exists>steps. \<forall>mem. \<exists>r. eval_prog steps D mem x = Some r"
  and "\<exists>steps. \<forall>mem. \<exists>r. eval_prog steps D mem y = Some r"

  then obtain x_steps and y_steps
    where "\<forall>mem. \<exists>r. eval_prog x_steps D mem x = Some r"
    and "\<forall>mem. \<exists>r. eval_prog y_steps D mem y = Some r"
    by auto

  thus "\<exists>steps. \<forall>mem. \<exists>r. eval_prog steps D mem (If P x y) = Some r"
    apply (rule_tac x = "Suc (max x_steps y_steps)" in exI)
    apply auto
    apply (cases "x_steps > y_steps")
    apply smt
    apply (subgoal_tac "\<exists>n. max x_steps y_steps = x_steps + n")
    apply (metis min_terminates)
    apply (metis add_0_right le_iff_add less_imp_add_positive linorder_cases max_absorb2)
    apply (cases "y_steps > x_steps")
    apply smt
    apply (subgoal_tac "\<exists>n. max x_steps y_steps = y_steps + n")
    apply (metis min_terminates)
    by (metis add_0_right le_iff_add less_imp_add_positive linorder_cases max_absorb2 min_max.sup.commute)
qed

lemma Seq_terminates [intro]: "\<lbrakk>terminates D x; terminates D y\<rbrakk> \<Longrightarrow> terminates D (Seq x y)"
proof (simp add: terminates_def)
  assume "\<exists>steps. \<forall>mem. \<exists>r. eval_prog steps D mem x = Some r"
  and "\<exists>steps. \<forall>mem. \<exists>r. eval_prog steps D mem y = Some r"

  then obtain x_steps and y_steps
    where "\<forall>mem. \<exists>r. eval_prog x_steps D mem x = Some r"
    and "\<forall>mem. \<exists>r. eval_prog y_steps D mem y = Some r"
    by auto

  thus "\<exists>steps. \<forall>mem. \<exists>r. eval_prog steps D mem (Seq x y) = Some r"
    apply (rule_tac x = "Suc (x_steps + y_steps)" in exI, simp)
    by (metis (lifting) min_terminates nat_add_commute option.simps(5))
qed

lemma Seq_sub_terminates: assumes "terminates D (Seq x y)" shows "terminates D x" and "terminates D y"
proof (insert assms)
  assume "terminates D (Seq x y)"
  then obtain n where seq_term: "\<forall>mem. eval_prog (Suc n) D mem (Seq x y) \<noteq> None"
    by (metis eval_prog.simps(1) not0_implies_Suc terminates_def)
  hence x_term: "\<forall>mem. eval_prog n D mem x \<noteq> None"
    by (auto, metis not_Some_eq option.simps(4))
  thus "terminates D x"
    by (metis terminates_def)
  from this and assms obtain m where "\<forall>mem. eval_prog (Suc (Suc m)) D mem (Seq x y) \<noteq> None"
    by (simp add: terminates_def, metis add_Suc_right eval_prog.simps(4) min_terminates)
  from this and x_term have "\<forall>mem. eval_prog n D mem y \<noteq> None"
    sorry
  thus "terminates D y"
    by (metis terminates_def)
qed

(*
lemma least_steps: "terminates D x \<Longrightarrow> \<exists>!n. eval_prog n D mem x \<noteq> None \<and> eval_prog (n - 1) D mem x = None"
proof (induct x)
  assume "terminates D Skip"
  hence "\<exists>n. eval_prog n D mem Skip \<noteq> None \<and> eval_prog (n - 1) D mem Skip = None"
    by (rule_tac x = 1 in exI, auto)
  thus "\<exists>!n. eval_prog n D mem Skip \<noteq> None \<and> eval_prog (n - 1) D mem Skip = None"
    by (auto, metis diff_Suc_less diffs0_imp_equal eval_prog.simps(5) less_Suc0 nat.exhaust option.simps(3))
next
  fix x s
  assume "terminates D (Assign x s)"
  hence "eval_prog 1 D mem (Assign x s) \<noteq> None \<and> eval_prog 0 D mem (Assign x s) = None"
    by auto
  moreover
  {
    fix n :: nat
    assume "n > 1"
    then obtain m where n_def: "n = Suc (Suc m)"
      by (metis One_nat_def gr_implies_not0 linorder_not_le nat.exhaust order_refl)
    hence "eval_prog (Suc (Suc m)) D mem (Assign x s) \<noteq> None \<and> eval_prog (Suc m) D mem (Assign x s) \<noteq> None"
      by auto
    hence "eval_prog n D mem (Assign x s) \<noteq> None \<and> eval_prog (n - 1) D mem (Assign x s) \<noteq> None"
      by (metis diff_Suc_1 n_def)
  }
  ultimately show "\<exists>!n. eval_prog n D mem (Assign x s) \<noteq> None \<and> eval_prog (n - 1) D mem (Assign x s) = None"
    by smt
next
  fix x1 x2
  assume ind_hyp1: "terminates D x1 \<Longrightarrow> \<exists>!n. eval_prog n D mem x1 \<noteq> None \<and> eval_prog (n - 1) D mem x1 = None"
  and ind_hyp2: "terminates D x2 \<Longrightarrow> \<exists>!n. eval_prog n D mem x2 \<noteq> None \<and> eval_prog (n - 1) D mem x2 = None"
  and "terminates D (Seq x1 x2)"
  hence "\<exists>!n. eval_prog n D mem x1 \<noteq> None \<and> eval_prog (n - 1) D mem x1 = None"
  and "\<exists>!n. eval_prog n D mem x2 \<noteq> None \<and> eval_prog (n - 1) D mem x2 = None"
    

definition steps_eq :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> nat \<Rightarrow> 'b mem \<Rightarrow> 'a prog \<Rightarrow> 'a prog \<Rightarrow> bool" where
  "steps_eq D n mem pgm1 pgm2 \<equiv> eval_prog n D mem pgm1 = eval_prog n D mem pgm2"

definition schematic_eq :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a prog \<Rightarrow> 'a prog \<Rightarrow> bool" where
  "schematic_eq D pgm1 pgm2 \<equiv> \<forall>mem. \<exists>n. steps_eq D n mem pgm1 pgm2 \<and> eval_prog n D mem pgm1 \<noteq> None"

lemma schematic_eq_var: "schematic_eq D pgm1 pgm2 = (\<exists>n. \<forall>mem. steps_eq D n mem pgm1 pgm2 \<and> eval_prog n D mem pgm1 \<noteq> None)"
proof
  assume "schematic_eq D pgm1 pgm2"
  then obtain m where "m = Max {n. steps_eq D n mem pgm1 pgm2

lemma schematic_eq_var: "schematic_eq D pgm1 pgm2 = (\<forall>mem. (\<exists>n. (eval_prog n D mem pgm1 = eval_prog n D mem pgm2) \<and> (eval_prog n D mem pgm1 \<noteq> None)))"
  apply (simp add: schematic_eq_def, auto, blast)
  apply (rule_tac x = "Max {n. eval_prog n D mem pgm1 = eval_prog n D mem pgm2 \<and> eval_prog n D mem pgm1 \<noteq> None}" in exI)
  apply auto

lemma If_subterm_1: "\<lbrakk>terminates D (If P x y); \<forall>mem. eval_wf_pred D mem P\<rbrakk> \<Longrightarrow> schematic_eq D (If P x y) x"
proof (simp add: schematic_eq_def)
  assume "terminates D (If P x y)" and "\<forall>mem. eval_wf_pred D mem P"
  then moreover obtain m where "\<forall>mem. eval_prog m D mem (If P x y) \<noteq> None"
    by (metis terminates_def)
  ultimately have "\<exists>n. \<forall>mem. eval_prog n D mem (If P x y) = eval_prog n D mem x \<and>
                             (\<exists>r. eval_prog n D mem (If P x y) = Some r)"
    apply (rule_tac x = "Suc m" in exI, auto)
    apply (metis Nat.add_0_right add_Suc_right eval_prog.simps(2) min_terminates)
    by (metis add.comm_neutral add_Suc_right eval_prog.simps(2) min_terminates)
  thus "(\<exists>n. \<forall>mem. eval_prog n D mem (prog.If P x y) =
                   eval_prog n D mem x \<and>
                   (\<exists>ya. eval_prog n D mem (prog.If P x y) = Some ya)) \<or>
        (\<forall>n mem. eval_prog n D mem (prog.If P x y) = eval_prog n D mem x)"
    by metis
qed

lemma If_subterm_2: "\<lbrakk>terminates D (If P x y); \<forall>mem. \<not> eval_wf_pred D mem P\<rbrakk> \<Longrightarrow> schematic_eq D (If P x y) y"
proof (simp add: schematic_eq_def)
  assume "terminates D (If P x y)" and "\<forall>mem. \<not> eval_wf_pred D mem P"
  then moreover obtain m where "\<forall>mem. eval_prog m D mem (If P x y) \<noteq> None"
    by (metis terminates_def)
  ultimately show "\<exists>n. \<forall>mem. eval_prog n D mem (If P x y) = eval_prog n D mem y \<and>
                             (\<exists>r. eval_prog n D mem (If P x y) = Some r)"
    apply (rule_tac x = "Suc m" in exI, auto)
    apply (metis Nat.add_0_right add_Suc_right eval_prog.simps(2) min_terminates)
    by (metis add.comm_neutral add_Suc_right eval_prog.simps(2) min_terminates)
qed

lemma same_program_comm: "same_program D pgm1 pgm2 \<Longrightarrow> same_program D pgm2 pgm1"
  by (auto simp add: same_program_def, metis)

lemma same_program_trans: "\<lbrakk>same_program D pgm1 pgm2; same_program D pgm2 pgm3\<rbrakk> \<Longrightarrow> same_program D pgm1 pgm3"
  apply (auto simp add: same_program_def)
  by (metis comm_semiring_1_class.normalizing_semiring_rules(24) min_terminates)

lemma same_program_refl: "terminates D pgm \<Longrightarrow> same_program D pgm pgm"
  by (auto simp add: same_program_def terminates_def)

lemma all_loops_terminate: "\<lbrakk>\<And>loop. loop \<in> prog_whiles pgm \<Longrightarrow> terminates D loop\<rbrakk> \<Longrightarrow> terminates D pgm"
  by (induct pgm, auto)

lemma "terminates D pgm1 \<Longrightarrow> \<exists>pgm2. (\<forall>loop. loop \<in> prog_whiles pgm2 \<longrightarrow> terminates D loop) \<and> (same_result D pgm1 pgm2)"
  apply (induct pgm1)

*)
*)

fun FV :: "'a trm \<Rightarrow> nat set" where
  "FV (Var v) = {v}"
| "FV (App f xs) = foldr op \<union> (map FV xs) {}"

lemma app_FV: "v \<notin> FV (App f xs) \<Longrightarrow> \<forall>x\<in>set xs. v \<notin> FV x"
  by (erule contrapos_pp, simp, induct xs, auto)

lemma no_FV [simp]: "v \<notin> FV s \<Longrightarrow> s[v|t] = s"
proof (induct s)
  fix f xs
  assume asm: "\<forall>x\<in>set xs. v \<notin> FV x \<longrightarrow> trm_subst v t x = x"
    and "v \<notin> FV (App f xs)"
  hence "\<forall>x\<in>set xs. v \<notin> FV x"
    by (metis app_FV)
  thus "trm_subst v t (App f xs) = App f xs"
    by (metis (lifting) asm map_idI trm_subst.simps(2))
next
  fix v' assume "v \<notin> FV (Var v')"
  thus "trm_subst v t (Var v') = Var v'" by simp
next
  show "\<forall>x\<in>set []. v \<notin> FV x \<longrightarrow> trm_subst v t x = x" by simp
next
  fix x xs
  assume "v \<notin> FV x \<Longrightarrow> trm_subst v t x = x"
    and "\<forall>y\<in>set xs. v \<notin> FV y \<longrightarrow> trm_subst v t y = y"
  thus "\<forall>y\<in>set (x # xs). v \<notin> FV y \<longrightarrow> trm_subst v t y = y"
    by auto
qed

primrec pred_vars :: "'a::ranked_alphabet pred \<Rightarrow> nat set" where
  "pred_vars (Pred P xs) = \<Union> (set (map FV xs))"

lemma no_pred_vars: "v \<notin> pred_vars \<phi> \<Longrightarrow> \<phi>[v|t] = \<phi>"
proof (induct \<phi>, simp)
  fix xs :: "'a trm list" assume "\<forall>x\<in>set xs. v \<notin> FV x"
  thus "map (trm_subst v t) xs = xs"
    by (induct xs, simp_all)
qed

ML {*
structure AlphabetRules = Named_Thms
  (val name = @{binding "alphabet"}
   val description = "Alphabet rules")
*}

setup {* AlphabetRules.setup *}

lemma trm_simple_induct': "\<lbrakk>\<And>f xs. (\<forall>x\<in>set xs. P x) \<Longrightarrow> P (App f xs); \<And>n. P (Var n)\<rbrakk> \<Longrightarrow> P s \<and> (\<forall>x\<in>set []. P x)"
  by (rule trm.induct[of "\<lambda>xs. (\<forall>x\<in>set xs. P x)" P], simp_all)

lemma trm_simple_induct: "\<lbrakk>\<And>n. P (Var n); \<And>f xs. (\<forall>x\<in>set xs. P x) \<Longrightarrow> P (App f xs)\<rbrakk> \<Longrightarrow> P s"
  by (metis trm_simple_induct')

lemma foldr_FV: "foldr op \<union> (map FV xs) {} = \<Union> (FV ` set xs)"
  by (induct xs, auto)

lemma eval_trm_eq_mem: "(\<forall>v\<in>FV s. m1 v = m2 v) \<Longrightarrow> eval_trm D m1 s = eval_trm D m2 s"
proof (induct rule: trm_simple_induct, auto)
  fix f :: "'a" and xs :: "'a trm list"
  assume asm1: "\<forall>x\<in>set xs. (\<forall>v\<in>FV x. m1 v = m2 v) \<longrightarrow> eval_trm D m1 x = eval_trm D m2 x"
  and asm2: "\<forall>v\<in>foldr op \<union> (map FV xs) {}. m1 v = m2 v"
  have "foldr op \<union> (map FV xs) {} = \<Union> (FV ` set xs)"
    by (induct xs, auto)
  hence "\<forall>v\<in>\<Union>(FV ` set xs). m1 v = m2 v"
    by (metis asm2)
  hence "\<forall>x\<in>set xs. (\<forall>v\<in>FV x. m1 v = m2 v)"
    by (metis UnionI imageI)
  hence "\<forall>x\<in>set xs. eval_trm D m1 x = eval_trm D m2 x"
    by (metis asm1)
  hence "map (eval_trm D m1) xs = map (eval_trm D m2) xs"
    by (induct xs, auto)
  thus "mf D f (map (eval_trm D m1) xs) = mf D f (map (eval_trm D m2) xs)"
    by metis
qed

definition set_mem :: "nat \<Rightarrow> 'a \<Rightarrow> 'a mem \<Rightarrow> 'a mem" where
  "set_mem x s mem \<equiv> \<lambda>v. if v = x then s else mem v"

definition assign ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> nat \<Rightarrow> 'a trm \<Rightarrow> 'b mem \<Rightarrow> 'b mem"
  where
  "assign D x s mem = set_mem x (eval_trm D mem s) mem"

definition halt_null :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'b mem"
  where
  "halt_null D mem \<equiv> \<lambda>v. if v \<notin> output_vars TYPE('a) then mf D NULL [] else mem v"

lemma eval_assign1:
  assumes xy: "x \<noteq> y" and ys: "y \<notin> FV s"
  shows "assign D y t (assign D x s mem) = assign D x s (assign D y (trm_subst x s t) mem)"
  apply (induct t rule: trm_simple_induct)
  apply (simp add: assign_def set_mem_def)
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
                      assign D x s (assign D y (trm_subst x s t) mem)"
  hence "\<forall>t\<in>set ts. assign D y t (assign D x s mem) v =
                     assign D x s (assign D y (trm_subst x s t) mem) v"
    by auto
  thus "assign D y (App f ts) (assign D x s mem) v =
        assign D x s (assign D y (App f (map (trm_subst x s) ts)) mem) v"
    apply (simp add: assign_def set_mem_def o_def)
    by (smt eval_trm_eq_mem map_eq_conv xy ys)
qed

lemma eval_assign2:
  assumes xy: "x \<noteq> y" and xs: "x \<notin> FV s"
  shows "assign D y t (assign D x s mem) =
         assign D y (trm_subst x s t) (assign D x s mem)"
  apply (induct t rule: trm_simple_induct)
  apply (simp add: assign_def set_mem_def)
  apply default
  apply default
  apply default
  apply (smt eval_trm_eq_mem xs)
  apply auto
proof
  fix f ts v
  assume "\<forall>t\<in>set ts. assign D y t (assign D x s mem) =
                      assign D y (trm_subst x s t) (assign D x s mem)"
  hence "\<forall>t\<in>set ts. assign D y t (assign D x s mem) v =
                     assign D y (trm_subst x s t) (assign D x s mem) v"
    by auto
  thus "assign D y (App f ts) (assign D x s mem) v =
        assign D y (App f (map (trm_subst x s) ts)) (assign D x s mem) v"
    apply (simp add: assign_def set_mem_def o_def)
    by (smt eval_trm_eq_mem map_eq_conv xy xs)
qed

lemma eval_assign3: "assign D x t (assign D x s mem) = assign D x (trm_subst x s t) mem"
proof (induct t rule: trm_simple_induct, simp add: assign_def set_mem_def, auto, default)
  fix f ts v
  assume "\<forall>t\<in>set ts. assign D x t (assign D x s mem) = assign D x (trm_subst x s t) mem"
  hence "\<forall>t\<in>set ts. assign D x t (assign D x s mem) v = assign D x (trm_subst x s t) mem v"
    by auto
  hence "v = x \<longrightarrow> map (eval_trm D (\<lambda>v. if v = x then eval_trm D mem s else mem v)) ts =
                  map (eval_trm D mem \<circ> trm_subst x s) ts"
    by (auto simp add: assign_def set_mem_def)
  thus "assign D x (App f ts) (assign D x s mem) v = assign D x (App f (map (trm_subst x s) ts)) mem v"
    by (auto simp add: assign_def set_mem_def o_def, smt map_eq_conv)
qed

lemma eval_halt:
  "x \<notin> output_vars TYPE('a::ranked_alphabet) \<Longrightarrow> halt_null D mem = halt_null D (assign D x (App (NULL::'a) []) mem)"
  by (auto simp add: halt_null_def assign_def set_mem_def)

lemma subst_preds: "P \<in> wf_preds \<Longrightarrow> P[x|s] \<in> wf_preds"
  apply (induct P)
  apply simp
  by (metis SKAT_Term.pred.inject length_map wf_preds.simps)

lemma eval_assign4: "P \<in> preds \<Longrightarrow> eval_pred D (assign D x t mem) P = eval_pred D mem (pred_subst x t P)"
proof (induct P)
  fix P and xs :: "'a trm list" assume "Pred P xs \<in> preds"
  have "\<And>s. s \<in> set xs \<Longrightarrow> eval_trm D (assign D x t mem) s = eval_trm D mem (s[x|t])"
    by (metis eval_assign3 set_mem_def assign_def)
  thus "eval_pred D (assign D x t mem) (Pred P xs) = eval_pred D mem (pred_subst x t (Pred P xs))"
    by (simp add: o_def, metis (lifting) map_ext)
qed

end
