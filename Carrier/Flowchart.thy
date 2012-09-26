theory Flowchart
  imports Base
begin

record 'a alphabet =
  symbols :: "'a set"

locale alphabet = fixes \<Sigma> (structure)
  assumes finite_symbols: "finite (symbols \<Sigma>)"

record 'a ranked_alphabet = "'a alphabet" +
  arity :: "'a \<Rightarrow> nat"
  funs :: "'a set"
  rels :: "'a set"
  outputs :: "nat set"

locale ranked_alphabet = alphabet +
  assumes "funs \<Sigma> \<inter> rels \<Sigma> = {}"
  and "funs \<Sigma> \<union> rels \<Sigma> = symbols \<Sigma>"
  and "finite (outputs \<Sigma>)"
  and "funs \<Sigma> \<noteq> {}"
  and "rels \<Sigma> \<noteq> {}"

datatype 'a trm = var nat | app 'a "('a trm) list"

datatype 'a atomic_formula = app_rel 'a "('a trm) list"

context ranked_alphabet
begin

  fun wf_term :: "'a trm \<Rightarrow> bool" where
    "wf_term (var _) = True"
  | "wf_term (app f xs) =
      (length xs = arity \<Sigma> f \<and> f \<in> funs \<Sigma> \<and> (\<forall>x\<in>set xs. wf_term x))"

  definition wf_term_set :: "('a trm) set" where
    "wf_term_set \<equiv> {x. wf_term x}"

  lemma wf_var: "wf_term (var x)" by simp

  fun wf_atomic_formula :: "'a atomic_formula \<Rightarrow> bool" where
    "wf_atomic_formula (app_rel P xs) =
      (length xs = arity \<Sigma> P \<and> P \<in> rels \<Sigma> \<and> (\<forall>x\<in>set xs. wf_term x))"

end

datatype 'a flowchart
  = assignment nat "'a trm" "'a flowchart"
  | skip "'a flowchart"
  | halt
  | undef "'a flowchart"
  | choice "'a atomic_formula" "'a flowchart" "'a flowchart" ("IF _ THEN _ ELSE _")

fun compose :: "'a flowchart \<Rightarrow> 'a flowchart \<Rightarrow> 'a flowchart" (infixl ";" 55) where
    "compose (assignment x y S) T = assignment x y (S ; T)"
  | "compose (skip S) T = (S ; T)"
  | "compose halt T = T"
  | "compose (undef S) T = undef (S ; T)"
  | "compose (IF p THEN S ELSE T) R = IF p THEN (S ; R) ELSE (T ; R)"

lemma compose_assoc: "(S ; T) ; U = S ; (T ; U)"
  by (induct S, auto)

definition ASSIGN :: "nat \<Rightarrow> 'a trm \<Rightarrow> 'a flowchart" (infix ":=" 80) where
  "ASSIGN x y = assignment x y halt"

definition SKIP :: "'a flowchart" where
  "SKIP = skip halt"

definition UNDEFINED :: "'a flowchart" where
  "UNDEFINED = undef halt"

definition atomic_programs :: "'a flowchart set" where
  "atomic_programs \<equiv> {SKIP, UNDEFINED} \<union> {a. \<exists>x y. a = x := y}"

lemma assign_compose: "x := y ; S = assignment x y S"
  by (auto simp add: ASSIGN_def)

inductive_set programs :: "'a flowchart set" where
  atomic [intro]: "S \<in> atomic_programs \<Longrightarrow> S \<in> programs"
| composition [intro]: "\<lbrakk>S \<in> programs; T \<in> programs\<rbrakk> \<Longrightarrow> S ; T \<in> programs"
| choice [intro]: "\<lbrakk>S \<in> programs; T \<in> programs\<rbrakk> \<Longrightarrow> IF P THEN S ELSE T \<in> programs"

lemma "SKIP ; T = T"
  by (metis SKIP_def compose.simps(2) compose.simps(3))

lemma halt_not_atomic: "halt \<notin> atomic_programs"
  by (auto simp add: atomic_programs_def SKIP_def UNDEFINED_def ASSIGN_def)

lemma any_undef_not_atomic: "S \<noteq> halt \<Longrightarrow> undef S \<notin> atomic_programs"
  by (auto simp add: atomic_programs_def SKIP_def UNDEFINED_def ASSIGN_def)

lemma any_skip_not_atomic: "S \<noteq> halt \<Longrightarrow> skip S \<notin> atomic_programs"
  by (auto simp add: atomic_programs_def SKIP_def UNDEFINED_def ASSIGN_def)

lemma halt_not_program: "halt \<notin> programs" sorry

lemma "T \<in> programs \<Longrightarrow> T ; SKIP = T"
  apply (induct T rule: programs.induct)
  
  apply auto
  
  
  
  

context ranked_alphabet
begin

  fun wf_flowchart :: "'a flowchart \<Rightarrow> bool" where
    "wf_flowchart (assignment x y S) = (wf_term y \<and> wf_flowchart S)"
  | "wf_flowchart (skip S) = wf_flowchart S"
  | "wf_flowchart halt = True"
  | "wf_flowchart connection = True"
  | "wf_flowchart (undef S) = wf_flowchart S"
  | "wf_flowchart (IF p THEN S ELSE T) = (wf_flowchart S \<and> wf_flowchart T)"

  lemma compose_wf: "\<lbrakk>wf_flowchart S; wf_flowchart T\<rbrakk> \<Longrightarrow> wf_flowchart (S ; T)"
    by (induct S, simp_all)

end

fun ntuples :: "'a set \<Rightarrow> nat \<Rightarrow> ('a list) set" ("_\<^bsup>_\<^esup>") where
  "X\<^bsup>0\<^esup> = {[]}"
| "X\<^bsup>Suc n\<^esup> = {x. \<exists>y\<in>X. \<exists>ys\<in>X\<^bsup>n\<^esup>. x = y#ys}"

lemma ntp1: "set xs \<subseteq> X \<longleftrightarrow> xs \<in> X\<^bsup>length xs\<^esup>" by (induct xs, simp_all)

lemma ntp2: "\<lbrakk>set xs \<subseteq> X; length xs = n\<rbrakk> \<Longrightarrow> xs \<in> X\<^bsup>n\<^esup>" by (metis ntp1)

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

definition eq_rel :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a relation" where
  "eq_rel n X = {xs. \<exists>y\<in>X. xs = replicate n y}"

lemma "eq_rel n X \<subseteq> X\<^bsup>n\<^esup>"
  by (auto simp add: ntuples_set eq_rel_def)

definition fplus :: "nat list \<Rightarrow> nat" where
  "fplus xs = foldr (op +) xs 0"

lemma "fplus : \<nat>\<^bsup>n\<^esup> \<rightarrow> \<nat>"
proof (auto simp add: ftype_def)
  fix xs :: "nat list"
  assume "set xs \<subseteq> \<nat>"
  thus "fplus xs \<in> \<nat>"
    by (induct xs, simp_all add: fplus_def)
qed

record 'a interp = "'a partial_object" +
  fun_map :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a"
  rel_map :: "'a \<Rightarrow> 'a relation"
  null :: "'a"

record 'a frame =
  alph :: "'a ranked_alphabet" ("\<Sigma>1\<index>")
  ip :: "'a interp" ("D1\<index>")

locale frame = fixes \<Theta> (structure)
  assumes is_ranked_alphabet: "ranked_alphabet \<Sigma>1"
  and null_closed: "null D1 \<in> carrier D1"
  and fun_meaning: "f \<in> funs \<Sigma>1 \<Longrightarrow> fun_map D1 f : (carrier D1)\<^bsup>arity \<Sigma>1 f\<^esup> \<rightarrow> carrier D1"
  and rel_meaning: "P \<in> rels \<Sigma>1 \<Longrightarrow> rel_map D1 P \<subseteq> (carrier D1)\<^bsup>arity \<Sigma>1 f\<^esup>"

sublocale frame \<subseteq> ranked_alphabet where \<Sigma> = \<Sigma>1 by (rule is_ranked_alphabet)

context frame
begin

  fun eval_term :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a trm \<Rightarrow> 'a" where
    "eval_term var_map (var x) = var_map x"
  | "eval_term var_map (app f xs) = fun_map D1 f (map (eval_term var_map) xs)"

  lemma wf_term_induction:
    "\<lbrakk>wf_term t; \<And>n. P (var n); \<And>f xs. \<lbrakk>f \<in> funs \<Sigma>1; length xs = arity \<Sigma>1 f; \<And>x. x \<in> set xs \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P (app f xs)\<rbrakk> \<Longrightarrow> P t"
    by (induct t rule: wf_term.induct, auto)

  lemma eval_term_closed:
    assumes var_map_type: "var_map : \<nat> \<rightarrow> carrier D1"
    and wft: "wf_term t"
    shows "eval_term var_map t : carrier D1"
    apply (induct t rule: wf_term_induction)
    apply (metis wft)
    apply (simp_all)
    apply (insert var_map_type, simp add: Nats_def)
    apply (metis UNIV_I ftype_pred)
    apply (subgoal_tac "map (eval_term var_map) xs \<in> (carrier D1)\<^bsup>length xs\<^esup>")
    apply (metis ftype_pred fun_meaning)
    apply (simp add: ntp1[symmetric])
    by auto

  fun eval_pred :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a atomic_formula \<Rightarrow> bool" where
    "eval_pred var_map (app_rel P xs) \<longleftrightarrow> map (eval_term var_map) xs \<in> rel_map D1 P"

  definition emp :: "nat \<Rightarrow> 'a" where
    "emp n = null D1"

  fun eval_flowchart :: "((nat \<Rightarrow> 'a) \<times> 'a flowchart) \<Rightarrow> ((nat \<Rightarrow> 'a) \<times> 'a flowchart)" where
    "eval_flowchart (vm, (assignment x y S)) = eval_flowchart ((\<lambda>z. if z=x then eval_term vm y else vm z), S)"
  | "eval_flowchart (vm, (skip S)) = eval_flowchart (vm, S)"
  | "eval_flowchart (vm, halt) = (vm, halt)"
  | "eval_flowchart (vm, connection) = (vm, connection)"
  | "eval_flowchart (vm, undef S) = (emp, undef S)"
  | "eval_flowchart (vm, IF P THEN S ELSE T) = eval_flowchart (vm, if eval_pred vm P then S else T)"

  lemma "eval_flowchart (z, SKIP ; S) = eval_flowchart (z, S)"
    by (simp add: SKIP_def)

  lemma "fst (eval_flowchart (z, S ; SKIP)) = fst (eval_flowchart (z, S))"
    by (induct S arbitrary: z, auto simp add: SKIP_def)

  lemma "fst (eval_flowchart (z, UNDEFINED ; S)) = fst (eval_flowchart (z, UNDEFINED))"
    by (induct S arbitrary: z, auto simp add: UNDEFINED_def)

  lemma "S \<in> programs \<Longrightarrow> fst (eval_flowchart (z, S ; UNDEFINED)) = emp"
    apply (induct S arbitrary: z)
    apply (auto simp add: UNDEFINED_def)
    apply (subgoal_tac "S \<in> programs")
    apply auto
    apply (subgoal_tac "nat := trm ; S \<in> programs")
    apply (simp add: compose_def)
    
    
    try
    
    nitpick
    

  lemma "fst (eval_flowchart (emp, T)) = fst (eval_flowchart (emp, U)) \<Longrightarrow> fst (eval_flowchart (emp, S ; T)) = fst (eval_flowchart (emp, S ; U))"
    apply (induct S)
    apply auto
    apply blast
    
    
    defer
    nitpick
nitpick [non_std, show_all]
    
    apply (cases "z = nat")
    sledgehammer
    apply (simp add: 

end

definition empty :: "'a interp \<Rightarrow> nat \<Rightarrow> 'a" where
  "empty D n = null D"

definition equivalent_scheme :: "'a ranked_alphabet \<Rightarrow> 'a flowchart \<Rightarrow> 'a flowchart \<Rightarrow> bool" where
  "equivalent_scheme \<Sigma> S T \<equiv> (\<forall>D::'a interp. frame \<lparr>alph = \<Sigma>, ip = D\<rparr> \<longrightarrow> frame.eval_flowchart \<lparr>alph = \<Sigma>, ip = D\<rparr> (empty D, S) = frame.eval_flowchart \<lparr>alph = \<Sigma>, ip = D\<rparr> (empty D, T))"

lemma assumes eq_ST: "equivalent_scheme \<Sigma> S T" shows "equivalent_scheme \<Sigma> (S 
; U) (T; U)"
  apply (auto simp add: equivalent_scheme_def)
  apply (induct U)
  

  apply (insert frame.wf_term_induction[of "\<lparr>alph = \<Sigma>, ip = D\<rparr>"])
  apply (auto simp add: equivalent_scheme_def)


lemma
  assumes eq_UV: "equivalent_scheme \<Sigma> U V"
  shows "equivalent_scheme \<Sigma> (S ; U) (S ; V)"
  apply (induct S, simp_all add: equivalent_scheme_def, auto)
  apply (auto simp add: equivalent_scheme_def)
  
  

record 'a equivalence_relation = "'a partial_object" +
  eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "~\<index>" 50)

locale equivalence_relation = fixes A (structure)
  assumes refl: "x \<in> carrier A \<Longrightarrow> x ~ x"
  and sym: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x ~ y\<rbrakk> \<Longrightarrow> y ~ x"
  and trans: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A; x ~ y; y ~ z\<rbrakk> \<Longrightarrow> x ~ z"

begin

  definition canonical_projection_map :: "'a \<Rightarrow> 'a set" ("\<pi>") where
    "\<pi> x \<equiv> {y. y \<in> carrier A \<and> x ~ y}"

  lemma cpm_closed: "x \<in> carrier A \<Longrightarrow> \<pi> x \<subseteq> carrier A"
    by (auto simp add: canonical_projection_map_def)

  definition quotient :: "'a set set" where
    "quotient \<equiv> {\<pi> x|x. x \<in> carrier A}"

end

definition frel :: "'a ranked_alphabet \<Rightarrow> ('a flowchart) equivalence_relation" where
  "frel \<Sigma> \<equiv> \<lparr>carrier = UNIV, eq = equivalent_scheme \<Sigma>\<rparr>"

lemma frel_eq: "equivalence_relation (frel \<Sigma>)"
  by (default, simp_all add: equivalent_scheme_def frel_def)

definition fquotient :: "'a ranked_alphabet \<Rightarrow> 'a flowchart set set" where
  "fquotient \<Sigma> = equivalence_relation.quotient (frel \<Sigma>)"

lemma "\<lbrakk>equivalence_relation \<lparr>carrier = X, eq = eq1\<rparr>; Y \<subseteq> X\<rbrakk> \<Longrightarrow> equivalence_relation \<lparr>carrier = Y, eq = eq1\<rparr>"
  by (simp add: equivalence_relation_def, safe, fast+)
