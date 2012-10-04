theory Flowchart
  imports Alphabet
begin

datatype trm = var nat | app nat "trm list"

datatype atomic_formula = app_rel nat "trm list"

fun wf_term :: "alphabet \<Rightarrow> trm \<Rightarrow> bool" where
    "wf_term \<Sigma> (var _) = True"
  | "wf_term \<Sigma> (app f xs) =
       (length xs = arity \<Sigma> f \<and> f \<in> funs \<Sigma> \<and> (\<forall>x\<in>set xs. wf_term \<Sigma> x))"

fun wf_atomic_formula :: "alphabet \<Rightarrow> atomic_formula \<Rightarrow> bool" where
    "wf_atomic_formula \<Sigma> (app_rel P xs) =
       (length xs = arity \<Sigma> P \<and> P \<in> rels \<Sigma> \<and> (\<forall>x\<in>set xs. wf_term \<Sigma> x))"

datatype flowchart
  = assignmenth nat trm
  | assignment nat trm flowchart
  | skiph
  | skip flowchart
  | undefh
  | undef flowchart
  | choicehh atomic_formula
  | choicefh atomic_formula flowchart
  | choicehf atomic_formula flowchart
  | choiceff atomic_formula flowchart flowchart

fun compose :: "flowchart \<Rightarrow> flowchart \<Rightarrow> flowchart" where
    "compose (assignmenth x y) T = assignment x y T"
  | "compose (assignment x y S) T = assignment x y (compose S T)"
  | "compose skiph T = T"
  | "compose (skip S) T = compose S T"
  | "compose undefh T = undef T"
  | "compose (undef S) T = undef (compose S T)"
  | "compose (choicehh p) R = R"
  | "compose (choicefh p S) R = choiceff p (compose S R) R"
  | "compose (choicehf p T) R = choiceff p R (compose T R)"
  | "compose (choiceff p S T) R = choiceff p (compose S R) (compose T R)"

lemma flowchart_assoc: "compose (compose S T) U = compose S (compose T U)" by (induct S, auto)

lemma skiph_onel: "compose skiph T = T" by simp

datatype expr
  = e_assignment nat trm
  | e_skip
  | e_undef
  | e_compose expr expr
  | e_choicehh atomic_formula
  | e_choicefh atomic_formula expr
  | e_choicehf atomic_formula expr
  | e_choiceff atomic_formula expr expr

fun flowchart_to_expr :: "flowchart \<Rightarrow> expr" where
    "flowchart_to_expr (assignmenth x y) = e_assignment x y"
  | "flowchart_to_expr skiph = e_skip"
  | "flowchart_to_expr undefh = e_undef"
  | "flowchart_to_expr (assignment x y S ) = e_compose (e_assignment x y) (flowchart_to_expr S)"
  | "flowchart_to_expr (skip S) = e_compose e_skip (flowchart_to_expr S)"
  | "flowchart_to_expr (undef S) = e_compose e_undef (flowchart_to_expr S)"
  | "flowchart_to_expr (choicehh p) = e_choicehh p"
  | "flowchart_to_expr (choicefh p S) = e_choicefh p (flowchart_to_expr S)"
  | "flowchart_to_expr (choicehf p T) = e_choicehf p (flowchart_to_expr T)"
  | "flowchart_to_expr (choiceff p S T) = e_choiceff p (flowchart_to_expr S) (flowchart_to_expr T)"

fun expr_to_flowchart :: "expr \<Rightarrow> flowchart" where
    "expr_to_flowchart (e_assignment x y) = assignmenth x y"
  | "expr_to_flowchart e_skip = skiph"
  | "expr_to_flowchart e_undef = undefh"
  | "expr_to_flowchart (e_compose S T) = compose (expr_to_flowchart S) (expr_to_flowchart T)"
  | "expr_to_flowchart (e_choicehh p) = choicehh p"
  | "expr_to_flowchart (e_choicefh p S) = choicefh p (expr_to_flowchart S)"
  | "expr_to_flowchart (e_choicehf p T) = choicehf p (expr_to_flowchart T)"
  | "expr_to_flowchart (e_choiceff p S T) = choiceff p (expr_to_flowchart S) (expr_to_flowchart T)"

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

record interp =
  fun_map :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
  rel_map :: "nat \<Rightarrow> nat relation"
  null :: "nat"

locale frame =
  fixes \<Sigma>l :: "alphabet"
  and Dl :: "interp"
  assumes fun_meaning: "f \<in> funs \<Sigma>l \<Longrightarrow> fun_map Dl f : \<nat>\<^bsup>arity \<Sigma>l f\<^esup> \<rightarrow> \<nat>"
  and rel_meaning: "P \<in> rels \<Sigma>l \<Longrightarrow> rel_map Dl P \<subseteq> \<nat>\<^bsup>arity \<Sigma>l f\<^esup>"

datatype mem = mem "nat \<Rightarrow> nat"
             | undefined_mem

datatype ('a, 'b) either = Left 'a | Right 'b

definition emp :: "interp \<Rightarrow>  mem" where
  "emp D = mem (\<lambda>n. null D)"

context frame
begin

  fun eval_term :: "(nat \<Rightarrow> nat) \<Rightarrow> trm \<Rightarrow> nat" where
    "eval_term var_map (var x) = var_map x"
  | "eval_term var_map (app f xs) = fun_map Dl f (map (eval_term var_map) xs)"

  lemma wf_term_induction:
    "\<lbrakk>wf_term \<Sigma>l t; \<And>n. P (var n); \<And>f xs. \<lbrakk>f \<in> funs \<Sigma>l; length xs = arity \<Sigma>l f; \<And>x. x \<in> set xs \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P (app f xs)\<rbrakk> \<Longrightarrow> P t"
    by (induct t rule: wf_term.induct, auto)

  lemma eval_term_closed:
    assumes var_map_type: "var_map : \<nat> \<rightarrow> \<nat>"
    and wft: "wf_term \<Sigma>l t"
    shows "eval_term var_map t : \<nat>"
    apply (induct t rule: wf_term_induction)
    apply (metis wft)
    apply (simp_all)
    apply (insert var_map_type, simp add: Nats_def)
    apply (subgoal_tac "map (eval_term var_map) xs \<in> \<nat>\<^bsup>length xs\<^esup>")
    apply (metis ftype_pred fun_meaning)
    apply (simp add: ntp1[symmetric])
    by auto

  fun eval_pred :: "(nat \<Rightarrow> nat) \<Rightarrow> atomic_formula \<Rightarrow> bool" where
    "eval_pred var_map (app_rel P xs) \<longleftrightarrow> map (eval_term var_map) xs \<in> rel_map Dl P"

  fun step_flowchart :: "(mem \<times> flowchart) \<Rightarrow> (mem, (mem \<times> flowchart)) either" where
      "step_flowchart (mem vm, (assignmenth x y)) = Left (mem (\<lambda>z. if z=x then eval_term vm y else vm z))"
    | "step_flowchart (mem vm, (assignment x y S)) = Right (mem (\<lambda>z. if z=x then eval_term vm y else vm z), S)"
    | "step_flowchart (m, skiph) = Left m"
    | "step_flowchart (m, skip S) = Right (m, S)"
    | "step_flowchart (_, undefh) = Left undefined_mem"
    | "step_flowchart (_, undef S) = Left undefined_mem"
    | "step_flowchart (m, choicehh _) = Left m"
    | "step_flowchart (mem vm, choicefh p S) = Right (mem vm, if eval_pred vm p then S else skiph)"
    | "step_flowchart (mem vm, choicehf p T) = Right (mem vm, if eval_pred vm p then skiph else T)"
    | "step_flowchart (mem vm, choiceff p S T) = Right (mem vm, if eval_pred vm p then S else T)"
    | "step_flowchart (undefined_mem, _) = Left undefined_mem"

  fun eval_flowchart :: "(mem \<times> flowchart) \<Rightarrow> mem" where
      "eval_flowchart (mem vm, (assignmenth x y)) = mem (\<lambda>z. if z=x then eval_term vm y else vm z)"
    | "eval_flowchart (mem vm, (assignment x y S)) = eval_flowchart (mem (\<lambda>z. if z=x then eval_term vm y else vm z), S)"
    | "eval_flowchart (m, skiph) = m"
    | "eval_flowchart (m, skip S) = eval_flowchart (m, S)"
    | "eval_flowchart (_, undefh) = undefined_mem"
    | "eval_flowchart (_, undef S) = undefined_mem"
    | "eval_flowchart (m, choicehh _) = m"
    | "eval_flowchart (mem vm, choicefh p S) = eval_flowchart (mem vm, if eval_pred vm p then S else skiph)"
    | "eval_flowchart (mem vm, choicehf p T) = eval_flowchart (mem vm, if eval_pred vm p then skiph else T)"
    | "eval_flowchart (mem vm, choiceff p S T) = eval_flowchart (mem vm, if eval_pred vm p then S else T)"
    | "eval_flowchart (undefined_mem, _) = undefined_mem"

  function eval_flowchart_var :: "(mem \<times> flowchart) \<Rightarrow> mem" where
      "eval_flowchart_var (m, S) = (case step_flowchart (m, S) of
                                      (Left m) \<Rightarrow> m
                                    | (Right (m, S')) \<Rightarrow> eval_flowchart_var (m, S'))"
    by (pat_completeness, auto)

  (*
  lemma "eval_flowchart (m, S) = eval_flowchart_var (m, S)"
  proof -
    have"\<And>vm. eval_flowchart (mem vm, S) = eval_flowchart_var (mem vm, S)"
      by (induct S arbitrary: vm, auto)
    moreover have "eval_flowchart (undefined_mem, S) = eval_flowchart_var (undefined_mem, S)"
      by (induct S, auto)
    ultimately show ?thesis
      by (metis mem.exhaust)
  qed
  *)

  lemma eval_skiph_onel: "eval_flowchart (m, compose skiph S) = eval_flowchart (m, S)" by auto

  lemma eval_skiph_oner: "eval_flowchart (m, compose S skiph) = eval_flowchart (m, S)"
  proof -
    have "\<And>vm. eval_flowchart (mem vm, compose S skiph) = eval_flowchart (mem vm, S)"
      by (induct S arbitrary: z, auto)
    moreover have "eval_flowchart (undefined_mem, compose S skiph) = eval_flowchart (undefined_mem, S)"
      by (induct S, auto)
    ultimately show ?thesis
      by (metis mem.exhaust)
  qed

  lemma eval_undefh_zerol: "eval_flowchart (m, compose undefh S) = eval_flowchart (m, undefh)" by auto

  lemma eval_undefh_zeror: "eval_flowchart (m, compose S undefh) = eval_flowchart (m, undefh)"
  proof -
    have "\<And>vm. eval_flowchart (mem vm, compose S undefh) = eval_flowchart (mem vm, undefh)"
      by (induct S arbitrary: z, auto)
    moreover have "eval_flowchart (undefined_mem, compose S undefh) = eval_flowchart (undefined_mem, undefh)"
      by (induct S, auto)
    ultimately show ?thesis
      by (metis mem.exhaust)
  qed

  lemma eval_undefined_mem: "eval_flowchart (undefined_mem, T) = undefined_mem" by (induct T, auto)

  lemma eval_compose: "eval_flowchart (m, compose S T) = eval_flowchart (eval_flowchart (m, S), T)"
  proof -
    have "\<And>vm. eval_flowchart (mem vm, compose S T) = eval_flowchart (eval_flowchart (mem vm, S), T)"
      apply (induct S, auto, induct T, auto, induct T, auto)
      by (metis skiph_onel eval_flowchart.simps(3))
    moreover have "eval_flowchart (undefined_mem, compose S T) = eval_flowchart (eval_flowchart (undefined_mem, S), T)"
      by (simp add: eval_undefined_mem)
    ultimately show ?thesis
      by (metis mem.exhaust)
  qed

end

typedef 'a nset = "{X::'a set. X \<noteq> {}}"
  by (metis (lifting, full_types) Collect_empty_eq ex_in_conv)

locale alph =
  fixes \<Sigma>l :: alphabet
  and outputs :: "nat set"

begin

  definition equivalent_scheme :: "flowchart \<Rightarrow> flowchart \<Rightarrow> bool" where
    "equivalent_scheme S T \<equiv> (\<forall>D m. frame \<Sigma>l D \<longrightarrow>
      frame.eval_flowchart D (m, S) = frame.eval_flowchart D (m, T))"

end

type_synonym flow = "flowchart set"

context alph begin

  definition cpm :: "flowchart \<Rightarrow> flow" ("\<pi>") where
    "\<pi> s = {t. equivalent_scheme s t}"

  lemma scheme_refl [intro]: "equivalent_scheme s s"
    by (simp add: equivalent_scheme_def)

  lemma scheme_sym [sym]: "equivalent_scheme s t \<Longrightarrow> equivalent_scheme t s"
    by (simp add: equivalent_scheme_def)

  lemma scheme_trans [trans]: "\<lbrakk>equivalent_scheme s t; equivalent_scheme t u\<rbrakk> \<Longrightarrow> equivalent_scheme s u"
    by (simp add: equivalent_scheme_def)

  lemma cpm_equiv [simp]: "\<pi> s = \<pi> t \<longleftrightarrow> equivalent_scheme s t"
    by (smt Collect_cong scheme_refl scheme_sym scheme_trans cpm_def mem_Collect_eq)

  lemma in_cpm: "s \<in> \<pi> s"
    by (auto simp add: cpm_def)

  lemma cpm_not_empty: "\<pi> s \<noteq> {}"
    by (metis empty_iff in_cpm)

  lemma cpm1: "\<not> equivalent_scheme s t \<Longrightarrow> s \<notin> \<pi> t"
    by (auto simp add: cpm_def, metis scheme_sym)

  lemma cpm2: "\<not> equivalent_scheme s t \<Longrightarrow> t \<notin> \<pi> s"
    by (metis scheme_sym cpm1)

  definition scheme_compose :: "flow \<Rightarrow> flow \<Rightarrow> flow" (infixr ";" 80) where
    "S ; T \<equiv> {U. \<exists>s\<in>S. \<exists>t\<in>T. equivalent_scheme U (compose s t)}"

  definition flows :: "flow set" where
    "flows \<equiv> {S. \<exists>s. S = \<pi> s}"

  lemma compose_eq1: "equivalent_scheme s t \<Longrightarrow> equivalent_scheme (compose s u) (compose t u)"
    by (simp add: equivalent_scheme_def frame.eval_compose)

  lemma compose_eq2: "equivalent_scheme t u \<Longrightarrow> equivalent_scheme (compose s t) (compose s u)"
    by (simp add: equivalent_scheme_def frame.eval_compose)

  lemma compose_prop: "\<pi> s ; \<pi> t = \<pi> (compose s t)"
    apply (auto simp add: cpm_def scheme_compose_def)
    apply (smt compose_eq1 compose_eq2 scheme_sym scheme_trans)
    by (metis scheme_refl scheme_sym)

  lemma compose_flows: "\<lbrakk>S \<in> flows; T \<in> flows\<rbrakk> \<Longrightarrow> S ; T \<in> flows"
    apply (auto simp add: flows_def)
    apply (rule_tac x = "compose s sa" in exI)
    by (simp add: compose_prop)

  lemma compose_assoc:
    assumes Sf: "S \<in> flows" and Tf: "T \<in> flows" and Uf: "U \<in> flows"
    shows "(S ; T) ; U = S ; (T ; U)"
  proof -
    obtain s t u where Ss: "S = \<pi> s" and Tt: "T = \<pi> t" and Uu: "U = \<pi> u"
      by (insert Sf Tf Uf, auto simp add: flows_def)
    have "(S ; T) ; U = (\<pi> s; \<pi> t) ; \<pi> u"
      by (simp add: Ss Tt Uu)
    also have "... = \<pi> (compose (compose s t) u)"
      by (simp add: compose_prop)
    also have "... = \<pi> (compose s (compose t u))"
      by (simp add: flowchart_assoc)
    also have "... = \<pi> s ; (\<pi> t ; \<pi> u)"
      by (simp add: compose_prop[symmetric])
    also have "... = S ; (T ; U)"
      by (metis Ss Tt Uu)
    finally show ?thesis .
  qed

  definition SKIP :: flow where
    "SKIP \<equiv> \<pi> skiph"

  lemma SKIP_flows: "SKIP \<in> flows"
    by (auto simp add: flows_def SKIP_def)

  lemma SKIP_onel: assumes Sf: "S \<in> flows" shows "SKIP ; S = S"
  proof -
    obtain s where Ss: "S = \<pi> s" by (insert Sf, auto simp add: flows_def)
    thus ?thesis
      by (simp add: SKIP_def compose_prop)
  qed

  lemma SKIP_oner: assumes Sf: "S \<in> flows" shows "S ; SKIP = S"
  proof -
    obtain s where Ss: "S = \<pi> s" by (insert Sf, auto simp add: flows_def)
    thus ?thesis
      apply (auto simp add: SKIP_def compose_prop equivalent_scheme_def)
      by (metis frame.eval_skiph_oner)
  qed

  definition UNDEFINED :: flow where
    "UNDEFINED \<equiv> \<pi> undefh"

  lemma UNDEFINED_flows: "UNDEFINED \<in> flows"
    by (auto simp add: flows_def UNDEFINED_def)

  lemma UNDEFINED_zerol: assumes Sf: "S \<in> flows" shows "UNDEFINED ; S = UNDEFINED"
  proof -
    obtain s where Ss: "S = \<pi> s" by (insert Sf, auto simp add: flows_def)
    thus ?thesis
      apply (auto simp add: UNDEFINED_def compose_prop equivalent_scheme_def)
      by (metis compose.simps(5) frame.eval_undefh_zerol)
  qed

  lemma UNDEFINED_zeror: assumes Sf: "S \<in> flows" shows "S ; UNDEFINED = UNDEFINED"
  proof -
    obtain s where Ss: "S = \<pi> s" by (insert Sf, auto simp add: flows_def)
    thus ?thesis
      apply (auto simp add: UNDEFINED_def compose_prop equivalent_scheme_def)
      by (metis frame.eval_undefh_zeror)
  qed

end

end
