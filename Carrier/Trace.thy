theory Trace
  imports Flowchart Quantale
begin

definition (in alph) atomic_programs :: "flow set" where
  "atomic_programs = {UNDEFINED, SKIP} \<union> {A. \<exists>x y. A = x y}"

definition (in alph) atomic_tests :: "atomic_formula set" where
  "atomic_tests = {t. wf_atomic_formula \<Sigma>l t}"

locale kripke_frame = fixes A (structure)
  fixes tests_map :: "atomic_formula \<Rightarrow> 'a set"
  and programs_map :: "flow set \<Rightarrow> ('a \<times> 'a) set"
  and \<Sigma>l :: alphabet
  assumes tests_map_type: "tests_map : atomic_tests \<rightarrow> Pow (carrier A)"
  and programs_map_type: "programs_map : atomic_programs \<rightarrow> Pow (carrier A \<times> carrier A)"

sublocale kripke_frame \<subseteq> alph .

datatype 'a trace = tlink 'a "flow set" "'a trace" | tend 'a

context kripke_frame
begin

  fun wf_trace :: "'a trace \<Rightarrow> bool" where
    "wf_trace (tlink u0 p0 (tlink u1 p1 \<sigma>)) = ((u0, u1) \<in> programs_map p0 \<and> wf_trace (tlink u1 p1 \<sigma>))"
  | "wf_trace (tlink u0 p0 (tend u1))       = ((u0, u1) \<in> programs_map p0)"
  | "wf_trace (tend u1)                     = True"

  fun first :: "'a trace \<Rightarrow> 'a" where
    "first (tlink u p \<sigma>) = u"
  | "first (tend u)      = u"

  fun last :: "'a trace \<Rightarrow> 'a" where
    "last (tlink u p \<sigma>) = last \<sigma>"
  | "last (tend u)      = u"

  fun join_traces :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" where
    "join_traces (tlink u p \<sigma>) \<tau> = tlink u p (join_traces \<sigma> \<tau>)"
  | "join_traces (tend u) \<tau> = \<tau>"

  definition join_trace_sets :: "'a trace set \<Rightarrow> 'a trace set \<Rightarrow> 'a trace set" where
    "join_trace_sets X Y = {Z. \<exists>\<sigma>\<in>X. \<exists>\<tau>\<in>Y. Z = join_traces \<sigma> \<tau> \<and> last \<sigma> = first \<tau>}"

  definition canonical_program :: "flow set \<Rightarrow> 'a trace set" ("\<lbrace>_\<rbrace>") where
    "\<lbrace>S\<rbrace> = {\<sigma>. \<exists>u0 u1. \<sigma> = tlink u0 S (tend u1) \<and> (u0, u1) \<in> programs_map S}"

  definition canonical_test :: "atomic_formula \<Rightarrow> 'a trace set" ("\<lbrace>_\<rbrace>") where
    "\<lbrace>p\<rbrace> = tend ` tests_map p"

  definition all_tests :: "'a trace set" where
    "all_tests = tend ` UNIV"

  lemma join_trace_onel: "join_trace_sets all_tests X = X"
    by (auto simp add: join_trace_sets_def all_tests_def)

  lemma join_trace_oner: "join_trace_sets X all_tests = X"
    apply (auto simp add: join_trace_sets_def all_tests_def)
  proof -
    fix \<sigma> :: "'a trace" assume "\<sigma> \<in> X"
    thus "join_traces \<sigma> (tend (last \<sigma>)) \<in> X"
      by (induct \<sigma> arbitrary: X, auto)
    from `\<sigma> \<in> X` show "\<exists>\<tau>\<in>X. \<sigma> = join_traces \<tau> (tend (local.last \<tau>))"
      by (rule_tac x = \<sigma> in bexI, induct \<sigma> arbitrary: X, auto)
  qed

  lemma join_last [simp]: "last (join_traces \<sigma> \<tau>) = last \<tau>"
    by (induct \<sigma>, auto)

  lemma join_first [simp]: "last \<sigma> = first \<tau> \<Longrightarrow> first (join_traces \<sigma> \<tau>) = first \<sigma>"
    by (induct \<sigma>, auto)

  lemma join_traces_assoc: "join_traces (join_traces \<sigma> \<tau>) \<phi> = join_traces \<sigma> (join_traces \<tau> \<phi>)"
    by (induct \<sigma>, auto)

  lemma join_trace_set_assoc:
    "join_trace_sets (join_trace_sets X Y) Z = join_trace_sets X (join_trace_sets Y Z)"
  proof (auto simp add: join_trace_sets_def)
    fix \<sigma> \<tau> \<phi>
    assume \<sigma>X: "\<sigma> \<in> X" and \<tau>Y: "\<tau> \<in> Y " and \<phi>Z: "\<phi> \<in> Z"
    and \<tau>\<phi>: "last \<tau> = first \<phi>"
    and \<sigma>\<tau>: "last \<sigma> = first \<tau>"
    thus "\<exists>\<nu>\<in>X. \<exists>\<chi>. (\<exists>\<sigma>'\<in>Y. \<exists>\<tau>'\<in>Z. \<chi> = join_traces \<sigma>' \<tau>' \<and> local.last \<sigma>' = first \<tau>')
                  \<and> join_traces (join_traces \<sigma> \<tau>) \<phi> = join_traces \<nu> \<chi>
                  \<and> local.last \<nu> = first \<chi>"
      apply (rule_tac x = \<sigma> in bexI, auto)
      apply (rule_tac x = "join_traces \<tau> \<phi>" in exI, auto)
      by (metis join_traces_assoc)
    from \<sigma>X \<tau>Y \<phi>Z \<tau>\<phi> \<sigma>\<tau>
    show "\<exists>\<chi>. (\<exists>\<sigma>'\<in>X. \<exists>\<tau>'\<in>Y. \<chi> = join_traces \<sigma>' \<tau>' \<and> local.last \<sigma>' = first \<tau>')
            \<and> (\<exists>\<nu>\<in>Z. join_traces \<sigma> (join_traces \<tau> \<phi>) = join_traces \<chi> \<nu>
              \<and> local.last \<chi> = first \<nu>)"
      apply (rule_tac x = "join_traces \<sigma> \<tau>" in exI, auto)
      apply (rule_tac x = \<phi> in bexI, auto)
      by (metis join_traces_assoc)
  qed

  abbreviation traces :: "('a trace set) mult_ord" where
    "traces \<equiv> \<lparr>carrier = UNIV, le = op \<subseteq>, one = all_tests, mult = join_trace_sets\<rparr>"

  lemma traces_ord: "order traces"
    by (auto simp add: order_def)

  lemma traces_lub [simp]: "\<Sigma>\<^bsub>traces\<^esub> X = \<Union> X"
    apply (simp add: order.lub_simp[OF traces_ord])
    apply (rule the1I2)
    apply (safe, blast, blast)
    apply (metis in_mono)
    by blast+

  lemma "unital_quantale traces"
    apply (simp add: unital_quantale_def, intro conjI)
    apply unfold_locales
    apply (simp_all add: order.is_lub_simp[OF traces_ord] order.is_glb_simp[OF traces_ord])
    apply blast+
    apply (metis UNIV_I typed_abstraction)
    apply (metis join_trace_set_assoc)
    defer defer
    apply (metis join_trace_onel)
    apply (metis join_trace_oner)
    by (auto simp add: join_trace_sets_def all_tests_def)

end
