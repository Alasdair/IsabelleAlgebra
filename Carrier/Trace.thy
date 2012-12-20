theory Trace
  imports Quantale
begin



datatype ('a, 'b) trace = tlink 'a 'b "('a, 'b) trace" | tend 'a

fun fusion_product :: "('a, 'b) trace \<Rightarrow> ('a, 'b) trace \<Rightarrow> ('a, 'b) trace" where
  "fusion_product (tlink u p \<sigma>) \<tau> = tlink u p (fusion_product \<sigma> \<tau>)"
| "fusion_product (tend u) \<tau> = \<tau>"

fun first :: "('a, 'b) trace \<Rightarrow> 'a" where
  "first (tlink u _ _) = u"
| "first (tend u)      = u"

fun last :: "('a, 'b) trace \<Rightarrow> 'a" where
  "last (tlink _ _ \<sigma>) = last \<sigma>"
| "last (tend u)      = u"

definition fuse :: "('a, 'b) trace set \<Rightarrow> ('a, 'b) trace set \<Rightarrow> ('a, 'b) trace set" where
  "fuse X Y = {Z. \<exists>\<sigma>\<in>X. \<exists>\<tau>\<in>Y. Z = fusion_product \<sigma> \<tau> \<and> last \<sigma> = first \<tau>}"

definition all_tests :: "('a, 'b) trace set" where
  "all_tests = tend ` UNIV"

lemma fuse_onel: "fuse all_tests X = X"
  by (auto simp add: fuse_def all_tests_def)

lemma fuse_oner: "fuse X all_tests = X"
  apply (auto simp add: fuse_def all_tests_def)
proof -
  fix \<sigma> :: "('a, 'b) trace" assume "\<sigma> \<in> X"
  thus "fusion_product \<sigma> (tend (last \<sigma>)) \<in> X"
    by (induct \<sigma> arbitrary: X, auto)
  from `\<sigma> \<in> X` show "\<exists>\<tau>\<in>X. \<sigma> = fusion_product \<tau> (tend (last \<tau>))"
    by (rule_tac x = \<sigma> in bexI, induct \<sigma> arbitrary: X, auto)
qed

lemma fusion_last [simp]: "last (fusion_product \<sigma> \<tau>) = last \<tau>"
  by (induct \<sigma>, auto)

lemma fusion_first [simp]: "last \<sigma> = first \<tau> \<Longrightarrow> first (fusion_product \<sigma> \<tau>) = first \<sigma>"
  by (induct \<sigma>, auto)

lemma fusion_assoc: "fusion_product (fusion_product \<sigma> \<tau>) \<phi> = fusion_product \<sigma> (fusion_product \<tau> \<phi>)"
  by (induct \<sigma>, auto)

lemma fuse_assoc:
  "fuse (fuse X Y) Z = fuse X (fuse Y Z)"
proof (auto simp add: fuse_def)
  fix \<sigma> \<tau> \<phi>
  assume \<sigma>X: "\<sigma> \<in> X" and \<tau>Y: "\<tau> \<in> Y " and \<phi>Z: "\<phi> \<in> Z"
  and \<tau>\<phi>: "last \<tau> = first \<phi>"
  and \<sigma>\<tau>: "last \<sigma> = first \<tau>"
  thus "\<exists>\<nu>\<in>X. \<exists>\<chi>. (\<exists>\<sigma>'\<in>Y. \<exists>\<tau>'\<in>Z. \<chi> = fusion_product \<sigma>' \<tau>' \<and> last \<sigma>' = first \<tau>')
                  \<and> fusion_product (fusion_product \<sigma> \<tau>) \<phi> = fusion_product \<nu> \<chi>
                  \<and> last \<nu> = first \<chi>"
    apply (rule_tac x = \<sigma> in bexI, auto)
    apply (rule_tac x = "fusion_product \<tau> \<phi>" in exI, auto)
    by (metis fusion_assoc)
  from \<sigma>X \<tau>Y \<phi>Z \<tau>\<phi> \<sigma>\<tau>
  show "\<exists>\<chi>. (\<exists>\<sigma>'\<in>X. \<exists>\<tau>'\<in>Y. \<chi> = fusion_product \<sigma>' \<tau>' \<and> last \<sigma>' = first \<tau>')
          \<and> (\<exists>\<nu>\<in>Z. fusion_product \<sigma> (fusion_product \<tau> \<phi>) = fusion_product \<chi> \<nu>
            \<and> last \<chi> = first \<nu>)"
    apply (rule_tac x = "fusion_product \<sigma> \<tau>" in exI, auto)
    apply (rule_tac x = \<phi> in bexI, auto)
    by (metis fusion_assoc)
qed

fun trace_states :: "('a, 'b) trace \<Rightarrow> 'a list" where
  "trace_states (tlink s u \<sigma>) = (s # trace_states \<sigma>)"
| "trace_states (tend s)      = [s]"

fun trace_transitions :: "('a, 'b) trace \<Rightarrow> 'b list" where
  "trace_transitions (tlink s u \<sigma>) = (u # trace_transitions \<sigma>)"
| "trace_transitions (tend s)      = []"

abbreviation traces :: "('a, 'b) trace set \<Rightarrow> ('a, 'b) trace set mult_ord" where
  "traces X \<equiv> \<lparr>carrier = Pow X, le = op \<subseteq>, one = all_tests, mult = fuse\<rparr>"

lemma traces_ord: "order (traces X)"
  by (auto simp add: order_def)

lemma traces_lub [simp]: "X \<subseteq> Pow Y \<Longrightarrow> \<Sigma>\<^bsub>traces Y\<^esub> X = \<Union> X"
  apply (simp add: order.lub_simp[OF traces_ord], rule the1I2)
  apply safe
  apply blast
  apply (metis PowI in_mono)
  apply (metis PowI in_mono)
  apply (metis PowI Sup_upper UnionI Union_Pow_eq Union_mono)
  apply (metis set_mp)
  done

lemma traces_cjs: "complete_join_semilattice (traces X)"
  by (unfold_locales, auto simp add: order.is_lub_simp[OF traces_ord])

lemma traces_cms: "complete_meet_semilattice (traces X)"
  by (rule complete_join_semilattice.is_cms[OF traces_cjs])

lemma traces_cl: "complete_lattice (traces X)"
  by (simp add: complete_lattice_def traces_cjs traces_cms)

lemma traces_quantale:
  assumes fuse_type: "fuse \<in> Pow X \<rightarrow> Pow X \<rightarrow> Pow X"
  and all_tests_in_X: "all_tests \<subseteq> X"
  shows "unital_quantale (traces X)"
proof (simp add: unital_quantale_def, intro conjI)
  show "complete_lattice (traces X)"
    by (rule traces_cl)

  show "fuse \<in> Pow X \<rightarrow> Pow X \<rightarrow> Pow X"
    by (rule fuse_type)

  show "\<forall>x\<subseteq>X. \<forall>y\<subseteq>X. \<forall>z\<subseteq>X. fuse (fuse x y) z = fuse x (fuse y z)"
    by (metis fuse_assoc)

  from fuse_type show "\<forall>x\<subseteq>X. \<forall>Y\<subseteq>Pow X. fuse x (\<Union>Y) = \<Sigma>\<^bsub>traces X\<^esub>(fuse x ` Y)"
    apply (clarify, subgoal_tac "(fuse x ` Y) \<subseteq> Pow X", simp add: fuse_def, blast)
    by (simp add: ftype_pred, clarify, smt Pow_iff set_mp)

  from fuse_type show "\<forall>x\<subseteq>X. \<forall>Y\<subseteq>Pow X. fuse (\<Union>Y) x = \<Sigma>\<^bsub>traces X\<^esub>((\<lambda>y. fuse y x) ` Y)"
    apply (clarify, subgoal_tac "((\<lambda>y. fuse y x) ` Y) \<subseteq> Pow X", simp add: fuse_def, blast)
    by (simp add: ftype_pred, clarify, smt Pow_iff set_mp)

  show "all_tests \<subseteq> X"
    by (rule all_tests_in_X)

  show "\<forall>x\<subseteq>X. fuse all_tests x = x"
    by (metis fuse_onel)

  show "\<forall>x\<subseteq>X. fuse x all_tests = x"
    by (metis fuse_oner)
qed

lemma traces_quantale_UNIV: "unital_quantale (traces UNIV)"
  by (rule traces_quantale, simp add: ftype_pred, rule subset_UNIV)

end


