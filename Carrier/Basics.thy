theory Basics
imports Main Lattice

begin

datatype intplus = inf | neginf | integer int

fun less_eq_intplus :: "intplus \<Rightarrow> intplus \<Rightarrow> bool" where
  "less_eq_intplus neginf _ = True"
| "less_eq_intplus _ inf    = True"
| "less_eq_intplus inf _    = False"
| "less_eq_intplus _ neginf = False"
| "less_eq_intplus (integer x) (integer y) = less_eq x y"

definition INTPLUS :: "intplus ord" ("\<int>+") where
  "\<int>+ \<equiv> \<lparr>carrier = UNIV, le = less_eq_intplus\<rparr>"

lemma intplus_ord: "order \<int>+"
  apply default
  apply (simp_all add: INTPLUS_def)
  apply (metis intplus.exhaust less_eq_intplus.simps(1) less_eq_intplus.simps(2) less_eq_intplus.simps(7) order_refl)
  apply (smt intplus.exhaust less_eq_intplus.simps(1) less_eq_intplus.simps(3) less_eq_intplus.simps(4) less_eq_intplus.simps(5) less_eq_intplus.simps(6) less_eq_intplus.simps(7))
  by (metis intplus.exhaust less_eq_intplus.simps(4) less_eq_intplus.simps(5) less_eq_intplus.simps(6) less_eq_intplus.simps(7) order_antisym)

lemma intplus_total_order: "total_order \<int>+"
  apply (simp add: total_order_def total_order_axioms_def)
  apply safe
  apply (metis intplus_ord)
  apply (simp add: INTPLUS_def)
  by (smt intplus.exhaust less_eq_intplus.simps(1) less_eq_intplus.simps(2) less_eq_intplus.simps(3) less_eq_intplus.simps(7))

lemma intplus_induct:
  assumes base_case: "P (integer k)"
  and inf_case: "P inf"
  and neginf_case: "P neginf"
  and induct_step1: "\<And>i. \<lbrakk>i \<le> k; P (integer i)\<rbrakk> \<Longrightarrow> P (integer (i - 1))"
  and induct_step2: "\<And>i. \<lbrakk>k \<le> i; P (integer i)\<rbrakk> \<Longrightarrow> P (integer (i + 1))"
  shows "P i"
  apply (rule intplus.exhaust[of i])
  apply (metis inf_case)
  apply (metis neginf_case)
  apply (simp)
proof -
  fix n :: int
  show "P (integer n)"
    apply (rule int_induct[of "\<lambda>w. P (integer w)" k n])
    apply (metis base_case)
    apply (metis induct_step2)
    by (metis induct_step1)
qed

lemma intplus_carrier [simp]: "carrier \<int>+ = UNIV"
  by (simp add: INTPLUS_def)

lemma intplus_cjs: "complete_join_semilattice \<int>+"
  sorry

lemma intplus_cms: "complete_meet_semilattice \<int>+"
  sorry

lemma intplus_cl: "complete_lattice \<int>+"
  sorry

typedef Interval
  = "{\<Delta>:: int set . \<Delta> \<subseteq> Ints \<and> (\<forall>t v u. t \<in> \<Delta> \<and> v \<in> \<Delta> \<and> u \<in> Ints \<and> t \<le> u \<and> u \<le> v \<longrightarrow> u \<in> \<Delta>)}"
  by blast

definition interval_set :: "Interval \<Rightarrow> intplus set" where
  "interval_set X = integer ` (Rep_Interval X)"

definition Interval_iso1 :: "Interval \<Rightarrow> intplus \<times> intplus" where
  "Interval_iso1 \<Delta> \<equiv> (\<Pi>\<^bsub>\<int>+\<^esub> (interval_set \<Delta>), \<Sigma>\<^bsub>\<int>+\<^esub> (interval_set \<Delta>))"

abbreviation empty_interval :: "Interval" ("\<emptyset>") where
  "\<emptyset> \<equiv> Abs_Interval {}"

fun Interval_iso2 :: "intplus \<times> intplus \<Rightarrow> Interval" where
  "Interval_iso2 (inf, neginf) = \<emptyset>"
| "Interval_iso2 (x, y) = Abs_Interval {z. x \<sqsubseteq>\<^bsub>\<int>+\<^esub> integer z \<and> integer z \<sqsubseteq>\<^bsub>\<int>+\<^esub> y}"

(*
lemma Interval_iso12: "Interval_iso1 (Interval_iso2 x) = x"
  sorry

lemma Interval_iso21: "Interval_iso2 (Interval_iso1 x) = x"
  sorry
*)

lemma "{} \<in> Interval"
  by (simp add: Interval_def)

lemma "\<int> \<in> Interval"
  by (simp add: Interval_def)

definition wf_interval :: "Interval \<Rightarrow> bool" where
  "wf_interval \<Delta> \<equiv> Rep_Interval \<Delta> \<in> Interval"

abbreviation interval_union :: "Interval \<Rightarrow> Interval \<Rightarrow> Interval" (infix "\<union>" 80) where
  "d1 \<union> d2 \<equiv> Abs_Interval (Rep_Interval d1 \<union> Rep_Interval d2)"

abbreviation interval_intersection :: "Interval \<Rightarrow> Interval \<Rightarrow> Interval" (infix "\<inter>" 80) where
  "d1 \<inter> d2 \<equiv> Abs_Interval (Rep_Interval d1 \<inter> Rep_Interval d2)"

lemma empty_wf: "wf_interval \<emptyset>"
  by (metis Rep_Interval wf_interval_def)

lemma intersection_wf: "\<lbrakk>wf_interval d1; wf_interval d2\<rbrakk> \<Longrightarrow> wf_interval (d1 \<inter> d2)"
  by (metis Rep_Interval wf_interval_def)

primrec dec :: "intplus \<Rightarrow> intplus" where
  "dec inf = inf"
| "dec neginf = neginf"
| "dec (integer x) = integer (x - 1)"

lemma union_wf_iso: "\<lbrakk>wf_interval d1; wf_interval d2; snd (Interval_iso1 d1) = dec (fst (Interval_iso d2))\<rbrakk> \<Longrightarrow> wf_interval (d1 \<union> d2)"
  by (metis Rep_Interval wf_interval_def)

type_synonym Var = nat

type_synonym Val = nat

type_synonym State = "Var \<Rightarrow> Val"

type_synonym StatePred = "State \<Rightarrow> bool"

type_synonym Time = int

type_synonym Stream = "Time \<Rightarrow> State"

type_synonym IntervalPred = "Interval \<Rightarrow> Stream \<Rightarrow> bool"

definition empty :: "IntervalPred" where
  "empty \<equiv> \<lambda>\<Delta> s. \<Delta> = \<emptyset>"

definition false :: "IntervalPred" where
  "false \<equiv> \<lambda>\<Delta> s. False"

definition adjoins :: "Interval \<Rightarrow> Interval \<Rightarrow> bool" where
  "adjoins \<Delta> \<Gamma> \<equiv> (\<Delta> \<noteq> \<emptyset>) \<and> (\<Gamma> \<noteq> \<emptyset>) \<longrightarrow> (\<Sigma>\<^bsub>\<int>+\<^esub>(interval_set \<Delta>) \<sqsubset>\<^bsub>\<int>+\<^esub> \<Pi>\<^bsub>\<int>+\<^esub>(interval_set \<Gamma>)) \<and> ((\<Delta> \<inter> \<Gamma>) \<noteq> \<emptyset>) \<and> wf_interval (\<Delta> \<union> \<Gamma>)"

lemma "adjoins \<Delta> \<emptyset>"
  by (simp add: adjoins_def)

lemma "adjoins \<emptyset> \<Delta>"
  by (simp add: adjoins_def)

lemma wf_union: "adjoins d1 d2 \<Longrightarrow> wf_interval (d1 \<union> d2)"
  by (metis Rep_Interval wf_interval_def)

definition Inf :: "IntervalPred" where
  "Inf \<equiv> \<lambda>\<Delta> s. \<Sigma>\<^bsub>\<int>+\<^esub> (interval_set \<Delta>) = inf"

definition Fin :: "IntervalPred" where
  "Fin \<equiv> \<lambda>\<Delta> s. \<not> (Inf \<Delta> s)"

definition true :: "IntervalPred" where
  "true \<equiv> \<lambda>\<Delta> s. True"

definition box :: "IntervalPred \<Rightarrow> IntervalPred" ("\<box>") where
  "box P \<equiv> \<lambda>\<Delta> s. \<forall>d. Rep_Interval d \<subseteq> Rep_Interval \<Delta> \<longrightarrow> P d s"

definition diamond :: "IntervalPred \<Rightarrow> IntervalPred" ("\<diamond>") where
  "diamond P \<equiv> \<lambda>\<Delta> s. \<exists>d. Rep_Interval d \<subseteq> Rep_Interval \<Delta> \<and> P d s"

definition not_ip :: "IntervalPred \<Rightarrow> IntervalPred" ("\<not>")  where
  "not_ip P \<equiv> \<lambda>\<Delta> s. \<not> (P \<Delta> s)"

lemma box_diamond_dual: "\<box>P = \<not>(\<diamond> (\<not>P))"
  by (simp add: diamond_def box_def not_ip_def)

definition box_dot :: "StatePred \<Rightarrow> IntervalPred" where
  "box_dot C \<equiv> \<lambda>\<Delta> s. \<forall>t\<in>(Rep_Interval \<Delta>). C (s t)"

definition diamond_dot :: "StatePred \<Rightarrow> IntervalPred" where
  "diamond_dot C \<equiv> \<lambda>\<Delta> s.  \<exists>t\<in>(Rep_Interval \<Delta>). C (s t)"

definition not_sp :: "StatePred \<Rightarrow> StatePred" ("\<not>") where
  "not_sp C \<equiv> \<lambda>s. \<not> (C s)"

lemma box_diamond_dot_dual: "box_dot C = \<not> (diamond_dot (\<not> C))"
  by (simp add: diamond_dot_def box_dot_def not_sp_def not_ip_def)

definition chop :: "IntervalPred \<Rightarrow> IntervalPred \<Rightarrow> IntervalPred" (infix ";" 70) where
  "chop P1 P2 \<equiv> \<lambda>\<Delta> s. (\<exists>d1 d2. d1 \<union> d2 = \<Delta> \<and> adjoins d1 d2 \<and> P1 d1 s \<and> P2 d2 s) \<or> (Inf \<Delta> s \<and> P1 \<Delta> s)"

definition entails_ip :: "IntervalPred \<Rightarrow> IntervalPred \<Rightarrow> bool" (infixr "\<turnstile>" 60) where
  "P1 \<turnstile> P2 \<equiv> \<forall>\<Delta> s. P1 \<Delta> s \<longrightarrow> P2 \<Delta> s"

lemma "(\<forall>x. f x = g x) \<longleftrightarrow> f = g"
  by auto

lemma equiv_ip: assumes a: "P1 \<turnstile> P2" and b: "P2 \<turnstile> P1" shows "P1 = P2"
proof -
  have "\<forall>\<Delta> s. P1 \<Delta> s \<longleftrightarrow> P2 \<Delta> s"
    apply (insert a b)
    apply (simp add: entails_ip_def)
    by auto
  thus "P1 = P2" by auto
qed

lemma helper: "\<Delta> \<union> \<emptyset> = \<Delta>"
proof -
  have a: "wf_interval \<Delta>"
    by (metis Rep_Interval wf_interval_def)
  have "adjoins \<Delta> \<emptyset>"
    by (metis adjoins_def)
  hence "wf_interval (\<Delta> \<union> \<emptyset>)"
    by (metis wf_union)
  thus ?thesis
    sorry
qed

lemma unit_helper: "(\<exists>d2 d1. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> P d1 s \<and> empty d2 s) = P \<Delta> s"
proof -
  have "(\<exists>d2 d1. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> P d1 s \<and> empty d2 s) = (\<exists>d1. adjoins d1 \<emptyset> \<and> d1 = \<Delta> \<and> P d1 s)"
    apply default
    defer
    apply (rule_tac x = "\<emptyset>" in exI)
    apply (metis Basics.empty_def Rep_Interval helper wf_interval_def)
    by (metis (no_types) Basics.empty_def Rep_Interval helper wf_interval_def)
  moreover have "... = (\<exists>d1. (d1 = \<Delta>) \<and> P d1 s)"
    by (metis adjoins_def)
  moreover have "... = P \<Delta> s" by simp
  ultimately show ?thesis
    by auto
qed

lemma right_unit: "(P ; empty) = P"
proof -
  have "\<And>\<Delta> s. (P ; empty) \<Delta> s = P \<Delta> s"
  proof -
    fix \<Delta> s
    show "(P ; empty) \<Delta> s = P \<Delta> s"
      by (cases "Inf \<Delta> s", (metis chop_def unit_helper)+)
  qed
  thus ?thesis by auto
qed

lemma inf_not_empty: "Inf \<Delta> s \<Longrightarrow> (\<not> empty) \<Delta> s" sorry

lemma contradiction_ip: "\<lbrakk>P \<Delta> s; (\<not> P) \<Delta> s\<rbrakk> \<Longrightarrow> False"
  by (simp add: not_ip_def)

lemma left_unit: "(empty ; P) = P"
proof -
  have "\<And>\<Delta> s. (empty ; P) \<Delta> s = P \<Delta> s"
  proof -
    fix \<Delta> s
    have "(empty ; P) \<Delta> s = (\<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> empty d1 s \<and> P d2 s)"
      by (smt chop_def contradiction_ip inf_not_empty)
    moreover have "... = (\<exists>d2. adjoins \<emptyset> d2 \<and> d2 = \<Delta> \<and> P d2 s)"
      by (metis Basics.empty_def helper sup_commute)
    moreover have "... = P \<Delta> s"
      by (metis (lifting) adjoins_def)
    ultimately show "(empty ; P) \<Delta> s = P \<Delta> s" by auto
  qed
  thus ?thesis by auto
qed

abbreviation IP_LATTICE :: "IntervalPred ord" ("\<Psi>") where
  "\<Psi> \<equiv> \<up> (\<up> BOOL)"

lemma ip_cjs: "complete_join_semilattice IP_LATTICE"
  by (metis bool_cjs extend_cjs)

lemma ip_cl: "complete_lattice IP_LATTICE"
  by (metis bool_cl extend_cl)

lemma ip_cbl: "complete_boolean_lattice IP_LATTICE"
  by (metis bool_cbl extend_cbl)

lemma extend_lub_var:
  assumes cjs_A: "complete_join_semilattice A" and F_subset: "F \<subseteq> carrier (\<up> A)"
  shows "(\<Sigma>\<^bsub>\<up> A\<^esub> F) x = \<Sigma>\<^bsub>A\<^esub> ((\<lambda>f. f x) ` F)"
  by (smt F_subset cjs_A complete_join_semilattice.is_lub_lub complete_join_semilattice.lub_ex_var extend_cjs extend_lub image_cong)

lemma extend_lub_var_2:
  assumes cjs_A: "complete_join_semilattice A" and F_subset: "F \<subseteq> carrier (\<up> (\<up> A))"
  shows "(\<Sigma>\<^bsub>\<up> (\<up> A)\<^esub> F) x y = \<Sigma>\<^bsub>A\<^esub> ((\<lambda>f. f x y) ` F)"
proof -
  have cjs_A_ex: "complete_join_semilattice (\<up> A)"
    by (metis cjs_A extend_cjs)
  have a: "((\<lambda>f. f x) ` F) \<subseteq> carrier (\<up> A)"
    apply safe
    apply (insert F_subset, simp add: pointwise_extension_def)
    by (metis UNIV_I set_mp typed_application)
  show ?thesis
    apply (simp add: extend_lub_var[OF cjs_A_ex F_subset])
    apply (simp add: extend_lub_var[OF cjs_A a])
    apply (simp add: image_def)
    by (smt Collect_cong)
qed

lemma bool_lub:
  shows "\<Sigma>\<^bsub>BOOL\<^esub> X = (\<exists>x\<in>X. x)"
  apply (simp add: order.lub_simp[OF bool_ord])
  apply (simp add: BOOL_def)
  apply (rule the1I2)
  by auto

lemma ip_inf_distl:
  assumes Q_subset: "Q \<subseteq> carrier \<Psi>"
  shows "\<Sigma>\<^bsub>\<Psi>\<^esub> Q ; p = \<Sigma>\<^bsub>\<Psi>\<^esub> ((\<lambda>q. q ; p) ` Q)"
proof -
  have cjs_bool_ex: "complete_join_semilattice (\<up> BOOL)"
    by (metis bool_cjs extend_cjs)

  have "\<forall>\<Delta> s. ((\<Sigma>\<^bsub>\<Psi>\<^esub> Q) ; p) \<Delta> s = (\<Sigma>\<^bsub>\<Psi>\<^esub> ((\<lambda>q. q ; p) ` Q)) \<Delta> s"
  proof (intro allI)
    fix \<Delta> s

    have helper: "((\<lambda>q. q ; p) ` Q) \<subseteq> carrier \<Psi>"
      apply (insert Q_subset, simp add: pointwise_extension_def)
      apply clarsimp
      apply (simp add: chop_def)
      by (smt bool_bot bool_cjs complete_join_semilattice.bot_closed eqelem_imp_iff ftype_pred iso_tuple_UNIV_I set_rev_mp)

    have "(\<Sigma>\<^bsub>\<Psi>\<^esub>Q ; p) \<Delta> s = ((\<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> (\<Sigma>\<^bsub>\<Psi>\<^esub> Q) d1 s \<and> p d2 s) \<or> (Inf \<Delta> s \<and> (\<Sigma>\<^bsub>\<Psi>\<^esub> Q) \<Delta> s))"
      by (simp add: chop_def, auto)
    moreover have "... = ((\<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> (\<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. q d1 s) ` Q)) \<and> p d2 s) \<or> (Inf \<Delta> s \<and> (\<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. q \<Delta> s) ` Q))))"
      by (simp add: extend_lub_var_2[OF bool_cjs Q_subset])
    moreover have "... = (\<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. \<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> q d1 s  \<and> p d2 s) ` Q) \<or> \<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. Inf \<Delta> s \<and> q \<Delta> s) ` Q))"
      by (simp add: bool_lub, safe, metis+)
    moreover have "... = \<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. (\<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> q d1 s  \<and> p d2 s) \<or> (Inf \<Delta> s \<and> q \<Delta> s)) ` Q)"
      by (simp add: bool_lub, safe, metis+)
    moreover have "... = \<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. (q ; p) \<Delta> s) ` Q)"
      by (simp add: chop_def, rule_tac f = "\<lambda>a. \<Sigma>\<^bsub>BOOL\<^esub>(a ` Q)" in arg_cong, default, auto)
    moreover have "... = (\<Sigma>\<^bsub>\<Psi>\<^esub> ((\<lambda>q. q ; p) ` Q)) \<Delta> s"
      by (simp add: extend_lub_var_2[OF bool_cjs helper], simp add: image_def, smt Collect_cong)
    ultimately show "((\<Sigma>\<^bsub>\<Psi>\<^esub> Q) ; p) \<Delta> s = (\<Sigma>\<^bsub>\<Psi>\<^esub> ((\<lambda>q. q ; p) ` Q)) \<Delta> s"
      by auto
  qed
  thus ?thesis by auto
qed

lemma ip_inf_distr:
  assumes Q_subset: "Q \<subseteq> carrier \<Psi>" and Q_ne: "Q \<noteq> {}"
  shows "p ; \<Sigma>\<^bsub>\<Psi>\<^esub> Q = \<Sigma>\<^bsub>\<Psi>\<^esub> ((\<lambda>q. p ; q) ` Q)"
proof -
  have cjs_bool_ex: "complete_join_semilattice (\<up> BOOL)"
    by (metis bool_cjs extend_cjs)
    
  have "\<forall>\<Delta> s. (p ; (\<Sigma>\<^bsub>\<Psi>\<^esub> Q)) \<Delta> s = (\<Sigma>\<^bsub>\<Psi>\<^esub> ((\<lambda>q. p ; q) ` Q)) \<Delta> s"
  proof (intro allI)
    fix \<Delta> s

    have helper: "((\<lambda>q. p ; q) ` Q) \<subseteq> carrier \<Psi>"
      apply (insert Q_subset, simp add: pointwise_extension_def)
      apply clarsimp
      apply (simp add: chop_def)
      sorry

    have "(p ; \<Sigma>\<^bsub>\<Psi>\<^esub>Q) \<Delta> s = ((\<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> (\<Sigma>\<^bsub>\<Psi>\<^esub> Q) d2 s \<and> p d1 s) \<or> (Inf \<Delta> s \<and> p \<Delta> s))"
      by (simp add: chop_def, auto)
    moreover have "... = ((\<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> (\<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. q d2 s) ` Q)) \<and> p d1 s) \<or> (Inf \<Delta> s \<and> p \<Delta> s))"
      by (simp add: extend_lub_var_2[OF bool_cjs Q_subset])
    moreover have "... = (\<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. \<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> q d2 s  \<and> p d1 s) ` Q) \<or> (Inf \<Delta> s \<and> p \<Delta> s))"
      by (simp add: bool_lub, auto)
    moreover have "... = \<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. (\<exists>d1 d2. adjoins d1 d2 \<and> d1 \<union> d2 = \<Delta> \<and> q d2 s  \<and> p d1 s) \<or> (Inf \<Delta> s \<and> p \<Delta> s)) ` Q)"
      by (simp add: bool_lub, auto, metis Q_ne ex_in_conv) (* This is where Q_ne is used *)
    moreover have "... = \<Sigma>\<^bsub>BOOL\<^esub> ((\<lambda>q. (p ; q) \<Delta> s) ` Q)"
      by (simp add: chop_def, rule_tac f = "\<lambda>a. \<Sigma>\<^bsub>BOOL\<^esub>(a ` Q)" in arg_cong, default, auto)
    moreover have "... = (\<Sigma>\<^bsub>\<Psi>\<^esub> ((\<lambda>q. p ; q) ` Q)) \<Delta> s"
      by (simp add: extend_lub_var_2[OF bool_cjs helper], simp add: image_def, smt Collect_cong)
    ultimately show "(p ; (\<Sigma>\<^bsub>\<Psi>\<^esub> Q)) \<Delta> s = (\<Sigma>\<^bsub>\<Psi>\<^esub> ((\<lambda>q. p ; q) ` Q)) \<Delta> s"
      by auto
  qed
  thus ?thesis by auto
qed
      
sledgehammer min [spass] (Rep_Interval_inject Un_commute)
      
      apply (simp add: complete_distrib simp_help)
      
      
      
      

instantiation IntervalPred :: order
begin

lemma "empty_ip ; P = P"
  apply (simp add: chop_def empty_ip_def)

definition ftype :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<rightarrow>" 60) where
  "ftype A B \<equiv> {f. \<forall>x. x \<in> A \<longrightarrow> f x \<in> B}"

lemma typed_composition: "\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C\<rbrakk> \<Longrightarrow> g \<circ> f \<in> A \<rightarrow> C"
  by (simp add: ftype_def)

lemma typed_application: "\<lbrakk>x \<in> A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> f x \<in> B"
  by (simp add: ftype_def)


type_synonym Addr = nat

typedecl Val
datatype Valbool = Val | bool 
typedecl Var
typedecl Field 

definition State :: "Var set \<Rightarrow> Val set => (Var \<Rightarrow> Val) set" where
  "State var val \<equiv> var \<rightarrow> val"

definition StatePredicate :: "(Var \<Rightarrow> Val) set \<Rightarrow> bool" where
  "StatePredicate X \<equiv> "




type_synonym Addr = nat

typedecl Val
datatype Valplus = Val | Addr | bool 
typedecl Var
typedecl Field



definition Heap :: "Addr set \<Rightarrow> Valplus set \<Rightarrow> (Addr \<Rightarrow> Valplus) set" where
  "Heap A B \<equiv> ftype A B"

definition Store :: "Var set \<Rightarrow> Valplus set \<Rightarrow> (Var \<Rightarrow> Valplus) set" where
  "Store V B \<equiv> ftype V B"



(*type_synonym Heap = "Addr \<Rightarrow> Valplus"
type_synonym Store = "Var \<Rightarrow> Valplus"*)
definition State :: "Var set => Addr set \<Rightarrow> Valplus set \<Rightarrow> ((Var \<Rightarrow> Valplus) set \<times> (Addr \<Rightarrow> Valplus) set)" where 
"State V A B \<equiv> (Store V B) \<times> (Heap A B)"

type_synonym StoreExpr = "Store \<Rightarrow> Valplus"

datatype HeapExpr = hAddr Addr | hStar HeapExpr | hOffset HeapExpr 

datatype StateExpr = sHeapExpr HeapExpr | sConstant Val | sVar Var | sField Field

type_synonym Time = int

type_synonym Stream = "Time \<Rightarrow> State"


f \<in> X \<rightarrow> B



end
