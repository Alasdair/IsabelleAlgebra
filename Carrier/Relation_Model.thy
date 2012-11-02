theory Relation_Model
  imports Kleene_Algebra KAT Quantale
begin

abbreviation rel_id_ba :: "('a \<times> 'a) set ord" where
  "rel_id_ba \<equiv> \<lparr>carrier = Pow Id, le = op \<subseteq>\<rparr>"

lemma rel_id_ord: "order rel_id_ba"
  by (default, simp_all)

lemmas ba_lub_simp [simp] = order.lub_simp[OF rel_id_ord]
  and ba_is_lub_simp [simp] = order.is_lub_simp[OF rel_id_ord]
  and ba_glb_simp [simp] = order.glb_simp[OF rel_id_ord]
  and ba_is_glb_simp [simp] = order.is_glb_simp[OF rel_id_ord]
  and ba_join_def [simp] = order.join_def[OF rel_id_ord]
  and ba_meet_def [simp] = order.meet_def[OF rel_id_ord]

lemma ba_lub_simp2 [simp]: "X \<subseteq> Pow Id \<Longrightarrow> \<Sigma>\<^bsub>rel_id_ba\<^esub> X = \<Union> X"
  apply simp
  apply (rule the_equality)
  apply safe
  apply blast
  apply blast
  apply blast
  apply (smt PowI Sup_upper Union_Pow_eq Union_mono set_mp)
  apply blast
  done

lemma ba_glb_simp2 [simp]: "X \<subseteq> Pow Id \<Longrightarrow> \<Pi>\<^bsub>rel_id_ba\<^esub> X = \<Inter> X"
  sorry

lemma rel_id_bl: "bounded_lattice rel_id_ba"
  apply default
  apply simp_all
  apply blast+
  apply (rule_tac x = "{}" in bexI)
  apply clarify
  apply (rule the_equality)
  apply blast+
  apply (rule_tac x = "Id" in bexI)
  apply clarify
  apply (rule the_equality)
  apply blast+
  done

lemma rel_id_lattice: "lattice rel_id_ba"
  by (default, simp_all, blast+)

declare ba_lub_simp [simp del]
declare ba_glb_simp [simp del]

lemma rel_id_dist: "distributive_lattice rel_id_ba"
  apply (simp add: distributive_lattice_def distributive_lattice_axioms_def)
  apply safe
  apply (metis rel_id_lattice)
  apply (subgoal_tac "{x \<inter> y , x \<inter> z} \<subseteq> Pow Id", simp, blast)+
  apply (subgoal_tac "{x, y \<inter> z} \<subseteq> Pow Id", simp, blast)+
  done

lemma [simp]: "bounded_lattice.top rel_id_ba = Id"
  apply (simp add: bounded_lattice.top_def[OF rel_id_bl])
  apply (rule the_equality)
  apply blast+
  done

lemma [simp]: "bounded_lattice.bot rel_id_ba = {}"
  apply (simp add: bounded_lattice.bot_def[OF rel_id_bl])
  apply (rule the_equality)
  apply blast+
  done

lemma rel_id_compl: "complemented_lattice rel_id_ba"
  apply (simp add: complemented_lattice_def complemented_lattice_axioms_def)
  apply safe
  apply (metis rel_id_bl)
  apply (rule_tac x = "(- x \<inter> Id)" in exI)
  apply (subgoal_tac "{x, - x \<inter> Id} \<subseteq> Pow Id", simp, blast+)
  done

lemma rel_id_ba: "boolean_algebra rel_id_ba"
  by (simp add: boolean_algebra_def, metis rel_id_compl rel_id_dist)

definition rel_ka :: "('a \<times> 'a) set test" where
  "rel_ka \<equiv> \<lparr>
     carrier = UNIV,
     plus = op \<union>,
     mult = op O,
     one = Id,
     zero = {},
     star = rtrancl,
     test = rel_id_ba
   \<rparr>"

definition rel_ord :: "('a \<times> 'a) set mult_ord" where
  "rel_ord \<equiv> \<lparr>carrier = UNIV, le = op \<subseteq>, one = Id, mult = op O\<rparr>"

lemma rel_ka_dioid: "dioid rel_ka" by (default, auto simp add: rel_ka_def)

lemma rel_ord: "order rel_ord" by (default, simp_all add: rel_ord_def)

lemma rel_cjs: "complete_join_semilattice rel_ord"
  by (default, simp_all add: order.is_lub_simp[OF rel_ord], auto simp add: rel_ord_def)

lemma rel_cms: "complete_meet_semilattice rel_ord"
  by (metis complete_join_semilattice.is_cms rel_cjs)

lemma rel_cl: "complete_lattice rel_ord"
  by (simp add: complete_lattice_def, metis rel_cjs rel_cms)

lemma [simp]: "\<Sigma>\<^bsub>rel_ord\<^esub> X = \<Union> X"
  apply (simp add: order.lub_simp[OF rel_ord])
  apply (rule the1I2)
  apply (simp_all add: rel_ord_def)
  apply safe
  apply (rule_tac x = "\<Union>X" in exI)
  apply blast
  apply blast
  apply (metis in_mono)
  apply blast
  apply blast
  done

lemma [simp]: "x \<squnion>\<^bsub>rel_ord\<^esub> y = x \<union> y" by (simp add: order.join_def[OF rel_ord])

lemma rel_quantale: "unital_quantale rel_ord"
  by (simp add: unital_quantale_def, safe, metis rel_cl, auto simp add: rel_ord_def ftype_pred)

lemma rel_ord_UNIV: "x \<in> carrier rel_ord"
  by (simp add: rel_ord_def)

primrec power :: "('a \<times> 'a) set \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a) set" ("_\<^bsup>_\<^esup>" [101,50] 100) where
  "x\<^bsup>0\<^esup> = Id"
| "x\<^bsup>Suc n\<^esup> = x O x\<^bsup>n\<^esup>"

lemma [simp]: "1\<^bsub>rel_ord\<^esub> = Id" by (simp add: rel_ord_def)

lemma [simp]: "x \<cdot>\<^bsub>rel_ord\<^esub> y = x O y" by (simp add: rel_ord_def)

lemma [simp]: "unital_quantale.power rel_ord x n = x\<^bsup>n\<^esup>"
  apply (induct n)
  apply (simp add: power.simps(1) unital_quantale.power.simps(1)[OF rel_quantale])
  apply (simp add: power.simps(2) unital_quantale.power.simps(2)[OF rel_quantale])
  done

lemma [simp]: "unital_quantale.powers rel_ord x = {y. \<exists>i. y = x\<^bsup>i\<^esup>}"
  by (simp add: unital_quantale.powers_def[OF rel_quantale])

lemma power_comm: "x\<^bsup>n\<^esup> O x = x O x\<^bsup>n\<^esup>" by (induct n, simp, simp add: O_assoc)

lemma [simp]: "unital_quantale.star rel_ord x = x\<^sup>*"
proof (simp add: unital_quantale.star_power[OF rel_quantale rel_ord_UNIV], auto)
  fix a b i assume "(a, b) \<in> x\<^bsup>i\<^esup>"
  thus "(a, b) \<in> x\<^sup>*"
    by (induct i arbitrary: a b, simp, auto, metis converse_rtrancl_into_rtrancl)
next
  fix a b assume x_star: "(a, b) \<in> x\<^sup>*"
  show "\<exists>y. (\<exists>i. y = x\<^bsup>i\<^esup>) \<and> (a, b) \<in> y"
    apply (rule rtrancl.induct[OF x_star, of "\<lambda>a b. \<exists>y. (\<exists>i. y = x\<^bsup>i\<^esup>) \<and> (a, b) \<in> y"])
  proof (metis IdI power.simps(1))
    fix a b c
    assume "\<exists>y. (\<exists>i. y = x\<^bsup>i\<^esup>) \<and> (a, b) \<in> y" and "(b, c) \<in> x"
    then obtain y where "\<exists>i. y = x\<^bsup>i\<^esup>" and "(a, b) \<in> y" by auto
    then obtain i where "y = x\<^bsup>i\<^esup>" by auto
    show  "\<exists>y. (\<exists>i. y = x\<^bsup>i\<^esup>) \<and> (a, c) \<in> y"
    proof (intro exI conjI)
      from `y = x\<^bsup>i\<^esup>` show "y O x = x\<^bsup>Suc i\<^esup>" by (simp add: power_comm)
      from `(a, b) \<in> y` and `(b, c) \<in> x` show "(a, c) \<in> y O x"
        by (metis relcomp.intros)
    qed
  qed
qed

interpretation rq: unital_quantale rel_ord
  where "\<Sigma>\<^bsub>rel_ord\<^esub> X = \<Union> X"
  and "x \<cdot>\<^bsub>rel_ord\<^esub> y = x O y"
  and "x \<squnion>\<^bsub>rel_ord\<^esub> y = x \<union> y"
  and "1\<^bsub>rel_ord\<^esub> = Id"
  and "carrier rel_ord = UNIV"
  and "x \<sqsubseteq>\<^bsub>rel_ord\<^esub> y \<longleftrightarrow> x \<subseteq> y"
  and "unital_quantale.power rel_ord x n = power x n"
  and "unital_quantale.powers rel_ord x = {y. \<exists>i. y = power x i}"
  and "unital_quantale.star rel_ord x = x\<^sup>*"
  by (metis rel_quantale, (simp|simp add: rel_ord_def)+)

lemma rel_ka: "kleene_algebra rel_ka"
  apply (simp add: kleene_algebra_def kleene_algebra_axioms_def, safe)
  apply (simp_all add: dioid.nat_order_def[OF rel_ka_dioid])
  apply (metis rel_ka_dioid)
  apply (simp_all add: rel_ka_def)
  apply (smt Sup_fin.idem r_comp_rtrancl_eq rtrancl_unfold)
  apply (metis rtrancl_unfold sup_idem)
  apply (metis UNIV_I Un_commute inf_sup_ord(4) rq.star_inductl sup_absorb1)
  by (metis UNIV_I Un_commute inf_sup_ord(4) rq.star_inductr sup_absorb1)

lemmas nat_order_simp [simp] = dioid.nat_order_def[OF rel_ka_dioid]

interpretation rka: kleene_algebra rel_ka
  where "dioid.mult rel_ka x y = x O y"
  and "dioid.plus rel_ka x y = x \<union> y"
  and "dioid.one rel_ka = Id"
  and "carrier rel_ka = UNIV"
  and "kleene_algebra.star rel_ka x = x\<^sup>*"
  and "dioid.nat_order rel_ka x y \<longleftrightarrow> x \<subseteq> y"
  and "x \<in> UNIV \<longleftrightarrow> True"
  apply (metis rel_ka, (simp|simp add: rel_ka_def)+, metis subset_Un_eq)
  apply (metis UNIV_I)
  done

lemma helper: "\<forall>x y. f x y = g x y \<Longrightarrow> f = g" by blast

lemma [simp]: "dioid.nat_order rel_ka = op \<subseteq>"
  by (rule helper, simp, simp add: rel_ka_def, metis subset_Un_eq)

hide_fact helper

lemma rel_kat: "kat rel_ka"
  apply (simp add: kat_def kat_axioms_def kat'_def, safe)
  apply (metis rel_ka)
  apply (simp add: rel_ka_def)
  apply (simp add: rel_ka_def)
  apply (simp add: rel_ka_def)
  apply (metis rel_id_ba)
  apply (simp_all add: rel_ka_def)
  sorry

interpretation rkat: kat rel_ka
  where "dioid.mult rel_ka x y = x O y"
  and "dioid.plus rel_ka x y = x \<union> y"
  and "dioid.one rel_ka = Id"
  and "carrier rel_ka = UNIV"
  and "kleene_algebra.star rel_ka x = x\<^sup>*"
  and "dioid.nat_order rel_ka x y \<longleftrightarrow> x \<subseteq> y"
  and "x \<in> UNIV \<longleftrightarrow> True"
  and "tests rel_ka = Pow Id"
  and "kat.complement rel_ka x = (-x \<inter> Id)"
  apply (metis rel_kat)
  sorry
  






















