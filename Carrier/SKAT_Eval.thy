theory SKAT_Eval
  imports SKAT
begin

type_synonym 'a mems = "(nat \<Rightarrow> 'a) set"

fun eval_bexpr ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a wf_pred bexpr \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> bool"
  where
  "eval_bexpr D (BLeaf P) mem = eval_wf_pred D mem P"
| "eval_bexpr D (P :+: Q) mem = (eval_bexpr D P mem \<or> eval_bexpr D Q mem)"
| "eval_bexpr D (P :\<cdot>: Q) mem = (eval_bexpr D P mem \<and> eval_bexpr D Q mem)"
| "eval_bexpr D (BNot P) mem = (\<not> eval_bexpr D P mem)"
| "eval_bexpr D BOne mem = True"
| "eval_bexpr D BZero mem = False"

definition filter_set :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "filter_set p X \<equiv> \<Union>x\<in>X. if p x then {x} else {}"

definition set_mems :: "nat \<Rightarrow> ('a mem \<Rightarrow> 'a) \<Rightarrow> 'a mems \<Rightarrow> 'a mems" where
  "set_mems x f \<Delta> \<equiv> (\<lambda>mem. set_mem x (f mem) mem) ` \<Delta>"

definition wf_assigns ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> nat \<Rightarrow> 'a wf_trm \<Rightarrow> 'b mems \<Rightarrow> 'b mems"
  where
  "wf_assigns D x s mems = set_mems x (\<lambda>mem. eval_wf_trm D mem s) mems"

lemma finite_set_mems: assumes "finite \<Delta>" shows "finite (set_mems x f \<Delta>)"
  by (induct rule: finite_subset_induct_var[OF assms(1), of "\<Delta>"], simp_all add: set_mems_def)

lemma card_set_mems: "finite \<Delta> \<Longrightarrow> card (set_mems X f \<Delta>) \<le> card \<Delta>"
  by (simp add: set_mems_def, smt card_image_le)

lemma wf_assign_image: "wf_assigns D x t mems = wf_assign D x t ` mems"
  by (auto simp add: wf_assigns_def set_mems_def wf_assign_def[symmetric])

lemma eval_wf_assigns1:
  assumes xy: "x \<noteq> y" and ys: "y \<notin> FV s"
  shows "wf_assigns D y t (wf_assigns D x s mems) = wf_assigns D x s (wf_assigns D y (t[x|s]) mems)"
  by (auto simp add: wf_assign_image image_def, (metis eval_wf_assign1 xy ys)+)

lemma eval_wf_assigns2:
  assumes xy: "x \<noteq> y" and xs: "x \<notin> FV s"
  shows "wf_assigns D y t (wf_assigns D x s mems) =
         wf_assigns D y (t[x|s]) (wf_assigns D x s mems)"
  by (auto simp add: wf_assign_image image_def, (metis eval_wf_assign2 xy xs)+)

lemma eval_wf_assigns3: "wf_assigns D x t (wf_assigns D x s mems) = wf_assigns D x (t[x|s]) mems"
  by (auto simp add: wf_assign_image image_def, (metis eval_wf_assign3)+)

fun eval_skat_expr ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a skat_expr \<Rightarrow> 'b mems \<Rightarrow> 'b mems"
  where
  "eval_skat_expr D (SKLeaf x s) \<Delta> = wf_assigns D x s \<Delta>"
| "eval_skat_expr D (SKBool P) \<Delta> = filter_set (eval_bexpr D P) \<Delta>"
| "eval_skat_expr D (s :\<odot>: t) \<Delta> = eval_skat_expr D t (eval_skat_expr D s \<Delta>)"
| "eval_skat_expr D (s :\<oplus>: t) \<Delta> = eval_skat_expr D s \<Delta> \<union> eval_skat_expr D t \<Delta>"
| "eval_skat_expr D (SKStar s) \<Delta> = (\<Union>n. iter n (eval_skat_expr D s) \<Delta>)"
| "eval_skat_expr D SKOne \<Delta> = \<Delta>"
| "eval_skat_expr D SKZero \<Delta> = {}"

definition eval_power :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a skat_expr \<Rightarrow> nat \<Rightarrow> 'b mems \<Rightarrow> 'b mems"
  where "eval_power D s n \<Delta> = iter n (eval_skat_expr D s) \<Delta>"

lemma eval_star_power: "eval_skat_expr D (SKStar s) \<Delta> = \<Union> {y. \<exists>n. y = eval_power D s n \<Delta>}"
  by (auto simp add: eval_power_def)

lemma eval_iter1: "eval_skat_expr D s (iter n (eval_skat_expr D s) \<Delta>)
     = iter n (eval_skat_expr D s) (eval_skat_expr D s \<Delta>)"
  by (induct n, auto)

lemma eval_mod1: "eval_skat_expr D s {} = {}"
proof (induct s, simp_all add: wf_assigns_def set_mems_def, intro allI)
  fix s n assume "eval_skat_expr D s {} = {}"
  thus "iter n (eval_skat_expr D s) {} = {}"
    by (induct n, auto)
next
  fix P show "filter_set (eval_bexpr D P) {} = {}"
    by (induct P, auto simp add: filter_set_def)
qed

lemma eval_mod2: "eval_skat_expr D s (\<Delta> \<union> \<Gamma>) = eval_skat_expr D s \<Delta> \<union> eval_skat_expr D s \<Gamma>"
  apply (induct s arbitrary: \<Delta> \<Gamma>, simp_all add: wf_assigns_def set_mems_def filter_set_def)
  apply (metis image_Un)
  apply (metis Un_assoc Un_left_commute)
proof -
  fix s \<Delta> \<Gamma>
  assume asm: "\<And>\<Delta> \<Gamma>. eval_skat_expr D s (\<Delta> \<union> \<Gamma>) = eval_skat_expr D s \<Delta> \<union> eval_skat_expr D s \<Gamma>"
  have "\<And>n. iter n (eval_skat_expr D s) (\<Delta> \<union> \<Gamma>) = iter n (eval_skat_expr D s) \<Delta> \<union> iter n (eval_skat_expr D s) \<Gamma>"
  proof -
    fix n
    show "iter n (eval_skat_expr D s) (\<Delta> \<union> \<Gamma>) = iter n (eval_skat_expr D s) \<Delta> \<union> iter n (eval_skat_expr D s) \<Gamma>"
      by (induct n, simp_all, metis asm)
  qed
  hence "(\<Union>n. iter n (eval_skat_expr D s) (\<Delta> \<union> \<Gamma>)) = (\<Union>n. iter n (eval_skat_expr D s) \<Delta> \<union> iter n (eval_skat_expr D s) \<Gamma>)"
    by auto
  thus "(\<Union>n. iter n (eval_skat_expr D s) (\<Delta> \<union> \<Gamma>)) =
        (\<Union>n. iter n (eval_skat_expr D s) \<Delta>) \<union>
        (\<Union>n. iter n (eval_skat_expr D s) \<Gamma>)"
    by auto
qed

lemma eval_mod3: "eval_skat_expr D r b \<union> a \<union> b = b \<Longrightarrow> eval_skat_expr D (SKStar r) a \<union> b = b"
proof simp
  assume asm: "eval_skat_expr D r b \<union> a \<union> b = b"
  have "\<And>n. iter n (eval_skat_expr D r) a \<union> b = b"
  proof -
    fix n show "iter n (eval_skat_expr D r) a \<union> b = b"
      apply (induct n)
      apply (simp, metis Un_assoc Un_commute asm sup.left_idem)
      by (simp, metis (no_types) asm eval_mod2 sup.assoc)
  qed
  thus "(\<Union>n. iter n (eval_skat_expr D r) a) \<union> b = b"
    by blast
qed

lemma eval_iter:
  "iter n (eval_skat_expr D x) (eval_skat_expr D x \<Delta>) = iter (Suc n) (eval_skat_expr D x) \<Delta>"
  by (induct n, auto)

lemma eval_star_unfoldl:
  fixes \<Delta> :: "'b mems"
  shows "eval_skat_expr D (SKOne :\<oplus>: x :\<odot>: SKStar x :\<oplus>: SKStar x) \<Delta> = eval_skat_expr D (SKStar x) \<Delta>"
proof auto
  fix mem :: "'b mem" assume "mem \<in> \<Delta>"
  thus "\<exists>n. mem \<in> iter n (eval_skat_expr D x) \<Delta>"
    by (rule_tac x = 0 in exI, simp)
next
  fix mem :: "'b mem" and n
  assume "mem \<in> iter n (eval_skat_expr D x) (eval_skat_expr D x \<Delta>)"
  thus "\<exists>n. mem \<in> iter n (eval_skat_expr D x) \<Delta>"
    by (rule_tac x = "Suc n" in exI, metis eval_iter)
qed

lemma eval_iso: "\<Delta> \<subseteq> \<Gamma> \<Longrightarrow> eval_skat_expr D s \<Delta> \<subseteq> eval_skat_expr D s \<Gamma>"
  by (metis eval_mod2 subset_Un_eq)

lemma iter_jp:
  assumes f_jp: "\<And>X. f (\<Union>X) = \<Union>(f ` X)"
  shows "iter n f (\<Union>X) = \<Union>(iter n f ` X)"
proof (induct n arbitrary: X, simp)
  fix n X
  assume "\<And>X. iter n f (\<Union>X) = \<Union>iter n f ` X"
  hence ind_hyp2: "iter n f (\<Union>X) = \<Union>iter n f ` X"
    by auto
  have "iter (Suc n) f (\<Union>X) = f (iter n f (\<Union> X))"
    by simp
  also have "... = f (\<Union>iter n f ` X)"
    by (metis ind_hyp2)
  also have "... = \<Union>f ` iter n f ` X"
    by (metis f_jp)
  also have "... = \<Union>iter (Suc n) f ` X"
    by (auto simp add: image_def)
  finally show "iter (Suc n) f (\<Union>X) = \<Union>iter (Suc n) f ` X" .
qed

lemma eval_jp: "eval_skat_expr D s (\<Union>X) = \<Union>(eval_skat_expr D s ` X)"
proof (induct s arbitrary: X)
  fix x and s :: "'b wf_trm" and X
  show "eval_skat_expr D (SKLeaf x s) (\<Union>X) = \<Union>eval_skat_expr D (SKLeaf x s) ` X"
    by (auto simp add: wf_assigns_def set_mems_def)
next
  fix s t :: "'b skat_expr" and X
  assume "\<And>X. eval_skat_expr D s (\<Union>X) = \<Union>eval_skat_expr D s ` X"
  and "\<And>X. eval_skat_expr D t (\<Union>X) = \<Union>eval_skat_expr D t ` X"
  thus "eval_skat_expr D (s :\<oplus>: t) (\<Union>X) = \<Union>eval_skat_expr D (s :\<oplus>: t) ` X"
    by auto
next
  fix s t :: "'b skat_expr" and X
  assume asm1: "\<And>X. eval_skat_expr D s (\<Union>X) = \<Union>eval_skat_expr D s ` X"
  and asm2: "\<And>X. eval_skat_expr D t (\<Union>X) = \<Union>eval_skat_expr D t ` X"
  have "eval_skat_expr D (s :\<odot>: t) (\<Union>X) = eval_skat_expr D t (eval_skat_expr D s (\<Union>X))"
    by simp
  also have "... = eval_skat_expr D t (\<Union>eval_skat_expr D s ` X)"
    by (simp add: asm1[of X])
  also have "... = \<Union>(eval_skat_expr D t ` eval_skat_expr D s ` X)"
    by (insert asm2[of "eval_skat_expr D s ` X"])
  also have "... = \<Union>eval_skat_expr D (s :\<odot>: t) ` X"
    by simp
  finally show "eval_skat_expr D (s :\<odot>: t) (\<Union>X) = \<Union>eval_skat_expr D (s :\<odot>: t) ` X" .
next
  fix s :: "'b skat_expr" and X
  assume asm: "\<And>X. eval_skat_expr D s (\<Union>X) = \<Union>eval_skat_expr D s ` X"
  show "eval_skat_expr D (SKStar s) (\<Union>X) = \<Union>eval_skat_expr D (SKStar s) ` X"
  proof auto
    fix x n assume "x \<in> iter n (eval_skat_expr D s) (\<Union>X)"
    hence "x \<in> \<Union>(iter n (eval_skat_expr D s) ` X)"
      by (metis asm iter_jp)
    thus "\<exists>y\<in>X. \<exists>n. x \<in> iter n (eval_skat_expr D s) y"
      by (metis (no_types) UnionE image_iff)
  next
    fix x y n assume "y \<in> X" and "x \<in> iter n (eval_skat_expr D s) y"
    hence "\<exists>n. x \<in> \<Union>(iter n (eval_skat_expr D s) ` X)"
      by (metis UnionI image_eqI)
    thus "\<exists>n. x \<in> iter n (eval_skat_expr D s) (\<Union>X)"
      by (metis asm iter_jp)
  qed
next
  fix P :: "'b wf_pred bexpr" and X
  show "eval_skat_expr D (SKBool P) (\<Union>X) = \<Union>eval_skat_expr D (SKBool P) ` X"
    by (auto simp add: filter_set_def)
next
  fix X
  show "eval_skat_expr D SKOne (\<Union>X) = \<Union>eval_skat_expr D SKOne ` X"
    by auto
next
  fix X
  show "eval_skat_expr D SKZero (\<Union>X) = \<Union>eval_skat_expr D SKZero ` X"
    by auto
qed

lemma eval_star_slide:
  fixes \<Delta> :: "'b mems"
  shows "eval_skat_expr D (SKStar x :\<odot>: x) \<Delta> = eval_skat_expr D (x :\<odot>: SKStar x) \<Delta>"
  apply (simp add: eval_star_power del: eval_skat_expr.simps(5))
  apply (simp add: eval_jp)
  apply auto
  apply (metis (no_types) iter.simps(2) eval_iter eval_power_def)
  by (metis (no_types) iter.simps(2) eval_iter eval_power_def)

lemma eval_star_unfoldr:
  fixes \<Delta> :: "'b mems"
  shows "eval_skat_expr D (SKOne :\<oplus>: SKStar x :\<odot>: x :\<oplus>: SKStar x) \<Delta> = eval_skat_expr D (SKStar x) \<Delta>"
  by (subst eval_star_unfoldl[symmetric], insert eval_star_slide, auto)

lemma eval_star_inductl:
  assumes asm2: "\<forall>\<Delta>::'b mems. eval_skat_expr D (z :\<oplus>: x :\<odot>: y :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
  shows "\<forall>\<Delta>. eval_skat_expr D (SKStar x :\<odot>: z :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
proof (auto simp add: eval_star_power eval_jp eval_power_def simp del: eval_skat_expr.simps(5))
  fix \<Delta> :: "'b mems" and mem :: "'b mem" and n
  assume "mem \<in> eval_skat_expr D z (iter n (eval_skat_expr D x) \<Delta>)"
  hence "mem \<in> eval_skat_expr D (z :\<oplus>: x :\<odot>: y :\<oplus>: y) \<Delta>"
  proof (induct n arbitrary: \<Delta>, simp, simp only: iter.simps eval_iter1)
    fix m and \<Gamma> :: "'b mems"
    assume "\<And>\<Delta>. mem \<in> eval_skat_expr D z (iter m (eval_skat_expr D x) \<Delta>) \<Longrightarrow>
                mem \<in> eval_skat_expr D (z :\<oplus>: x :\<odot>: y :\<oplus>: y) \<Delta>"
      and "mem \<in> eval_skat_expr D z (iter m (eval_skat_expr D x) (eval_skat_expr D x \<Gamma>))"
    hence a: "mem \<in> eval_skat_expr D (z :\<oplus>: x :\<odot>: y :\<oplus>: y) (eval_skat_expr D x \<Gamma>)"
      by auto
    thus "mem \<in> eval_skat_expr D (z :\<oplus>: x :\<odot>: y :\<oplus>: y) \<Gamma>"
      by (auto, (metis a asm2)+)
  qed
  thus "mem \<in> eval_skat_expr D y \<Delta>"
    by (metis asm2)
qed

lemma eval_iso2:
  assumes "\<And>mem. mem \<in> \<Delta> \<Longrightarrow> mem \<in> \<Gamma>"
  and "mem \<in> eval_skat_expr D s \<Delta>"
  shows "mem \<in> eval_skat_expr D s \<Gamma>"
proof -
  have "\<Delta> \<subseteq> \<Gamma>"
    by (insert assms(1), auto)
  thus ?thesis
    by (metis assms(2) eval_iso set_mp)
qed

lemma eval_star_inductr:
  assumes asm2: "\<forall>\<Delta>::'b mems. eval_skat_expr D (z :\<oplus>: y :\<odot>: x :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
  shows "\<forall>\<Delta>. eval_skat_expr D (z :\<odot>: SKStar x :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
proof auto
  fix \<Delta> :: "'b mems" and mem :: "'b mem" and n
  assume "mem \<in> iter n (eval_skat_expr D x) (eval_skat_expr D z \<Delta>)"
  hence "mem \<in> eval_skat_expr D (z :\<oplus>: y :\<odot>: x :\<oplus>: y) \<Delta>"
  proof (induct n arbitrary: mem, simp)
    fix n mem
    assume asm:
      "\<And>mem. mem \<in> iter n (eval_skat_expr D x) (eval_skat_expr D z \<Delta>) \<Longrightarrow>
             mem \<in> eval_skat_expr D (z :\<oplus>: y :\<odot>: x :\<oplus>: y) \<Delta>"
    and "mem \<in> iter (Suc n) (eval_skat_expr D x) (eval_skat_expr D z \<Delta>)"
    hence "mem \<in> eval_skat_expr D x (iter n (eval_skat_expr D x) (eval_skat_expr D z \<Delta>))"
      by simp
    hence "mem \<in> eval_skat_expr D x (eval_skat_expr D (z :\<oplus>: y :\<odot>: x :\<oplus>: y) \<Delta>)"
      by (smt asm eval_iso2)
    thus "mem \<in> eval_skat_expr D (z :\<oplus>: y :\<odot>: x :\<oplus>: y) \<Delta>"
      by (metis (lifting) UnI1 UnI2 asm2 eval_skat_expr.simps(3) eval_skat_expr.simps(4))
  qed
  thus "mem \<in> eval_skat_expr D y \<Delta>"
    by (metis asm2)
qed

theorem hunt_con_eval: "hunt_con s t \<Longrightarrow> \<forall>\<Delta>. eval_bexpr D s \<Delta> = eval_bexpr D t \<Delta>"
  by (induct rule: hunt_con.induct, auto)

lemma evap_bexpr_not[simp]: "eval_bexpr D (BNot x) \<Delta> = (\<not> eval_bexpr D x \<Delta>)" by simp

lemma filter_compl [simp]: "filter_set (\<lambda>x. \<not> p x) X = (- filter_set p X \<inter> X)"
proof -
  have "filter_set (\<lambda>x. \<not> p x) X \<subseteq> (- filter_set p X \<inter> X)"
    by (auto simp add: filter_set_def, (metis empty_iff singleton_iff)+)
  moreover have "(- filter_set p X \<inter> X) \<subseteq> filter_set (\<lambda>x. \<not> p x) X"
    by (auto simp add: filter_set_def, metis insertI1)
  ultimately show ?thesis
    by blast
qed

lemma eval_skat_not: "eval_skat_expr D (SKBool (BNot x)) \<Delta> = (- eval_skat_expr D (SKBool x) \<Delta> \<inter> \<Delta>)"
  by (simp add: filter_set_def, metis Compl_UN filter_compl filter_set_def)

method_setup simp_solve = {*
Scan.succeed (fn ctxt =>
  ALLGOALS (fn n => TRY (SOLVED' (asm_full_simp_tac (simpset_of ctxt)) n) ORELSE all_tac)
  |> SIMPLE_METHOD)
*}

declare filter_set_def [simp]

theorem skat_con_eval: "skat_con s t \<Longrightarrow> \<forall>\<Delta>. eval_skat_expr D s \<Delta> = eval_skat_expr D t \<Delta>"
proof (induct rule: skat_con.induct, simp_solve)
  fix x y assume asm1: "skat_con x y"
  and asm2: "\<forall>\<Delta>. eval_skat_expr D x \<Delta> = eval_skat_expr D y \<Delta>"
  hence "\<And>n. \<forall>\<Delta>. iter n (eval_skat_expr D x) \<Delta> = iter n (eval_skat_expr D y) \<Delta>"
  proof -
    fix n show "\<forall>\<Delta>. iter n (eval_skat_expr D x) \<Delta> = iter n (eval_skat_expr D y) \<Delta>"
      by (induct n, simp_all add: asm2)
  qed
  thus "\<forall>\<Delta>. eval_skat_expr D (SKStar x) \<Delta> = eval_skat_expr D (SKStar y) \<Delta>"
    by auto
next
  fix x y assume "skat_con (SKBool x) (SKBool y)"
  and "\<forall>\<Delta>. eval_skat_expr D (SKBool x) \<Delta> = eval_skat_expr D (SKBool y) \<Delta>"
  thus "\<forall>\<Delta>. eval_skat_expr D (SKBool (BNot x)) \<Delta> = eval_skat_expr D (SKBool (BNot y)) \<Delta>"
    by (simp only: eval_skat_not, auto)
next
 fix x y z show "\<forall>\<Delta>. eval_skat_expr D (x :\<oplus>: y :\<oplus>: z) \<Delta> = eval_skat_expr D (x :\<oplus>: (y :\<oplus>: z)) \<Delta>"
   by auto
next
  fix x y show "\<forall>\<Delta>. eval_skat_expr D (x :\<oplus>: y) \<Delta> = eval_skat_expr D (y :\<oplus>: x) \<Delta>"
    by auto
next
  fix x y z show "\<forall>\<Delta>. eval_skat_expr D ((x :\<oplus>: y) :\<odot>: z) \<Delta> = eval_skat_expr D (x :\<odot>: z :\<oplus>: y :\<odot>: z) \<Delta>"
    by (simp, metis eval_mod2)
next
  fix x show "\<forall>\<Delta>. eval_skat_expr D (SKZero :\<odot>: x) \<Delta> = eval_skat_expr D SKZero \<Delta>"
    by (simp, metis eval_mod1)
next
  fix x
  show "\<forall>\<Delta>. eval_skat_expr D (SKOne :\<oplus>: x :\<odot>: SKStar x :\<oplus>: SKStar x) \<Delta> = eval_skat_expr D (SKStar x) \<Delta>"
    by (metis eval_star_unfoldl)
next
  fix x
  show "\<forall>\<Delta>. eval_skat_expr D (SKOne :\<oplus>: SKStar x :\<odot>: x :\<oplus>: SKStar x) \<Delta> = eval_skat_expr D (SKStar x) \<Delta>"
    by (metis eval_star_unfoldr)
next
  fix z x y assume "\<forall>\<Delta>. eval_skat_expr D (z :\<oplus>: x :\<odot>: y :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
  thus "\<forall>\<Delta>. eval_skat_expr D (SKStar x :\<odot>: z :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
    by (metis eval_star_inductl)
next
  fix z y x assume "skat_con (z :\<oplus>: y :\<odot>: x :\<oplus>: y) y"
  and "\<forall>\<Delta>. eval_skat_expr D (z :\<oplus>: y :\<odot>: x :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
  thus "\<forall>\<Delta>. eval_skat_expr D (z :\<odot>: SKStar x :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
    by (metis eval_star_inductr)
next
  fix x y :: "'a wf_pred bexpr" assume "hunt_con x y"
  hence "\<forall>\<Delta>. eval_bexpr D x \<Delta> = eval_bexpr D y \<Delta>"
    by (metis hunt_con_eval)
  hence "eval_bexpr D x = eval_bexpr D y"
    by auto
  thus "\<forall>\<Delta>. eval_skat_expr D (SKBool x) \<Delta> = eval_skat_expr D (SKBool y) \<Delta>"
    by (simp del: filter_set_def)
next
  fix x y show "\<forall>\<Delta>. eval_skat_expr D (SKBool (x :\<cdot>: y)) \<Delta> = eval_skat_expr D (SKBool x :\<odot>: SKBool y) \<Delta>"
    by (auto, (metis empty_iff singleton_iff)+)
next
  fix x y show "\<forall>\<Delta>. eval_skat_expr D (SKBool (x :+: y)) \<Delta> = eval_skat_expr D (SKBool x :\<oplus>: SKBool y) \<Delta>"
    by (auto, (metis empty_iff singleton_iff)+)
next
  fix x y :: nat and s t :: "'a wf_trm" assume "x \<noteq> y" and "y \<notin> FV s"
  thus "\<forall>\<Delta>. eval_skat_expr D (SKLeaf x s :\<odot>: SKLeaf y t) \<Delta> =
            eval_skat_expr D (SKLeaf y (t[x|s]) :\<odot>: SKLeaf x s) \<Delta>"
    by (simp, metis eval_wf_assigns1)
next
  fix x y :: nat and s t :: "'a wf_trm" assume "x \<noteq> y" and "x \<notin> FV s"
  thus "\<forall>\<Delta>. eval_skat_expr D (SKLeaf x s :\<odot>: SKLeaf y t) \<Delta> =
            eval_skat_expr D (SKLeaf x s :\<odot>: SKLeaf y (t[x|s])) \<Delta>"
    by (simp, metis eval_wf_assigns2)
next
  fix x s t
  show "\<forall>\<Delta>. eval_skat_expr D (SKLeaf x s :\<odot>: SKLeaf x t) \<Delta> =
            eval_skat_expr D (SKLeaf x (t[x|s])) \<Delta>"
    by (simp, metis eval_wf_assigns3)
next
  fix x t \<phi>
  show "\<forall>\<Delta>. eval_skat_expr D (SKBool (bexpr_map (wf_pred_subst x t) \<phi>) :\<odot>: SKLeaf x t) \<Delta> =
            eval_skat_expr D (SKLeaf x t :\<odot>: SKBool \<phi>) \<Delta>"
    sorry
qed

lift_definition eval ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a skat \<Rightarrow> 'b mems \<Rightarrow> 'b mems"
  is eval_skat_expr
proof -
  fix D :: "('a::ranked_alphabet, 'b) interp" and s t :: "'a skat_expr"
  assume "skat_con s t"
  hence "\<forall>\<Delta>. eval_skat_expr D s \<Delta> = eval_skat_expr D t \<Delta>"
    by (metis skat_con_eval)
  thus "eval_skat_expr D s = eval_skat_expr D t"
    by auto
qed

definition expr_determ ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a skat_expr \<Rightarrow> bool"
  where
  "expr_determ D s \<equiv> \<forall>\<Delta>. \<exists>mem. eval_skat_expr D s \<Delta> = {mem}"

fun skat_prog :: "'a::ranked_alphabet prog \<Rightarrow> 'a skat" where
  "skat_prog (If \<phi> x y) = pred \<phi> \<cdot> skat_prog x + !(pred \<phi>) \<cdot> skat_prog y"
| "skat_prog (While \<phi> x) = (pred \<phi> \<cdot> skat_prog x)\<^sup>\<star> \<cdot> !(pred \<phi>)"
| "skat_prog (Seq []) = \<one>"
| "skat_prog (Seq (x#xs)) = skat_prog x \<cdot> skat_prog (Seq xs)"
| "skat_prog (Assign x s) = x := s"

fun skat_expr_prog :: "'a::ranked_alphabet prog \<Rightarrow> 'a skat_expr" where
  "skat_expr_prog (If \<phi> x y) =
    (SKBool (BLeaf \<phi>) :\<odot>: skat_expr_prog x) :\<oplus>: (SKBool (BNot (BLeaf \<phi>)) :\<odot>: skat_expr_prog y)"
| "skat_expr_prog (While \<phi> x) = SKStar (SKBool (BLeaf \<phi>) :\<odot>: skat_expr_prog x) :\<odot>: SKBool (BNot (BLeaf \<phi>))"
| "skat_expr_prog (Seq []) = SKOne"
| "skat_expr_prog (Seq (x#xs)) = skat_expr_prog x :\<odot>: skat_expr_prog (Seq xs)"
| "skat_expr_prog (Assign x s) = SKLeaf x s"

lemma "skat_prog pgm = \<lfloor>skat_expr_prog pgm\<rfloor>"
proof (induct pgm)
  fix pgms :: "'a prog list"
  assume "\<forall>pgm\<in>set pgms. skat_prog pgm = \<lfloor>skat_expr_prog pgm\<rfloor>"
  thus "skat_prog (Seq pgms) = \<lfloor>skat_expr_prog (Seq pgms)\<rfloor>"
    by (induct pgms, auto)
qed auto

context valid_interp
begin

  definition module :: "'b mems \<Rightarrow> 'a skat \<Rightarrow> 'b mems" (infix "\<Colon>" 75) where
    "module \<Delta> x \<equiv> eval D x \<Delta>"

  definition mod_le :: "'b mems \<Rightarrow> 'b mems \<Rightarrow> bool" (infix "\<preceq>" 60) where
    "x \<preceq> y \<equiv> x \<union> y = y"

  (* Properties from Kleene modules and linear languages by Hans Leiss *)

  lemma mod_empty [simp]: "{} \<Colon> r = {}"
    by (simp add: module_def, transfer, metis eval_mod1)

  lemma "(a \<union> b) \<Colon> r = a \<Colon> r \<union> b \<Colon> r"
    by (simp add: module_def, transfer, metis eval_mod2)

  lemma mod_zero [simp]: "a \<Colon> \<zero> = {}"
    by (simp add: module_def, transfer, simp)

  lemma mod_plus: "a \<Colon> (r + s) = a \<Colon> r \<union> a \<Colon> s"
    by (simp add: module_def, transfer, simp)

  lemma mod_one [simp]: "a \<Colon> \<one> = a"
    by (simp add: module_def, transfer, simp)

  lemma mod_mult: "a \<Colon> (r \<cdot> s) = (a \<Colon> r) \<Colon> s"
    by (simp add: module_def, transfer, simp)

  lemma "a \<union> b \<Colon> r \<preceq> b \<Longrightarrow> a \<Colon> r\<^sup>\<star> \<preceq> b"
    apply (simp add: module_def mod_le_def)
    apply transfer
    by (metis (lifting) eval_mod3 sup.commute)

  lemma mod_assign: "\<Delta> \<Colon> x := s = wf_assigns D x s \<Delta>"
    apply (simp add: module_def)
    apply transfer
    apply simp
    done

  lemma mod_pred_expr: "\<Delta> \<Colon> pred_expr P = filter_set (eval_bexpr D P) \<Delta>"
    apply (simp add: module_def)
    apply transfer
    apply simp
    done

  lemma mod_eval: "\<Delta> \<Colon> \<lfloor>s\<rfloor> = eval_skat_expr D s \<Delta>"
  proof -
    have "eval_skat_expr D s \<Delta> = \<Delta> \<Colon> abs_skat s"
      by (simp add: module_def, transfer, auto)
    thus ?thesis
      by (metis unfold_is_abs)
  qed

  lemma mod_star_eval: "\<Delta> \<Colon> \<lfloor>s\<rfloor>\<^sup>\<star> = (\<Union>n. iter n (eval_skat_expr D s) \<Delta>)"
    by (subgoal_tac "\<lfloor>s\<rfloor>\<^sup>\<star> = \<lfloor>SKStar s\<rfloor>", simp only: mod_eval, transfer, auto)

  definition terminates :: "'a prog \<Rightarrow> bool" where
    "terminates prgm \<equiv> \<exists>steps. \<forall>mem. eval_prog steps D mem prgm \<noteq> None"

  definition deterministic :: "'a skat \<Rightarrow> bool" where
    "deterministic s \<equiv> \<forall>mem. card ({mem} \<Colon> s) = 1"

  lemma det_mult: "\<lbrakk>deterministic x; deterministic y\<rbrakk> \<Longrightarrow> deterministic (x \<cdot> y)"
    by (auto simp add: deterministic_def mod_mult, metis card_eq_SucD)

  lemma "terminates pgm \<Longrightarrow> deterministic (skat_prog pgm)"
  proof (induct pgm)
    show "\<forall>x\<in>set[]. deterministic (skat_prog x)"
      by auto
  next
    fix xs assume "\<forall>x\<in>set xs. deterministic (skat_prog x)"
    thus "deterministic (skat_prog (Seq xs))"
      by (induct xs, simp add: deterministic_def, auto intro: det_mult)
  next
    fix x s
    show "deterministic (skat_prog (Assign x s))"
      by (simp add: deterministic_def mod_assign wf_assigns_def set_mems_def)
  next
    fix \<phi> pgm1 pgm2
    assume "deterministic (skat_prog pgm1)"
    and "deterministic (skat_prog pgm2)"
    thus "deterministic (skat_prog (If \<phi> pgm1 pgm2))"
    proof (auto simp add: deterministic_def)
      fix mem
      assume "\<forall>mem. card ({mem} \<Colon> skat_prog pgm1) = Suc 0"
      and "\<forall>mem. card ({mem} \<Colon> skat_prog pgm2) = Suc 0"
      hence "card ({mem} \<Colon> (pred_expr (BLeaf \<phi>) \<cdot> skat_prog pgm1 +
                            pred_expr (BNot (BLeaf \<phi>)) \<cdot> skat_prog pgm2)) =
             Suc 0"
        by (simp add: mod_plus mod_mult mod_pred_expr)
      thus "card ({mem} \<Colon> (pred \<phi> \<cdot> skat_prog pgm1 + !(pred \<phi>) \<cdot> skat_prog pgm2)) = Suc 0"
        by (metis pred_expr_not pred_to_expr)
    qed
  next
    fix \<phi> pgm
    assume "deterministic (skat_prog pgm)"
    thus "deterministic (skat_prog (While \<phi> pgm))"
    proof (auto simp add: deterministic_def mod_mult)
      fix mem
      assume "\<forall>mem. card ({mem} \<Colon> skat_prog pgm) = Suc 0"
      have "card (({mem} \<Colon> \<lfloor>(SKBool (BLeaf \<phi>) :\<odot>: skat_expr_prog pgm)\<rfloor>\<^sup>\<star>) \<Colon> pred_expr (BNot (BLeaf \<phi>))) = Suc 0"
        apply (simp only: mod_star_eval mod_pred_expr)
        apply auto
        apply (simp add: eval_skat_expr.simps)
        
      thus "card (({mem} \<Colon> (pred \<phi> \<cdot> skat_prog pgm)\<^sup>\<star>) \<Colon> !(pred \<phi>)) = Suc 0"
        
    qed
  qed
end

definition deterministic :: "'a::ranked_alphabet skat \<Rightarrow> bool" where
  "deterministic s \<equiv> \<forall>D. valid_interp D \<longrightarrow> valid_interp.deterministic D s"

end

