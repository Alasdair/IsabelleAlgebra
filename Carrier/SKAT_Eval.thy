theory SKAT_Eval
  imports SKAT
begin

type_synonym 'a mems = "(nat \<Rightarrow> 'a) set"

(* Non-deterministic memory forms and idempotent commutative monoid *)

primrec iter :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "iter 0 f = id"
| "iter (Suc n) f = f \<circ> iter n f"

value eval_wf_pred

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

abbreviation set_mem where "set_mem \<equiv> setMem"

definition set_mems :: "nat \<Rightarrow> ('a mem \<Rightarrow> 'a) \<Rightarrow> 'a mems \<Rightarrow> 'a mems" where
  "set_mems x f \<Delta> \<equiv> (\<lambda>mem. set_mem x (f mem) mem) ` \<Delta>"

definition assigns ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> nat \<Rightarrow> 'a trm \<Rightarrow> 'b mems \<Rightarrow> 'b mems"
  where
  "assigns D x s mems = set_mems x (\<lambda>mem. eval_trm D mem s) mems"

lemma finite_set_mems: assumes "finite \<Delta>" shows "finite (set_mems x f \<Delta>)"
  by (induct rule: finite_subset_induct_var[OF assms(1), of "\<Delta>"], simp_all add: set_mems_def)

lemma card_set_mems: "finite \<Delta> \<Longrightarrow> card (set_mems X f \<Delta>) \<le> card \<Delta>"
  by (simp add: set_mems_def, smt card_image_le)

lemma assign_image: "assigns D x t mems = assign D x t ` mems"
  by (auto simp add: assigns_def set_mems_def assign_def[symmetric])

lemma eval_assigns3: "assigns D x t (assigns D x s mems) = assigns D x (trm_subst {x} s t) mems"
proof (auto simp add: assign_image image_def)
  fix mem assume mem_in: "mem \<in> mems"
  show "\<exists>m\<in>mems. assign D x t (assign D x s mem) = assign D x (trm_subst {x} s t) m"
    by (rule bexI[OF _ mem_in], simp add: eval_assign3)
next
  fix mem assume mem_in: "mem \<in> mems"
  thus "\<exists>m1. (\<exists>m2\<in>mems. m1 = assign D x s m2) \<and>
              assign D x (trm_subst {x} s t) mem = assign D x t m1"
    by (rule_tac x = "assign D x s mem" in exI, auto simp add: eval_assign3)
qed

fun eval_skat_expr ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a skat_expr \<Rightarrow> 'b mem \<Rightarrow> 'b mem"
  where
  "eval_skat_expr D (SKLeaf X s) \<Delta> = set_mems X (\<lambda>mem. eval_wf_trm D mem s) \<Delta>"
| "eval_skat_expr D (SKBool P) \<Delta> = filter_set (eval_bexpr D P) \<Delta>"
| "eval_skat_expr D (s :\<odot>: t) \<Delta> = eval_skat_expr D t (eval_skat_expr D s \<Delta>)"
| "eval_skat_expr D (s :\<oplus>: t) \<Delta> = eval_skat_expr D s \<Delta> \<union> eval_skat_expr D t \<Delta>"
| "eval_skat_expr D (SKStar s) \<Delta> = (\<Union>n. iter n (eval_skat_expr D s) \<Delta>)"
| "eval_skat_expr D SKOne \<Delta> = \<Delta>"
| "eval_skat_expr D SKZero \<Delta> = {}"

lemma eval_mod1: "eval_skat_expr D s {} = {}"
proof (induct s, simp_all add: update_mem_def, clarify)
  fix s n assume "eval_skat_expr D s {} = {}"
  thus "iter n (eval_skat_expr D s) {} = {}"
    by (induct n, auto)
next
  fix P show "filter_set (eval_bexpr D P) {} = {}"
    by (induct P, auto simp add: filter_set_def)
qed

lemma eval_mod2: "eval_skat_expr D s (\<Delta> \<union> \<Gamma>) = eval_skat_expr D s \<Delta> \<union> eval_skat_expr D s \<Gamma>"
  apply (induct s arbitrary: \<Delta> \<Gamma>, simp_all add: update_mem_def filter_set_def)
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
  fix x show "\<forall>\<Delta>. eval_skat_expr D (SKOne :\<oplus>: x :\<odot>: SKStar x :\<oplus>: SKStar x) \<Delta> = eval_skat_expr D (SKStar x) \<Delta>"
    sorry (* unfolding *)
next
  fix x show "\<forall>\<Delta>. eval_skat_expr D (SKOne :\<oplus>: SKStar x :\<odot>: x :\<oplus>: SKStar x) \<Delta> = eval_skat_expr D (SKStar x) \<Delta>"
    sorry
next
  fix z x y assume "skat_con (z :\<oplus>: x :\<odot>: y :\<oplus>: y) y"
  and "\<forall>\<Delta>. eval_skat_expr D (z :\<oplus>: x :\<odot>: y :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
  thus "\<forall>\<Delta>. eval_skat_expr D (SKStar x :\<odot>: z :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
    sorry
next
 fix z y x assume "skat_con (z :\<oplus>: y :\<odot>: x :\<oplus>: y) y"
 and "\<forall>\<Delta>. eval_skat_expr D (z :\<oplus>: y :\<odot>: x :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
 thus "\<forall>\<Delta>. eval_skat_expr D (z :\<odot>: SKStar x :\<oplus>: y) \<Delta> = eval_skat_expr D y \<Delta>"
   sorry
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
  fix Y and s :: "'a wf_trm" and X and t :: "'a wf_trm" assume Ys: "Y \<inter> FV s = {}"
  thus "\<forall>\<Delta>. eval_skat_expr D (SKLeaf X s :\<odot>: SKLeaf Y t) \<Delta> =
            eval_skat_expr D (SKLeaf Y (t[X|s]) :\<odot>: SKLeaf X s) \<Delta>"
  proof (intro allI)
    fix \<Delta>
    have "eval_skat_expr D (SKLeaf X s :\<odot>: SKLeaf Y t) \<Delta> =
          eval_skat_expr D (SKLeaf Y t) (eval_skat_expr D (SKLeaf X s) \<Delta>)"
      by simp
    also have "... = eval_skat_expr D (SKLeaf X s) (eval_skat_expr D (SKLeaf Y (t[X|s])) \<Delta>)"
      sorry
    also have "... = eval_skat_expr D (SKLeaf Y (t[X|s]) :\<odot>: SKLeaf X s) \<Delta>"
      by simp
    finally show "eval_skat_expr D (SKLeaf X s :\<odot>: SKLeaf Y t) \<Delta> =
                  eval_skat_expr D (SKLeaf Y (t[X|s]) :\<odot>: SKLeaf X s) \<Delta>" .
  qed
next

qed

lift_definition eval ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a skat \<Rightarrow> 'b mem \<Rightarrow> 'b mem"
  is eval_skat_expr
proof -
  fix D :: "('a::ranked_alphabet, 'b) interp" and s t :: "'a skat_expr"
  assume "skat_con s t"
  hence "\<forall>\<Delta>. eval_skat_expr D s (\<Delta> :: 'b mem) = eval_skat_expr D t \<Delta>"
    by (metis skat_con_eval)
  thus "eval_skat_expr D s = eval_skat_expr D t"
    by auto
qed

context valid_interp
begin

  definition module :: "'a skat \<Rightarrow> 'b mem \<Rightarrow> 'b mem" (infix "\<Colon>" 75) where
    "module \<equiv> eval D"

  definition mod_le :: "'b mem \<Rightarrow> 'b mem \<Rightarrow> bool" (infix "\<preceq>" 60) where
    "x \<preceq> y \<equiv> x \<union> y = y"

  declare module_def [skat_simp]
  declare mod_le_def [skat_simp]

  (* Properties from Kleene modules and linear languages by Hans Leiss *)

  lemma "r \<Colon> {} = {}"
    by (skat_simp, transfer, metis eval_mod1)

  lemma "r \<Colon> (b \<union> a) = r \<Colon> b \<union> r \<Colon> a"
    by (skat_simp, transfer, metis eval_mod2)

  lemma "\<zero> \<Colon> a = {}"
    by (skat_simp, transfer, simp)

  lemma "(r + s) \<Colon> a = r \<Colon> a \<union> s \<Colon> a"
    by (skat_simp, transfer, simp)

  lemma "\<one> \<Colon> a = a"
    by (skat_simp, transfer, simp)

  (* This is the opposite from the paper -- it has r \<Colon> (s \<Colon> a) *)
  lemma "(r \<cdot> s) \<Colon> a = s \<Colon> (r \<Colon> a)"
    by (skat_simp, transfer, simp)

  lemma "r \<Colon> b \<union> a \<preceq> b \<Longrightarrow> r\<^sup>\<star> \<Colon> a \<preceq> b"
    by (skat_simp, transfer, metis eval_mod3)

end

end

