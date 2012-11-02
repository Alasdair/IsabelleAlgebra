theory Kleene_Algebra_Extras
  imports Dioid "Regular-Sets/Equivalence_Checking"
begin


(* +------------------------------------------------------------------------+ *)
subsection {* Free Kleene Algebra *}
(* +------------------------------------------------------------------------+ *)

inductive_set languages :: "'a set \<Rightarrow> 'a lang" for \<Sigma> :: "'a set" where
  "[] \<in> languages \<Sigma>"
| "\<lbrakk>x \<in> \<Sigma>; xs \<in> languages \<Sigma>\<rbrakk> \<Longrightarrow> x#xs \<in> languages \<Sigma>"

lemma languages_empty [simp]: "languages {} = {[]}"
  by (metis equals0D insert_iff languages.simps nonempty_iff)

inductive_set free_ka_set :: "'a set \<Rightarrow> 'a lang set" for \<Sigma> :: "'a set" where
  empty: "{} \<in> free_ka_set \<Sigma>"
| lang: "x \<in> languages \<Sigma> \<Longrightarrow> {x} \<in> free_ka_set \<Sigma>"
| union: "\<lbrakk>p \<in> free_ka_set \<Sigma>; q \<in> free_ka_set \<Sigma>\<rbrakk> \<Longrightarrow> p \<union> q \<in> free_ka_set \<Sigma>"
| concat: "\<lbrakk>p \<in> free_ka_set \<Sigma>; q \<in> free_ka_set \<Sigma>\<rbrakk> \<Longrightarrow> p @@ q \<in> free_ka_set \<Sigma>"
| star: "p \<in> free_ka_set \<Sigma> \<Longrightarrow> Regular_Set.star p \<in> free_ka_set \<Sigma>"

lemma free_ka_set_empty [simp]: "free_ka_set {} = {{}, {[]}}"
proof
  show "free_ka_set {} \<subseteq> {{}, {[]}}"
  proof
    fix x assume "x \<in> free_ka_set {}"
    thus "x \<in> {{}, {[]}}"
      apply (induct x)
      apply simp
      apply simp
      apply (metis empty_iff insert_iff sup_bot_left sup_bot_right sup_idem)
      apply (metis conc_empty(2) conc_epsilon(2) insert_iff singleton_iff)
      by (metis empty_iff insert_iff star_empty star_insert_eps)
  qed
  show "{{}, {[]}} \<subseteq> free_ka_set {}"
    apply (auto, metis free_ka_set.empty)
    by (metis free_ka_set.lang languages.intros(1))
qed

definition free_ka :: "'a set \<Rightarrow> 'a lang kleene_algebra" where
  "free_ka \<Sigma> \<equiv> \<lparr>carrier = free_ka_set \<Sigma>, plus = op \<union>, mult = op @@, one = {[]}, zero = {}, star = Regular_Set.star\<rparr>"

lemma "carrier \<in> {K. kleene_algebra K} \<rightarrow> UNIV"
  by (simp add: ftype_def)

lemma free_ka_dioid: "dioid (free_ka \<Sigma>)"
  apply (default, simp_all add: free_ka_def)
  apply (metis free_ka_set.union)
  apply (metis free_ka_set.concat)
  apply (metis free_ka_set.lang languages.intros(1))
  apply (metis free_ka_set.empty)
  apply (metis conc_assoc)
  by auto

lemma lang_inf_distl:
  assumes xc: "x \<in> free_ka_set \<Sigma>"
  and Xc: "X \<subseteq> free_ka_set \<Sigma>"
  shows "x @@ \<Union> X = \<Union> {x @@ y |y. y \<in> X}"
  by fast

lemma lang_inf_distr:
  assumes xc: "x \<in> free_ka_set \<Sigma>"
  and Xc: "X \<subseteq> free_ka_set \<Sigma>"
  shows "\<Union> X @@ x = \<Union> {y @@ x |y. y \<in> X}"
  by fast

lemma RStar_inductr_var:
  assumes xc: "x \<in> free_ka_set \<Sigma>" and yc: "y \<in> free_ka_set \<Sigma>"
  and asm: "y @@ x \<subseteq> y" shows "y @@ Regular_Set.star x \<subseteq> y"
proof -
  have "\<forall>n. y @@ x ^^ n \<subseteq> y"
  proof (intro allI)
    fix n show "y @@ x ^^ n \<subseteq> y"
      apply (induct n, simp)
      by (smt Un_absorb1 Un_upper1 asm conc_Un_distrib(2) conc_assoc lang_pow.simps(2) order_trans)
  qed
  hence "(\<Union>n. y @@ x ^^ n) \<subseteq> y"
    by (metis (lifting) SUP_le_iff)
  thus ?thesis
    by (metis Regular_Set.star_def conc_UNION_distrib(1))
qed

lemma RStar_inductr:
  assumes xc: "x \<in> free_ka_set \<Sigma>"
  and yc: "y \<in> free_ka_set \<Sigma>"
  and zc: "z \<in> free_ka_set \<Sigma>"
  shows "z \<union> y @@ x \<subseteq> y \<longrightarrow> z @@ Regular_Set.star x \<subseteq> y"
proof
  assume hyp: "z \<union> y @@ x \<subseteq> y"
  hence "z \<subseteq> y" and "y @@ x \<subseteq> y"
    by blast+
  hence "y @@ Regular_Set.star x \<subseteq> y"
    by (metis RStar_inductr_var xc yc)
  thus "z @@ Regular_Set.star x \<subseteq> y"
    using `z \<subseteq> y` by blast
qed

lemma RStar_inductl_var:
  assumes xc: "x \<in> free_ka_set \<Sigma>" and yc: "y \<in> free_ka_set \<Sigma>"
  and asm: "x @@ y \<subseteq> y" shows "Regular_Set.star x @@ y \<subseteq> y"
proof -
  have "\<forall>n. x ^^ n @@ y \<subseteq> y"
  proof (intro allI)
    fix n show "x ^^ n @@ y \<subseteq> y"
      apply (induct n, simp)
      by (smt asm conc_Un_distrib(1) conc_assoc lang_pow.simps(2) lang_pow_code_def order_trans subset_Un_eq)
  qed
  hence "(\<Union>n. x ^^ n @@ y) \<subseteq> y"
    by (metis (lifting) SUP_le_iff)
  thus ?thesis
    by (metis Regular_Set.star_def conc_UNION_distrib(2))
qed

lemma RStar_inductl:
  assumes xc: "x \<in> free_ka_set \<Sigma>"
  and yc: "y \<in> free_ka_set \<Sigma>"
  and zc: "z \<in> free_ka_set \<Sigma>"
  shows "z \<union> x @@ y \<subseteq> y \<longrightarrow> Regular_Set.star x @@ z \<subseteq> y"
proof
  assume hyp: "z \<union> x @@ y \<subseteq> y"
  hence "z \<subseteq> y" and "x @@ y \<subseteq> y"
    by blast+
  hence "Regular_Set.star x @@ y \<subseteq> y"
    by (metis RStar_inductl_var xc yc)
  thus "Regular_Set.star x @@ z \<subseteq> y"
    using `z \<subseteq> y` by blast
qed

lemma free_ka_prop:
  shows "kleene_algebra (free_ka \<Sigma>)"
  apply (simp add: kleene_algebra_def kleene_algebra_axioms_def, safe)
  apply (rule free_ka_dioid)
  apply (simp_all add: dioid.nat_order_def[OF free_ka_dioid])
  apply (simp_all add: free_ka_def)
  apply (rule free_ka_set.star, assumption)
  apply (metis (lifting) Un_insert_left Un_insert_right star_unfold_left sup_left_idem)
  apply (metis (lifting) Un_insert_left Un_insert_right conc_star_comm star_unfold_left sup.idem sup.left_idem)
  apply (metis RStar_inductl inf_sup_ord(4) sup_absorb1 sup_commute)
  by (metis (lifting) RStar_inductr subset_Un_eq)

(* +------------------------------------------------------------------------+ *)
subsection {* Decision Procedure for KA *}
(* +------------------------------------------------------------------------+ *)

lemma atoms_finite: "finite (atoms x)"
  by (induct x, simp_all)

lemma rexp_in_fka:
  shows "lang x \<in> free_ka_set (atoms x \<union> y)"
  apply (induct x arbitrary: y, simp_all)
  apply (metis free_ka_set.empty)
  apply (metis free_ka_set.lang languages.intros(1))
  apply (metis free_ka_set.lang insertI1 languages.intros(1) languages.intros(2))
  apply (metis free_ka_set.union sup_commute sup_left_commute)
  apply (metis (lifting) Un_assoc Un_left_commute free_ka_set.concat)
  by (metis free_ka_set.star)

lemma fka_lang: "x \<in> free_ka_set \<Sigma> \<Longrightarrow> \<exists>y. lang y = x"
proof (induct x rule: free_ka_set.induct)
  show "\<exists>y. lang y = {}"
    by (rule_tac x = Zero in exI, simp)
next
  fix z assume "z \<in> languages \<Sigma>"
  thus "\<exists>y. lang y = {z}"
  proof (induct z)
    show "\<exists>y. lang y = {[]}"
      by (rule_tac x = "One" in exI, simp)
    fix x xs assume "\<exists>y. lang y = {xs}"
    then obtain y where "lang y = {xs}" by auto
    thus "\<exists>y. lang y = {x # xs}"
      by (rule_tac x = "Times (Atom x) y" in exI, simp add: conc_def)
  qed
next
  fix p q assume "p \<in> free_ka_set \<Sigma>" "\<exists>y. lang y = p"
  and "q \<in> free_ka_set \<Sigma>" "\<exists>y. lang y = q"
  then obtain y1 y2 where "lang y1 = p" and "lang y2 = q" by auto
  thus "\<exists>y. lang y = p \<union> q"
    by (rule_tac x = "Plus y1 y2" in exI, simp)
next
  fix p q assume "p \<in> free_ka_set \<Sigma>" "\<exists>y. lang y = p"
  and "q \<in> free_ka_set \<Sigma>" "\<exists>y. lang y = q"
  then obtain y1 y2 where "lang y1 = p" and "lang y2 = q" by auto
  thus "\<exists>y. lang y = conc p q"
    by (rule_tac x = "Times y1 y2" in exI, simp)
next
  fix p assume "p \<in> free_ka_set \<Sigma>" "\<exists>y. lang y = p"
  then obtain y where "lang y = p" by auto
  thus "\<exists>y. lang y = Regular_Set.star p"
    by (rule_tac x = "Star y" in exI, simp)
qed

fun change_atoms :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a rexp \<Rightarrow> 'b rexp" where
  "change_atoms f (Atom x) = Atom (f x)"
| "change_atoms f (Plus x y) = Plus (change_atoms f x) (change_atoms f y)"
| "change_atoms f (Times x y) = Times (change_atoms f x) (change_atoms f y)"
| "change_atoms f One = One"
| "change_atoms f Zero = Zero"
| "change_atoms f (Star x) = Star (change_atoms f x)"

lemma change_atoms_inv:
  assumes surjf: "surj f"
  shows "change_atoms f (change_atoms (inv f) x) = x"
  by (induct x, simp_all, metis assms surj_iff_all)

lemma change_atoms_surj:
  assumes surjf: "surj f"
  shows "surj (change_atoms f)"
  by (metis assms change_atoms_inv surjI)

definition lang_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a lang \<Rightarrow> 'b lang" where
  "lang_map f x \<equiv> map f ` x"

lemma lang_map_def_var: "lang_map f = (\<lambda>x. map f ` x)"
  by (default, simp add: lang_map_def)

lemma bij_map: "bij f \<Longrightarrow> bij (map f)"
  by (simp add: bij_def surj_def, metis ex_map_conv)

lemma bij_image: "bij f \<Longrightarrow> bij (op ` f)"
  apply (auto simp add: bij_def surj_def inj_on_def image_def)
  apply blast
  apply blast
  apply (rule_tac x = "inv f ` x" in exI)
  apply (subgoal_tac "\<And>a. f (inv f a) = a")
  apply simp
  by (smt CollectD UNIV_I inv_def tfl_some)

lemma bij_lang_map: "bij f \<Longrightarrow> bij (lang_map f)"
  by (simp add: lang_map_def_var, metis bij_image bij_map)

lemma image_conc: "map f ` (\<alpha> @@ \<beta>) = map f ` \<alpha> @@ map f ` \<beta>"
proof (simp add: conc_def)
  have "map f ` {xs @ ys |xs ys. xs \<in> \<alpha> \<and> ys \<in> \<beta>} = {map f (xs @ ys) |xs ys. xs \<in> \<alpha> \<and> ys \<in> \<beta>}"
    by blast
  also have "... = {(map f xs @ map f ys) |xs ys. xs \<in> \<alpha> \<and> ys \<in> \<beta>}"
    by (smt Collect_cong map_append)
  also have "... = {(xs @ ys) |xs ys. xs \<in> map f ` \<alpha> \<and> ys \<in> map f ` \<beta>}"
    by blast
  finally show "map f ` {xs @ ys |xs ys. xs \<in> \<alpha> \<and> ys \<in> \<beta>} = {xs @ ys |xs ys. xs \<in> map f ` \<alpha> \<and> ys \<in> map f ` \<beta>}" .
qed

lemma image_star1: "map f ` Regular_Set.star x \<subseteq> Regular_Set.star (map f ` x)"
proof auto
  fix a assume "a \<in> Regular_Set.star x"
  thus "map f a \<in> Regular_Set.star (map f ` x)"
    apply (induct a)
    apply (simp add: Regular_Set.star_def)
    apply (rule_tac x = 0 in exI, simp)
    by (metis (lifting) append_in_starI image_eqI map_append star_if_lang)
qed

lemma image_star2: "Regular_Set.star (map f ` x) \<subseteq> map f ` Regular_Set.star x"
proof auto
  fix a assume "a \<in> Regular_Set.star (map f ` x)"
  thus "a \<in> map f ` Regular_Set.star x"
    apply (induct a)
    apply auto
    by (metis (lifting) append_in_starI image_iff map_append star_if_lang)
qed

lemma image_star: "map f ` Regular_Set.star x = Regular_Set.star (map f ` x)"
  by (metis equalityI image_star1 image_star2)

lemma change_atoms_map: shows "lang (change_atoms f \<alpha>) = lang_map f (lang \<alpha>)"
  apply (induct \<alpha>)
  apply (simp add: lang_map_def)
  apply (simp add: lang_map_def)
  apply (simp add: lang_map_def)
  apply (simp add: lang_map_def)
  apply (metis image_Un)
  apply (simp add: lang_map_def)
  apply (metis image_conc)
  apply (simp add: lang_map_def)
  by (metis image_star)

lemma lang_change:
  assumes bij_f: "bij f"
  shows "lang (change_atoms f \<alpha>) = lang (change_atoms f \<beta>) \<Longrightarrow> lang \<alpha> = lang \<beta>"
  by (insert bij_lang_map[OF bij_f], simp add: change_atoms_map bij_def inj_on_def)

theorem changed_soundness:
  assumes bij_f: "bij f"
  shows "check_eqv (change_atoms f \<alpha>) (change_atoms f \<beta>) \<Longrightarrow> lang \<alpha> = lang \<beta>"
  by (metis soundness lang_change bij_f)

(* FIXME: Construct correct bijection in tactic *)
lemma bij_hack: "bij (\<lambda>x. 0::nat)" sorry

context kleene_algebra
begin

  fun rexp_unfold :: "'a rexp \<Rightarrow> 'a" where
    "rexp_unfold (Atom x) = x"
  | "rexp_unfold (Plus x y) = rexp_unfold x + rexp_unfold y"
  | "rexp_unfold (Times x y) = rexp_unfold x \<cdot> rexp_unfold y"
  | "rexp_unfold One = 1"
  | "rexp_unfold Zero = 0"
  | "rexp_unfold (Star x) = (rexp_unfold x)\<^sup>\<star>"

  lemma completeness:
    assumes "rexp_unfold \<alpha> \<in> carrier A" and "rexp_unfold \<beta> \<in> carrier A"
    shows "lang \<alpha> = lang \<beta> \<Longrightarrow> rexp_unfold \<alpha> = rexp_unfold \<beta>"
    sorry

end

lemma ka_is_dioid: "kleene_algebra A \<Longrightarrow> dioid A"
  by (simp add: kleene_algebra_def)

lemma (in kleene_algebra) atoms_closed: "atoms \<alpha> \<subseteq> carrier A \<Longrightarrow> rexp_unfold \<alpha> \<in> carrier A"
  by (induct \<alpha>, simp_all add: zero_closed one_closed add_closed mult_closed star_closed)

fun mk_bij_fun :: "('a \<times> 'b) list \<times> 'b \<Rightarrow> 'a \<Rightarrow> 'b" where
  "mk_bij_fun (((x, y)#xs), y') x' = (if x = x' then y else mk_bij_fun (xs, y') x')"
| "mk_bij_fun ([], y') x' = y'"

ML {*
fun safe_dest_comb ct = SOME (Thm.dest_comb ct)
  handle CTERM _ => NONE

datatype ctree = CNode of ctree * ctree
               | CLeaf of cterm;

fun mk_ctree ct =
  case safe_dest_comb ct of
    SOME (ct1, ct2) => CNode (mk_ctree ct1, mk_ctree ct2)
  | NONE => CLeaf ct;

fun flatten (CNode (t1, t2)) = flatten t1 @ flatten t2
  | flatten (CLeaf c) = [c]

fun delete_alpha_eq y (x::xs) =
    if y aconvc x
    then delete_alpha_eq y xs
    else x :: (delete_alpha_eq y xs)
  | delete_alpha_eq _ [] = []

fun rem_alpha_eq (x::xs) = x :: rem_alpha_eq (delete_alpha_eq x xs)
  | rem_alpha_eq [] = []

val cvars = rem_alpha_eq o flatten o mk_ctree

fun inst_thm thm ctrm = SOME (Drule.instantiate' [] [SOME ctrm] thm)
  handle _ => NONE

fun inst_thms thm ctrms = List.mapPartial (inst_thm thm) ctrms

val dka_expand_vars_tac = Subgoal.FOCUS (fn {concl, context, ...} =>
  let
    val vars = cvars concl
    val witnesses = Locale.get_witnesses context
    val var_subst = hd (witnesses RL @{thms kleene_algebra.rexp_unfold.simps(1)[symmetric]})
    val var_substs = inst_thms var_subst vars
  in
    Method.insert_tac var_substs 1 THEN REPEAT (etac @{thm ssubst} 1)
  end)

*}

method_setup ka = {*
Scan.succeed (fn ctxt =>
  let
    val (k::_) = Locale.get_witnesses ctxt
    val vars = map fst (Variable.dest_fixes ctxt)
  in
    METHOD (fn thms =>
      dka_expand_vars_tac ctxt 1
      THEN asm_full_simp_tac (HOL_basic_ss addsimps
        (k :: @{thms ka_is_dioid dioid.nat_order_def kleene_algebra.rexp_unfold.simps[symmetric]})) 1
      THEN rtac @{thm kleene_algebra.completeness} 1
      THEN rtac k 1
      THEN rtac @{thm kleene_algebra.atoms_closed} 1
      THEN asm_full_simp_tac (HOL_basic_ss addsimps [k]) 1
      THEN asm_full_simp_tac @{simpset} 1
      THEN rtac @{thm kleene_algebra.atoms_closed} 1
      THEN asm_full_simp_tac (HOL_basic_ss addsimps [k]) 1
      THEN asm_full_simp_tac @{simpset} 1
      THEN rtac @{thm changed_soundness[OF bij_hack]} 1
      THEN asm_full_simp_tac @{simpset} 1
      THEN eval_tac ctxt 1)
  end)
*}

context kleene_algebra
begin

  lemma "x \<in> carrier A \<Longrightarrow> x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>" by ka

  lemma "x \<in> carrier A \<Longrightarrow> x + x \<sqsubseteq> x\<^sup>\<star>" by ka

end

end
