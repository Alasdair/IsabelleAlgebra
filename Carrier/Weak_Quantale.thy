theory WeakQuantale
  imports Lattice Galois_Connection
begin

section {* Quantales *}

record 'a mult_ord = "'a ord" +
  one :: "'a" ("1\<index>")
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<index>" 80)

lemma set_comp_subset: "{x. P x \<and> x \<in> A} \<subseteq> A"
  by (metis (lifting) mem_Collect_eq subsetI)

locale weak_quantale = fixes A (structure)
  assumes weak_quantale_cl: "complete_lattice A"
  and mult_type: "op \<cdot> \<in> carrier A \<rightarrow> carrier A \<rightarrow> carrier A"
  and mult_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
  and weak_inf_distl: "\<lbrakk>x \<in> carrier A; Y \<subseteq> carrier A; Y \<noteq> {}\<rbrakk> \<Longrightarrow> x \<cdot> order.lub A Y = order.lub A ((\<lambda>y. x\<cdot>y) ` Y)"
  and inf_distr: "\<lbrakk>x \<in> carrier A; Y \<subseteq> carrier A\<rbrakk> \<Longrightarrow> order.lub A Y \<cdot> x = order.lub A ((\<lambda>y. y\<cdot>x) ` Y)"
  and one_closed: "one A \<in> carrier A"
  and mult_onel [simp]: "x \<in> carrier A \<Longrightarrow> one A \<cdot> x = x"
  and mult_oner [simp]: "x \<in> carrier A \<Longrightarrow> x \<cdot> one A = x"

sublocale weak_quantale \<subseteq> lat: complete_lattice A
  by (metis weak_quantale_cl)

context weak_quantale
begin

  lemma mult_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier A"
    by (metis typed_application mult_type)

  lemma quantale_order: "order A"
    by (metis cl_to_order weak_quantale_cl)

  abbreviation qplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 70) where
    "x + y \<equiv> order.join A x y"

  abbreviation qzero :: "'a" ("0") where
    "qzero \<equiv> complete_join_semilattice.bot A"

  lemma distl: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> (y + z) = (x \<cdot> y) + (x \<cdot> z)"
  proof -
    assume xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    hence "{y,z} \<subseteq> carrier A" by (metis is_lub_def is_ub_def join_ex)
    hence "x \<cdot> \<Sigma> {y,z} = \<Sigma> ((\<lambda>y. x\<cdot>y) ` {y,z})" by (metis empty_not_insert weak_inf_distl xc)
    thus ?thesis by (simp add: join_def)
  qed

  lemma distr: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (y + z) \<cdot> x = (y \<cdot> x) + (z \<cdot> x)"
  proof -
    assume xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    hence "{y,z} \<subseteq> carrier A" by (metis is_lub_def is_ub_def join_ex)
    hence "\<Sigma> {y,z} \<cdot> x = \<Sigma> ((\<lambda>y. y\<cdot>x) ` {y,z})" by (metis inf_distr xc)
    thus ?thesis by (simp add: join_def)
  qed

  lemma bot_zero: "x \<in> carrier A \<Longrightarrow> 0 \<cdot> x = 0"
    by (metis empty_lub empty_subsetI image_empty inf_distr)

  definition star :: "'a \<Rightarrow> 'a"  ("_\<^sup>*" [101] 100) where
    "x\<^sup>* = \<mu>\<^bsub>A\<^esub>(\<lambda>y. 1 + y\<cdot>x)"

  lemma star_closed: assumes xc: "x \<in> carrier A" shows "x\<^sup>* \<in> carrier A"
    unfolding star_def
  proof (rule least_fixpoint_closed)
    show "complete_lattice A"
      by (metis weak_quantale_cl)

    show "(\<lambda>y. 1 + y\<cdot>x) \<in> carrier A \<rightarrow> carrier A"
      by (metis (lifting, no_types) assms ftype_pred join_closed mult_closed one_closed)

    show "isotone A A (\<lambda>y. 1 + y\<cdot>x)"
      apply (simp add: isotone_def, safe, metis quantale_order)
      by (smt assms bin_lub_var distr join_closed join_idem leq_def mult_closed one_closed)
  qed

  (* FIXME: Definition of directedness *)

  text {* The star is scott continuous, i.e. it preserves suprema in
  all directed subsets. *}

  lemma star_scott_continuous:
    assumes xc: "x \<in> carrier A"
    and D_subset: "D \<subseteq> carrier A"
    and D_directed: "directed \<lparr>carrier = D, le = op \<sqsubseteq>, \<dots> = ord.more A\<rparr>"
    and D_non_empty: "D \<noteq> {}"
    shows "1 + \<Sigma> D \<cdot> x = \<Sigma> ((\<lambda>y. 1 + y\<cdot>x) ` D)"
  proof -
    have "\<Sigma> ((\<lambda>y. 1 + y\<cdot>x) ` D) = \<Sigma> (((\<lambda>y. 1+y) \<circ> (\<lambda>y. y\<cdot>x)) ` D)"
      by (simp add: o_def)
    moreover have "... = \<Sigma> ((\<lambda>y. 1+y) ` (\<lambda>y. y\<cdot>x) ` D)"
      by (metis image_compose)
    moreover have "... = \<Sigma> ((\<Sigma> \<circ> (\<lambda>y. {1,y})) ` (\<lambda>y. y\<cdot>x) ` D)"
      by (simp add: join_def o_def)
    moreover have "... = \<Sigma> (\<Sigma> ` (\<lambda>y. {1,y}) ` (\<lambda>y. y\<cdot>x) ` D)"
      by (metis image_compose)
    moreover have "... = \<Sigma> (\<Union> ((\<lambda>y. {1,y}) ` (\<lambda>y. y\<cdot>x) ` D))"
      apply (rule lub_inf_idem)
      apply (rule_tac ?A = "carrier A" in set_image_type)+
      apply (metis D_subset)
      apply (simp add: ftype_pred)
      apply (metis mult_closed xc)
      apply (simp add: ftype_pred)
      by (metis one_closed)
    moreover have "... = \<Sigma> ({1} \<union> ((\<lambda>y. y\<cdot>x) ` D))"
      by (simp, metis D_non_empty)
    moreover have "... = \<Sigma> {1} + \<Sigma> ((\<lambda>y. y\<cdot>x) ` D)"
      apply (rule lub_union, simp_all add: one_closed)
      apply (rule_tac ?A = "carrier A" in set_image_type, simp add: D_subset)
      by (metis (no_types) ftype_pred mult_closed xc)
    moreover have "... = 1 + \<Sigma> ((\<lambda>y. y\<cdot>x) ` D)"
      by (metis one_closed singleton_lub)
    moreover have "... = 1 + \<Sigma> D \<cdot> x"
      by (metis D_non_empty D_subset inf_distr xc)
    ultimately show ?thesis by metis
  qed

  primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<^bsup>_\<^esup>" [101,50] 100) where
    "x\<^bsup>0\<^esup>  = 1"
  | "x\<^bsup>Suc n\<^esup> = x\<cdot>x\<^bsup>n\<^esup>"

  lemma power_closed: "x \<in> carrier A \<Longrightarrow> x\<^bsup>n\<^esup> \<in> carrier A"
  proof (induct n)
    case 0 show ?case by (simp, metis one_closed)
    case (Suc m) show ?case
      by (metis "0" Suc.hyps mult_closed power.simps(2))
  qed

  lemma power_add: assumes xc: "x \<in> carrier A" shows "x\<^bsup>m\<^esup>\<cdot>x\<^bsup>n\<^esup> = x\<^bsup>m+n\<^esup>"
  proof (induct m)
    case 0 show ?case by (metis add_0 assms mult_onel power.simps(1) power_closed)
    case (Suc m) show ?case by (smt Suc assms mult_assoc power.simps(2) power_closed)
  qed

  lemma power_commutes: "x \<in> carrier A \<Longrightarrow> x\<^bsup>n\<^esup>\<cdot>x = x\<cdot>x\<^bsup>n\<^esup>"
    by (smt power_add mult_oner power.simps)

  lemma power_inductl_var:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "x\<cdot>y \<sqsubseteq> y \<longrightarrow> x\<^bsup>n\<^esup>\<cdot>y \<sqsubseteq> y"
    apply (induct n)
    apply (metis eq_refl mult_onel power.simps(1) yc)
    by (smt distl join_assoc leq_def mult_assoc mult_closed power.simps(2) power_closed xc yc)

  lemma power_inductr_var:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "y\<cdot>x \<sqsubseteq> y \<longrightarrow> y\<cdot>x\<^bsup>n\<^esup> \<sqsubseteq> y"
    apply (induct n)
    apply (metis eq_refl mult_oner power.simps(1) yc)
    by (smt distr join_assoc leq_def mult_assoc mult_closed power.simps(2) power_closed xc yc)

  definition powers :: "'a \<Rightarrow> 'a set" where
    "powers x  = {y. (\<exists>i. y = x\<^bsup>i\<^esup>)}"

  lemma powers_closed: "x \<in> carrier A \<Longrightarrow> powers x \<subseteq> carrier A"
    by (simp add: powers_def, auto, metis power_closed)

  definition powersUpTo :: "nat \<Rightarrow> 'a \<Rightarrow> 'a set" where
    "powersUpTo n x \<equiv> {x\<^bsup>i\<^esup> |i. Suc i \<le> n}"

  subsection {* The star as a sum of powers *}

  text {* We can now show that $x^*$ in a quantale can be defined as
    the sum of the powers of $x$. *}

  lemma star_power: assumes xc: "x \<in> carrier A" shows "x\<^sup>* = \<Sigma> (powers x)"
  proof -
    let ?STAR_FUN = "\<lambda>y. 1 + y\<cdot>x"

    have star_chain: "\<mu>\<^bsub>A\<^esub>?STAR_FUN = \<Sigma> (carrier (kleene_chain A ?STAR_FUN))"
    proof (rule kleene_fixed_point, unfold_locales)
      show "?STAR_FUN \<in> carrier A \<rightarrow> carrier A"
        by (smt ftype_pred one_closed mult_closed join_closed xc)
    next
      show "isotone A A ?STAR_FUN"
        apply (simp add: isotone_def, safe, metis quantale_order)
        by (smt assms distr join_assoc join_closed join_idem leq_def mult_closed one_closed)
    next
      fix D assume "D \<subseteq> carrier A" and "directed \<lparr>carrier = D, le = op \<sqsubseteq>, \<dots> = ord.more A\<rparr>" and "D \<noteq> {}"
      thus "1 + \<Sigma> D \<cdot> x = \<Sigma> ((\<lambda>y. 1 + y\<cdot>x) ` D)"
        by (metis assms star_scott_continuous)
    qed

    have iter_powersUpTo: "\<forall>n. iter n ?STAR_FUN 0 = \<Sigma> (powersUpTo n x)"
    proof
      fix n show "iter n ?STAR_FUN 0 = \<Sigma> (powersUpTo n x)"
      proof (induct n)
        case 0 show ?case
          by (simp add: iter_def powersUpTo_def)
        case (Suc n)
        have "iter (Suc n) ?STAR_FUN 0 = 1 + iter n ?STAR_FUN 0 \<cdot> x"
          by (metis Lattice.iter.simps(2) Suc)
        moreover have "... = 1 + \<Sigma> (powersUpTo n x) \<cdot> x"
          by (metis Suc)
        moreover have "... = 1 + \<Sigma> {x\<^bsup>i\<^esup> |i. Suc i \<le> n} \<cdot> x"
          by (simp add: powersUpTo_def)
        moreover have "... = 1 + \<Sigma> ((\<lambda>y. y\<cdot>x) ` {x\<^bsup>i\<^esup> |i. Suc i \<le> n})"
          apply (rule_tac f = "\<lambda>x. (1::'a) + x" in arg_cong)
          apply (rule inf_distr)
          apply (metis xc)
          by (smt CollectD assms power_closed subsetI)
        moreover have "... = 1 + \<Sigma> {x\<^bsup>i\<^esup> \<cdot> x |i. Suc i \<le> n}"
          by (simp add: image_def, rule_tac ?f = "\<lambda>Y. 1 + \<Sigma> Y" in arg_cong, safe, auto+)
        moreover have "... = 1 + \<Sigma> {x\<^bsup>Suc i\<^esup> |i. Suc i \<le> n}"
          by (simp add: power_commutes[OF xc])
        moreover have "... = \<Sigma> {1} + \<Sigma> {x\<^bsup>Suc i\<^esup> |i. Suc i \<le> n}"
          by (metis (lifting) one_closed singleton_lub)
        moreover have "... = \<Sigma> ({1} \<union> {x\<^bsup>Suc i\<^esup> |i. Suc i \<le> n})"
          apply (rule HOL.sym, rule lub_union)
          apply (metis empty_subsetI insert_subset one_closed)
          apply (safe, auto)
          by (metis assms power.simps(2) power_closed)
        moreover have "... = \<Sigma> (powersUpTo (Suc n) x)"
          apply (rule_tac ?f = "\<lambda>Y. \<Sigma> Y" in arg_cong)
          apply (simp add: powersUpTo_def, safe, auto+, (metis le0 power.simps)+)
          by (metis not0_implies_Suc power.simps(1) power.simps(2))
        ultimately show ?case by metis
      qed
    qed

    have "\<mu>\<^bsub>A\<^esub>?STAR_FUN = \<Sigma> {z. \<exists>i. z = \<Sigma> (powersUpTo i x)}"
      by (simp add: star_chain kleene_chain_def iter_powersUpTo)
    moreover have "... = \<Sigma> (\<Sigma> ` {z. \<exists>i. z = powersUpTo i x})"
      by (rule_tac ?f = "\<lambda>Y. \<Sigma> Y" in arg_cong, safe, auto+)
    moreover have "... = \<Sigma> (\<Union> {z. \<exists>i. z = powersUpTo i x})"
      by (rule lub_inf_idem, safe, auto, simp add: powersUpTo_def, safe, metis assms power_closed)
    moreover have "... = \<Sigma> (powers x)"
      apply (rule_tac ?f = "\<lambda>Y. \<Sigma> Y" in arg_cong, safe, auto+)
      apply (simp_all add: powersUpTo_def powers_def, metis)
      by (metis (lifting, full_types) le_add2 mem_Collect_eq)
    ultimately show ?thesis
      by (metis star_def)
  qed

  lemma star_unfoldl: assumes xc: "x \<in> carrier A" shows "1 + x\<cdot>x\<^sup>* = x\<^sup>*"
  proof (insert xc, unfold star_power)
    have power_unfold: "({1} \<union> ((\<lambda>y. x\<cdot>y) ` powers x)) = (powers x)"
      apply (simp add: image_def powers_def, auto)
      by (metis assms nat.exhaust power.simps(1) power.simps(2) power_commutes)+
    hence "\<Sigma> (powers x) = \<Sigma> ({1} \<union> ((\<lambda>y. x\<cdot>y) ` powers x))"
      by auto
    moreover have "... = \<Sigma> {1} + \<Sigma> ((\<lambda>y. x\<cdot>y) ` powers x)"
      by (rule lub_union, simp_all, metis one_closed, metis power_unfold assms le_supE powers_closed)
    moreover have "... = 1 + \<Sigma> ((\<lambda>y. x\<cdot>y) ` powers x)"
      by (metis one_closed singleton_lub)
    moreover have "... = 1 + x \<cdot> \<Sigma> (powers x)"
      by (metis (lifting) assms empty_is_image empty_not_insert le_sup_iff power_unfold powers_closed sup_eq_bot_iff weak_inf_distl)
    ultimately show "1 + x \<cdot> \<Sigma> (powers x) = \<Sigma> (powers x)"
      by auto
  qed

  lemma star_unfoldr: assumes xc: "x \<in> carrier A" shows "1 + x\<^sup>*\<cdot>x = x\<^sup>*"
    unfolding star_def
  proof (rule fixpoint_computation)
    show "complete_lattice A"
      by (metis weak_quantale_cl)

    show "(\<lambda>y. 1 + y\<cdot>x) \<in> carrier A \<rightarrow> carrier A"
      apply (simp add: ftype_pred)
      by (metis assms join_closed mult_closed one_closed)

    show "isotone A A (\<lambda>y. 1 + y\<cdot>x)"
      apply (simp add: isotone_def, safe, metis quantale_order)
      by (smt assms bin_lub_var distr join_closed join_idem leq_def mult_closed one_closed)
  qed

  text {* Infinite iteration *}

  definition loop :: "'a \<Rightarrow> 'a" ("_\<^sup>\<infinity>" [101] 100) where
    "x\<^sup>\<infinity> \<equiv> \<nu>\<^bsub>A\<^esub>(\<lambda>y. x\<cdot>y)"

  lemma mult_left_iso: assumes xc: "x \<in> carrier A" shows "isotone A A (op \<cdot> x)"
    unfolding isotone_def
    apply safe
    apply (metis quantale_order)+
    by (metis (lifting) assms distl leq_def mult_closed)

  lemma loop_unfold: assumes xc: "x \<in> carrier A" shows "x\<cdot>x\<^sup>\<infinity> = x\<^sup>\<infinity>"
    unfolding loop_def
  proof (rule greatest_fixpoint_computation)
    show "complete_lattice A"
      by (metis weak_quantale_cl)

    show "op \<cdot> x \<in> carrier A \<rightarrow> carrier A"
      by (metis (lifting) assms typed_application mult_type)

    show "isotone A A (op \<cdot> x)"
      by (metis assms mult_left_iso)
  qed

  text {* Finite or infinite iteration *}

  definition omega :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [101] 100) where
    "x\<^sup>\<omega> \<equiv> \<nu>\<^bsub>A\<^esub>(\<lambda>y. 1 + x\<cdot>y)"

  definition splits :: "'a \<Rightarrow> bool" where
    "splits x \<equiv> \<forall>y\<in>carrier A. \<forall>z\<in>carrier A. (x \<sqinter> y\<cdot>z) \<sqsubseteq> (x \<sqinter> y) \<cdot> (x \<sqinter> z)"

end


locale weak_boolean_quantale = weak_quantale +
  assumes weak_boolean_quantale_cbl: "complete_boolean_lattice A"

sublocale weak_boolean_quantale \<subseteq> complete_boolean_lattice
  by (metis weak_boolean_quantale_cbl)

context weak_boolean_quantale
begin

  lemma double_compl: "x \<in> carrier A \<Longrightarrow> !(!x) = x"
    by (smt bot_closed bot_oner ccompl_bot ccompl_closed ccompl_top dist1 eq_refl leq_meet_def meet_comm)

  lemma zero_not_top: "!\<top> = 0"
    by (metis ccompl_bot ccompl_closed top_closed top_onel)

  lemma top_not_zero: "\<top> = !0"
    by (metis double_compl top_closed zero_not_top)

  lemma de_morgan1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !x \<sqinter> !y = !(x + y)"
    apply (subgoal_tac "!x \<in> carrier A" "!y \<in> carrier A" "!x \<sqinter> !y \<in> carrier A" "!(x + y) \<in> carrier A")
    apply (rule order.order_antisym[of A])
    defer
    apply (simp_all add: leq_def)
    apply (smt bot_oner ccompl_bot ccompl_top dist1 dist2 double_compl join_closed join_comm meet_assoc top_oner)
    apply (smt absorb2 bot_closed bot_onel ccompl_top complete_boolean_lattice.ccompl_bot dist1 join_closed meet_assoc meet_comm top_oner weak_boolean_quantale_cbl)
    apply (metis ccompl_closed join_closed)
    apply (metis meet_closed)
    apply (metis ccompl_closed)
    apply (metis ccompl_closed)
    by (metis quantale_order)

  lemma meet_def_boolean: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> y = !((!x)+(!y))"
    by (metis ccompl_closed de_morgan1 double_compl)

  lemma de_morgan2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !x + !y = !(x \<sqinter> y)"
    by (metis (lifting) complete_boolean_lattice.ccompl_closed double_compl join_closed meet_def_boolean weak_boolean_quantale_cbl)

  lemma compl_anti: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longleftrightarrow> !y \<sqsubseteq> !x"
    by (smt ccompl_closed double_compl join_comm leq_def_right leq_meet_def meet_def_boolean)

  lemma de_morgan3: "x+y = !(!x \<sqinter> !y)"
    sledgehammer [timeout = 300]
    by (metis double_compl meet_def)


  lemma shunting:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "x \<sqinter> y \<sqsubseteq> z \<longleftrightarrow> y \<sqsubseteq> !x + z"
  proof -
    have xyc: "x \<sqinter> y \<in> carrier A"
      by (metis meet_closed xc yc)
    have xzc: "!x + z \<in> carrier A"
      by (metis ccompl_closed join_closed xc zc)

    from xc xyc yc xzc have "x \<sqinter> y \<sqsubseteq> z \<longrightarrow> y \<sqsubseteq> !x + z"
      apply (simp add: leq_def)
      
      
      
      
      
    apply (simp add: leq_def)

  lemma split_distribute_star:
    assumes xc: "x \<in> carrier A" and "splits x"
    shows "\<forall>y\<in>carrier A. x \<sqinter> y\<^sup>* \<sqsubseteq> (x \<sqinter> y)\<^sup>*"
  proof
    fix y assume yc: "y \<in> carrier A"
    have "x \<sqinter> y\<^sup>* \<sqsubseteq> (x \<sqinter> y)\<^sup>* \<longleftrightarrow> y\<^sup>* \<sqsubseteq> !x + (x \<sqinter> y)\<^sup>*"
      
    

end

end
