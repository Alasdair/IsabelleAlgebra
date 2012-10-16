theory Quantale
  imports Lattice Galois_Connection
begin

section {* Quantales *}

record 'a mult_ord = "'a ord" +
  one :: "'a" ("1\<index>")
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<index>" 80)

lemma set_comp_subset: "{x. P x \<and> x \<in> A} \<subseteq> A"
  by (metis (lifting) mem_Collect_eq subsetI)

locale unital_quantale = fixes A (structure)
  assumes quantale_complete_lattice: "complete_lattice A"
  and mult_type: "op \<cdot> \<in> carrier A \<rightarrow> carrier A \<rightarrow> carrier A"
  and mult_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
  and inf_distl: "\<lbrakk>x \<in> carrier A; Y \<subseteq> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> order.lub A Y = order.lub A ((\<lambda>y. x\<cdot>y) ` Y)"
  and inf_distr: "\<lbrakk>x \<in> carrier A; Y \<subseteq> carrier A\<rbrakk> \<Longrightarrow> order.lub A Y \<cdot> x = order.lub A ((\<lambda>y. y\<cdot>x) ` Y)"
  and one_closed: "one A \<in> carrier A"
  and mult_onel [simp]: "x \<in> carrier A \<Longrightarrow> one A \<cdot> x = x"
  and mult_oner [simp]: "x \<in> carrier A \<Longrightarrow> x \<cdot> one A = x"

sublocale unital_quantale \<subseteq> lat: complete_lattice A
  by (metis quantale_complete_lattice)

context unital_quantale
begin

  lemma mult_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier A"
    by (metis typed_application mult_type)

  lemma quantale_order: "order A"
    by (metis cl_to_order quantale_complete_lattice)

  abbreviation qzero :: "'a" ("0") where
    "qzero \<equiv> complete_join_semilattice.bot A"

  abbreviation qplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 70) where
    "x + y \<equiv> order.join A x y"

  lemma bot_zeror: "x \<in> carrier A \<Longrightarrow> x \<cdot> 0 = 0"
    by (metis empty_lub empty_subsetI image_empty inf_distl)

  lemma bot_zerol: "x \<in> carrier A \<Longrightarrow> 0 \<cdot> x = 0"
    by (metis empty_lub empty_subsetI image_empty inf_distr)

  lemma distl: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> (y + z) = (x \<cdot> y) + (x \<cdot> z)"
  proof -
    assume xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    hence "{y,z} \<subseteq> carrier A" by (metis is_lub_def is_ub_def join_ex)
    hence "x \<cdot> \<Sigma> {y,z} = \<Sigma> ((\<lambda>y. x\<cdot>y) ` {y,z})" by (metis inf_distl xc)
    thus ?thesis by (simp add: join_def)
  qed

  lemma distr: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (y + z) \<cdot> x = (y \<cdot> x) + (z \<cdot> x)"
  proof -
    assume xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    hence "{y,z} \<subseteq> carrier A" by (metis is_lub_def is_ub_def join_ex)
    hence "\<Sigma> {y,z} \<cdot> x = \<Sigma> ((\<lambda>y. y\<cdot>x) ` {y,z})" by (metis inf_distr xc)
    thus ?thesis by (simp add: join_def)
  qed

  lemma mult_left_join_preserving: "x \<in> carrier A \<Longrightarrow> join_preserving A A (\<lambda>y. x\<cdot>y)"
    by (metis assms inf_distl join_preserving_def quantale_order)

  lemma mult_right_join_preserving: "x \<in> carrier A \<Longrightarrow> join_preserving A A (\<lambda>y. y\<cdot>x)"
    by (metis assms inf_distr join_preserving_def quantale_order)

  definition preimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightharpoondown>" 60) where
    "preimp x y \<equiv> \<Sigma> {z. x \<cdot> z \<sqsubseteq> y \<and> z \<in> carrier A}"

  lemma preimp_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<rightharpoondown> y \<in> carrier A"
  proof -
    let ?S = "{z. x\<cdot>z \<sqsubseteq> y \<and> z \<in> carrier A}"

    have "?S \<subseteq> carrier A" by (rule set_comp_subset)
    moreover hence "\<exists>x\<in>carrier A. is_lub x ?S" by (smt lub_ex)
    ultimately have "\<Sigma> ?S \<in> carrier A" by (smt lub_closed)
    thus ?thesis by (metis preimp_def)
  qed

  lemma preimp_type: "op \<rightharpoondown> \<in> carrier A \<rightarrow> carrier A \<rightarrow> carrier A"
    by (metis (no_types) ftype_pred preimp_closed)

  lemma preimp_conn: assumes xc: "x \<in> carrier A"
    shows "complete_lattice_connection A A (\<lambda>y. x\<cdot>y) (\<lambda>y. x \<rightharpoondown> y)"
  proof (rule suprema_galois_left, (metis quantale_complete_lattice)+)
    show "(\<lambda>y. x\<cdot>y) \<in> carrier A \<rightarrow> carrier A"
      by (metis mult_type xc typed_application)

    show "(\<lambda>y. x \<rightharpoondown> y) \<in> carrier A \<rightarrow> carrier A"
      by (metis preimp_type xc typed_application)

    show "ex_join_preserving A A (\<lambda>y. x\<cdot>y)"
      by (metis assms ex_join_preserving_def inf_distl quantale_order)

    show "\<forall>y\<in>carrier A. order.is_lub A (x \<rightharpoondown> y) {z. x\<cdot>z \<sqsubseteq> y \<and> z \<in> carrier A}"
      by (metis (full_types) is_lub_lub preimp_def set_comp_subset)
  qed

  lemma mult_left_iso: "x \<in> carrier A \<Longrightarrow> isotone A A (\<lambda>y. x\<cdot>y)"
    by (metis cl_to_galois galois_connection.lower_iso preimp_conn)

  lemma preimp_conn_prop:
    "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> y \<sqsubseteq> z \<longleftrightarrow> y \<sqsubseteq> x \<rightharpoondown> z"
    apply (rule galois_connection.galois_property)
    by (metis cl_to_galois preimp_conn mult_closed preimp_closed)+

  lemma preimp_mp: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> (x \<rightharpoondown> y) \<sqsubseteq> y"
    by (metis (lifting) order.order_refl preimp_closed preimp_conn_prop quantale_order)

  lemma preimp_refl: "x \<in> carrier A \<Longrightarrow> 1 \<sqsubseteq> x \<rightharpoondown> x"
    by (metis mult_oner one_closed order_refl preimp_conn_prop)

  lemma preimp_trans:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "(x \<rightharpoondown> y) \<cdot> (y \<rightharpoondown> z) \<sqsubseteq> x \<rightharpoondown> z"
  proof -
    have "y \<cdot> (y \<rightharpoondown> z) \<sqsubseteq> z"
      by (metis preimp_mp yc zc)
    moreover have "x \<cdot> (x \<rightharpoondown> y) \<cdot> (y \<rightharpoondown> z) \<sqsubseteq> y \<cdot> (y \<rightharpoondown> z)"
      by (metis (no_types) distr leq_def mult_closed preimp_closed preimp_mp xc yc zc)
    ultimately have "x \<cdot> (x \<rightharpoondown> y) \<cdot> (y \<rightharpoondown> z) \<sqsubseteq> z"
      by (metis (lifting) mult_closed order_trans preimp_closed xc yc zc)
    thus "(x \<rightharpoondown> y) \<cdot> (y \<rightharpoondown> z) \<sqsubseteq> x \<rightharpoondown> z"
      by (metis mult_assoc mult_closed preimp_closed preimp_conn_prop xc yc zc)
  qed

  definition postimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leftharpoondown>" 60) where
    "postimp x y \<equiv> \<Sigma> {z. z \<cdot> y \<sqsubseteq> x \<and> z \<in> carrier A}"

  lemma postimp_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<leftharpoondown> y \<in> carrier A"
  proof -
    let ?S = "{z. z\<cdot>y \<sqsubseteq> x \<and> z \<in> carrier A}"

    have "?S \<subseteq> carrier A" by (rule set_comp_subset)
    moreover hence "\<exists>x\<in>carrier A. is_lub x ?S" by (smt lub_ex)
    ultimately have "\<Sigma> ?S \<in> carrier A" by (smt lub_closed)
    thus ?thesis by (metis postimp_def)
  qed

  lemma postimp_type: "op \<leftharpoondown> \<in> carrier A \<rightarrow> carrier A \<rightarrow> carrier A"
    by (metis (no_types) ftype_pred postimp_closed)

  lemma postimp_conn: assumes xc: "x \<in> carrier A"
    shows "complete_lattice_connection A A (\<lambda>y. y\<cdot>x) (\<lambda>y. y \<leftharpoondown> x)"
  proof (rule suprema_galois_left, metis quantale_complete_lattice, metis quantale_complete_lattice)
    show "(\<lambda>y. y\<cdot>x) \<in> carrier A \<rightarrow> carrier A"
      by (metis (no_types) assms ftype_pred mult_closed)

    show "(\<lambda>y. y \<leftharpoondown> x) \<in> carrier A \<rightarrow> carrier A"
      by (metis (no_types) assms ftype_pred postimp_closed)

    show "ex_join_preserving A A (\<lambda>y. y\<cdot>x)"
      by (metis assms ex_join_preserving_def inf_distr quantale_order)

    show "\<forall>y\<in>carrier A. order.is_lub A (y \<leftharpoondown> x) {z. z\<cdot>x \<sqsubseteq> y \<and> z \<in> carrier A}"
      by (metis (full_types) is_lub_lub postimp_def set_comp_subset)
  qed

  lemma mult_right_iso: "x \<in> carrier A \<Longrightarrow> isotone A A (\<lambda>y. y\<cdot>x)"
    by (metis cl_to_galois galois_connection.lower_iso postimp_conn)

  lemma postimp_conn_prop:
    "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<cdot> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<leftharpoondown> y"
    apply (rule galois_connection.galois_property)
    by (metis (lifting) cl_to_galois postimp_conn mult_closed postimp_closed)+

  lemma postimp_mp: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (y \<leftharpoondown> x) \<cdot> x \<sqsubseteq> y"
    by (metis (lifting) order.order_refl postimp_closed postimp_conn_prop quantale_order)

  lemma postimp_refl: "x \<in> carrier A \<Longrightarrow> 1 \<sqsubseteq> x \<leftharpoondown> x"
    by (metis eq_refl mult_onel one_closed postimp_conn_prop)

  lemma postimp_trans:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "(x \<leftharpoondown> y) \<cdot> (y \<leftharpoondown> z) \<sqsubseteq> x \<leftharpoondown> z"
  proof -
    have "(x \<leftharpoondown> y) \<cdot> (y \<leftharpoondown> z) \<cdot> z \<sqsubseteq> (x \<leftharpoondown> y) \<cdot> y"
      by (metis (no_types) postimp_mp distl leq_def mult_assoc mult_closed postimp_closed xc yc zc)
    hence "(x \<leftharpoondown> y) \<cdot> (y \<leftharpoondown> z) \<cdot> z \<sqsubseteq> x"
      by (metis (lifting) mult_closed order.order_trans postimp_closed postimp_mp quantale_order xc yc zc)
    thus "(x \<leftharpoondown> y) \<cdot> (y \<leftharpoondown> z) \<sqsubseteq> x \<leftharpoondown> z"
      by (metis mult_closed postimp_closed postimp_conn_prop xc yc zc)
  qed

  subsection {* Defining the star operation *}

  definition star :: "'a \<Rightarrow> 'a"  ("_\<^sup>\<star>" [101] 100) where
    "x\<^sup>\<star> = \<mu>\<^bsub>A\<^esub>(\<lambda>y. 1 + x\<cdot>y)"

  lemma star_closed: assumes xc: "x \<in> carrier A" shows "x\<^sup>\<star> \<in> carrier A"
    unfolding star_def
  proof (rule least_fixpoint_closed)
    show "complete_lattice A"
      by (metis quantale_complete_lattice)

    show "(\<lambda>y. 1 + x \<cdot> y) \<in> carrier A \<rightarrow> carrier A"
      by (metis (no_types) assms ftype_pred join_closed mult_type one_closed)

    show "isotone A A (\<lambda>y. 1 + x \<cdot> y)"
      apply (simp add: isotone_def, safe, metis quantale_order)
      by (smt assms bin_lub_var distl join_closed join_idem leq_def mult_closed one_closed)
  qed

  subsection {* Continuity of the star operation *}

  lemma star_scott_ne_continuous:
    assumes xc: "x \<in> carrier A"
    and D_subset: "D \<subseteq> carrier A"
    and D_directed: "directed \<lparr>carrier = D, le = op \<sqsubseteq>, \<dots> = ord.more A\<rparr>"
    and D_non_empty: "D \<noteq> {}"
    shows "1 + x \<cdot> \<Sigma> D = \<Sigma> ((\<lambda>y. 1 + x\<cdot>y) ` D)"
  proof -
    have "\<Sigma> ((\<lambda>y. 1 + x\<cdot>y) ` D) = \<Sigma> (((\<lambda>y. 1+y) \<circ> (\<lambda>y. x\<cdot>y)) ` D)"
      by (simp add: o_def)
    moreover have "... = \<Sigma> ((\<lambda>y. 1+y) ` (\<lambda>y. x\<cdot>y) ` D)"
      by (metis image_compose)
    moreover have "... = \<Sigma> ((\<Sigma> \<circ> (\<lambda>y. {1,y})) ` (\<lambda>y. x\<cdot>y) ` D)"
      by (simp add: join_def o_def)
    moreover have "... = \<Sigma> (\<Sigma> ` (\<lambda>y. {1,y}) ` (\<lambda>y. x\<cdot>y) ` D)"
      by (metis image_compose)
    moreover have "... = \<Sigma> (\<Union> ((\<lambda>y. {1,y}) ` (\<lambda>y. x\<cdot>y) ` D))"
      apply (rule lub_inf_idem)
      apply (rule_tac ?A = "carrier A" in set_image_type)+
      apply (metis D_subset)
      apply (metis ftype_pred mult_type xc)
      apply (simp add: ftype_pred)
      by (metis one_closed)
    moreover have "... = \<Sigma> ({1} \<union> ((\<lambda>y. x\<cdot>y) ` D))"
      by (simp, metis D_non_empty)
    moreover have "... = \<Sigma> {1} + \<Sigma> ((\<lambda>y. x\<cdot>y) ` D)"
      apply (rule lub_union, simp_all add: one_closed)
      apply (rule_tac ?A = "carrier A" in set_image_type, simp add: D_subset)
      by (metis ftype_pred mult_type xc)
    moreover have "... = 1 + \<Sigma> ((\<lambda>y. x\<cdot>y) ` D)"
      by (metis one_closed singleton_lub)
    moreover have "... = 1 + x \<cdot> \<Sigma> D"
      by (metis (lifting) D_subset inf_distl xc)
    ultimately show ?thesis by metis
  qed

  subsection {* Powers *}

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

  lemma star_power: assumes xc: "x \<in> carrier A" shows "x\<^sup>\<star> = \<Sigma> (powers x)"
  proof -
    let ?STAR_FUN = "\<lambda>y. 1 + x\<cdot>y"

    have star_chain: "\<mu>\<^bsub>A\<^esub>?STAR_FUN = \<Sigma> (carrier (kleene_chain A ?STAR_FUN))"
    proof (rule kleene_fixed_point, unfold_locales)
      show "?STAR_FUN \<in> carrier A \<rightarrow> carrier A"
        by (smt ftype_pred one_closed mult_closed join_closed xc)
    next
      show "isotone A A ?STAR_FUN"
        apply (simp add: isotone_def, safe, metis quantale_order)
        by (smt assms bin_lub_var distl join_closed join_idem leq_def mult_closed one_closed)
    next
      fix D assume "D \<subseteq> carrier A" and "directed \<lparr>carrier = D, le = op \<sqsubseteq>, \<dots> = ord.more A\<rparr>" and "D \<noteq> {}"
      thus "1 + x \<cdot> \<Sigma> D = \<Sigma> ((\<lambda>y. 1 + x \<cdot> y) ` D)"
        by (metis assms star_scott_ne_continuous)
    qed

    have iter_powersUpTo: "\<forall>n. iter n ?STAR_FUN 0 = \<Sigma> (powersUpTo n x)"
    proof
      fix n show "iter n ?STAR_FUN 0 = \<Sigma> (powersUpTo n x)"
      proof (induct n)
        case 0 show ?case
          by (simp add: iter_def powersUpTo_def)
        case (Suc n)
        have "iter (Suc n) ?STAR_FUN 0 = 1 + x \<cdot> iter n ?STAR_FUN 0"
          by (metis Lattice.iter.simps(2) Suc)
        moreover have "... = 1 + x \<cdot> \<Sigma> (powersUpTo n x)"
          by (metis Suc)
        moreover have "... = 1 + x \<cdot> \<Sigma> {x\<^bsup>i\<^esup> |i. Suc i \<le> n}"
          by (simp add: powersUpTo_def)
        moreover have "... = 1 + \<Sigma> ((\<lambda>y. x\<cdot>y) ` {x\<^bsup>i\<^esup> |i. Suc i \<le> n})"
          by (smt assms inf_distl mem_Collect_eq power_closed subsetI)
        moreover have "... = 1 + \<Sigma> {x \<cdot> x\<^bsup>i\<^esup> |i. Suc i \<le> n}"
          by (simp add: image_def, rule_tac ?f = "\<lambda>Y. 1 + \<Sigma> Y" in arg_cong, safe, auto+)
        moreover have "... = 1 + \<Sigma> {x\<^bsup>Suc i\<^esup> |i. Suc i \<le> n}"
          by simp
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

  definition omega :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [101] 100) where
    "x\<^sup>\<omega> = \<nu>\<^bsub>A\<^esub>(\<lambda>y. x\<cdot>y)"

  lemma omega_unfoldl: assumes xc: "x \<in> carrier A" shows "x\<cdot>x\<^sup>\<omega> = x\<^sup>\<omega>"
    unfolding omega_def
  proof (rule greatest_fixpoint_computation)
    show "complete_lattice A"
      by (metis quantale_complete_lattice)

    show "op \<cdot> x \<in> carrier A \<rightarrow> carrier A"
      by (metis (lifting) assms typed_application mult_type)

    show "isotone A A (op \<cdot> x)"
      by (metis assms mult_left_iso)
  qed

  lemma star_unfoldl: assumes xc: "x \<in> carrier A" shows "1 + x\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
    unfolding star_def
  proof (rule fixpoint_computation)
    show "complete_lattice A"
      by (metis quantale_complete_lattice)

    show "(\<lambda>y. 1 + x \<cdot> y) \<in> carrier A \<rightarrow> carrier A"
      by (metis (no_types) assms ftype_pred join_closed mult_type one_closed)

    show "isotone A A (\<lambda>y. 1 + x \<cdot> y)"
      apply (simp add: isotone_def, safe, metis quantale_order)
      by (smt assms bin_lub_var distl join_closed join_idem leq_def mult_closed one_closed)
  qed

  lemma star_unfoldr: assumes xc: "x \<in> carrier A" shows "1 + x\<^sup>\<star>\<cdot>x = x\<^sup>\<star>"
  proof (insert xc, unfold star_power)
    have power_unfold: "({1} \<union> ((\<lambda>y. y\<cdot>x) ` powers x)) = (powers x)"
      apply (simp add: image_def powers_def, auto)
      by (metis assms nat.exhaust power.simps(1) power.simps(2) power_commutes)+
    hence "\<Sigma> (powers x) = \<Sigma> ({1} \<union> ((\<lambda>y. y\<cdot>x) ` powers x))"
      by auto
    moreover have "... = \<Sigma> {1} + \<Sigma> ((\<lambda>y. y\<cdot>x) ` powers x)"
      by (rule lub_union, simp_all, metis one_closed, metis power_unfold assms le_supE powers_closed)
    moreover have "... = 1 + \<Sigma> ((\<lambda>y. y\<cdot>x) ` powers x)"
      by (metis one_closed singleton_lub)
    moreover have "... = 1 + \<Sigma> (powers x) \<cdot> x"
      by (metis assms inf_distr powers_closed)
    ultimately show "1 + \<Sigma> (powers x) \<cdot> x = \<Sigma> (powers x)"
      by auto
  qed

  lemma star_continuity:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "x\<cdot>y\<^sup>\<star>\<cdot>z = \<Sigma> {x\<cdot>u\<cdot>z |u. \<exists>i. u = y\<^bsup>i\<^esup>}"
  proof (insert yc, unfold star_power powers_def)
    have closure_xu: "{x\<cdot>u |u. \<exists>i. u = y\<^bsup>i\<^esup>} \<subseteq> carrier A"
      by (safe, metis mult_closed power_closed xc yc)

    have "x \<cdot> \<Sigma> {u. \<exists>i. u = y\<^bsup>i\<^esup>} \<cdot> z = \<Sigma> (op \<cdot> x ` {u. \<exists>i. u = y\<^bsup>i\<^esup>}) \<cdot> z"
      by (metis inf_distl powers_closed powers_def xc yc)
    moreover have "... = \<Sigma> {x\<cdot>u |u. \<exists>i. u = y\<^bsup>i\<^esup>} \<cdot> z"
      by (simp add: image_def, rule_tac f = "\<lambda>X. \<Sigma> X \<cdot> z" in arg_cong, safe, metis+)
    moreover have "... = \<Sigma> ((\<lambda>a. a\<cdot>z) ` {x\<cdot>u |u. \<exists>i. u = y\<^bsup>i\<^esup>})"
      by (metis (lifting) closure_xu inf_distr zc)
    moreover have "... = \<Sigma> {x\<cdot>u\<cdot>z |u. \<exists>i. u = y\<^bsup>i\<^esup>}"
      by (simp add: image_def, rule_tac f = "\<lambda>X. \<Sigma> X" in arg_cong, safe, metis+)
    ultimately show "x \<cdot> \<Sigma> {u. \<exists>i. u = y\<^bsup>i\<^esup>} \<cdot> z = \<Sigma> {x \<cdot> u \<cdot> z |u. \<exists>i. u = y\<^bsup>i\<^esup>}"
      by auto
  qed

  lemma prod_cstar_unique:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "is_lub w {x\<cdot>u\<cdot>z |u. \<exists>i. u = y\<^bsup>i\<^esup>} \<Longrightarrow> x\<cdot>y\<^sup>\<star>\<cdot>z = w"
    by (simp add: star_continuity[OF xc yc zc], smt lub_is_lub)

  lemma star_unique: "x \<in> carrier A \<Longrightarrow> is_lub w (powers x) \<Longrightarrow> x\<^sup>\<star> = w"
    by (metis lub_is_lub star_power)

  lemma ex_star: "\<forall>x\<in>carrier A. \<exists>y\<in>carrier A. is_lub y (powers x)"
    by (metis (lifting) lub_ex powers_closed)

  lemma star_is_lub: "x \<in> carrier A \<Longrightarrow> is_lub (x\<^sup>\<star>) (powers x)"
    by (metis ex_star star_unique)

  lemma star_lub:
    assumes xc: "x \<in> carrier A" and zc: "z \<in> carrier A"
    shows "(\<forall>y\<in>(powers x). y \<sqsubseteq> z) \<longleftrightarrow> (x\<^sup>\<star> \<sqsubseteq> z)"
    by (insert star_is_lub[OF xc], simp add: is_lub_simp, metis (hide_lams, no_types) in_mono order_trans zc)

  lemma star_lub_var:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "(\<forall>n. x\<^bsup>n\<^esup> \<sqsubseteq> y) \<longleftrightarrow> (x\<^sup>\<star> \<sqsubseteq> y)"
    apply (insert star_is_lub[OF xc])
    apply (simp add: is_lub_simp powers_def, clarify)
    by (metis (lifting) order_trans power_closed xc yc)

  lemma star_inductl_var:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "x\<cdot>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<sqsubseteq> y"
  proof
    have yy_c: "y \<leftharpoondown> y \<in> carrier A"
      by (metis postimp_closed yc)

    assume "x\<cdot>y \<sqsubseteq> y"
    hence "x \<sqsubseteq> y \<leftharpoondown> y"
      by (metis postimp_conn_prop xc yc)
    hence "\<forall>n. x\<^bsup>n\<^esup> \<sqsubseteq> y \<leftharpoondown> y"
      by (metis postimp_conn_prop power_closed power_inductl_var xc yc)
    hence "x\<^sup>\<star> \<sqsubseteq> y \<leftharpoondown> y"
      by (insert star_lub_var[OF xc yy_c], auto)
    thus "x\<^sup>\<star>\<cdot>y \<sqsubseteq> y"
      by (metis postimp_conn_prop star_closed xc yc)
  qed

  lemma star_inductl:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "z+x\<cdot>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<sqsubseteq> y"
  proof
    assume hyp: "z+x\<cdot>y \<sqsubseteq> y"
    hence "z \<sqsubseteq> y" and "x\<cdot>y \<sqsubseteq> y"
      apply (metis bin_lub_var mult_closed xc yc zc)
      by (metis bin_lub_var hyp mult_closed xc yc zc)
    hence "x\<^sup>\<star>\<cdot>y \<sqsubseteq> y"
      by (metis star_inductl_var xc yc)
    thus "x\<^sup>\<star>\<cdot>z \<sqsubseteq> y"
      by (smt `z \<sqsubseteq> y` distl join_assoc leq_def mult_closed star_closed xc yc zc)
  qed

  lemma star_inductr_var:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "y\<cdot>x \<sqsubseteq> y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<sqsubseteq> y"
  proof
    have yy_c: "y \<rightharpoondown> y \<in> carrier A"
      by (metis preimp_closed yc)

    assume "y\<cdot>x \<sqsubseteq> y"
    hence "x \<sqsubseteq> y \<rightharpoondown> y"
      by (metis preimp_conn_prop xc yc)
    hence "\<forall>n. x\<^bsup>n\<^esup> \<sqsubseteq> y \<rightharpoondown> y"
      by (metis preimp_conn_prop power_closed power_inductr_var xc yc)
    hence "x\<^sup>\<star> \<sqsubseteq> y \<rightharpoondown> y"
      by (insert star_lub_var[OF xc yy_c], auto)
    thus "y\<cdot>x\<^sup>\<star> \<sqsubseteq> y"
      by (metis preimp_conn_prop star_closed xc yc)
  qed

  lemma star_inductr:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "z+y\<cdot>x \<sqsubseteq> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<sqsubseteq> y"
  proof
    assume hyp: "z+y\<cdot>x \<sqsubseteq> y"
    hence "z \<sqsubseteq> y" and "y\<cdot>x \<sqsubseteq> y"
      apply (metis bin_lub_var mult_closed xc yc zc)
      by (metis bin_lub_var hyp mult_closed xc yc zc)
    hence "y\<cdot>x\<^sup>\<star> \<sqsubseteq> y"
      by (metis star_inductr_var xc yc)
    thus "z\<cdot>x\<^sup>\<star> \<sqsubseteq> y"
      by (smt `z \<sqsubseteq> y` distr join_assoc leq_def mult_closed star_closed xc yc zc)
  qed

  lemma star_subid:
    assumes xc: "x \<in> carrier A" shows "x \<sqsubseteq> 1 \<longrightarrow> x\<^sup>\<star> = 1"
  proof
    assume "x \<sqsubseteq> 1"
    hence "x\<^sup>\<star> \<sqsubseteq> 1"
      by (metis assms mult_oner one_closed star_closed star_inductl_var)
    moreover have "1 \<sqsubseteq> x\<^sup>\<star>"
      by (metis assms eq_refl power.simps(1) star_closed star_lub_var)
    ultimately show "x\<^sup>\<star> = 1"
      by (metis assms one_closed order_antisym star_closed)
  qed

  lemma mult_isol:
    "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> z\<cdot>x \<sqsubseteq> z\<cdot>y"
    by (metis (lifting) distl leq_def mult_closed)

  lemma mult_isor:
    "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x\<cdot>z \<sqsubseteq> y\<cdot>z"
    by (metis (lifting) distr leq_def mult_closed)

  lemma leq_one_multl: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; y \<sqsubseteq> 1; x \<sqsubseteq> y\<cdot>x\<rbrakk> \<Longrightarrow> x = y\<cdot>x"
    by (metis mult_closed mult_isor mult_onel one_closed order_antisym)

  lemma leq_one_multr: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; y \<sqsubseteq> 1; x \<sqsubseteq> x\<cdot>y\<rbrakk> \<Longrightarrow> x = x\<cdot>y"
    by (metis mult_closed mult_isol mult_oner one_closed order_antisym)

end

end
