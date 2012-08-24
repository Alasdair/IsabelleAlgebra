theory Quantale
  imports Lattice Galois_Connection
begin

section {* Quantales *}

record 'a mult_ord = "'a ord" +
  one :: "'a"
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<index>" 80)

lemma set_comp_subset: "{x. P x \<and> x \<in> A} \<subseteq> A"
  by (metis (lifting) mem_Collect_eq subsetI)

locale unital_quantale = fixes Q (structure)
  assumes quantale_complete_lattice: "complete_lattice Q"
  and mult_type: "op \<cdot> \<in> carrier Q \<rightarrow> carrier Q \<rightarrow> carrier Q"
  and mult_assoc: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
  and inf_distl: "\<lbrakk>x \<in> carrier Q; Y \<subseteq> carrier Q\<rbrakk> \<Longrightarrow> x \<cdot> order.lub Q Y = order.lub Q ((\<lambda>y. x\<cdot>y) ` Y)"
  and inf_distr: "\<lbrakk>x \<in> carrier Q; Y \<subseteq> carrier Q\<rbrakk> \<Longrightarrow> order.lub Q Y \<cdot> x = order.lub Q ((\<lambda>y. y\<cdot>x) ` Y)"
  and one_closed: "one Q \<in> carrier Q"
  and mult_onel [simp]: "x \<in> carrier Q \<Longrightarrow> one Q \<cdot> x = x"
  and mult_oner [simp]: "x \<in> carrier Q \<Longrightarrow> x \<cdot> one Q = x"

sublocale unital_quantale \<subseteq> lat: complete_lattice Q
  by (metis quantale_complete_lattice)

context unital_quantale
begin

  lemma mult_closed: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier Q"
    by (metis typed_application mult_type)

  lemma quantale_order: "order Q"
    by (metis cl_to_order quantale_complete_lattice)

  abbreviation qone :: "'a" ("1") where
    "qone \<equiv> one Q"

  abbreviation sum :: "'a set \<Rightarrow> 'a" ("\<Sigma>") where
    "\<Sigma> X \<equiv> order.lub Q X"

  abbreviation qzero :: "'a" ("0") where
    "qzero \<equiv> complete_join_semilattice.bot Q"

  abbreviation qplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 70) where
    "x + y \<equiv> order.join Q x y"

  abbreviation qmeet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70) where
    "x \<sqinter> y \<equiv> order.meet Q x y"

  lemma bot_zeror: "x \<in> carrier Q \<Longrightarrow> x \<cdot> 0 = 0"
    by (metis empty_lub empty_subsetI image_empty inf_distl)

  lemma bot_zerol: "x \<in> carrier Q \<Longrightarrow> 0 \<cdot> x = 0"
    by (metis empty_lub empty_subsetI image_empty inf_distr)

  lemma distl: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<cdot> (y + z) = (x \<cdot> y) + (x \<cdot> z)"
  proof -
    assume xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    hence "{y,z} \<subseteq> carrier Q" by (metis is_lub_def is_ub_def join_ex)
    hence "x \<cdot> \<Sigma> {y,z} = \<Sigma> ((\<lambda>y. x\<cdot>y) ` {y,z})" by (metis inf_distl xc)
    thus ?thesis by (simp add: join_def)
  qed

  lemma distr: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q\<rbrakk> \<Longrightarrow> (y + z) \<cdot> x = (y \<cdot> x) + (z \<cdot> x)"
  proof -
    assume xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    hence "{y,z} \<subseteq> carrier Q" by (metis is_lub_def is_ub_def join_ex)
    hence "\<Sigma> {y,z} \<cdot> x = \<Sigma> ((\<lambda>y. y\<cdot>x) ` {y,z})" by (metis inf_distr xc)
    thus ?thesis by (simp add: join_def)
  qed

  lemma mult_left_join_preserving: "x \<in> carrier Q \<Longrightarrow> join_preserving Q Q (\<lambda>y. x\<cdot>y)"
    by (metis assms inf_distl join_preserving_def quantale_order)

  lemma mult_right_join_preserving: "x \<in> carrier Q \<Longrightarrow> join_preserving Q Q (\<lambda>y. y\<cdot>x)"
    by (metis assms inf_distr join_preserving_def quantale_order)

  definition preimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightharpoondown>" 60) where
    "preimp x y \<equiv> \<Sigma> {z. x \<cdot> z \<sqsubseteq> y \<and> z \<in> carrier Q}"

  lemma preimp_closed: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<rightharpoondown> y \<in> carrier Q"
  proof -
    let ?S = "{z. x\<cdot>z \<sqsubseteq> y \<and> z \<in> carrier Q}"

    have "?S \<subseteq> carrier Q" by (rule set_comp_subset)
    moreover hence "\<exists>x\<in>carrier Q. is_lub x ?S" by (smt lub_ex)
    ultimately have "\<Sigma> ?S \<in> carrier Q" by (smt lub_closed)
    thus ?thesis by (metis preimp_def)
  qed

  lemma preimp_type: "op \<rightharpoondown> \<in> carrier Q \<rightarrow> carrier Q \<rightarrow> carrier Q"
    by (metis (no_types) ftype_pred preimp_closed)

  lemma preimp_conn: assumes xc: "x \<in> carrier Q"
    shows "complete_lattice_connection Q Q (\<lambda>y. x\<cdot>y) (\<lambda>y. x \<rightharpoondown> y)"
  proof (rule suprema_galois_left, (metis quantale_complete_lattice)+)
    show "(\<lambda>y. x\<cdot>y) \<in> carrier Q \<rightarrow> carrier Q"
      by (metis mult_type xc typed_application)

    show "(\<lambda>y. x \<rightharpoondown> y) \<in> carrier Q \<rightarrow> carrier Q"
      by (metis preimp_type xc typed_application)

    show "ex_join_preserving Q Q (\<lambda>y. x\<cdot>y)"
      by (metis assms ex_join_preserving_def inf_distl quantale_order)

    show "\<forall>y\<in>carrier Q. order.is_lub Q (x \<rightharpoondown> y) {z. x\<cdot>z \<sqsubseteq> y \<and> z \<in> carrier Q}"
      by (metis (full_types) is_lub_lub preimp_def set_comp_subset)
  qed

  lemma mult_left_iso: "x \<in> carrier Q \<Longrightarrow> isotone Q Q (\<lambda>y. x\<cdot>y)"
    by (metis cl_to_galois galois_connection.lower_iso preimp_conn)

  lemma preimp_conn_prop:
    "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<cdot> y \<sqsubseteq> z \<longleftrightarrow> y \<sqsubseteq> x \<rightharpoondown> z"
    apply (rule galois_connection.galois_property)
    by (metis cl_to_galois preimp_conn mult_closed preimp_closed)+

  lemma preimp_mp: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<cdot> (x \<rightharpoondown> y) \<sqsubseteq> y"
    by (metis (lifting) order.order_refl preimp_closed preimp_conn_prop quantale_order)

  lemma preimp_refl: "x \<in> carrier Q \<Longrightarrow> 1 \<sqsubseteq> x \<rightharpoondown> x"
    by (metis mult_oner one_closed order_refl preimp_conn_prop)

  lemma preimp_trans:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
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
    "postimp x y \<equiv> \<Sigma> {z. z \<cdot> y \<sqsubseteq> x \<and> z \<in> carrier Q}"

  lemma postimp_closed: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<leftharpoondown> y \<in> carrier Q"
  proof -
    let ?S = "{z. z\<cdot>y \<sqsubseteq> x \<and> z \<in> carrier Q}"

    have "?S \<subseteq> carrier Q" by (rule set_comp_subset)
    moreover hence "\<exists>x\<in>carrier Q. is_lub x ?S" by (smt lub_ex)
    ultimately have "\<Sigma> ?S \<in> carrier Q" by (smt lub_closed)
    thus ?thesis by (metis postimp_def)
  qed

  lemma postimp_type: "op \<leftharpoondown> \<in> carrier Q \<rightarrow> carrier Q \<rightarrow> carrier Q"
    by (metis (no_types) ftype_pred postimp_closed)

  lemma postimp_conn: assumes xc: "x \<in> carrier Q"
    shows "complete_lattice_connection Q Q (\<lambda>y. y\<cdot>x) (\<lambda>y. y \<leftharpoondown> x)"
  proof (rule suprema_galois_left, metis quantale_complete_lattice, metis quantale_complete_lattice)
    show "(\<lambda>y. y\<cdot>x) \<in> carrier Q \<rightarrow> carrier Q"
      by (metis (no_types) assms ftype_pred mult_closed)

    show "(\<lambda>y. y \<leftharpoondown> x) \<in> carrier Q \<rightarrow> carrier Q"
      by (metis (no_types) assms ftype_pred postimp_closed)

    show "ex_join_preserving Q Q (\<lambda>y. y\<cdot>x)"
      by (metis assms ex_join_preserving_def inf_distr quantale_order)

    show "\<forall>y\<in>carrier Q. order.is_lub Q (y \<leftharpoondown> x) {z. z\<cdot>x \<sqsubseteq> y \<and> z \<in> carrier Q}"
      by (metis (full_types) is_lub_lub postimp_def set_comp_subset)
  qed

  lemma mult_right_iso: "x \<in> carrier Q \<Longrightarrow> isotone Q Q (\<lambda>y. y\<cdot>x)"
    by (metis cl_to_galois galois_connection.lower_iso postimp_conn)

  lemma postimp_conn_prop:
    "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<cdot> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<leftharpoondown> y"
    apply (rule galois_connection.galois_property)
    by (metis (lifting) cl_to_galois postimp_conn mult_closed postimp_closed)+

  lemma postimp_mp: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> (y \<leftharpoondown> x) \<cdot> x \<sqsubseteq> y"
    by (metis (lifting) order.order_refl postimp_closed postimp_conn_prop quantale_order)

  lemma postimp_refl: "x \<in> carrier Q \<Longrightarrow> 1 \<sqsubseteq> x \<leftharpoondown> x"
    by (metis eq_refl mult_onel one_closed postimp_conn_prop)

  lemma postimp_trans:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
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

  definition star :: "'a \<Rightarrow> 'a"  ("_\<^sup>*" [101] 100) where
    "x\<^sup>* = \<mu>\<^bsub>Q\<^esub>(\<lambda>y. 1 + x\<cdot>y)"

  lemma star_closed: assumes xc: "x \<in> carrier Q" shows "x\<^sup>* \<in> carrier Q"
    unfolding star_def
  proof (rule least_fixpoint_closed)
    show "complete_lattice Q"
      by (metis quantale_complete_lattice)

    show "(\<lambda>y. 1 + x \<cdot> y) \<in> carrier Q \<rightarrow> carrier Q"
      by (metis (no_types) assms ftype_pred join_closed mult_type one_closed)

    show "isotone Q Q (\<lambda>y. 1 + x \<cdot> y)"
      apply (simp add: isotone_def, safe, metis quantale_order)
      by (smt assms bin_lub_var distl join_closed join_idem leq_def mult_closed one_closed)
  qed

  subsection {* Continuity of the star operation *}

  lemma star_scott_ne_continuous:
    assumes xc: "x \<in> carrier Q"
    and D_subset: "D \<subseteq> carrier Q"
    and D_directed: "directed \<lparr>carrier = D, le = op \<sqsubseteq>, \<dots> = ord.more Q\<rparr>"
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
      apply (rule_tac ?A = "carrier Q" in set_image_type)+
      apply (metis D_subset)
      apply (metis ftype_pred mult_type xc)
      apply (simp add: ftype_pred)
      by (metis one_closed)
    moreover have "... = \<Sigma> ({1} \<union> ((\<lambda>y. x\<cdot>y) ` D))"
      by (simp, metis D_non_empty)
    moreover have "... = \<Sigma> {1} + \<Sigma> ((\<lambda>y. x\<cdot>y) ` D)"
      apply (rule lub_union, simp_all add: one_closed)
      apply (rule_tac ?A = "carrier Q" in set_image_type, simp add: D_subset)
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

  lemma power_closed: "x \<in> carrier Q \<Longrightarrow> x\<^bsup>n\<^esup> \<in> carrier Q"
  proof (induct n)
    case 0 show ?case by (simp, metis one_closed)
    case (Suc m) show ?case
      by (metis "0" Suc.hyps mult_closed power.simps(2))
  qed

  lemma power_add: assumes xc: "x \<in> carrier Q" shows "x\<^bsup>m\<^esup>\<cdot>x\<^bsup>n\<^esup> = x\<^bsup>m+n\<^esup>"
  proof (induct m)
    case 0 show ?case by (metis add_0 assms mult_onel power.simps(1) power_closed)
    case (Suc m) show ?case by (smt Suc assms mult_assoc power.simps(2) power_closed)
  qed

  lemma power_commutes: "x \<in> carrier Q \<Longrightarrow> x\<^bsup>n\<^esup>\<cdot>x = x\<cdot>x\<^bsup>n\<^esup>"
    by (smt power_add mult_oner power.simps)

  lemma power_inductl_var:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q"
    shows "x\<cdot>y \<sqsubseteq> y \<longrightarrow> x\<^bsup>n\<^esup>\<cdot>y \<sqsubseteq> y"
    apply (induct n)
    apply (metis eq_refl mult_onel power.simps(1) yc)
    by (smt distl join_assoc leq_def mult_assoc mult_closed power.simps(2) power_closed xc yc)

  lemma power_inductr_var:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q"
    shows "y\<cdot>x \<sqsubseteq> y \<longrightarrow> y\<cdot>x\<^bsup>n\<^esup> \<sqsubseteq> y"
    apply (induct n)
    apply (metis eq_refl mult_oner power.simps(1) yc)
    by (smt distr join_assoc leq_def mult_assoc mult_closed power.simps(2) power_closed xc yc)

  definition powers :: "'a \<Rightarrow> 'a set" where
    "powers x  = {y. (\<exists>i. y = x\<^bsup>i\<^esup>)}"

  lemma powers_closed: "x \<in> carrier Q \<Longrightarrow> powers x \<subseteq> carrier Q"
    by (simp add: powers_def, auto, metis power_closed)

  definition powersUpTo :: "nat \<Rightarrow> 'a \<Rightarrow> 'a set" where
    "powersUpTo n x \<equiv> {x\<^bsup>i\<^esup> |i. Suc i \<le> n}"

  subsection {* The star as a sum of powers *}

  text {* We can now show that $x^*$ in a quantale can be defined as
    the sum of the powers of $x$. *}

  lemma star_power: assumes xc: "x \<in> carrier Q" shows "x\<^sup>* = \<Sigma> (powers x)"
  proof -
    let ?STAR_FUN = "\<lambda>y. 1 + x\<cdot>y"

    have star_chain: "\<mu>\<^bsub>Q\<^esub>?STAR_FUN = \<Sigma> (carrier (kleene_chain Q ?STAR_FUN))"
    proof (rule kleene_fixed_point, unfold_locales)
      show "?STAR_FUN \<in> carrier Q \<rightarrow> carrier Q"
        by (smt ftype_pred one_closed mult_closed join_closed xc)
    next
      show "isotone Q Q ?STAR_FUN"
        apply (simp add: isotone_def, safe, metis quantale_order)
        by (smt assms bin_lub_var distl join_closed join_idem leq_def mult_closed one_closed)
    next
      fix D assume "D \<subseteq> carrier Q" and "directed \<lparr>carrier = D, le = op \<sqsubseteq>, \<dots> = ord.more Q\<rparr>" and "D \<noteq> {}"
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

    have "\<mu>\<^bsub>Q\<^esub>?STAR_FUN = \<Sigma> {z. \<exists>i. z = \<Sigma> (powersUpTo i x)}"
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
    "x\<^sup>\<omega> = \<nu>\<^bsub>Q\<^esub>(\<lambda>y. x\<cdot>y)"

  lemma omega_unfoldl: assumes xc: "x \<in> carrier Q" shows "x\<cdot>x\<^sup>\<omega> = x\<^sup>\<omega>"
    unfolding omega_def
  proof (rule greatest_fixpoint_computation)
    show "complete_lattice Q"
      by (metis quantale_complete_lattice)

    show "op \<cdot> x \<in> carrier Q \<rightarrow> carrier Q"
      by (metis (lifting) assms typed_application mult_type)

    show "isotone Q Q (op \<cdot> x)"
      by (metis assms mult_left_iso)
  qed

  lemma star_unfoldl: assumes xc: "x \<in> carrier Q" shows "1 + x\<cdot>x\<^sup>* = x\<^sup>*"
    unfolding star_def
  proof (rule fixpoint_computation)
    show "complete_lattice Q"
      by (metis quantale_complete_lattice)

    show "(\<lambda>y. 1 + x \<cdot> y) \<in> carrier Q \<rightarrow> carrier Q"
      by (metis (no_types) assms ftype_pred join_closed mult_type one_closed)

    show "isotone Q Q (\<lambda>y. 1 + x \<cdot> y)"
      apply (simp add: isotone_def, safe, metis quantale_order)
      by (smt assms bin_lub_var distl join_closed join_idem leq_def mult_closed one_closed)
  qed

  lemma star_unfoldr: assumes xc: "x \<in> carrier Q" shows "1 + x\<^sup>*\<cdot>x = x\<^sup>*"
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
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    shows "x\<cdot>y\<^sup>*\<cdot>z = \<Sigma> {x\<cdot>u\<cdot>z |u. \<exists>i. u = y\<^bsup>i\<^esup>}"
  proof (insert yc, unfold star_power powers_def)
    have closure_xu: "{x\<cdot>u |u. \<exists>i. u = y\<^bsup>i\<^esup>} \<subseteq> carrier Q"
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
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    shows "is_lub w {x\<cdot>u\<cdot>z |u. \<exists>i. u = y\<^bsup>i\<^esup>} \<Longrightarrow> x\<cdot>y\<^sup>*\<cdot>z = w"
    by (simp add: star_continuity[OF xc yc zc], smt lub_is_lub)

  lemma star_unique: "x \<in> carrier Q \<Longrightarrow> is_lub w (powers x) \<Longrightarrow> x\<^sup>* = w"
    by (metis lub_is_lub star_power)

  lemma ex_star: "\<forall>x\<in>carrier Q. \<exists>y\<in>carrier Q. is_lub y (powers x)"
    by (metis (lifting) lub_ex powers_closed)

  lemma star_is_lub: "x \<in> carrier Q \<Longrightarrow> is_lub (x\<^sup>*) (powers x)"
    by (metis ex_star star_unique)

  lemma star_lub:
    assumes xc: "x \<in> carrier Q" and zc: "z \<in> carrier Q"
    shows "(\<forall>y\<in>(powers x). y \<sqsubseteq> z) \<longleftrightarrow> (x\<^sup>* \<sqsubseteq> z)"
    by (insert star_is_lub[OF xc], simp add: is_lub_simp, metis (hide_lams, no_types) in_mono order_trans zc)

  lemma star_lub_var:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q"
    shows "(\<forall>n. x\<^bsup>n\<^esup> \<sqsubseteq> y) \<longleftrightarrow> (x\<^sup>* \<sqsubseteq> y)"
    apply (insert star_is_lub[OF xc])
    apply (simp add: is_lub_simp powers_def, clarify)
    by (metis (lifting) order_trans power_closed xc yc)

  lemma star_inductl_var:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q"
    shows "x\<cdot>y \<sqsubseteq> y \<longrightarrow> x\<^sup>*\<cdot>y \<sqsubseteq> y"
  proof
    have yy_c: "y \<leftharpoondown> y \<in> carrier Q"
      by (metis postimp_closed yc)

    assume "x\<cdot>y \<sqsubseteq> y"
    hence "x \<sqsubseteq> y \<leftharpoondown> y"
      by (metis postimp_conn_prop xc yc)
    hence "\<forall>n. x\<^bsup>n\<^esup> \<sqsubseteq> y \<leftharpoondown> y"
      by (metis postimp_conn_prop power_closed power_inductl_var xc yc)
    hence "x\<^sup>* \<sqsubseteq> y \<leftharpoondown> y"
      by (insert star_lub_var[OF xc yy_c], auto)
    thus "x\<^sup>*\<cdot>y \<sqsubseteq> y"
      by (metis postimp_conn_prop star_closed xc yc)
  qed

  lemma star_inductl:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    shows "z+x\<cdot>y \<sqsubseteq> y \<longrightarrow> x\<^sup>*\<cdot>z \<sqsubseteq> y"
  proof
    assume hyp: "z+x\<cdot>y \<sqsubseteq> y"
    hence "z \<sqsubseteq> y" and "x\<cdot>y \<sqsubseteq> y"
      apply (metis bin_lub_var mult_closed xc yc zc)
      by (metis bin_lub_var hyp mult_closed xc yc zc)
    hence "x\<^sup>*\<cdot>y \<sqsubseteq> y"
      by (metis star_inductl_var xc yc)
    thus "x\<^sup>*\<cdot>z \<sqsubseteq> y"
      by (smt `z \<sqsubseteq> y` distl join_assoc leq_def mult_closed star_closed xc yc zc)
  qed

  lemma star_inductr_var:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q"
    shows "y\<cdot>x \<sqsubseteq> y \<longrightarrow> y\<cdot>x\<^sup>* \<sqsubseteq> y"
  proof
    have yy_c: "y \<rightharpoondown> y \<in> carrier Q"
      by (metis preimp_closed yc)

    assume "y\<cdot>x \<sqsubseteq> y"
    hence "x \<sqsubseteq> y \<rightharpoondown> y"
      by (metis preimp_conn_prop xc yc)
    hence "\<forall>n. x\<^bsup>n\<^esup> \<sqsubseteq> y \<rightharpoondown> y"
      by (metis preimp_conn_prop power_closed power_inductr_var xc yc)
    hence "x\<^sup>* \<sqsubseteq> y \<rightharpoondown> y"
      by (insert star_lub_var[OF xc yy_c], auto)
    thus "y\<cdot>x\<^sup>* \<sqsubseteq> y"
      by (metis preimp_conn_prop star_closed xc yc)
  qed

  lemma star_inductr:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    shows "z+y\<cdot>x \<sqsubseteq> y \<longrightarrow> z\<cdot>x\<^sup>* \<sqsubseteq> y"
  proof
    assume hyp: "z+y\<cdot>x \<sqsubseteq> y"
    hence "z \<sqsubseteq> y" and "y\<cdot>x \<sqsubseteq> y"
      apply (metis bin_lub_var mult_closed xc yc zc)
      by (metis bin_lub_var hyp mult_closed xc yc zc)
    hence "y\<cdot>x\<^sup>* \<sqsubseteq> y"
      by (metis star_inductr_var xc yc)
    thus "z\<cdot>x\<^sup>* \<sqsubseteq> y"
      by (smt `z \<sqsubseteq> y` distr join_assoc leq_def mult_closed star_closed xc yc zc)
  qed

  lemma star_subid:
    assumes xc: "x \<in> carrier Q" shows "x \<sqsubseteq> 1 \<longrightarrow> x\<^sup>* = 1"
  proof
    assume "x \<sqsubseteq> 1"
    hence "x\<^sup>* \<sqsubseteq> 1"
      by (metis assms mult_oner one_closed star_closed star_inductl_var)
    moreover have "1 \<sqsubseteq> x\<^sup>*"
      by (metis assms eq_refl power.simps(1) star_closed star_lub_var)
    ultimately show "x\<^sup>* = 1"
      by (metis assms one_closed order_antisym star_closed)
  qed

  lemma mult_isol:
    "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> z\<cdot>x \<sqsubseteq> z\<cdot>y"
    by (metis (lifting) distl leq_def mult_closed)

  lemma mult_isor:
    "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x\<cdot>z \<sqsubseteq> y\<cdot>z"
    by (metis (lifting) distr leq_def mult_closed)

  lemma leq_one_multl: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; y \<sqsubseteq> 1; x \<sqsubseteq> y\<cdot>x\<rbrakk> \<Longrightarrow> x = y\<cdot>x"
    by (metis mult_closed mult_isor mult_onel one_closed order_antisym)

  lemma leq_one_multr: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; y \<sqsubseteq> 1; x \<sqsubseteq> x\<cdot>y\<rbrakk> \<Longrightarrow> x = x\<cdot>y"
    by (metis mult_closed mult_isol mult_oner one_closed order_antisym)

end

record 'a test_ord = "'a mult_ord" +
  test :: "'a bounded_ord"

abbreviation tests :: "('a, 'b) test_ord_scheme \<Rightarrow> 'a set" where
    "tests A \<equiv> carrier (test A)"

locale kat = fixes Q (structure)
  assumes tquantale: "unital_quantale Q"
  and test_ba: "boolean_algebra (test Q)"
  and test_subset: "tests Q \<subseteq> carrier Q"
  and test_one: "unital_quantale.qone Q = \<top>\<^bsub>test Q\<^esub>"
  and test_zero: "unital_quantale.qzero Q = botf (test Q)"
  and test_le: "x \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>test Q\<^esub> y"
  and test_join: "order.join Q x y = order.join (test Q) x y"
  and test_meet: "order.meet Q x y = order.meet (test Q) x y"

sublocale kat \<subseteq> unital_quantale by (metis tquantale)

context kat
begin

  lemma test_subset_var: "p \<in> tests Q \<Longrightarrow> p \<in> carrier Q"
    by (metis insert_absorb insert_subset test_subset)

  lemma test_ord: "order (test Q)"
    apply (insert test_ba)
    by (simp add: boolean_algebra_def distributive_lattice_def lattice_def join_semilattice_def)

  lemma test_bl: "bounded_lattice (test Q)"
    by (insert test_ba, simp add: boolean_algebra_def complemented_lattice_def)

  definition complement :: "'a \<Rightarrow> 'a" ("_\<^sup>\<bottom>" [101] 100) where
    "complement x = (THE y. y \<in> tests Q \<and> qplus x y = qone \<and> x \<sqinter> y = qzero)"

  lemma complement_closed: assumes xc: "x \<in> tests Q" shows "x\<^sup>\<bottom> \<in> tests Q"
    apply (simp add: complement_def)
    apply (rule the1I2)
    apply (insert boolean_algebra.compl_uniq[OF test_ba xc])
    apply (metis test_join test_meet test_one test_zero)
    by metis

  lemma complement1: "p \<in> tests Q \<Longrightarrow> p + p\<^sup>\<bottom> = 1"
    apply (simp add: complement_def)
    apply (rule the1I2)
    apply (metis boolean_algebra.compl_uniq test_ba test_join test_meet test_one test_zero)
    by auto

  lemma complement2: "p \<in> tests Q \<Longrightarrow> p \<sqinter> p\<^sup>\<bottom> = 0"
    apply (simp add: complement_def)
    apply (rule the1I2)
    apply (metis boolean_algebra.compl_uniq test_ba test_join test_meet test_one test_zero)
    by auto

  lemma test_under_one: "p \<in> tests Q \<Longrightarrow> p \<sqsubseteq> 1"
    by (metis test_one test_le bounded_lattice.top_greatest test_bl)

  lemma test_star: "p \<in> tests Q \<Longrightarrow> p\<^sup>* = 1"
    by (metis (lifting) set_rev_mp star_subid test_subset test_under_one)

end

record 'a dom_ord = "'a test_ord" +
  dom :: "'a \<Rightarrow> 'a" ("\<delta>\<index>_" [1000] 100)

locale modal_quantale = fixes Q (structure)
  assumes mkat: "kat Q"
  and dom_type: "dom Q \<in> carrier Q \<rightarrow> tests Q"
  and dom1: "x \<in> carrier Q \<Longrightarrow> x \<sqsubseteq> \<delta>(x)\<cdot>x"
  and dom2: "\<lbrakk>x \<in> carrier Q; p \<in> tests Q\<rbrakk> \<Longrightarrow> \<delta>(p\<cdot>x) \<sqsubseteq> p"

sublocale modal_quantale \<subseteq> kat by (metis mkat)

context modal_quantale
begin


  abbreviation qtop :: "'a" ("\<top>") where
    "\<top> \<equiv> complete_meet_semilattice.top Q"

  lemma dom_closed: "\<lbrakk>x \<in> carrier Q\<rbrakk> \<Longrightarrow> \<delta>(x) \<in> tests Q"
    by (metis (lifting) dom_type typed_application)

  lemma dom_under_one: "x \<in> carrier Q \<Longrightarrow> \<delta>(x) \<sqsubseteq> 1"
    by (metis dom_closed test_under_one)

  lemma dom_strictness: assumes xc: "x \<in> carrier Q" shows "\<delta>(x) = 0 \<longleftrightarrow> x = 0"
    apply default
    apply (metis assms bot_closed bot_zerol dom1 less_def less_le_trans prop_bot)
    by (metis bot_onel bot_zerol bounded_lattice.bot_closed dom2 dom_closed in_mono join_comm leq_def_right test_bl test_subset test_zero)

  lemma dom_llp:
    assumes xc: "x \<in> carrier Q" and pc: "p \<in> tests Q"
    shows "\<delta>(x) \<sqsubseteq> p \<longleftrightarrow> x \<sqsubseteq> p\<cdot>x"
  proof
    assume asm: "\<delta>(x) \<sqsubseteq> p"
    have "x \<sqsubseteq> \<delta>(x)\<cdot>x"
      by (metis dom1 xc)
    moreover have "... \<sqsubseteq> p\<cdot>x"
      by (metis dom_closed mult_isor pc test_subset_var xc asm)
    ultimately show "x \<sqsubseteq> p\<cdot>x"
      by (metis dom_closed mult_closed order_trans pc test_subset_var xc)
  next
    assume "x \<sqsubseteq> p\<cdot>x"
    thus "\<delta>(x) \<sqsubseteq> p"
      by (metis bounded_lattice.top_greatest dom2 leq_one_multl pc test_bl test_le test_one test_subset_var xc)
  qed

  lemma
    assumes xc: "x \<in> carrier Q" and pc: "p \<in> tests Q"
    shows "x \<sqsubseteq> p\<cdot>\<top> \<longleftrightarrow> x \<sqsubseteq> p\<cdot>x"
  proof
    assume asm: "x \<sqsubseteq> p\<cdot>\<top>"
    hence "x = x \<sqinter> p\<cdot>\<top>"
      by (metis leq_meet_def mult_closed pc test_subset_var top_closed xc)
    then obtain y where yc: "y \<in> carrier Q" and "... = x \<sqinter> (x + y)"
      by (metis absorb2 xc)
    hence "... = (x \<sqinter> p\<cdot>x) + (x \<sqinter> p\<cdot>y)"
      sorry
    hence "... \<sqsubseteq> (x \<sqinter> p\<cdot>x) + (x \<sqinter> 1\<cdot>y)"
      sorry
    hence
      
      
    

  lemma dom_conn_prop:
    assumes xc: "x \<in> carrier Q" and pc: "p \<in> tests Q"
    shows "\<delta>(x) \<sqsubseteq> p \<longleftrightarrow> x \<sqsubseteq> p\<cdot>\<top>"
  proof
    assume asm: "\<delta>(x) \<sqsubseteq> p"
    have "x \<sqsubseteq> \<delta>(x)\<cdot>x"
      by (metis dom1 xc)
    moreover have "... \<sqsubseteq> \<delta>(x)\<cdot>\<top>"
      by (metis dom_closed mult_isol prop_top test_subset_var top_closed xc)
    moreover have "... \<sqsubseteq> p\<cdot>\<top>"
      by (metis asm dom_closed mult_isor pc test_subset_var top_closed xc)
  next
    assume asm: "x \<sqsubseteq> p\<cdot>\<top>"
    

  lemma
    assumes xc: "x \<in> carrier Q"
    shows "x \<sqsubseteq> \<delta>(x)\<cdot>\<top>"
  proof -
    have "x\<cdot>\<top> \<sqsubseteq> \<delta>(x\<cdot>\<top>)\<cdot>(x\<cdot>\<top>)"
      by (metis assms dom1 mult_closed top_closed)
    hence "x \<sqsubseteq> \<delta>(x\<cdot>\<top>)\<cdot>(x\<cdot>\<top>) \<leftharpoondown> \<top>"
      apply (insert postimp_conn_prop[of x "\<top>" "\<delta>(x\<cdot>\<top>)\<cdot>(x\<cdot>\<top>)"])
      
      
      

  lemma
    assumes xc: "x \<in> carrier Q" and pc: "p \<in> tests Q"
    shows "\<delta>(x) \<sqsubseteq> p \<longleftrightarrow> x \<sqsubseteq> p\<cdot>(complete_meet_semilattice.top Q)"
    nitpick
    apply default
    
    
    

  lemma dom_lower_adjoint: "lower_adjoint Q Q (\<lambda>x. \<delta>(x))"
    

  lemma dom_join_preserving:
    assumes X_subset: "X \<subseteq> carrier Q"
    shows "\<delta>(\<Sigma> X) = \<Sigma> ((\<lambda>x. \<delta>(x)) ` X)"
  proof -

  lemma dom_additivity:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q"
    shows "\<delta>(x + y) = \<delta>(x) + \<delta>(y)"
    apply (simp add: join_def)
    apply (rule order_antisym)
    defer
    
    by (metis (lifting) bot_oner dom_strictness kat.test_one mkat order_change top_closed top_onel xc yc)
    
  proof (rule order_antisym)
    have "\<delta>(x + y) \<sqsubseteq> p \<longleftrightarrow> p\<^sup>\<bottom>\<cdot>(x + y) \<sqsubseteq> 0"
      
      

  definition fdiamond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("| _ \<rangle> _" [50,90] 95) where
    "|a\<rangle>p = \<delta>(a\<cdot>p)"


end

record 'a con_ord = "'a mult_ord" +
  con :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<bar>\<index>" 79)

locale concurrent_ka = fixes Q (structure)
  assumes con_quantale: "unital_quantale \<lparr>carrier = carrier Q, le = op \<sqsubseteq>, one = one Q, mult = op \<bar>\<rparr>"
  and seq_quantale: "unital_quantale \<lparr>carrier = carrier Q, le = op \<sqsubseteq>, one = one Q, mult = op \<cdot>\<rparr>"
  and exchange: "\<lbrakk>a \<in> carrier Q; b \<in> carrier Q; c \<in> carrier Q; d \<in> carrier Q\<rbrakk> \<Longrightarrow> (a \<bar> b ) \<cdot> (c \<bar> d) \<sqsubseteq> (b \<cdot> c) \<bar> (a \<cdot> d)"

begin

  definition CON :: "'a mult_ord" where
    "CON \<equiv> \<lparr>carrier = carrier Q, le = op \<sqsubseteq>, one = one Q, mult = op \<bar>\<rparr>"

  lemma con_quantale_var: "unital_quantale CON"
    by (insert con_quantale, simp add: CON_def)

  lemma con_cl: "complete_lattice CON"
    by (metis con_quantale unital_quantale.quantale_complete_lattice CON_def)

  lemma con_ord: "order CON"
    by (metis cl_to_order con_cl)

  lemma con_carrier: "carrier Q = carrier CON"
    by (simp add: CON_def)

  lemma con_le: "(x \<sqsubseteq> y) = (x \<sqsubseteq>\<^bsub>CON\<^esub> y)"
    by (simp add: CON_def)

  definition SEQ :: "'a mult_ord" where
    "SEQ \<equiv> \<lparr>carrier = carrier Q, le = op \<sqsubseteq>, one = one Q, mult = op \<cdot>\<rparr>"

  lemma seq_quantale_var: "unital_quantale SEQ"
    by (insert seq_quantale, simp add: SEQ_def)

  lemma seq_cl: "complete_lattice SEQ"
    by (metis seq_quantale unital_quantale.quantale_complete_lattice SEQ_def)

  lemma seq_ord: "order SEQ"
    by (metis cl_to_order seq_cl)

  lemma seq_con_ord_eq: "order SEQ = order CON"
    by (metis cl_to_order con_cl seq_ord)

  lemma seq_con_cl_eq: "complete_lattice SEQ = complete_lattice CON"
    by (metis con_cl seq_cl)

  lemma seq_carrier: "carrier Q = carrier SEQ"
    by (simp add: SEQ_def)

  lemma seq_le: "(x \<sqsubseteq> y) = (x \<sqsubseteq>\<^bsub>SEQ\<^esub> y)"
    by (simp add: SEQ_def)

  lemma cka_ord: "order Q"
    apply default
    apply (simp_all only: seq_carrier seq_le)
    apply (metis order.eq_refl seq_ord)
    apply (metis order.order_trans seq_ord)
    by (metis order.order_antisym seq_ord)

  lemma cka_ord_is_seq: "order Q = order SEQ"
    by (metis cka_ord seq_ord)

  lemma cka_ord_is_con: "order Q = order CON"
    by (metis cka_ord seq_con_ord_eq seq_ord)

  lemma cka_lub_is_seq_lub: "order.is_lub Q x X = order.is_lub SEQ x X"
    apply (insert seq_ord cka_ord)
    apply (simp add: order.is_lub_simp)
    by (simp add: seq_carrier seq_le)

  lemma cka_glb_is_seq_glb: "order.is_glb Q x X = order.is_glb SEQ x X"
    apply (insert seq_ord cka_ord)
    apply (simp add: order.is_glb_simp)
    by (simp add: seq_carrier seq_le)

  lemma cka_lub_to_seq: "\<Sigma>\<^bsub>Q\<^esub>X = \<Sigma>\<^bsub>SEQ\<^esub>X"
    apply (insert seq_ord cka_ord)
    by (simp add: order.lub_def cka_lub_is_seq_lub)

  lemma cka_cl: "complete_lattice Q"
    apply default
    apply (insert cka_ord)
    apply (simp_all only: seq_carrier seq_le)
    apply (metis order.order_refl seq_ord)
    apply (metis order.order_trans seq_carrier seq_le)
    apply (metis order.order_antisym seq_ord)
    apply (simp add: cka_lub_is_seq_lub)
    apply (metis (lifting) cl_to_cjs complete_join_semilattice.lub_ex seq_cl)
    apply (simp add: cka_glb_is_seq_glb)
    by (metis cl_to_cms complete_meet_semilattice.glb_ex seq_cl)

  lemma cka_one_is_seq_one: "one Q = one SEQ"
    by (simp add: SEQ_def)

  lemma cka_one_is_con_one: "one Q = one CON"
    by (simp add: CON_def)

  lemma cka_cl_is_seq_cl: "complete_lattice Q = complete_lattice SEQ"
    by (metis cka_cl seq_cl)

  lemma default_quantale: "unital_quantale Q"
    apply (insert seq_quantale_var)
    apply (unfold unital_quantale_def)
    apply safe
    apply (metis cka_cl)
    apply (simp_all add: seq_carrier seq_le cka_lub_to_seq cka_one_is_seq_one)
    by (simp add: SEQ_def)+

end

sublocale concurrent_ka \<subseteq> unital_quantale
  by (metis default_quantale)

context concurrent_ka
begin

  lemma con_mult: "op \<bar> = op \<cdot>\<^bsub>CON\<^esub>"
    by (simp add: CON_def)

  lemma con_type: "op \<bar> \<in> carrier Q \<rightarrow> carrier Q \<rightarrow> carrier Q"
    apply (simp add: con_carrier con_mult)
    by (metis con_quantale_var unital_quantale.mult_type)

  lemma con_closed: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> x\<bar>y \<in> carrier Q"
    by (metis con_type typed_application)

  lemma con_assoc: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q\<rbrakk> \<Longrightarrow> (x \<bar> y) \<bar> z = x \<bar> (y \<bar> z)"
    apply (simp add: con_carrier con_mult)
    by (metis con_quantale_var unital_quantale.mult_assoc)

  lemma con_oner [simp]: "x \<in> carrier Q \<Longrightarrow> x \<bar> 1 = x"
    apply (simp add: con_mult con_carrier cka_one_is_con_one)
    by (metis con_quantale_var unital_quantale.mult_oner)

  lemma con_commutative:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q"
    shows "x\<bar>y = y\<bar>x"
  proof -
    have "x\<bar>y \<sqsubseteq> y\<bar>x"
      apply (insert exchange[OF xc yc one_closed one_closed])
      by (metis con_closed con_oner mult_oner one_closed xc yc)
    moreover have "y\<bar>x \<sqsubseteq> x\<bar>y"
      apply (insert exchange[OF yc xc one_closed one_closed])
      by (metis con_closed con_oner mult_oner one_closed xc yc)
    ultimately show ?thesis
      by (metis con_closed order_antisym xc yc)
  qed

  lemma con_onel [simp]: "x \<in> carrier Q \<Longrightarrow> 1 \<bar> x = x"
    by (metis con_commutative con_oner one_closed)

  lemma exchange_var:
    "\<lbrakk>a \<in> carrier Q; b \<in> carrier Q; c \<in> carrier Q; d \<in> carrier Q\<rbrakk> \<Longrightarrow> (a \<bar> b ) \<cdot> (c \<bar> d) \<sqsubseteq> (a \<cdot> c) \<bar> (b \<cdot> d)"
    by (metis (lifting) con_commutative exchange)

  lemma seq_le_con:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q"
    shows "x\<cdot>y \<sqsubseteq> x\<bar>y"
    by (metis con_onel con_oner exchange_var mult_onel mult_oner one_closed xc yc)

  lemma con_seq_slide1:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    shows "(x \<bar> y) \<cdot> z \<sqsubseteq> x \<bar> (y \<cdot> z)"
    sorry

  lemma con_seq_slide2:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    shows "x \<cdot> (y \<bar> z) \<sqsubseteq> (x \<cdot> y) \<bar> z"
    sorry

  abbreviation conimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<mapsto>" 60) where
    "x \<mapsto> y \<equiv> unital_quantale.preimp CON x y"

  abbreviation constar :: "'a \<Rightarrow> 'a"  ("_\<^sup>\<triangle>" [101] 100) where
    "x\<^sup>\<triangle> \<equiv> unital_quantale.star CON x"

  lemma con_plus: "x + y = order.join CON x y"
    apply (simp add: order.join_def[OF con_ord, of x y] order.lub_simp[OF con_ord, of "{x,y}"])
    by (simp add: CON_def join_def lub_simp)

  lemma constar_unfold: assumes xc: "x \<in> carrier Q " shows "1 + x\<bar>x\<^sup>\<triangle> = x\<^sup>\<triangle>"
    apply (simp add: con_mult cka_one_is_con_one con_plus)
    by (metis (lifting) assms con_carrier con_quantale_var unital_quantale.star_unfoldl)

  lemma constar_induct:
    assumes xc: "x \<in> carrier Q" and yc: "y \<in> carrier Q" and zc: "z \<in> carrier Q"
    shows "z+x\<bar>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<triangle>\<bar>z \<sqsubseteq> y"
    apply (simp add: con_mult con_plus con_le)
    apply (insert unital_quantale.star_inductl[of CON x y z, OF con_quantale_var])
    apply (simp add: con_carrier[symmetric])
    by (metis xc yc zc)

end

record 'a invar_ord = "'a con_ord" +
  iota :: "'a \<Rightarrow> 'a" ("\<iota>\<index>_" [1000] 100)

locale cka_with_invariants = fixes Q (structure)
  assumes cka: "concurrent_ka Q"
  and invar_unit: "x \<in> carrier Q \<Longrightarrow> x \<sqsubseteq> \<iota> x"
  and invar_iso: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> \<iota> x \<sqsubseteq> \<iota> y"
  and invar_idem: "x \<in> carrier Q \<Longrightarrow> \<iota> x \<sqsubseteq> \<iota> (\<iota> x)"
  and invar_i1: "x \<in> carrier Q \<Longrightarrow> 1 \<sqsubseteq> \<iota> x"
  and invar_i2: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> \<iota> (x \<bar> y) \<sqsubseteq> \<iota> (x + y)"

sublocale cka_with_invariants \<subseteq> concurrent_ka by (metis cka)

context cka_with_invariants
begin

  definition invariant :: "'a \<Rightarrow> bool" where
    "invariant s \<equiv> s \<in> carrier Q \<and> \<iota> s = s"

  lemma invariant_closed: "invariant s \<Longrightarrow> s \<in> carrier Q"
    by (metis invariant_def)

  lemma invariant_fix: "invariant s \<Longrightarrow> \<iota> s = s"
    by (metis invariant_def)

  

end
