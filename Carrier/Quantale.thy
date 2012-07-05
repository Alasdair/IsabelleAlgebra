theory Quantale
  imports Lattice Galois_Connection
begin

record 'a mult_ord = "'a ord" +
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<index>" 80)
  one :: "'a"

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
    by (metis closed_application mult_type)

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
      by (metis mult_type xc closed_application)

    show "(\<lambda>y. x \<rightharpoondown> y) \<in> carrier Q \<rightarrow> carrier Q"
      by (metis preimp_type xc closed_application)

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

   lemma star_scott_continuous: "scott_continuous Q Q star"
     unfolding scott_continuous_def
   proof clarify
     fix D assume D_set: "D \<subseteq> carrier Q" and D_directed: "directed \<lparr>carrier = D, le = op \<sqsubseteq>\<rparr>"

     let ?DIR = "\<lparr>carrier = D, le = op \<sqsubseteq>\<rparr>"

     

     have "\<forall>x\<in>D. \<forall>y\<in>D. \<exists>z\<in>D. x \<sqsubseteq>\<^bsub>?DIR\<^esub> z \<and> y \<sqsubseteq>\<^bsub>?DIR\<^esub> z"
     proof safe
       

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

  definition powers :: "'a \<Rightarrow> 'a set" where
    "powers x  = {y. (\<exists>i. y = x\<^bsup>i\<^esup>)}"

  lemma power_is_iter: assumes xc: "x \<in> carrier Q"
    shows "x\<^bsup>i\<^esup> = iter (Suc i) (\<lambda>y. 1 + x\<cdot>y) 0"
  proof (induct i)
    case 0 show ?case apply simp
      by (metis (lifting) "0" bot_oner bot_zeror one_closed xc)
    case (Suc m)
    fix i assume "x\<^bsup>i\<^esup> = iter (Suc i) (\<lambda>y. 1 + x \<cdot> y) 0"
    have "x\<cdot>x\<^bsup>i\<^esup> = 1 + x\<cdot>(iter (Suc i) (\<lambda>y. 1 + x\<cdot>y) 0)
    thus "x\<^bsup>Suc i\<^esup> = iter (Suc (Suc i)) (\<lambda>y. 1 + x \<cdot> y) 0"
      

  lemma star_power: "x \<in> carrier Q \<Longrightarrow> x\<^sup>* = \<Sigma> (powers x)"
    unfolding star_def powers_def
    apply (rule kleene_fixed_point)
    

    definition omega :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [101] 100) where
     "x\<^sup>\<omega> = \<nu>\<^bsub>Q\<^esub>(\<lambda>y. x\<cdot>y)"

   lemma omega_unfoldl: assumes xc: "x \<in> carrier Q" shows "x\<cdot>x\<^sup>\<omega> = x\<^sup>\<omega>"
     unfolding omega_def
   proof (rule greatest_fixpoint_computation)
     show "complete_lattice Q"
       by (metis quantale_complete_lattice)

     show "op \<cdot> x \<in> carrier Q \<rightarrow> carrier Q"
       by (metis (lifting) assms closed_application mult_type)

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

  definition powers :: "'a \<Rightarrow> 'a set" where
    "powers x  = {y. (\<exists>i. y = x\<^bsup>i\<^esup>)}"

  lemma set_image_comp: "f ` {z. P z} = {f z | z. P z}"
    by (simp add: image_def, smt Collect_cong)

  lemma set_closure_condition [simp]: "X \<subseteq> Y \<Longrightarrow> {x. x \<in> X \<and> x \<in> Y} = X"
    by (metis Int_absorb1 Int_commute Int_def)

  lemma powers_subset: "x \<in> carrier Q \<Longrightarrow> powers x \<subseteq> carrier Q"
    by (simp add: powers_def, default, smt CollectD power_closed)

  lemma inf_distl_comp: assumes xc: "x \<in> carrier Q"
    shows "x \<cdot> \<Sigma> {z. P z \<and> z \<in> carrier Q} = \<Sigma> {x\<cdot>z | z. P z \<and> z \<in> carrier Q}"
  proof -
    have "x \<cdot> \<Sigma> {z. P z \<and> z \<in> carrier Q} = \<Sigma> ((\<lambda>y. x\<cdot>y) ` {z. P z \<and> z \<in> carrier Q})"
      by (metis (lifting) CollectE assms inf_distl subsetI)
    moreover have "... = \<Sigma> {x\<cdot>z | z. P z \<and> z \<in> carrier Q}"
      by (metis set_image_comp)
    ultimately show ?thesis by metis
  qed

  lemma inf_distr_comp: assumes xc: "x \<in> carrier Q"
    shows "\<Sigma> {z. P z \<and> z \<in> carrier Q} \<cdot> x = \<Sigma> {z\<cdot>x | z. P z \<and> z \<in> carrier Q}"
  proof -
    have "\<Sigma> {z. P z \<and> z \<in> carrier Q} \<cdot> x = \<Sigma> ((\<lambda>y. y\<cdot>x) ` {z. P z \<and> z \<in> carrier Q})"
      by (metis (lifting) CollectE assms inf_distr subsetI)
    moreover have "... = \<Sigma> {z\<cdot>x | z. P z \<and> z \<in> carrier Q}"
      by (metis set_image_comp)
    ultimately show ?thesis by metis
  qed

  lemma star_power: "\<Sigma> (powers x) = x\<^sup>*"
    unfolding star_def
  proof

   lemma star_unfoldr: assumes xc: "x \<in> carrier Q" shows "1 + x\<cdot>x\<^sup>* = x\<^sup>*"
     sorry
   lemma assumes xc: "x \<in> carrier Q" shows "x\<cdot>x\<^sup>* = x\<^sup>*\<cdot>x"
   proof -
     have "x\<cdot>x\<^sup>* = x\<cdot>(1 + x\<^sup>*\<cdot>x)"
       by (metis assms star_unfoldr)
     moreover have "... = (1 + x\<cdot>x\<^sup>*)\<cdot>x"
       by (smt assms distl distr mult_assoc mult_closed mult_onel mult_oner one_closed star_closed)
     moreover have "... = x\<^sup>*\<cdot>x"
       by (metis assms star_unfoldl)
     ultimately show ?thesis by metis
   qed

   lemma star_def_var: assumes xc: "x \<in> carrier Q" shows "\<mu>\<^bsub>Q\<^esub>(\<lambda>y. 1 + y\<cdot>x)"
     unfolding star_def
   proof -
     have "\<mu>\<^bsub>Q\<^esub>(\<lambda>y. 1 + x \<cdot> y) \<sqsubseteq> \<mu>\<^bsub>Q\<^esub>(\<lambda>y. 1 + y \<cdot> x)"
       apply (rule fixpoint_induction)
       prefer 5
       

end
