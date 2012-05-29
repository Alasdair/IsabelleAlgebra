theory Quantale
  imports Lattice
begin

record 'a mult_ord = "'a ord" +
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<index>" 80)
  one :: "'a"

lemma set_comp_subset: "{x. P x \<and> x \<in> A} \<subseteq> A"
  by (smt Collect_def mem_def predicate1I)

locale unital_quantale = fixes Q (structure)
  assumes quantale_complete_lattice: "complete_lattice Q"
  and mult_closed: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier Q"
  and mult_assoc: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
  and inf_distl: "\<lbrakk>x \<in> carrier Q; Y \<subseteq> carrier Q\<rbrakk> \<Longrightarrow> x \<cdot> lub Y = lub ((\<lambda>y. x\<cdot>y) ` Y)"
  and inf_distr: "\<lbrakk>x \<in> carrier Q; Y \<subseteq> carrier Q\<rbrakk> \<Longrightarrow> lub Y \<cdot> x = lub ((\<lambda>y. y\<cdot>x) ` Y)"
  and one_closed: "one Q \<in> carrier Q"
  and mult_onel: "x \<in> carrier Q \<Longrightarrow> one Q \<cdot> x = x"
  and mult_oner: "x \<in> carrier Q \<Longrightarrow> x \<cdot> one Q = x"

sublocale unital_quantale \<subseteq> lat: complete_lattice Q
  by (metis quantale_complete_lattice)

context unital_quantale
begin

  abbreviation qone :: "'a" ("1") where
    "qone \<equiv> one Q"

  abbreviation sum :: "'a set \<Rightarrow> 'a" ("\<Sigma>") where
    "\<Sigma> X \<equiv> lub X"

  abbreviation qzero :: "'a" ("0") where
    "qzero \<equiv> bot"

  abbreviation qplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 70) where
    "x + y \<equiv> join x y"

  lemma add_comm: "qplus x y = qplus y x" by (metis join_comm)

  lemma add_assoc: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q; z \<in> carrier Q\<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)" by (metis join_assoc)

  lemma add_idem: "x \<in> carrier Q \<Longrightarrow> x + x = x" by (metis join_idem)

  lemma add_oner: "x \<in> carrier Q \<Longrightarrow> x + 0 = x" by (metis bot_oner)

  lemma add_onel: "x \<in> carrier Q \<Longrightarrow> 0 + x = x" by (metis bot_onel)

  lemma add_closed: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> x + y \<in> carrier Q" by (metis join_closed)

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

  definition preimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightharpoondown>" 60) where
    "preimp x y \<equiv> \<Sigma> {z. x \<cdot> z \<sqsubseteq> y \<and> z \<in> carrier Q}"

  lemma preimp_closed: "\<lbrakk>x \<in> carrier Q; y \<in> carrier Q\<rbrakk> \<Longrightarrow> x \<rightharpoondown> y \<in> carrier Q"
    apply (unfold preimp_def)
    apply (rule lub_closed)
    apply (metis (full_types) Collect_conj_eq Collect_disj_eq Int_lower2 Un_absorb Un_def)
    by (metis (full_types) Collect_conj_eq Collect_disj_eq Int_lower2 Un_absorb Un_def is_lub_lub)

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

end

end
