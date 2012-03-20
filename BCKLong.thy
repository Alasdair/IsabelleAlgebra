(*<*)
theory BCK
  imports "~~/src/HOL/Algebra/Lattice" Finite_Set

begin

declare [[ smt_solver = remote_z3 ]]
(*>*)

section {* Dioids, Powers and Finite Sums with Explicit Carrier Sets *}

record 'a dioid = "'a gorder" +
  plus :: "['a , 'a]  \<Rightarrow> 'a" (infixl "\<oplus>\<index>" 70)
  mult :: "['a , 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 80)
  one  :: "'a" ("\<one>\<index>")
  zero :: "'a" ("\<zero>\<index>")

locale dioid = weak_partial_order D for D (structure) +
  assumes leq_def: "\<lbrakk>x\<in>carrier D; y\<in>carrier D\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y \<longleftrightarrow> x\<oplus>y=y)"
  and add_closed: "\<lbrakk> x\<in>carrier D; y\<in>carrier D\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<in>carrier D"
  and mult_closed: "\<lbrakk> x\<in>carrier D; y\<in>carrier D\<rbrakk> \<Longrightarrow> (x\<otimes>y)\<in>carrier D"
  and one_closed: "\<one>\<in>carrier D"
  and zero_closed: "\<zero>\<in>carrier D"
  and mult_assoc: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x\<otimes>(y\<otimes>z) = (x\<otimes>y)\<otimes>z"
  assumes add_assoc: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x\<oplus>(y\<oplus>z) = (x\<oplus>y)\<oplus>z"
  and add_comm: "\<lbrakk>x\<in>carrier D; y\<in>carrier D\<rbrakk> \<Longrightarrow> x\<oplus>y = y\<oplus>x"
  and idem: "x\<in>carrier D \<Longrightarrow> x\<oplus>x = x"
  and distl: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x\<otimes>(y\<oplus>z) = (x\<otimes>y)\<oplus>(x\<otimes>z)"
  and distr: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<otimes>z = (x\<otimes>z)\<oplus>(y\<otimes>z)"
  and mult_onel: "x\<in>carrier D \<Longrightarrow> \<one>\<otimes>x = x"
  and mult_oner: "x\<in>carrier D \<Longrightarrow> x\<otimes>\<one> = x"
  and add_zerol: "x\<in>carrier D \<Longrightarrow> \<zero>\<oplus>x = x"
  and annir: "x\<in>carrier D \<Longrightarrow> \<zero>\<otimes>x = \<zero>"
  and annil: "x\<in>carrier D \<Longrightarrow> x\<otimes>\<zero> = \<zero>"

context dioid
begin

lemma order_prop: "\<lbrakk> x \<in> carrier D ; y \<in> carrier D \<rbrakk> \<Longrightarrow> (\<forall>z\<in>carrier D.((x \<sqsubseteq> z) \<longleftrightarrow> (y \<sqsubseteq> z))) \<longrightarrow> x = y"
  by (metis add_comm le_refl leq_def)

lemma add_zeror: "x\<in>carrier D \<Longrightarrow> x\<oplus>\<zero> = x"
  by (metis add_comm add_zerol zero_closed)

lemma add_lub: "\<lbrakk>x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z  \<longleftrightarrow> x\<oplus>y \<sqsubseteq> z"
  by (metis (no_types) add_assoc add_closed add_comm idem leq_def)

lemma add_iso: "\<lbrakk>x\<in>carrier D;y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> z\<oplus>x \<sqsubseteq> z\<oplus>y"
  by (metis add_closed add_comm add_lub idem leq_def)

lemma mult_isol: "\<lbrakk>x\<in>carrier D;y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> z\<otimes>x \<sqsubseteq> z\<otimes>y"
  by (metis (no_types) distl leq_def mult_closed)

lemma mult_isor: "\<lbrakk>x\<in>carrier D;y\<in>carrier D;z\<in>carrier D\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> x\<otimes>z \<sqsubseteq> y\<otimes>z"
by (metis (no_types) distr leq_def mult_closed)

lemma mult_double_iso: "\<lbrakk>w\<in>carrier D; x\<in>carrier D; y\<in>carrier D; z\<in>carrier D\<rbrakk> \<Longrightarrow> w \<sqsubseteq> x \<and> y \<sqsubseteq> z \<longrightarrow> w\<otimes>y \<sqsubseteq> x\<otimes>z"
  by (smt add_assoc distl distr idem leq_def mult_closed)

lemma subdistl: "\<lbrakk>x\<in> carrier D; y\<in>carrier D;z\<in>carrier D\<rbrakk> \<Longrightarrow> z\<otimes>x \<sqsubseteq> z\<otimes>(x\<oplus>y)"
  by (metis add_assoc add_closed idem leq_def mult_double_iso)

end

record 'a dioid_finsup = "'a dioid" +
  finsup :: "'a set \<Rightarrow> 'a" ("\<Sigma>\<index> _" [81] 80)

locale dioid_finsup = dioid D for D (structure) +
  assumes finsup_closed : "\<lbrakk> finite A ; A \<subseteq> carrier D \<rbrakk> \<Longrightarrow>\<Sigma> A \<in> carrier D"
  and finsup_empty: "\<Sigma> {} = \<zero>"
  and finsup_insert: "\<lbrakk> A \<subseteq> carrier D ; finite A ; x \<in> carrier D \<rbrakk> \<Longrightarrow> \<Sigma> (insert x A) = x \<oplus> \<Sigma> A" 
begin

text {* We could have defined $\Sigma$ in terms of a fold over finite
sets in Isabelle, but that makes proofs much more complicated. *}

lemma finsup_x: assumes "x\<in>carrier D"
  shows "\<Sigma>{x} = x"
  by (metis (no_types) add_zeror assms empty_subsetI finite.emptyI finsup_empty finsup_insert)

lemma finsup: 
  assumes "A \<subseteq> carrier D" and "finite A" and "y \<in> carrier D"
  shows "(\<forall>x\<in>A. x \<sqsubseteq> y) \<longleftrightarrow> (\<Sigma> A \<sqsubseteq> y)" 
  using assms
  proof (induct rule: finite_induct [OF assms(2)]) 
    case 1 thus ?case
      by (metis add_zerol assms(3) finsup_empty leq_def zero_closed empty_iff)
  next 
    case 2 thus ?case
      by auto (metis add_lub finsup_closed finsup_insert) +
qed

lemma finsup_intro: 
  assumes "A \<subseteq> carrier D" and "B \<subseteq> carrier D" and "finite A" and "finite B"
  shows "(\<forall>x\<in>A. \<exists>y\<in>B. x \<sqsubseteq> y) \<longrightarrow> (\<Sigma> A \<sqsubseteq> \<Sigma> B)"
  by (smt assms(1) assms(2) assms(3) assms(4) finsup finsup_closed in_mono le_refl le_trans)

lemma finsup_union: 
  assumes "A \<subseteq> carrier D" and "B \<subseteq> carrier D" and "finite A"  and "finite B"
  shows "\<Sigma>(A\<union>B) = (\<Sigma> A)\<oplus>(\<Sigma> B)"
proof -
  have "A\<union>B \<subseteq> carrier D"
    by (metis assms(1) assms(2) Un_least) 
  also have "finite (A\<union>B)"
    by (metis assms(3) assms(4) finite_UnI)
  ultimately show ?thesis
    by (smt assms(1) assms(2) UnCI UnE add_closed add_lub assms(3) assms(4) finsup finsup_closed le_refl le_trans leq_def order_prop)
qed

lemma finsup_iso: 
  assumes "B \<subseteq> carrier D" and "finite B" 
  shows "A \<subseteq> B \<longrightarrow> \<Sigma> A \<sqsubseteq> \<Sigma> B"
  by (metis assms(1) assms(2) finite_subset finsup_intro in_mono le_refl subset_trans)

lemma finsup_fin_prod_var:
  "\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> finite {a\<otimes>b | a b. a\<in>A \<and> b\<in>B}"
 proof-
  assume "finite A" and "finite B"
  hence "finite ((\<lambda> p . ((fst p) \<otimes> (snd p))) ` { p . (A \<times> B) p})"
    by (metis (no_types) Collect_def finite_SigmaI finite_imageI)
  also have   "{a\<otimes>b | a b. a\<in>A \<and> b\<in>B} = {(\<lambda>p. ((fst p)\<otimes>(snd p))) p | p. (A\<times>B) p}"
    by (auto, metis SigmaI mem_def, metis SigmaE2 mem_def)
  moreover have  "(\<lambda>p. ((fst p)\<otimes>(snd p))) ` {p. (A\<times>B) p} = {(\<lambda>p. ((fst p)\<otimes>(snd p))) p | p. (A\<times>B) p}"
    by (auto, metis, smt Collect_def fst_conv image_iff mem_def snd_conv)
  ultimately show ?thesis by auto
qed

lemma finsup_dist_el:
  assumes "finite A" and "A \<subseteq> carrier D" and "x \<in> carrier D"
  shows "x\<otimes>(\<Sigma> A) = \<Sigma> {x\<otimes>a | a. a\<in>A}" using assms
proof (induct rule: finite_induct[OF assms(1) ])
  case 1 thus ?case
    by (smt annil finsup_empty assms(2) Collect_empty_eq empty_iff)
next
  case 2 thus ?case 
  proof -
   fix y F 
    assume  fF: "finite F"
      and indhyp: "\<lbrakk>finite F; F \<subseteq> carrier D; x\<in>carrier D\<rbrakk>
      \<Longrightarrow> x\<otimes>(\<Sigma> F) = \<Sigma>{x\<otimes>a |a. a\<in>F}" 
       and yFD: "insert y F \<subseteq> carrier D"
    hence fxa:"finite {x\<otimes>a | a . a\<in>F}"
      by  auto
    also have xyD: "{x\<otimes>a | a . a\<in>F} \<subseteq> carrier D"
      by (auto, metis insert_subset mult_closed set_rev_mp assms(3) yFD) 
    moreover have "x\<otimes>(\<Sigma>(insert y F)) = \<Sigma>(insert (x\<otimes>y) {x\<otimes>a | a . a\<in>F})"
     by (smt "2"(6) calculation fF distl finsup_closed finsup_insert fxa indhyp insert_subset mult_closed yFD)
   moreover have  "(insert (x\<otimes>y) {x\<otimes>z | z. z\<in>F}) = {x\<otimes>z |z. z \<in> insert y F}"
     by auto 
   ultimately show "x\<otimes>(\<Sigma> insert y F)  = \<Sigma>{x\<otimes>a |a. a\<in>(insert y F)}"
     by auto
  qed
qed

lemma prod_carrier: 
  "\<lbrakk>A \<subseteq> carrier D; B \<subseteq> carrier D\<rbrakk> \<Longrightarrow> {a\<otimes>b | a b. a\<in>A \<and> b\<in>B} \<subseteq> carrier D"
  by (auto, metis mult_closed set_mp)

lemma finsup_dist:
  assumes "A \<subseteq> carrier D" and "B \<subseteq> carrier D" and "finite A" and "finite B" 
  shows "(\<Sigma> A) \<otimes> (\<Sigma> B) = \<Sigma> {a\<otimes>b | a b. a\<in>A \<and> b\<in>B}"
  using  assms
proof (induct rule: finite_induct[OF assms(3)])
  case 1 thus ?case
    by (smt assms(2) annir assms(4) finsup_closed finsup_empty Collect_empty_eq empty_iff)
next
  case 2 thus ?case
  proof -
    fix x A
    assume fF: "finite A"
      and indhyp: "\<lbrakk>A \<subseteq> carrier D; B \<subseteq> carrier D; finite A; finite B\<rbrakk>
      \<Longrightarrow> \<Sigma> A \<otimes> (\<Sigma> B) = \<Sigma> {a\<otimes>b |a b. a\<in>A \<and> b\<in>B}"
      and xFD: "(insert x A) \<subseteq> carrier D"
     have FD: "A \<subseteq> carrier D"
      by (metis insert_subset xFD)
    have xD: "x\<in>carrier D"
      by (metis insert_subset xFD) 
    have Dxy: "{x\<otimes>y | y. y\<in>B} \<subseteq> carrier D"
      by (auto, metis assms(2) mult_closed subsetD xD)
    have  prod_union:
  "{x\<otimes>b | b. b\<in>B }\<union>{a\<otimes>b | a b. a\<in>A \<and> b\<in>B} = {a\<otimes>b |a b. a\<in>(insert x A) \<and> b\<in>B}"
      by auto
    have "\<Sigma>( insert x A)\<otimes>(\<Sigma> B) = (x\<otimes>(\<Sigma> B))\<oplus>((\<Sigma> A)\<otimes>(\<Sigma> B))"
      by (metis fF finsup_insert insert_subset xFD assms(2) distr assms(4) finsup_closed)
   also have "... = \<Sigma> ({x\<otimes>a | a. a\<in>B}\<union>{a\<otimes>b | a b. a\<in>A \<and> b\<in> B})" 
     by (simp add: fF assms(4)  FD xD indhyp finsup_dist_el assms(2) Dxy finsup_union finsup_fin_prod_var prod_carrier)
    ultimately show  "(\<Sigma> insert x A)\<otimes>(\<Sigma> B) = \<Sigma> {a\<otimes>b |a b. a\<in>(insert x A) \<and> b\<in>B}"
      by (metis prod_union) 
  qed
qed

lemma dioid_setsum_prod: 
  assumes "finite A" and "{F x | x. x\<in>A} \<subseteq> carrier D"
  shows "(\<Sigma> {(F x) | x. x\<in>A})\<otimes>(\<Sigma> {(F x) | x. x\<in>A}) = \<Sigma> {(F x)\<otimes>(F y) | x y. x\<in>A \<and> y\<in>A}"
proof -
  have "{x\<otimes>y | x y. (\<exists>a. x = (F a) \<and> a\<in>A) \<and> (\<exists>b. y = (F b) \<and> b\<in>A)} = {(F a)\<otimes>(F b) | a b. a\<in>A \<and> b\<in>A}"
    by auto
  thus ?thesis
    by (simp add: assms(1) assms(2) finsup_dist)
qed

end

(*******************************************************************************)

section {* Boffa Algebras with Carriers and Conway's Group Identities *}

record 'a boffa = "'a dioid_finsup"+
  star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>\<index>" [101] 100)

locale boffa = dioid_finsup B for B (structure) + 
  assumes star_closed: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star>\<in>carrier B"

locale boffa1 = boffa +
  assumes C11: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<^sup>\<star>=(x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>"
  and C12: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<otimes>y)\<^sup>\<star> = \<one>\<oplus>x\<otimes>((y\<otimes>x)\<^sup>\<star>)\<otimes>y"
  and R: "x\<in>carrier B \<Longrightarrow> (x\<otimes>x = x \<longrightarrow> x\<^sup>\<star> = \<one>\<oplus>x)"

locale boffa2 = boffa +
  assumes B1: "x\<in>carrier B \<Longrightarrow> \<one>\<oplus>x \<sqsubseteq> x\<^sup>\<star>"
  and B2: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star>\<otimes>x\<^sup>\<star> = x\<^sup>\<star>"
  and B3: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> \<one>\<oplus>x \<sqsubseteq> y \<and> y\<otimes>y = y \<longrightarrow> x\<^sup>\<star> \<sqsubseteq> y"

record ('a, 'b) boffa_gen = "'a boffa" +
  gen :: "'b \<Rightarrow> 'a" ("\<gamma>\<index>_")
  gen_set :: "'b set" ("\<Gamma>\<index>")

locale boffa_gen = boffa1 G for G (structure) +
  assumes gen_closed: "x\<in>\<Gamma> \<Longrightarrow> (\<gamma> x) \<in> carrier G"

record ('a, 'b) boffa_monoid = "('a, 'b) boffa_gen" +
  comp :: "['b, 'b] => 'b"  (infix "\<odot>\<index>" 80)
  unit :: "'b" ("e\<index>")

definition mon_pair :: "('a , 'b,  'c) boffa_monoid_scheme => 'b \<Rightarrow> 'b => 'a" ("_,\<index>_") where
   "x ,\<^bsub>G\<^esub> y = \<Sigma>\<^bsub>G\<^esub> { (\<gamma>\<^bsub>G\<^esub> z) | z . ((z\<in>\<Gamma>\<^bsub>G\<^esub>) \<and> ((x\<odot>\<^bsub>G\<^esub>z) = y)) }"

locale boffa_monoid = boffa_gen G for G (structure) +
  assumes comp_closed: "\<lbrakk>x\<in>gen_set G; y\<in>gen_set G\<rbrakk> \<Longrightarrow> x\<odot>y\<in>gen_set G"
  and gen_finite: "finite (gen_set G)"
  and unit_closed: "e \<in> gen_set G"
  and unit_left: "\<lbrakk> x\<in>gen_set G \<rbrakk> \<Longrightarrow> e\<odot>x = x"
  and unit_right: "\<lbrakk> x\<in>gen_set G \<rbrakk> \<Longrightarrow> x\<odot>e = x"
  and comp_assoc: "\<lbrakk> x\<in>gen_set G ; y\<in>gen_set G ; z\<in>gen_set G \<rbrakk> \<Longrightarrow> x\<odot>(y\<odot>z) = (x\<odot>y)\<odot>z"

begin

lemma mon_pair_e: "(e,e) = \<gamma> e"
proof -
  have "\<forall>x.(x\<in>{\<gamma> z | z . z\<in>\<Gamma> \<and> e\<odot>z = e} \<longleftrightarrow> x\<in>{\<gamma> e})"
    by (simp, metis unit_closed unit_left)   
  hence "\<Sigma> {\<gamma> z | z . z\<in>\<Gamma> \<and> e\<odot>z = e} = \<Sigma> {\<gamma> e}"
    by (simp add: set_eqI)
  thus ?thesis
    by (metis (no_types) finsup_x gen_closed mon_pair_def unit_closed)
qed

lemma gen_carrier: "{\<gamma> x | x. x\<in>\<Gamma>} \<subseteq> carrier G"
by  auto (metis gen_closed)

lemma gen_carrier_finite: "finite {\<gamma> x | x. x\<in>\<Gamma>}"
  by (metis (no_types) finite.insertI finite_Collect_disjI finite_image_set gen_finite insert_compr)

lemma gen_in_carrier: "\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>} \<in> carrier G"
  by (metis (no_types) finsup_closed gen_carrier gen_carrier_finite)

lemma dioid_Gen_carrier: "\<lbrakk>finite A; A \<subseteq> \<Gamma>\<rbrakk> \<Longrightarrow> {\<gamma> x | x. x\<in>A} \<subseteq> carrier G"
  by (auto, metis gen_closed subsetD)

lemma dioid_Gen_finite: "\<lbrakk>finite A; A \<subseteq> \<Gamma>\<rbrakk> \<Longrightarrow> finite {\<gamma> x | x. x\<in>A}"
  by (metis (no_types) finite.insertI finite_Collect_disjI finite_image_set insert_compr)

lemma dioid_setsum_GS: "\<lbrakk>finite A; A \<subseteq> \<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma> {\<gamma> x | x. x\<in>A}\<in>carrier G"
  by (simp add: dioid_Gen_carrier dioid_Gen_finite finsup_closed)

lemma gen_prod_carrier_var: "{(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>} \<subseteq> carrier G"
  by (auto, metis gen_closed mult_closed)

lemma gen_prod_carrier: "\<Sigma> {(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>} \<in> carrier G"
proof -
  have "\<Sigma> {(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>} = (\<Sigma> {\<gamma> x | x . x\<in>\<Gamma>})\<otimes>(\<Sigma> {\<gamma> x | x . x\<in>\<Gamma>})"
    by (simp add: dioid_setsum_prod gen_carrier gen_finite)
  thus ?thesis
    by (smt gen_in_carrier mult_closed)
qed

lemma gen_finsup_fin_prod_var: "finite {(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>}"
 proof-
   have "(\<lambda>p. ((\<gamma> (fst p))\<otimes>(\<gamma> (snd p)))) ` {p. (\<Gamma>\<times>\<Gamma>) p} = {(\<lambda>p. ((\<gamma> (fst p))\<otimes>(\<gamma> (snd p)))) p | p. (\<Gamma>\<times>\<Gamma>) p}"
     by  (auto, metis, smt Collect_def fst_conv image_iff mem_def snd_conv)
   hence "(\<lambda>p. ((\<gamma> (fst p))\<otimes>(\<gamma> (snd p)))) ` {p. (\<Gamma>\<times>\<Gamma>) p} =  {(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>}" 
     by (auto, metis mem_Sigma_iff mem_def, smt mem_Sigma_iff mem_def)
   thus ?thesis
     by (smt Collect_def finite_SigmaI finite_imageI gen_finite)
qed

lemma gen_e_carrier: "{\<gamma> x | x. x\<in>(\<Gamma>-{e})} \<subseteq> carrier G"
  by (metis (no_types) finite_Diff gen_finite Diff_subset dioid_Gen_carrier)

lemma gen_e_finite: "finite {\<gamma> x | x. x\<in>(\<Gamma>-{e})}"
  by (metis (no_types) Diff_subset dioid_Gen_finite finite_Diff gen_finite)

lemma gen_e_setsum: "\<Sigma> {\<gamma> x | x. x\<in>(\<Gamma>-{e})} \<in> carrier G"
  by (metis (no_types) finsup_closed gen_e_carrier gen_e_finite)
 
lemma gen_e: "(\<forall>g\<in>\<Gamma>. \<forall>h\<in>\<Gamma>. (g,h)\<^sup>\<star> = (g,h)) \<Longrightarrow> (\<gamma> e) = \<one>\<oplus>(\<gamma> e)"
  by (metis mon_pair_e unit_closed C11 R add_comm gen_closed idem mult_onel mult_oner one_closed unit_closed)

lemma gen_e_split: "\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>} = (\<gamma> e)\<oplus> \<Sigma> {\<gamma> x | x. x\<in>(\<Gamma>-{e})}"
proof -
  have fin1: "finite {\<gamma> e}" 
    by simp 
  have "{\<gamma> x | x. x\<in>\<Gamma>} = ({\<gamma> x | x. x\<in>{e}} \<union> {\<gamma> x | x. x\<in>(\<Gamma>-{e})})"
    by (auto, metis unit_closed)
  hence "\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>} = \<Sigma> ({\<gamma> e} \<union> {\<gamma> x | x. x\<in>(\<Gamma>-{e})})"
    by simp
  thus ?thesis
    by (smt fin1 gen_e_finite gen_e_carrier finsup_x finsup_union empty_subsetI gen_closed insert_subset unit_closed)
qed

lemma gen_split_one: 
  "(\<forall>g\<in>\<Gamma>. \<forall>h\<in>\<Gamma>. (g,h)\<^sup>\<star> = (g,h)) \<Longrightarrow> \<Sigma> {\<gamma> x | x. x\<in>\<Gamma>} = \<one>\<oplus>\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>}"
   by (smt gen_e gen_e_split add_assoc gen_e_setsum gen_closed one_closed unit_closed)

lemma aux1: "{\<gamma> x\<odot>y | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>} = {\<gamma> z | z . z\<in>\<Gamma>}"
  by (auto, metis comp_closed, metis unit_closed unit_left)

lemma aux2: 
  "(\<forall>x\<in>\<Gamma>. \<forall>y\<in>\<Gamma>. (\<gamma> x)\<otimes>(\<gamma> y) \<sqsubseteq> \<gamma> x\<odot>y)
  \<Longrightarrow> (\<Sigma> {(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>}) \<sqsubseteq> (\<Sigma> {\<gamma> x\<odot>y | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>})"
proof -
  assume "\<forall>x\<in>\<Gamma>. \<forall>y\<in>\<Gamma>. (\<gamma> x)\<otimes>(\<gamma> y) \<sqsubseteq> \<gamma> x\<odot>y"
  hence "\<forall>x\<in>{(\<gamma> x)\<otimes>(\<gamma> y) |x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>}. \<exists>y\<in>{\<gamma> (x\<odot>y) |x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>}. x \<sqsubseteq> y"
    by (auto, metis)
  thus ?thesis
    by (simp add: aux1 finsup_intro gen_carrier_finite gen_finsup_fin_prod_var gen_carrier gen_prod_carrier_var)
qed

lemma conway_group_identities: 
  "(\<forall>x\<in>\<Gamma>. \<forall>y\<in>\<Gamma>. (\<gamma> x)\<otimes>(\<gamma> y) \<sqsubseteq> (\<gamma> x\<odot>y) \<and> (x,y)\<^sup>\<star> = (x,y))
  \<Longrightarrow> (\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})\<^sup>\<star> = \<Sigma> {\<gamma> x | x. x\<in>\<Gamma>}"
proof -
  assume  hyp: "\<forall>x\<in>\<Gamma>. \<forall>y\<in>\<Gamma>. (\<gamma> x)\<otimes>(\<gamma> y) \<sqsubseteq> (\<gamma> x\<odot>y) \<and> (x,y)\<^sup>\<star> = (x,y)"
  have "(\<Sigma> {(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>}) \<sqsubseteq>  (\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})"
    by (smt hyp aux1 aux2)
  hence  one: "(\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})\<oplus>(\<Sigma> {(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>}) = (\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})"
    by (simp add: add_comm gen_in_carrier gen_prod_carrier leq_def)
  have "(\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})\<otimes>(\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>}) 
    = \<one>\<oplus>(\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})\<oplus>((\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})\<otimes>(\<Sigma> {\<gamma> y | y. y\<in>\<Gamma>}))"
    by (smt hyp gen_split_one add_closed gen_e_setsum distr gen_closed mult_onel one_closed gen_e_split unit_closed)
  also have "... =  \<one>\<oplus>((\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})\<oplus>\<Sigma> {(\<gamma> x)\<otimes>(\<gamma> y) | x y. x\<in>\<Gamma> \<and> y\<in>\<Gamma>})"
    by (simp add: dioid_setsum_prod gen_carrier gen_finite  add_assoc gen_in_carrier gen_prod_carrier one_closed)
  ultimately have "(\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})\<otimes>(\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>}) = (\<Sigma> {\<gamma> x | x . x\<in>\<Gamma>})"
    by (smt gen_split_one hyp one)
  thus "(\<Sigma> {\<gamma> x | x. x\<in>\<Gamma>})\<^sup>\<star> = \<Sigma> {\<gamma> x | x . x\<in>\<Gamma>}"
    by (smt R add_closed gen_e_setsum gen_closed gen_e_split unit_closed hyp gen_split_one)
qed

end

(********************************************************************************)

section {* Relating Boffa's Axiomatisations *}

sublocale boffa1 \<subseteq> boffa2
proof
 fix x y :: 'a
 show "x\<in>carrier B \<Longrightarrow> (\<one>\<Colon>'a) \<oplus> x \<sqsubseteq> x\<^sup>\<star>"
   by (smt C12 add_assoc add_closed distr idem leq_def mult_closed mult_onel mult_oner one_closed star_closed)
 show "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star> \<otimes> x\<^sup>\<star> = x\<^sup>\<star>"
   by (metis C11 C12 R `x \<in> carrier B \<Longrightarrow> \<one> \<oplus> x \<sqsubseteq> x\<^sup>\<star>` add_closed add_comm add_lub idem leq_def mult_onel mult_oner one_closed star_closed)
 show  "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (\<one>\<Colon>'a) \<oplus> x \<sqsubseteq> y \<and> y \<otimes> y = y \<longrightarrow> x\<^sup>\<star> \<sqsubseteq> y"
   by (metis C11 R `x \<in> carrier B \<Longrightarrow> x\<^sup>\<star> \<otimes> x\<^sup>\<star> = x\<^sup>\<star>` add_lub distr leq_def mult_assoc mult_closed mult_onel one_closed star_closed)
qed

context boffa2
begin

lemma star_ref: "x\<in>carrier B \<Longrightarrow> \<one> \<sqsubseteq> x\<^sup>\<star>"
  by (metis B1 add_lub one_closed star_closed)

lemma star_plus_one: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star> = \<one>\<oplus>x\<^sup>\<star>"
  by (metis leq_def one_closed star_closed star_ref)

lemma star_trans: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  by (metis B2 le_refl star_closed)

lemma star_trans_eq: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star>\<otimes>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B2)
 
lemma star_1l: "x\<in>carrier B \<Longrightarrow> x\<otimes>x\<^sup>\<star> \<sqsubseteq>  x\<^sup>\<star>"
  by (metis B1 B2 add_lub mult_isor one_closed star_closed)

lemma star_one: "\<one>\<^sup>\<star> = \<one>"
  by (metis B1 B3 add_comm idem leq_def mult_oner one_closed star_closed)
 
lemma star_subdist:  "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> x\<^sup>\<star> \<sqsubseteq> (x\<oplus>y)\<^sup>\<star>"
  by (metis (no_types) B1 B2 B3 add_closed add_lub one_closed star_closed)
  
lemma star_iso: "\<lbrakk>x\<in>carrier B;y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<sqsubseteq>y \<longrightarrow> x\<^sup>\<star>\<sqsubseteq>y\<^sup>\<star>)"
  by (metis leq_def star_subdist)

lemma star2: "x\<in>carrier B \<Longrightarrow> (\<one>\<oplus>x\<^sup>\<star>)= x\<^sup>\<star>"
  by (metis star_plus_one)
 
lemma star_unfoldl: "x\<in>carrier B \<Longrightarrow> \<one>\<oplus>x\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  by (metis add_lub mult_closed one_closed star_1l star_closed star_ref)

lemma star_unfoldr: "x\<in>carrier B \<Longrightarrow> \<one>\<oplus>x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<^sup>\<star>"
  by (metis B1 B2 add_lub mult_closed mult_isol one_closed star_closed star_ref)

lemma star_ext: "x\<in> carrier B \<Longrightarrow> x \<sqsubseteq> x\<^sup>\<star>"
  by (metis B1 add_lub one_closed star_closed)

lemma star_1r: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<^sup>\<star>"
  by (metis B2 mult_isol star_closed star_ext)

lemma star_unfoldl_eq: "x\<in>carrier B \<Longrightarrow> \<one>\<oplus>x\<otimes>x\<^sup>\<star> = x\<^sup>\<star>"
proof -
  assume "x\<in>carrier B"
  hence "(\<one>\<oplus>x\<otimes>x\<^sup>\<star>)\<otimes>(\<one>\<oplus>x\<otimes>x\<^sup>\<star>) = \<one>\<oplus>x\<otimes>x\<^sup>\<star>"
    by (smt B2 add_assoc add_closed add_comm distl distr idem leq_def mult_assoc mult_closed mult_onel mult_oner one_closed star_1l star_closed)
  hence "x\<^sup>\<star> \<sqsubseteq> \<one>\<oplus>x\<otimes>x\<^sup>\<star>"
    by (smt B3 `x \<in> carrier B` add_closed distl le_refl le_trans mult_closed mult_oner one_closed star2 star_closed star_subdist)
  thus ?thesis
    by (smt `x \<in> carrier B` add_assoc add_closed add_comm leq_def mult_closed one_closed star_1l star_closed star_plus_one)
qed

lemma star_unfoldr_eq: "x\<in>carrier B \<Longrightarrow> \<one>\<oplus>x\<^sup>\<star>\<otimes>x = x\<^sup>\<star>"
proof -
  assume "x\<in>carrier B"
  hence "(\<one>\<oplus>x\<^sup>\<star>\<otimes>x)\<otimes>(\<one>\<oplus>x\<^sup>\<star>\<otimes>x) = \<one>\<oplus>x\<^sup>\<star>\<otimes>x"
    by (smt B2 add_assoc add_closed add_comm distl distr idem leq_def mult_assoc mult_closed mult_onel mult_oner one_closed star_closed star_unfoldr)
  hence "x\<^sup>\<star> \<sqsubseteq> \<one>\<oplus>x\<^sup>\<star>\<otimes>x"
    by (smt B3 `x \<in> carrier B` add_closed distr le_refl le_trans mult_closed mult_onel one_closed star2 star_closed star_subdist)
  thus ?thesis
    by (smt B2 `x \<in> carrier B` add_assoc add_closed add_comm distl leq_def mult_closed one_closed star_closed star_ext star_plus_one)
qed

lemma star_prod_unfold1: "\<lbrakk> x\<in>carrier B ; y\<in>carrier B \<rbrakk> \<Longrightarrow> (x\<otimes>y)\<^sup>\<star> \<sqsubseteq> \<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y"
  proof -
  assume hyp1: "x\<in>carrier B" and hyp2: "y\<in>carrier B"
  have one: "(\<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y = (\<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y)\<otimes>(\<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y))"
    by (smt B2 hyp1 hyp2 add_assoc add_closed add_comm distl distr idem mult_assoc mult_closed mult_onel mult_oner one_closed star_closed star_unfoldl_eq)
  also have "\<one>\<oplus>x\<otimes>y \<sqsubseteq>  \<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y" 
    by (smt hyp1 hyp2 add_assoc add_closed distl distr idem leq_def mult_assoc mult_closed mult_onel one_closed star_closed star_plus_one)
  thus "(x\<otimes>y)\<^sup>\<star> \<sqsubseteq> \<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y" 
    by (metis B3 add_closed hyp1 hyp2 one mult_closed one_closed star_closed) 
qed

lemma star_prod_unfold2: "\<lbrakk> x\<in>carrier B ; y\<in>carrier B \<rbrakk> \<Longrightarrow> \<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y \<sqsubseteq> (x\<otimes>y)\<^sup>\<star>"
proof -
  assume  hyp1: "x\<in>carrier B" and hyp2: "y\<in>carrier B"
  hence "\<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y \<sqsubseteq> \<one>\<oplus>x\<otimes>y\<oplus>x\<otimes>y\<otimes>(x\<otimes>y)\<^sup>\<star>\<otimes>(x\<otimes>y)"
    by (smt star_prod_unfold1 add_closed add_iso hyp1 hyp2 leq_def mult_closed mult_isor one_closed star_closed subdistl add_assoc distl distr  mult_assoc mult_oner)
  thus "\<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y \<sqsubseteq> (x\<otimes>y)\<^sup>\<star>"
    by (smt add_assoc distl hyp1 hyp2 mult_assoc mult_closed mult_oner one_closed star_closed star_unfoldl_eq star_unfoldr_eq)
qed

lemma star_prod_unfold: "\<lbrakk> x\<in>carrier B ; y\<in>carrier B \<rbrakk> \<Longrightarrow> (x\<otimes>y)\<^sup>\<star> = \<one>\<oplus>x\<otimes>(y\<otimes>x)\<^sup>\<star>\<otimes>y"
  by (metis (no_types) add_closed add_comm leq_def mult_closed one_closed star_closed star_prod_unfold1 star_prod_unfold2)

lemma star_slide1: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<otimes>y)\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<otimes>(y\<otimes>x)\<^sup>\<star>"
  by (smt distl distr le_refl mult_assoc mult_closed mult_onel mult_oner one_closed star_closed star_prod_unfold star_unfoldl_eq)

lemma star_slide_var1: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star>\<otimes>x \<sqsubseteq> x\<otimes>x\<^sup>\<star>"
by (metis mult_onel mult_oner one_closed star_slide1)

lemma star_slide: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<otimes>y)\<^sup>\<star>\<otimes>x = x\<otimes>(y\<otimes>x)\<^sup>\<star>"
  by (smt distl distr mult_assoc mult_closed mult_onel mult_oner one_closed star_closed star_prod_unfold star_unfoldl_eq)

lemma star_rtc1: "x\<in>carrier B \<Longrightarrow> \<one>\<oplus>x\<oplus>x\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  by (metis B1 B2 add_closed leq_def one_closed star_closed star_trans)

lemma star_rtc1_eq: "x\<in>carrier B \<Longrightarrow> \<one>\<oplus>x\<oplus>x\<^sup>\<star>\<otimes>x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B1 B2 add_closed leq_def one_closed star_closed)

lemma star_subdist_var_1: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> x \<sqsubseteq> (x\<oplus>y)\<^sup>\<star>"
  by (metis (no_types) add_closed le_trans star_closed star_ext star_subdist)

lemma star_subdist_var_2: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> x\<otimes>y \<sqsubseteq> (x\<oplus>y)\<^sup>\<star>"
  by (metis (no_types) B2 add_closed add_comm mult_double_iso star_closed star_subdist_var_1)

lemma star_subdist_var_3: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<otimes>y\<^sup>\<star> \<sqsubseteq> (x\<oplus>y)\<^sup>\<star>"
  by (metis (no_types) B2 add_closed add_comm mult_double_iso star_closed star_subdist)

lemma R_lemma: "x\<in>carrier B \<Longrightarrow> (x\<otimes>x = x \<longrightarrow> x\<^sup>\<star> = \<one>\<oplus>x)"
    by (smt B3 add_assoc add_closed distl distr idem le_refl mult_onel mult_oner one_closed B2 add_comm leq_def star_closed star_rtc1_eq)

lemma one_star: "x\<in>carrier B \<longrightarrow> x\<^sup>\<star> = (\<one>\<oplus>x)\<^sup>\<star>"
  by (smt B2 R_lemma add_assoc add_closed add_comm add_lub idem le_refl leq_def one_closed star_closed star_iso star_one star_plus_one star_rtc1_eq star_subdist)

lemma star_denest: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<^sup>\<star> = (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star>"
proof -
  assume hyp1: "x\<in>carrier B" and hyp2: "y\<in>carrier B"
  hence "(x\<oplus>y)\<^sup>\<star> \<sqsubseteq> (x\<^sup>\<star>\<oplus>x\<^sup>\<star>\<otimes>y)\<^sup>\<star>"
    by (metis (no_types) B1 add_closed add_iso add_lub mult_closed mult_isor mult_onel one_closed star_closed star_iso add_comm  star_ext star_iso)
  also have "... \<sqsubseteq>  (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star>"
    by (smt distl mult_oner add_closed hyp1 hyp2 mult_closed mult_isol one_closed star_closed star_ext star_iso one_star)
  ultimately have "(x\<oplus>y)\<^sup>\<star> \<sqsubseteq> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star>"
    by (metis (no_types) add_closed hyp1 hyp2 le_trans mult_closed star_closed)
  thus ?thesis
    by (smt B2 B3 add_closed add_lub hyp1 hyp2 mult_closed one_closed star_closed star_ref star_subdist_var_3 add_comm leq_def)
qed

lemma star_denest_aux: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>"
proof -
  assume hyp1: "x\<in>carrier B" and hyp2: "y\<in>carrier B"
  hence "((x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>)\<otimes>((x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>) = (x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>"
    by (metis (no_types) B2 mult_assoc mult_closed star_closed star_slide)
  hence "((x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>"
    by (smt R_lemma hyp1 hyp2 mult_closed star_closed B2 distr mult_assoc one_closed star_plus_one star_slide)
  hence one: "(x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star> \<sqsubseteq> (x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>"
    by (metis hyp1 hyp2 mult_closed mult_isol mult_oner one_closed star_closed star_iso star_ref star_slide)
  also have  "(x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star>\<otimes>x\<^sup>\<star>"
    by (metis hyp1 hyp2 mult_closed mult_isol mult_isor star_closed star_ext star_iso)
  hence "(x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star> \<sqsubseteq> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star>"
    by (smt distl hyp1 hyp2 leq_def mult_closed mult_oner one_closed star2 star_closed star_slide mult_assoc star_1r le_trans)
  thus ?thesis using one
    by (metis add_comm hyp1 hyp2 leq_def mult_closed star_closed) 
qed

lemma star_denest_var: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<^sup>\<star> = x\<^sup>\<star>\<otimes>(y\<otimes>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_closed star_denest star_denest_aux star_slide)

lemma star_denest_var_0: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<^sup>\<star> = (x\<^sup>\<star>\<otimes>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>"
  by (metis star_denest star_denest_aux)

lemma star_denest_var_2: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<otimes>(y\<otimes>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var)

lemma star_denest_var_3: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<otimes>(y\<^sup>\<star>\<otimes>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis B2 R_lemma star_closed star_denest_var_2 star_plus_one)

lemma star_denest_var_4:  "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star> = (y\<^sup>\<star>\<otimes>x\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm star_denest)

lemma star_denest_var_5: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<otimes>(y\<otimes>x\<^sup>\<star>)\<^sup>\<star> = y\<^sup>\<star>\<otimes>(x\<otimes>y\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm star_denest_var)

lemma star_denest_var_6: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<^sup>\<star> = x\<^sup>\<star>\<otimes>y\<^sup>\<star>\<otimes>(x\<oplus>y)\<^sup>\<star>"
  by (metis (no_types) add_closed mult_assoc star_closed star_denest star_denest_var_3)

lemma star_denest_var_7: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<oplus>y)\<^sup>\<star> = (x\<oplus>y)\<^sup>\<star>\<otimes>x\<^sup>\<star>\<otimes>y\<^sup>\<star>"
  by (smt star_closed star_denest star_denest_var_3 star_denest_var_4 star_slide)

lemma star_denest_var_8: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>\<otimes>y\<^sup>\<star>\<otimes>(x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var_6)

lemma star_denest_var_9: " \<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow> (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star>\<otimes>y\<^sup>\<star>)\<^sup>\<star>\<otimes>x\<^sup>\<star>\<otimes>y\<^sup>\<star>"
  by (metis star_denest star_denest_var_7)

lemma star_slide_var: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star>\<otimes>x = x\<otimes>x\<^sup>\<star>"
  by (metis mult_onel mult_oner one_closed star_slide)

lemma star_sum_unfold: "\<lbrakk>x\<in>carrier B; y\<in>carrier B\<rbrakk> \<Longrightarrow>(x\<oplus>y)\<^sup>\<star> = x\<^sup>\<star>\<oplus>x\<^sup>\<star>\<otimes>y\<otimes>(x\<oplus>y)\<^sup>\<star>"
  by (smt distr mult_assoc mult_closed mult_onel one_closed star_closed star_denest_var_0 star_unfoldl_eq)

lemma troeger: "\<lbrakk>x\<in>carrier B; y\<in>carrier B; z\<in>carrier B\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<otimes>(y\<otimes>((x\<oplus>y)\<^sup>\<star>\<otimes>z)\<oplus>z) = (x\<oplus>y)\<^sup>\<star>\<otimes>z"
  by (smt star_sum_unfold add_closed distr mult_closed star_closed add_comm distl mult_assoc)


lemma sqstar: "x\<in>carrier B \<longrightarrow>(x\<otimes>x)\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
    by (metis B2 B3 add_lub idem mult_closed one_closed star_closed star_ref star_subdist_var_2)

lemma meyer_1: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star> = (\<one>\<oplus>x)\<otimes>(x\<otimes>x)\<^sup>\<star>"
proof -
  assume  hyp: "x\<in>carrier B"
   hence "(\<one>\<oplus>x)\<otimes>(x\<otimes>x)\<^sup>\<star>\<otimes>(\<one>\<oplus>x)\<otimes>(x\<otimes>x)\<^sup>\<star> = (\<one>\<oplus>x)\<otimes>(x\<otimes>x)\<^sup>\<star>"
      by (smt add_closed distr mult_assoc mult_closed mult_onel one_closed star_closed B2 add_assoc distl star_slide idem add_comm R_lemma star2 star_denest_var_6 star_one star_prod_unfold)
    hence one: "x\<^sup>\<star> \<sqsubseteq> (\<one>\<oplus>x)\<otimes>(x\<otimes>x)\<^sup>\<star>"
      by (smt B3 add_closed hyp mult_assoc mult_closed mult_isol mult_oner one_closed star_closed star_plus_one star_ref)
  thus " x\<^sup>\<star> = (\<one>\<oplus>x)\<otimes>(x\<otimes>x)\<^sup>\<star>"
      by (smt B1 B2 add_closed hyp mult_closed mult_double_iso one_closed sqstar star_closed leq_def add_comm)
qed

lemma star_zero: "\<zero>\<^sup>\<star> = \<one>"
  by (metis add_comm add_zerol leq_def one_closed star2 star_closed star_one star_subdist zero_closed)

lemma star_invol: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star> = (x\<^sup>\<star>)\<^sup>\<star>"
  by (metis B2 idem star_denest)

lemma star_subsum: "x\<in>carrier B \<Longrightarrow> x\<^sup>\<star>\<oplus>x\<^sup>\<star>\<otimes>x = x\<^sup>\<star>"
  by (metis B2 idem mult_assoc star_closed star_slide_var star_sum_unfold)

lemma prod_star_closure: "\<lbrakk>x\<in>carrier B; y\<in>carrier B; z\<in>carrier B\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> z\<^sup>\<star> \<and> y \<sqsubseteq> z\<^sup>\<star> \<longrightarrow> x\<otimes>y \<sqsubseteq> z\<^sup>\<star>)"
  by (metis B2 mult_double_iso star_closed)

end

sublocale boffa2 \<subseteq> boffa1
  by unfold_locales (metis star_denest_var_0, metis star_prod_unfold, metis R_lemma)

end


