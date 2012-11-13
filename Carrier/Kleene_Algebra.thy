theory Kleene_Algebra
  imports Dioid
begin

(* +------------------------------------------------------------------------+ *)
subsection {* Kleene Algebras *}
(* +------------------------------------------------------------------------+ *)

record 'a kleene_algebra = "'a dioid" +
  star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>\<index>" [101] 100)

locale kleene_algebra' =
  fixes A :: "('a, 'b) kleene_algebra_scheme" (structure)
  assumes ka_dioid: "dioid A"

declare kleene_algebra'_def [simp]

sublocale kleene_algebra' \<subseteq> dioid using ka_dioid .

locale kleene_algebra = kleene_algebra' +
  assumes star_closed: "x \<in> carrier A \<Longrightarrow> x\<^sup>\<star> \<in> carrier A"
  and star_unfoldl: "x \<in> carrier A \<Longrightarrow> 1 + x\<cdot>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  and star_unfoldr: "x \<in> carrier A \<Longrightarrow> 1 + x\<^sup>\<star>\<cdot>x \<sqsubseteq> x\<^sup>\<star>"
  and star_inductl: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z + x\<cdot>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<sqsubseteq> y"
  and star_inductr: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z + y\<cdot>x \<sqsubseteq> y \<longrightarrow> z\<cdot>x\<^sup>\<star> \<sqsubseteq> y"

begin

  lemma star_ref: "x \<in> carrier A \<Longrightarrow> 1 \<sqsubseteq> x\<^sup>\<star>"
    by (metis add_lub mult_closed one_closed star_closed star_unfoldl)

  lemma star_plus_one: "x \<in> carrier A \<Longrightarrow> x\<^sup>\<star> = 1 + x\<^sup>\<star>"
    by (metis add_lub nat_order_def star_unfoldl one_closed star_closed mult_closed)

  lemma star_trans: "x \<in> carrier A \<Longrightarrow> x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
    by (metis add_lub mult_closed nat_refl one_closed star_closed star_inductr star_unfoldr)

  lemma star_trans_eq: "x \<in> carrier A \<Longrightarrow> x\<^sup>\<star>\<cdot>x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis mult_closed mult_oner nat_antisym one_closed star_closed star_plus_one star_trans subdistl)

  lemma star_1l: "x \<in> carrier A \<Longrightarrow> x\<cdot>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
    by (metis add_lub mult_closed one_closed star_closed star_unfoldl)

  lemma star_subid: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> 1 \<longrightarrow> x\<^sup>\<star> = 1"
    by (smt add_comm mult_oner nat_order_def nat_refl one_closed star_closed star_inductl star_ref)

  lemma star_one: "1\<^sup>\<star> = 1"
    by (metis nat_refl one_closed star_subid)

  lemma star_inductl_var: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<sqsubseteq> y"
    by (metis add_lub mult_closed nat_refl star_inductl)

  lemma star_invol: "x \<in> carrier A \<Longrightarrow> x\<^sup>\<star> = (x\<^sup>\<star>)\<^sup>\<star>"
    apply (rule nat_antisym)
    apply (smt mult_closed mult_oner nat_trans one_closed star_1l star_closed star_plus_one subdistl)
    apply (smt mult_oner one_closed star_closed star_inductl star_plus_one star_trans star_trans_eq)
    apply (metis star_closed)+
    done

  lemma star_inductl_eq:  "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z+x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<sqsubseteq> y"
    by (metis nat_refl star_inductl)

  lemma star_inductl_var_eq:  "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>y = y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<sqsubseteq> y"
    by (metis nat_refl star_inductl_var)

end

datatype 'a ka_term = KAAtom 'a
                    | KAPlus "'a ka_term" "'a ka_term"
                    | KAMult "'a ka_term" "'a ka_term"
                    | KAStar "'a ka_term"
                    | KAOne
                    | KAZero

primrec (in kleene_algebra) ka_term_unfold :: "'a ka_term \<Rightarrow> 'a" where
  "ka_term_unfold (KAAtom x) = x"
| "ka_term_unfold (KAPlus x y) = (ka_term_unfold x) + (ka_term_unfold y)"
| "ka_term_unfold (KAMult x y) = (ka_term_unfold x) \<cdot> (ka_term_unfold y)"
| "ka_term_unfold (KAStar x) = (ka_term_unfold x)\<^sup>\<star>"
| "ka_term_unfold KAOne = 1"
| "ka_term_unfold KAZero = 0"

lemma (in kleene_algebra) ka_term_fold_atom:
  "x \<in> carrier A \<Longrightarrow> x = ka_term_unfold (KAAtom x)"
  by (rule ka_term_unfold.simps(1)[symmetric])

primrec (in kleene_algebra) ka_term_atoms :: "'a ka_term \<Rightarrow> 'a set" where
  "ka_term_atoms (KAAtom x) = {x}"
| "ka_term_atoms (KAPlus x y) = (ka_term_atoms x) \<union> (ka_term_atoms y)"
| "ka_term_atoms (KAMult x y) = (ka_term_atoms x) \<union> (ka_term_atoms y)"
| "ka_term_atoms (KAStar x) = ka_term_atoms x"
| "ka_term_atoms KAOne = {}"
| "ka_term_atoms KAZero = {}"

lemma (in kleene_algebra) ka_term_closure:
  "ka_term_atoms x \<subseteq> carrier A \<Longrightarrow> ka_term_unfold x \<in> carrier A"
  by (induct x, simp_all add: add_closed mult_closed one_closed zero_closed star_closed)

ML {*
val ka_term_fold_tac =
  term_fold_tac @{thm kleene_algebra.ka_term_fold_atom} @{thms kleene_algebra.ka_term_unfold.simps[symmetric]} @{thm kleene_algebra.ka_term_closure}
*}

method_setup ka_closure = {*
Scan.succeed (fn ctxt =>
  let
    val witnesses = Locale.get_witnesses ctxt
    val unfolds = witnesses RL @{thms kleene_algebra.ka_term_atoms.simps}
  in
    METHOD (fn _ =>
      ka_term_fold_tac true ctxt 1
      THEN asm_full_simp_tac (@{simpset} addsimps unfolds) 1)
  end)
*}

context kleene_algebra
begin

  lemma star_subdist:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "x\<^sup>\<star> \<sqsubseteq> (x+y)\<^sup>\<star>"
  proof -
    have "x\<^sup>\<star>\<cdot>1 \<sqsubseteq> (x+y)\<^sup>\<star>"
    proof (rule star_inductl[rule_format], insert xc yc, ka_closure+)
      have "1 + x\<cdot>(x+y)\<^sup>\<star> \<sqsubseteq> 1 + (x+y)\<cdot>(x+y)\<^sup>\<star>"
      proof (rule add_iso[rule_format, OF _ _ one_closed], insert xc yc, ka_closure+)
        show "x\<cdot>(x+y)\<^sup>\<star> \<sqsubseteq> (x+y)\<cdot>(x+y)\<^sup>\<star>"
          by (metis add_closed add_lub mult_isor nat_refl star_closed xc yc)
      qed
      moreover have "... \<sqsubseteq> (x+y)\<^sup>\<star>"
        by (metis add_closed star_unfoldl xc yc)
      ultimately show "1 + x\<cdot>(x+y)\<^sup>\<star> \<sqsubseteq> (x+y)\<^sup>\<star>"
        by (rule nat_trans, insert xc yc, ka_closure+)
    qed
    thus ?thesis
      by (metis mult_oner star_closed xc)
  qed

  lemma star_iso: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> x\<^sup>\<star> \<sqsubseteq> y\<^sup>\<star>"
    by (metis nat_order_def star_subdist)

  lemma star_ext: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> x\<^sup>\<star>"
    by (smt mult_closed mult_oner nat_trans one_closed star_1l star_closed star_plus_one subdistl)

  lemma add_lub_r1:
    "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A; x \<sqsubseteq> z; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x + y \<sqsubseteq> z"
    by (metis add_lub)

  lemma star_sim1:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "x\<cdot>z \<sqsubseteq> z\<cdot>y \<longrightarrow> x\<^sup>\<star>\<cdot>z \<sqsubseteq> z\<cdot>y\<^sup>\<star>"
  proof
    assume asm: "x\<cdot>z \<sqsubseteq> z\<cdot>y"
    show "x\<^sup>\<star> \<cdot> z \<sqsubseteq> z \<cdot> y\<^sup>\<star>"
    proof (rule star_inductl[rule_format], insert xc yc zc, ka_closure+)
      show "z + x \<cdot> (z \<cdot> y\<^sup>\<star>) \<sqsubseteq> z \<cdot> y\<^sup>\<star>"
      proof (rule add_lub_r1, insert xc yc zc, ka_closure+)
        show "z \<sqsubseteq> z\<cdot>y\<^sup>\<star>"
          by (smt mult_double_iso mult_oner nat_refl one_closed star_closed star_ref yc zc)
        have "x\<cdot>(z\<cdot>y\<^sup>\<star>) = x\<cdot>z\<cdot>y\<^sup>\<star>"
          by (metis mult_assoc star_closed xc yc zc)
        moreover have "... \<sqsubseteq> z\<cdot>y\<cdot>y\<^sup>\<star>"
          by (metis asm mult_closed mult_isor star_closed xc yc zc)
        moreover have "... \<sqsubseteq> z\<cdot>(y\<cdot>y\<^sup>\<star>)"
          by (metis mult_assoc mult_closed nat_refl star_closed yc zc)
        moreover have "... \<sqsubseteq> z\<cdot>y\<^sup>\<star>"
          by (metis mult_closed mult_isol star_1l star_closed yc zc)
        ultimately show "x\<cdot>(z\<cdot>y\<^sup>\<star>) \<sqsubseteq> z\<cdot>y\<^sup>\<star>"
          by (smt mult_closed nat_trans star_closed xc yc zc)
      qed
    qed
  qed

  lemma star_slide1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (x\<cdot>y)\<^sup>\<star>\<cdot>x \<sqsubseteq> x\<cdot>(y\<cdot>x)\<^sup>\<star>"
    by (metis mult_assoc mult_closed nat_refl star_sim1)

  lemma star_slide_var1: "x \<in> carrier A \<Longrightarrow> x\<^sup>\<star>\<cdot>x \<sqsubseteq> x\<cdot>x\<^sup>\<star>"
    by (frule star_slide1[OF _ one_closed], metis mult_onel mult_oner)

  lemma star2: assumes xc: "x \<in> carrier A" shows "(1+x)\<^sup>\<star> = x\<^sup>\<star>"
  proof -
    have "x\<^sup>\<star> \<sqsubseteq> (1+x)\<^sup>\<star>"
      by (metis add_comm assms one_closed star_subdist)
    moreover have "(1+x)\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
      by (metis add_closed add_lub assms mult_oner one_closed star_closed star_ext star_invol star_iso star_ref)
    ultimately show ?thesis
      by (metis add_closed assms nat_antisym one_closed star_closed)
  qed

  lemma star_unfoldl_eq: assumes xc: "x \<in> carrier A" shows "x\<^sup>\<star> = 1+x\<cdot>x\<^sup>\<star>"
  proof -
    have "x\<^sup>\<star>\<cdot>1 \<sqsubseteq> 1 + x\<cdot>x\<^sup>\<star>"
    proof (rule star_inductl[rule_format], insert xc, ka_closure+)
      show "1 + x \<cdot> (1 + x \<cdot> x\<^sup>\<star>) \<sqsubseteq> 1 + x \<cdot> x\<^sup>\<star>"
        apply (rule add_iso[rule_format], insert xc, ka_closure+)
        apply (rule mult_isol[rule_format], ka_closure+)
        by (rule star_unfoldl)
    qed
    thus ?thesis
      by (metis xc add_closed mult_closed mult_oner nat_antisym one_closed star_closed star_unfoldl)
  qed

  lemma star_rtc1: "x \<in> carrier A \<Longrightarrow> 1+x+x\<^sup>\<star>\<cdot>x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
    by (metis add_assoc nat_order_def one_closed star_closed star_ext star_plus_one star_trans star_trans_eq)

  lemma star_slide: assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "(x\<cdot>y)\<^sup>\<star>\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>\<star>"
  proof -
    have "x\<cdot>(y\<cdot>x)\<^sup>\<star> \<sqsubseteq> (x\<cdot>y)\<^sup>\<star>\<cdot>x"
      apply (rule star_inductr[rule_format], insert xc yc, ka_closure+)
      apply (rule add_lub_r1, ka_closure+)
      apply (smt mult_closed mult_double_iso mult_onel nat_refl one_closed star_closed star_ref)
      by (metis mult_assoc mult_closed mult_isol mult_isor star_closed star_ext star_trans_eq)
    thus ?thesis
      by (metis mult_closed nat_antisym star_closed star_slide1 xc yc)
  qed

  lemma star_denest_1:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star> \<sqsubseteq> (x + y)\<^sup>\<star>"
    apply (rule star_inductr[rule_format], insert xc yc, ka_closure+)
    apply (rule add_lub_r1, ka_closure+)
    apply (rule star_subdist, ka_closure+)
    apply (rule star_inductl[rule_format], ka_closure+)
    apply (rule add_lub_r1, ka_closure+)
    apply (smt add_closed add_lub mult_double_iso star_closed star_ext star_subdist star_trans_eq)
    by (metis add_closed star_1l)

  lemma star_subdist_var_1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> (x+y)\<^sup>\<star>"
    by (metis add_closed add_lub star_closed star_ext)

  lemma star_subdist_var_2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>y \<sqsubseteq> (x+y)\<^sup>\<star>"
    by (metis add_closed add_comm mult_double_iso star_closed star_subdist_var_1 star_trans_eq)

  lemma star_subdist_var_3: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<cdot>y\<^sup>\<star> \<sqsubseteq> (x+y)\<^sup>\<star>"
    by (metis add_closed add_comm mult_double_iso star_closed star_subdist star_trans_eq)

  lemma star_denest_2:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "(x + y)\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
  proof -
    have "(x + y)\<^sup>\<star>\<cdot>1 \<sqsubseteq> x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star>"
      apply (rule star_inductl[rule_format], insert xc yc, ka_closure+)
      apply (rule add_lub_r1, ka_closure+)
      apply (smt mult_closed mult_double_iso mult_onel one_closed star_closed star_ref)
      apply (subst distr, ka_closure+)
      apply (rule add_lub_r1, ka_closure+)
      apply (metis mult_closed mult_assoc mult_isor star_1l star_closed)
      by (smt mult_assoc mult_closed mult_double_iso mult_onel one_closed star_1l star_closed star_ref)
    thus ?thesis
      by (metis dioid.add_closed ka_dioid mult_oner star_closed xc yc)
  qed

  lemma star_denest: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<^sup>\<star>\<cdot>(y\<cdot>x\<^sup>\<star>)\<^sup>\<star> = (x + y)\<^sup>\<star>"
    by (smt add_closed mult_closed nat_antisym star_closed star_denest_1 star_denest_2)

  lemma kozen_skat_lemma:
    assumes uc: "u \<in> carrier A" and vc: "v \<in> carrier A" and wc: "w \<in> carrier A"
    and z3: "u\<cdot>v = 0" and z2: "u\<cdot>w = 0"
    shows "(u + v)\<^sup>\<star>\<cdot>w = v\<^sup>\<star>\<cdot>w"
  proof -
    have z1: "u\<cdot>v = u\<cdot>w"
      by (metis z3 z2)
    have "u\<^sup>\<star>\<cdot>w \<sqsubseteq> w"
      by (metis star_inductl_var uc wc z2 zero_min)
    moreover have "w \<sqsubseteq> u\<^sup>\<star>\<cdot>w"
      by (smt distr mult_onel nat_order_def one_closed star_closed star_plus_one uc wc)
    ultimately have a: "u\<^sup>\<star>\<cdot>w = w"
      by (smt nat_antisym uc wc star_closed mult_closed zero_closed)

    have "u\<^sup>\<star>\<cdot>v \<sqsubseteq> v"
      by (metis star_inductl_var uc vc z3 zero_min)
    moreover have "v \<sqsubseteq> u\<^sup>\<star>\<cdot>v"
      by (smt distr mult_onel nat_order_def one_closed star_closed star_plus_one uc vc)
    ultimately have b: "u\<^sup>\<star>\<cdot>v = v"
      by (metis mult_closed nat_antisym star_closed uc vc)

    from a and b show ?thesis
      by (smt add_closed mult_assoc mult_closed nat_antisym star_closed star_denest_1 star_denest_2 star_slide uc vc wc)
  qed

  lemma kozen_skat_lemma_dual:
    assumes uc: "u \<in> carrier A" and vc: "v \<in> carrier A" and wc: "w \<in> carrier A"
    and z3: "v\<cdot>u = 0" and z2: "w\<cdot>u = 0"
    shows "w\<cdot>(u + v)\<^sup>\<star> = w\<cdot>v\<^sup>\<star>"
  proof -
    have z1: "v\<cdot>u = w\<cdot>u"
      by (metis z3 z2)
    have "w\<cdot>u\<^sup>\<star> \<sqsubseteq> w"
      by (metis add_zeror nat_refl star_inductr uc wc z2)
    moreover have "w \<sqsubseteq> w\<cdot>u\<^sup>\<star>"
      by (smt distl mult_oner nat_order_def one_closed star_closed star_plus_one uc wc)
    ultimately have a: "w\<cdot>u\<^sup>\<star> = w"
      by (smt nat_antisym uc wc star_closed mult_closed zero_closed)

    have "v\<cdot>u\<^sup>\<star> \<sqsubseteq> v"
      by (metis add_zeror nat_refl star_inductr uc vc z3)
    moreover have "v \<sqsubseteq> v\<cdot>u\<^sup>\<star>"
      by (smt distl mult_oner nat_order_def one_closed star_closed star_plus_one uc vc)
    ultimately have b: "v\<cdot>u\<^sup>\<star> = v"
      by (metis mult_closed nat_antisym star_closed uc vc)

    from a and b show ?thesis
      by (metis mult_assoc star_closed star_denest uc vc wc)
  qed

  lemma star_comm: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>y = y\<cdot>x \<Longrightarrow> x\<cdot>y\<^sup>\<star> = y\<^sup>\<star>\<cdot>x"
    apply (rule nat_antisym[rotated 2], ka_closure+)
    apply (rule star_inductr[rule_format], ka_closure+)
    apply (rule add_lub_r1, ka_closure+)
    apply (metis distr mult_onel nat_order_def one_closed star_closed star_plus_one)
    apply (smt subdistl distr mult_assoc mult_closed nat_order_def star_closed star_ext star_trans_eq)
    apply (rule star_inductl[rule_format], ka_closure+)
    apply (rule add_lub_r1, ka_closure+)
    apply (smt mult_double_iso mult_oner nat_refl one_closed star_closed star_ref)
    by (smt mult_assoc mult_closed mult_double_iso nat_refl star_1l star_closed)

  lemma star_eliml1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = x\<cdot>x \<Longrightarrow> x\<cdot>y = y\<cdot>x \<Longrightarrow> x\<cdot>(x\<cdot>y)\<^sup>\<star> \<sqsubseteq> x\<cdot>y\<^sup>\<star>"
    apply (rule star_inductr[rule_format], ka_closure+)
    apply (rule add_lub_r1, ka_closure+)
    apply (smt mult_double_iso mult_oner nat_refl one_closed star_closed star_ref)
    by (smt mult_assoc mult_closed mult_isol star_1l star_closed star_comm)

  lemma star_eliml2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = x\<cdot>x \<Longrightarrow> x\<cdot>y = y\<cdot>x \<Longrightarrow> x\<cdot>y\<^sup>\<star> \<sqsubseteq> x\<cdot>(x\<cdot>y)\<^sup>\<star>"
    by (metis add_idem mult_assoc mult_closed nat_order_def star_comm star_sim1)

  lemma star_eliml: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = x\<cdot>x \<Longrightarrow> x\<cdot>y = y\<cdot>x \<Longrightarrow> x\<cdot>(x\<cdot>y)\<^sup>\<star> = x\<cdot>y\<^sup>\<star>"
    by (metis (no_types) mult_closed nat_antisym star_closed star_eliml1 star_eliml2)

  lemma star_elimr: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x = x\<cdot>x; x\<cdot>y = y\<cdot>x\<rbrakk> \<Longrightarrow> (y\<cdot>x)\<^sup>\<star>\<cdot>x = y\<^sup>\<star>\<cdot>x"
    by (metis star_comm star_eliml star_slide)

  lemma star_sim2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z\<cdot>x \<sqsubseteq> y\<cdot>z \<Longrightarrow> z\<cdot>x\<^sup>\<star> \<sqsubseteq> y\<^sup>\<star>\<cdot>z"
  proof (rule star_inductr[rule_format], ka_closure+)
    assume xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    and asm: "z\<cdot>x \<sqsubseteq> y\<cdot>z"
    have "y\<^sup>\<star>\<cdot>(z\<cdot>x) \<sqsubseteq> y\<^sup>\<star>\<cdot>y\<cdot>z"
      by (smt asm mult_assoc mult_closed mult_isol star_closed xc yc zc)
    moreover have "... \<sqsubseteq> y\<^sup>\<star>\<cdot>z"
      by (smt mult_closed mult_isor star_1l star_closed star_comm yc zc)
    ultimately have "y\<^sup>\<star>\<cdot>z\<cdot>x \<sqsubseteq> y\<^sup>\<star>\<cdot>z"
      by (metis (no_types) mult_assoc mult_closed nat_trans star_closed xc yc zc)

    moreover have "z \<sqsubseteq> y\<^sup>\<star>\<cdot>z"
      by (smt distr mult_onel nat_order_def one_closed star_closed star_plus_one yc zc)

    ultimately show "z + y\<^sup>\<star>\<cdot>z\<cdot>x \<sqsubseteq> y\<^sup>\<star>\<cdot>z"
      by (metis add_lub_r1 mult_closed star_closed xc yc zc)
  qed

  lemma star_sim: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z\<cdot>x = y\<cdot>z \<Longrightarrow> z\<cdot>x\<^sup>\<star> = y\<^sup>\<star>\<cdot>z"
    apply (rule nat_antisym[rotated 2], ka_closure+)
    apply (rule star_sim2, ka_closure+)
    apply (metis mult_isor nat_refl)
    apply (rule star_sim1[rule_format], ka_closure+)
    by (metis mult_closed nat_refl)

  lemma star_elim:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    and zz: "z = z\<cdot>z" and yz: "y\<cdot>z = z\<cdot>y" and xz: "x\<cdot>z = z"
    shows "y\<^sup>\<star>\<cdot>z = (x\<cdot>y)\<^sup>\<star>\<cdot>z"
  proof -
    have "z\<cdot>y\<^sup>\<star> = (x\<cdot>y)\<^sup>\<star>\<cdot>z"
    proof (rule star_sim, insert xc yc zc, ka_closure+)
      show "z\<cdot>y = x\<cdot>y\<cdot>z"
        by (metis mult_assoc xc xz yc yz zc)
    qed
    thus ?thesis
      by (metis star_comm yc yz zc)
  qed

end

end
