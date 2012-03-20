(*<*)
theory StarContinuousKA
  imports Dioid

(**************************************************************************)

begin

context dioid_one_zero
begin

text {* Powers are needed in the definition of star-continuity. *}

primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<^bsup>_\<^esup>" [101,50] 100)
  where "x\<^bsup>0\<^esup>  = 1"
  | "x\<^bsup>Suc n\<^esup> = x\<cdot>x\<^bsup>n\<^esup>"

lemma power_add: "x\<^bsup>m\<^esup>\<cdot>x\<^bsup>n\<^esup> = x\<^bsup>m+n\<^esup>"
proof (induct m)
  case 0 show ?case by (metis add_0_left mult_onel power.simps(1))
  case (Suc m) show ?case by (smt Suc add_Suc mult_assoc power.simps(2))
qed

lemma power_commutes: "x\<^bsup>n\<^esup>\<cdot>x = x\<cdot>x\<^bsup>n\<^esup>"
  by (smt power_add mult_oner power.simps)

lemma power_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> (power x n)\<cdot>y \<le> y"
  by (induct n,  metis eq_refl mult_onel power.simps(1), smt add_assoc distl leq_def mult_assoc order_prop power.simps(2) power_commutes)

lemma power_inductr_var: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>(power x n) \<le> y"
  by (induct n, metis mult_oner power.simps(1) order_refl, smt add_assoc distr leq_def mult_assoc order_prop power.simps(2)) --"5"

text {* I define suprema over arbitrary sets in a given poset; but
don't assume they always exist. *}

definition is_sup :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_sup x A \<longleftrightarrow> (\<forall>z. (x \<le> z \<longleftrightarrow> (\<forall>y\<in>A. y \<le> z)))"

lemma is_sup_unique: "is_sup x A \<longrightarrow> is_sup y A \<longrightarrow> x = y"
  by (metis eq_iff is_sup_def)

lemma sup_plus: "is_sup (x+y) {x,y}"
  by (simp add: is_sup_def add_lub)

lemma sup_un: "is_sup w A \<longrightarrow> is_sup (x+w) ({x}\<union>A)"
  by (simp add: is_sup_def add_lub)


text {* These sets of powers are needed in the definition of
star-continuity. *}

definition powers_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "powers_c x y z = {x\<cdot>w\<cdot>z| w. (\<exists>i. w = power y i)}"

definition powers :: "'a \<Rightarrow> 'a set" where
  "powers x  = {y. (\<exists>i. y = power x i)}"

lemma powers_c_elim: "v\<in>(powers_c x y z) \<longleftrightarrow> (\<exists>w. v = x\<cdot>w\<cdot>z \<and> (\<exists>i. w = power y i))"
  by (simp add: powers_c_def)

lemma powers_to_powers_c: "powers x = powers_c 1 x 1"
  by auto (simp add: powers_c_elim mult_onel mult_oner, smt Collect_def mem_def powers_def)+

lemma power_in_powers_c: "\<forall>i. x\<cdot>(power y i)\<cdot>z \<in> powers_c x y z"
  by (metis powers_c_elim)

lemma powers_sucl: "powers_c x x 1 = {y. (\<exists>i. y = power x (Suc i))}"
  by  auto (metis mult_oner powers_c_elim, metis mult_oner power_in_powers_c)

lemma powers_sucr: "powers_c 1 x x = {y. (\<exists>i. y = power x (Suc i))}"
  by auto (metis mult_onel power_commutes powers_c_elim, metis mult_onel power_commutes power_in_powers_c)

lemma powers_suc: "powers_c x x 1 = powers_c 1 x x"
  by (metis powers_sucl powers_sucr)

text {* The following lemmas prepare the derivation of the star unfold
rules. *}

lemma powers_unfoldl: "{1}\<union>(powers_c x x 1) = powers x"
proof -
  have  "{1}\<union>(powers_c x x 1) = {y. y = power x 0 \<or> (\<exists>i. y = power x (Suc i))}"
    by (metis insert_def insert_is_Un power.simps(1) powers_sucl Collect_disj_eq)
  also have "... = {y. (\<exists>i. y = power x i)}"
    by auto (smt power.simps(1), metis power.simps(2), metis (full_types) nat.exhaust power.simps(1) power.simps(2))
  ultimately show ?thesis
    by (metis powers_def)
qed

end

text {* Star-continuous Kleene algebras can now be defined. Suprema
are only assumed to exist for these special sets of powers. The
definition via definite descriptions is somewhat awkward in proofs,
but there seems no better way...

*}

class star_continuous_ka = dioid_one_zero +
  fixes star :: "'a \<Rightarrow> 'a"
  assumes ex_star: "\<forall>x y z. \<exists>w. is_sup w (powers_c x y z)"
  and star_def:"x\<cdot>(star y)\<cdot>z = (THE w. is_sup w (powers_c x y z))"

begin

lemma prod_star_unique: "is_sup w (powers_c x y z) \<Longrightarrow> x\<cdot>(star y)\<cdot>z = w"
  by (metis star_def is_sup_unique the_equality)

lemma star_unique: "is_sup w (powers x) \<Longrightarrow> star x = w"
  by (metis mult_onel mult_oner powers_to_powers_c prod_star_unique)

lemma prod_star_is_sup: "is_sup (x\<cdot>(star y)\<cdot>z) (powers_c x y z)"
  by (metis ex_star prod_star_unique)

lemma star_lub: "(\<forall>v\<in>(powers_c x y z). v \<le> w) \<longleftrightarrow> x\<cdot>(star y)\<cdot>z \<le> w"
  by (metis (full_types) is_sup_def prod_star_is_sup)

lemma cstar_unfoldl: "1+x\<cdot>(star x) = star x"
proof -
  have "is_sup (1+x\<cdot>(star x)) (powers x)"
    by (metis ex_star mult_oner prod_star_unique sup_un powers_unfoldl)
  thus ?thesis
    by (metis star_unique)
qed

lemma cstar_unfoldr: "1+(star x)\<cdot>x = star x"
  by (metis mult_onel mult_oner powers_suc prod_star_is_sup prod_star_unique cstar_unfoldl)

lemma cstar_inductl: "x\<cdot>y \<le> y \<longrightarrow> (star x)\<cdot>y \<le> y"
  by (metis power_inductl_var mult_onel powers_c_elim star_lub)

lemma cstar_inductr: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>(star x) \<le> y"
  by (metis power_inductr_var mult_oner powers_c_elim star_lub)

end

text {* Finally I define "normal" Kleene algebras and show that every
star-continuous Kleene algebra is a Kleene algebra. *}

class kleene_algebra = dioid_one_zero + star_op +
  assumes star_unfoldl': "1+x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
  assumes star_unfoldr': "1+x\<^sup>\<star>\<cdot>x \<le> x\<^sup>\<star>"
  assumes star_inductl: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>\<star>\<cdot>y \<le> y"
  assumes star_inductr: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>x\<^sup>\<star> \<le> y"

sublocale star_continuous_ka \<subseteq> kleene_algebra
  by (unfold_locales) (metis eq_refl cstar_unfoldl, metis order_refl cstar_unfoldr,  metis cstar_inductl, metis cstar_inductr)

end

