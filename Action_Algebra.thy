theory Action_Algebra
  imports Dioid My_Kleene_Algebra GaloisConnection
begin

declare [[ smt_solver = remote_z3 ]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

class action_algebra = dioid_one_zero + star_op + postimp_op + preimp_op +
  assumes act1L: "(x \<le> z \<leftarrow> y) \<longleftrightarrow> (x\<cdot>y \<le> z)"
  and act1R: "(x\<cdot>y \<le> z) \<longleftrightarrow> y \<le> x \<rightarrow> z"
  and act2: "1 + x\<^sup>\<star>\<cdot>x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
  and act3: "(1 + y\<cdot>y + x \<le> y) \<longrightarrow> (x\<^sup>\<star> \<le> y)"

begin
  definition (in action_algebra) top :: "'a" where "top \<equiv> 0 \<leftarrow> 0"

  lemma conn: "galois_connection (\<lambda>y. x\<cdot>y) (\<lambda>z. x \<rightarrow> z)"
  proof (unfold_locales, intro allI)
    fix x y
    show "(x\<cdot>y \<le> z) \<longleftrightarrow> y \<le> x \<rightarrow> z"

  lemma top_annil: "x \<rightarrow> top = top" by (metis act1L act1R antisym min_zero top_def)
  lemma top2: "0 \<rightarrow> x = top" by (metis act1L act1R antisym min_zero top_def)

  lemma galois_unitR: "y \<le> x \<rightarrow> x\<cdot>y" by (metis act1R le_less)
  lemma galois_counitR: "x \<cdot> (x \<rightarrow> y) \<le> y" by (metis act1R le_less)

  lemma eq_ax1: "x \<rightarrow> y \<le> x \<rightarrow> (y + y')" by (metis act1R add_ub galois_counitR order_trans)

  lemma galois_unitL: "x \<le> x\<cdot>y \<leftarrow> y" by (metis act1L le_less)
  lemma galois_counitL: "(y \<leftarrow> x) \<cdot> x \<le> y" by (metis act1L le_less)

  lemma eq_ax1': "x \<leftarrow> y \<le> (x + x') \<leftarrow> y" by (metis act1L add_ub galois_counitL order_trans)

  lemma postimp_trans: "(x \<rightarrow> y) \<cdot> (y \<rightarrow> z) \<le> x \<rightarrow> z"
    by (smt act1L act1R galois_counitR mult_assoc order_trans)

  lemma preimp_trans: "(x \<leftarrow> y) \<cdot> (y \<leftarrow> z) \<le> x \<leftarrow> z"
    by (smt act1L act1R galois_counitL mult_assoc order_trans)

  lemma postimp_refl: "1 \<le> x \<rightarrow> x" by (metis act1R mult_oner order_refl)
  lemma preimp_refl: "1 \<le> x \<leftarrow> x" by (metis galois_unitL mult_onel)

  lemma postimp_pure_induction: "(x \<rightarrow> x)\<^sup>\<star> \<le> (x \<rightarrow> x)"
    by (metis act3 add_lub eq_refl postimp_refl postimp_trans)

  lemma postimp_pure_induction_uncurried: "x\<cdot>(x \<rightarrow> x)\<^sup>\<star> \<le> x"
    by (metis act1R postimp_pure_induction)

  lemma preimp_pure_induction: "(x \<leftarrow> x)\<^sup>\<star> \<le> (x \<leftarrow> x)"
    by (metis act3 add_lub eq_refl preimp_refl preimp_trans)

  lemma star_refl: "1 \<le> x\<^sup>\<star>" by (metis act2 add_lub)
  lemma star3: "x \<le> x\<^sup>\<star>" by (metis act2 add_lub)

  lemma star_mon: "(x \<le> y) \<longrightarrow> (x\<^sup>\<star> \<le> y\<^sup>\<star>)" by (metis act2 act3 add_lub order_trans star3)

  lemma star_left_preserves: "(x\<cdot>y \<le> y) \<longrightarrow> (x\<^sup>\<star>\<cdot>y \<le> y)"
    by (metis act1L order_trans preimp_pure_induction star_mon)

  lemma star_right_preserves: "(y\<cdot>x \<le> y) \<longrightarrow> (y\<cdot>x\<^sup>\<star> \<le> y)"
    by (metis act1R order_trans postimp_pure_induction star_mon)
end

sublocale action_algebra \<subseteq> kleene_algebra
proof
  fix x y z :: 'a
  show "x + x = x" by (metis idem)
  show "1 + x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (smt act2 add_lub order_prop subdistr)
  show "z + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
    by (metis add_lub leq_def star_left_preserves subdistl)
  show "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
    by (metis add_lub mult_isor order_trans star_right_preserves)
qed

class equational_action_algebra = dioid_one_zero + star_op + postimp_op + preimp_op +
  assumes eq1: "x \<rightarrow> y \<le> x \<rightarrow> (y + y')"
  and eq2L: "x\<cdot>(x \<rightarrow> y) \<le> y"
  and eq2R: "y \<le> x \<rightarrow> x\<cdot>y"
  and eq3: "y \<leftarrow> x \<le> (y + y') \<leftarrow> x"
  and eq4L: "(y \<leftarrow> x)\<cdot>x \<le> y"
  and eq4R: "y \<le> y\<cdot>x \<leftarrow> x"
  and eq5: "1 + x\<^sup>\<star>\<cdot>x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
  and eq6: "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  and eq7: "(x \<rightarrow> x)\<^sup>\<star> \<le> x \<rightarrow> x"

sublocale action_algebra \<subseteq> equational_action_algebra
proof
  fix x y y' :: 'a
  show "x \<rightarrow> y \<le> x \<rightarrow> (y + y')"
    by (metis act1R add_ub galois_counitR order_trans)
  show "x \<cdot> (x \<rightarrow> y) \<le> y"
    by (metis galois_counitR)
  show "y \<le> x \<rightarrow> x \<cdot> y"
    by (metis galois_unitR)
  show "y \<leftarrow> x \<le> y + y' \<leftarrow> x"
    by (metis act1L add_ub galois_counitL order_trans)
  show "(y \<leftarrow> x) \<cdot> x \<le> y"
    by (metis galois_counitL)
  show "y \<le> y \<cdot> x \<leftarrow> x"
    by (metis galois_unitL)
  show "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
    by (metis act2)
  show "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (metis star_subdist)
  show "(x \<rightarrow> x)\<^sup>\<star> \<le> x \<rightarrow> x"
    by (metis postimp_pure_induction)
qed

sublocale equational_action_algebra \<subseteq> action_algebra
proof
  fix x y z :: 'a
  show "(x \<le> z \<leftarrow> y) = (x \<cdot> y \<le> z)"
    by (metis eq3 eq4L eq4R leq_def order_trans subdistr)
  show "(x \<cdot> y \<le> z) = (y \<le> x \<rightarrow> z)"
    by (metis eq1 eq2L eq2R order_prop order_trans subdistl)
  show "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
    by (metis eq5)
  show "1 + y \<cdot> y + x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis add_lub eq2L eq2R eq6 eq7 eq_iff leq_def mult_onel subdistl subdistr)
qed

sublocale equational_action_algebra \<subseteq> kleene_algebra
apply intro_locales
done

end
