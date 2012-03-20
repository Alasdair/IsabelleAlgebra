theory Domain_Semigroup_Carrier
imports Main
begin

record 'a partial_object =
  carrier :: "'a set"

record 'a semigroup =  "'a partial_object" +
  mult :: "['a, 'a] => 'a" (infixl "\<cdot>\<index>" 70)

locale semigroup =
  fixes G (structure)
  assumes m_closed [intro, simp]:
    "\<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> x\<cdot>y \<in> carrier G"
     and m_assoc:
    "\<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> (x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"

locale dsemigroup = semigroup +
  fixes d
  assumes dclosed [intro, simp]: "x \<in> carrier G \<Longrightarrow> d x \<in> carrier G"
  and d1: "x \<in> carrier G \<Longrightarrow> d(x)\<cdot>x = x"
  and d2: "\<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> d(x\<cdot>d(y)) = d(x\<cdot>y)"
  and d3: "\<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> d(d(x)\<cdot>y) = d(x)\<cdot>d(y)"
  and d4: "\<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> d(x)\<cdot>d(y) = d(y)\<cdot>d(x)"

begin

lemma d_idem: "x \<in> carrier G \<Longrightarrow> d(d(x)) = d(x)"
by (metis d1 d2 d3 dclosed)

lemma d_import_var: "\<lbrakk> x \<in> carrier G ; y \<in> carrier G \<rbrakk> \<Longrightarrow> d(x)\<cdot>d(x\<cdot>y) = d(x\<cdot>y)"
by (metis d1 d3 dclosed m_assoc m_closed)  -- {* proof found by Spass *}
(*
  proof -
    assume G : "x \<in> carrier G" "y \<in> carrier G"
    hence "d(x)\<cdot>d(x\<cdot>y) = d(d(x)\<cdot>(x\<cdot>y))"
      by (metis d3 m_closed)
    with G have "d(x)\<cdot>d(x\<cdot>y) = d(x\<cdot>y)"
      by (metis d1 dclosed m_assoc)
    with G show ?thesis by auto
  qed
*)

fun D :: "'a set \<Rightarrow> 'a set" where
  "D(S) = { d(x) | x . x \<in> S }"

lemma d_fixpoint:
  assumes "x \<in> carrier G"
  shows "x \<in> D(carrier G) \<longleftrightarrow> d(x) = x"
by (simp, metis assms d_idem)

end

end
