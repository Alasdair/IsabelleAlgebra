theory Dioid_Carrier
  imports "~~/src/HOL/Algebra/Lattice"
begin

declare [[ smt_solver = remote_z3 ]]

record 'a dioid = "'a gorder" +
  plus :: "['a , 'a]  \<Rightarrow> 'a" (infixl "\<oplus>\<index>" 70)
  mult :: "['a , 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 80)
  one  :: "'a" ("\<one>\<index>")
  zero :: "'a" ("\<zero>\<index>")

locale dioid = weak_partial_order D for D (structure) +
  assumes leq_def: "\<lbrakk> x \<in> carrier D; y \<in> carrier D \<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y \<longleftrightarrow> x\<oplus>y=y)"
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
end
