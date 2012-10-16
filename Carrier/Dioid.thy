theory Dioid
  imports Lattice
begin

record 'a dioid = "'a partial_object" +
  plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+\<index>" 70)
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<index>" 80)
  one :: "'a" ("1\<index>")
  zero :: "'a" ("0\<index>")

locale dioid = fixes A (structure)
  assumes add_closed: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x + y \<in> carrier A"
  and mult_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> carrier A"
  and one_closed: "(1::'a) \<in> carrier A"
  and zero_closed: "(0::'a) \<in> carrier A"
  and mult_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
  and add_assoc: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
  and add_comm: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x + y = y + x"
  and add_idem: "(x::'a) \<in> carrier A \<Longrightarrow> x + x = x"
  and distl: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x\<cdot>(y + z) = x\<cdot>y + x\<cdot>z"
  and distr: "\<lbrakk>(x::'a) \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x + y)\<cdot>z = x\<cdot>z + y\<cdot>z"
  and mult_onel: "(x::'a) \<in> carrier A \<Longrightarrow> 1\<cdot>x = x"
  and mult_oner: "(x::'a) \<in> carrier A \<Longrightarrow> x\<cdot>1 = x"
  and add_zerol: "(x::'a) \<in> carrier A \<Longrightarrow> 0 + x = x"
  and mult_zerol: "(x::'a) \<in> carrier A \<Longrightarrow> 0\<cdot>x = 0"
  and mult_zeror: "(x::'a) \<in> carrier A \<Longrightarrow> x\<cdot>0 = 0"

begin

  definition nat_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
    "x \<sqsubseteq> y \<equiv> x + y = y"

  abbreviation natural :: "'a ord" where
    "natural \<equiv> \<lparr>carrier = carrier A, le = nat_order\<rparr>"

  lemma natural: "order natural"
    by (default, auto simp add: nat_order_def, (metis add_idem add_assoc add_comm)+)

end

sublocale dioid \<subseteq> order "\<lparr>carrier = carrier A, le = nat_order\<rparr>" using natural .

sublocale dioid \<subseteq> join_semilattice "\<lparr>carrier = carrier A, le = nat_order\<rparr>"
  apply (default, auto simp add: order.is_lub_simp[OF natural])
  by (smt add_assoc add_closed add_comm add_idem nat_order_def)

context dioid
begin

  lemma add_zeror: "x \<in> carrier A \<Longrightarrow> x + 0 = x"
    by (metis add_comm add_zerol zero_closed)

  lemma add_lub: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z  \<longleftrightarrow> x + y \<sqsubseteq> z"
    by (metis add_assoc add_closed add_comm add_idem nat_order_def)

  lemma add_iso: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> z + x \<sqsubseteq> z + y"
    by (metis add_assoc add_closed add_comm add_idem nat_order_def)

  lemma mult_isol: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> z\<cdot>x \<sqsubseteq> z\<cdot>y"
    by (metis distl nat_order_def)

  lemma mult_isor: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longrightarrow> x\<cdot>z \<sqsubseteq> y\<cdot>z"
    by (metis distr nat_order_def)

  lemma mult_double_iso: "\<lbrakk>w \<in> carrier A; x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> w \<sqsubseteq> x \<and> y \<sqsubseteq> z \<longrightarrow> w\<cdot>y \<sqsubseteq> x\<cdot>z"
    by (smt add_assoc distl distr add_idem nat_order_def mult_closed)

  lemma subdistl: "\<lbrakk>x \<in>  carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z\<cdot>x \<sqsubseteq> z\<cdot>(x + y)"
    by (metis add_assoc add_closed add_idem nat_order_def mult_double_iso)

  lemma zero_min: "x \<in> carrier A \<Longrightarrow> 0 \<sqsubseteq> x"
    by (metis (lifting) add_zerol nat_order_def)

  lemma no_trivial_inverse: "\<forall>x\<in>carrier A.(x \<noteq> 0 \<longrightarrow> \<not>(\<exists>y\<in>carrier A.(x+y = 0)))"
    by (metis add_lub add_zeror nat_order_def zero_min)

  lemmas nat_antisym = order_antisym[simplified]
    and nat_refl = order_refl[simplified]
    and nat_trans = order_trans[simplified]

end

end
