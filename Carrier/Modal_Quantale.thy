theory Modal_Quantale
  imports KAT
begin

record 'a dom_ord = "'a test_ord" +
  dom :: "'a \<Rightarrow> 'a" ("\<delta>\<index>_" [1000] 100)

locale modal_quantale = fixes A (structure)
  assumes mkat: "kat A"
  and dom_type: "dom A \<in> carrier A \<rightarrow> tests A"
  and dom1: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> \<delta>(x)\<cdot>x"
  and dom2: "\<lbrakk>x \<in> carrier A; p \<in> tests A\<rbrakk> \<Longrightarrow> \<delta>(p\<cdot>x) \<sqsubseteq> p"

sublocale modal_quantale \<subseteq> kat by (metis mkat)

context modal_quantale
begin


  abbreviation qtop :: "'a" ("\<top>") where
    "\<top> \<equiv> complete_meet_semilattice.top A"

  lemma dom_closed: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> \<delta>(x) \<in> tests A"
    by (metis (lifting) dom_type typed_application)

  lemma dom_under_one: "x \<in> carrier A \<Longrightarrow> \<delta>(x) \<sqsubseteq> 1"
    by (metis dom_closed test_under_one)

  lemma dom_strictness: assumes xc: "x \<in> carrier A" shows "\<delta>(x) = 0 \<longleftrightarrow> x = 0"
    apply default
    apply (metis assms bot_closed bot_zerol dom1 less_def less_le_trans prop_bot)
    by (metis bot_onel bot_zerol bounded_lattice.bot_closed dom2 dom_closed in_mono join_comm leq_def_right test_bl test_subset test_zero)

  lemma dom_llp:
    assumes xc: "x \<in> carrier A" and pc: "p \<in> tests A"
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
    assumes xc: "x \<in> carrier A" and pc: "p \<in> tests A"
    shows "x \<sqsubseteq> p\<cdot>\<top> \<longleftrightarrow> x \<sqsubseteq> p\<cdot>x"
  proof
    assume asm: "x \<sqsubseteq> p\<cdot>\<top>"
    hence "x = x \<sqinter> p\<cdot>\<top>"
      by (metis leq_meet_def mult_closed pc test_subset_var top_closed xc)
    then obtain y where yc: "y \<in> carrier A" and "... = x \<sqinter> (x + y)"
      by (metis absorb2 xc)
    hence "... = (x \<sqinter> p\<cdot>x) + (x \<sqinter> p\<cdot>y)"
      sorry
    hence "... \<sqsubseteq> (x \<sqinter> p\<cdot>x) + (x \<sqinter> 1\<cdot>y)"
      sorry
    hence
      
      
    

  lemma dom_conn_prop:
    assumes xc: "x \<in> carrier A" and pc: "p \<in> tests A"
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
    assumes xc: "x \<in> carrier A"
    shows "x \<sqsubseteq> \<delta>(x)\<cdot>\<top>"
  proof -
    have "x\<cdot>\<top> \<sqsubseteq> \<delta>(x\<cdot>\<top>)\<cdot>(x\<cdot>\<top>)"
      by (metis assms dom1 mult_closed top_closed)
    hence "x \<sqsubseteq> \<delta>(x\<cdot>\<top>)\<cdot>(x\<cdot>\<top>) \<leftharpoondown> \<top>"
      apply (insert postimp_conn_prop[of x "\<top>" "\<delta>(x\<cdot>\<top>)\<cdot>(x\<cdot>\<top>)"])
      
      
      

  lemma
    assumes xc: "x \<in> carrier A" and pc: "p \<in> tests A"
    shows "\<delta>(x) \<sqsubseteq> p \<longleftrightarrow> x \<sqsubseteq> p\<cdot>(complete_meet_semilattice.top A)"
    nitpick
    apply default
    
    
    

  lemma dom_lower_adjoint: "lower_adjoint A A (\<lambda>x. \<delta>(x))"
    

  lemma dom_join_preserving:
    assumes X_subset: "X \<subseteq> carrier A"
    shows "\<delta>(\<Sigma> X) = \<Sigma> ((\<lambda>x. \<delta>(x)) ` X)"
  proof -

  lemma dom_additivity:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
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

locale concurrent_ka = fixes A (structure)
  assumes con_quantale: "unital_quantale \<lparr>carrier = carrier A, le = op \<sqsubseteq>, one = one A, mult = op \<bar>\<rparr>"
  and seq_quantale: "unital_quantale \<lparr>carrier = carrier A, le = op \<sqsubseteq>, one = one A, mult = op \<cdot>\<rparr>"
  and exchange: "\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A; d \<in> carrier A\<rbrakk> \<Longrightarrow> (a \<bar> b ) \<cdot> (c \<bar> d) \<sqsubseteq> (b \<cdot> c) \<bar> (a \<cdot> d)"

begin

  definition CON :: "'a mult_ord" where
    "CON \<equiv> \<lparr>carrier = carrier A, le = op \<sqsubseteq>, one = one A, mult = op \<bar>\<rparr>"

  lemma con_quantale_var: "unital_quantale CON"
    by (insert con_quantale, simp add: CON_def)

  lemma con_cl: "complete_lattice CON"
    by (metis con_quantale unital_quantale.quantale_complete_lattice CON_def)

  lemma con_ord: "order CON"
    by (metis cl_to_order con_cl)

  lemma con_carrier: "carrier A = carrier CON"
    by (simp add: CON_def)

  lemma con_le: "(x \<sqsubseteq> y) = (x \<sqsubseteq>\<^bsub>CON\<^esub> y)"
    by (simp add: CON_def)

  definition SEA :: "'a mult_ord" where
    "SEA \<equiv> \<lparr>carrier = carrier A, le = op \<sqsubseteq>, one = one A, mult = op \<cdot>\<rparr>"

  lemma seq_quantale_var: "unital_quantale SEA"
    by (insert seq_quantale, simp add: SEA_def)

  lemma seq_cl: "complete_lattice SEA"
    by (metis seq_quantale unital_quantale.quantale_complete_lattice SEA_def)

  lemma seq_ord: "order SEA"
    by (metis cl_to_order seq_cl)

  lemma seq_con_ord_eq: "order SEA = order CON"
    by (metis cl_to_order con_cl seq_ord)

  lemma seq_con_cl_eq: "complete_lattice SEA = complete_lattice CON"
    by (metis con_cl seq_cl)

  lemma seq_carrier: "carrier A = carrier SEA"
    by (simp add: SEA_def)

  lemma seq_le: "(x \<sqsubseteq> y) = (x \<sqsubseteq>\<^bsub>SEA\<^esub> y)"
    by (simp add: SEA_def)

  lemma cka_ord: "order A"
    apply default
    apply (simp_all only: seq_carrier seq_le)
    apply (metis order.eq_refl seq_ord)
    apply (metis order.order_trans seq_ord)
    by (metis order.order_antisym seq_ord)

  lemma cka_ord_is_seq: "order A = order SEA"
    by (metis cka_ord seq_ord)

  lemma cka_ord_is_con: "order A = order CON"
    by (metis cka_ord seq_con_ord_eq seq_ord)

  lemma cka_lub_is_seq_lub: "order.is_lub A x X = order.is_lub SEA x X"
    apply (insert seq_ord cka_ord)
    apply (simp add: order.is_lub_simp)
    by (simp add: seq_carrier seq_le)

  lemma cka_glb_is_seq_glb: "order.is_glb A x X = order.is_glb SEA x X"
    apply (insert seq_ord cka_ord)
    apply (simp add: order.is_glb_simp)
    by (simp add: seq_carrier seq_le)

  lemma cka_lub_to_seq: "\<Sigma>\<^bsub>A\<^esub>X = \<Sigma>\<^bsub>SEA\<^esub>X"
    apply (insert seq_ord cka_ord)
    by (simp add: order.lub_def cka_lub_is_seq_lub)

  lemma cka_cl: "complete_lattice A"
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

  lemma cka_one_is_seq_one: "one A = one SEA"
    by (simp add: SEA_def)

  lemma cka_one_is_con_one: "one A = one CON"
    by (simp add: CON_def)

  lemma cka_cl_is_seq_cl: "complete_lattice A = complete_lattice SEA"
    by (metis cka_cl seq_cl)

  lemma default_quantale: "unital_quantale A"
    apply (insert seq_quantale_var)
    apply (unfold unital_quantale_def)
    apply safe
    apply (metis cka_cl)
    apply (simp_all add: seq_carrier seq_le cka_lub_to_seq cka_one_is_seq_one)
    by (simp add: SEA_def)+

end

sublocale concurrent_ka \<subseteq> unital_quantale
  by (metis default_quantale)

context concurrent_ka
begin

  lemma con_mult: "op \<bar> = op \<cdot>\<^bsub>CON\<^esub>"
    by (simp add: CON_def)

  lemma con_type: "op \<bar> \<in> carrier A \<rightarrow> carrier A \<rightarrow> carrier A"
    apply (simp add: con_carrier con_mult)
    by (metis con_quantale_var unital_quantale.mult_type)

  lemma con_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<bar>y \<in> carrier A"
    by (metis con_type typed_application)

  lemma con_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<bar> y) \<bar> z = x \<bar> (y \<bar> z)"
    apply (simp add: con_carrier con_mult)
    by (metis con_quantale_var unital_quantale.mult_assoc)

  lemma con_oner [simp]: "x \<in> carrier A \<Longrightarrow> x \<bar> 1 = x"
    apply (simp add: con_mult con_carrier cka_one_is_con_one)
    by (metis con_quantale_var unital_quantale.mult_oner)

  lemma con_commutative:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
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

  lemma con_onel [simp]: "x \<in> carrier A \<Longrightarrow> 1 \<bar> x = x"
    by (metis con_commutative con_oner one_closed)

  lemma exchange_var:
    "\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A; d \<in> carrier A\<rbrakk> \<Longrightarrow> (a \<bar> b ) \<cdot> (c \<bar> d) \<sqsubseteq> (a \<cdot> c) \<bar> (b \<cdot> d)"
    by (metis (lifting) con_commutative exchange)

  lemma seq_le_con:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A"
    shows "x\<cdot>y \<sqsubseteq> x\<bar>y"
    by (metis con_onel con_oner exchange_var mult_onel mult_oner one_closed xc yc)

  lemma con_seq_slide1:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "(x \<bar> y) \<cdot> z \<sqsubseteq> x \<bar> (y \<cdot> z)"
    sorry

  lemma con_seq_slide2:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "x \<cdot> (y \<bar> z) \<sqsubseteq> (x \<cdot> y) \<bar> z"
    sorry

  abbreviation conimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<mapsto>" 60) where
    "x \<mapsto> y \<equiv> unital_quantale.preimp CON x y"

  abbreviation constar :: "'a \<Rightarrow> 'a"  ("_\<^sup>\<triangle>" [101] 100) where
    "x\<^sup>\<triangle> \<equiv> unital_quantale.star CON x"

  lemma con_plus: "x + y = order.join CON x y"
    apply (simp add: order.join_def[OF con_ord, of x y] order.lub_simp[OF con_ord, of "{x,y}"])
    by (simp add: CON_def join_def lub_simp)

  lemma constar_unfold: assumes xc: "x \<in> carrier A " shows "1 + x\<bar>x\<^sup>\<triangle> = x\<^sup>\<triangle>"
    apply (simp add: con_mult cka_one_is_con_one con_plus)
    by (metis (lifting) assms con_carrier con_quantale_var unital_quantale.star_unfoldl)

  lemma constar_induct:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "z+x\<bar>y \<sqsubseteq> y \<longrightarrow> x\<^sup>\<triangle>\<bar>z \<sqsubseteq> y"
    apply (simp add: con_mult con_plus con_le)
    apply (insert unital_quantale.star_inductl[of CON x y z, OF con_quantale_var])
    apply (simp add: con_carrier[symmetric])
    by (metis xc yc zc)

end

record 'a invar_ord = "'a con_ord" +
  iota :: "'a \<Rightarrow> 'a" ("\<iota>\<index>_" [1000] 100)

locale cka_with_invariants = fixes A (structure)
  assumes cka: "concurrent_ka A"
  and invar_unit: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> \<iota> x"
  and invar_iso: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> \<iota> x \<sqsubseteq> \<iota> y"
  and invar_idem: "x \<in> carrier A \<Longrightarrow> \<iota> x \<sqsubseteq> \<iota> (\<iota> x)"
  and invar_i1: "x \<in> carrier A \<Longrightarrow> 1 \<sqsubseteq> \<iota> x"
  and invar_i2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> \<iota> (x \<bar> y) \<sqsubseteq> \<iota> (x + y)"

sublocale cka_with_invariants \<subseteq> concurrent_ka by (metis cka)

context cka_with_invariants
begin

  definition invariant :: "'a \<Rightarrow> bool" where
    "invariant s \<equiv> s \<in> carrier A \<and> \<iota> s = s"

  lemma invariant_closed: "invariant s \<Longrightarrow> s \<in> carrier A"
    by (metis invariant_def)

  lemma invariant_fix: "invariant s \<Longrightarrow> \<iota> s = s"
    by (metis invariant_def)

  

end
