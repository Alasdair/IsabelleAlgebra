theory Concurrent_Kleene_Algebra
  imports Quantale
begin


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

  definition SEQ :: "'a mult_ord" where
    "SEQ \<equiv> \<lparr>carrier = carrier A, le = op \<sqsubseteq>, one = one A, mult = op \<cdot>\<rparr>"

  lemma seq_quantale_var: "unital_quantale SEQ"
    by (insert seq_quantale, simp add: SEQ_def)

  lemma seq_cl: "complete_lattice SEQ"
    by (metis seq_quantale unital_quantale.quantale_complete_lattice SEQ_def)

  lemma seq_ord: "order SEQ"
    by (metis cl_to_order seq_cl)

  lemma seq_con_ord_eq: "order SEQ = order CON"
    by (metis cl_to_order con_cl seq_ord)

  lemma seq_con_cl_eq: "complete_lattice SEQ = complete_lattice CON"
    by (metis con_cl seq_cl)

  lemma seq_carrier: "carrier A = carrier SEQ"
    by (simp add: SEQ_def)

  lemma seq_le: "(x \<sqsubseteq> y) = (x \<sqsubseteq>\<^bsub>SEQ\<^esub> y)"
    by (simp add: SEQ_def)

  lemma cka_ord: "order A"
    apply default
    apply (simp_all only: seq_carrier seq_le)
    apply (metis order.eq_refl seq_ord)
    apply (metis order.order_trans seq_ord)
    by (metis order.order_antisym seq_ord)

  lemma cka_ord_is_seq: "order A = order SEQ"
    by (metis cka_ord seq_ord)

  lemma cka_ord_is_con: "order A = order CON"
    by (metis cka_ord seq_con_ord_eq seq_ord)

  lemma cka_lub_is_seq_lub: "order.is_lub A x X = order.is_lub SEQ x X"
    apply (insert seq_ord cka_ord)
    apply (simp add: order.is_lub_simp)
    by (simp add: seq_carrier seq_le)

  lemma cka_glb_is_seq_glb: "order.is_glb A x X = order.is_glb SEQ x X"
    apply (insert seq_ord cka_ord)
    apply (simp add: order.is_glb_simp)
    by (simp add: seq_carrier seq_le)

  lemma cka_lub_to_seq: "\<Sigma>\<^bsub>A\<^esub>X = \<Sigma>\<^bsub>SEQ\<^esub>X"
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

  lemma cka_one_is_seq_one: "one A = one SEQ"
    by (simp add: SEQ_def)

  lemma cka_one_is_con_one: "one A = one CON"
    by (simp add: CON_def)

  lemma cka_cl_is_seq_cl: "complete_lattice A = complete_lattice SEQ"
    by (metis cka_cl seq_cl)

  lemma default_quantale: "unital_quantale A"
    apply (insert seq_quantale_var)
    apply (unfold unital_quantale_def)
    apply safe
    apply (metis cka_cl)
    apply (simp_all add: seq_carrier seq_le cka_lub_to_seq cka_one_is_seq_one)
    by (simp add: SEQ_def)+

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
    by (metis con_onel exchange_var mult_oner one_closed xc yc zc)

  lemma con_seq_slide2:
    assumes xc: "x \<in> carrier A" and yc: "y \<in> carrier A" and zc: "z \<in> carrier A"
    shows "x \<cdot> (y \<bar> z) \<sqsubseteq> (x \<cdot> y) \<bar> z"
    by (metis con_oner exchange_var mult_onel one_closed xc yc zc)

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

(*
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
*)

type_synonym 'a lan = "'a list set"

definition lan_product :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<bowtie>" 70) where
  "X \<bowtie> Y \<equiv> {Z. \<exists>x\<in>X. \<exists>y\<in>Y. Z = x @ y}"

definition lan_one :: "'a lan" where
  "lan_one = {[]}"

no_notation
  Groups.one_class.one ("1")

notation
  lan_one ("1")

fun interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a lan" where
  "interleave [] x = {x}"
| "interleave x [] = {x}"
| "interleave (x#xs) (y#ys) = (op # x ` interleave xs (y#ys)) \<union> (op # y ` interleave (x#xs) ys)"

definition interleaving :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<parallel>" 75) where
  "X \<parallel> Y \<equiv> \<Union> {Z. \<exists>x\<in>X. \<exists>y\<in>Y. Z = interleave x y}"

definition language :: "'a lan con_ord" where
  "language \<equiv> \<lparr>carrier = UNIV, le = op \<subseteq>, one = lan_one, mult = op \<bowtie>, con = op \<parallel>\<rparr>"

abbreviation seq_language :: "'a lan mult_ord" where
  "seq_language \<equiv> \<lparr>carrier = UNIV, le = op \<subseteq>, one = 1, mult = op \<bowtie>\<rparr>"

lemma seq_ord: "order seq_language"
  by (auto simp add: order_def)

lemma seq_lub [simp]: "\<Sigma>\<^bsub>seq_language\<^esub> X = \<Union> X"
  apply (simp add: order.lub_simp[OF seq_ord], rule the1I2)
  apply safe
  apply blast
  apply (metis PowI in_mono)
  apply (metis PowI in_mono)
  apply (metis PowI Sup_upper UnionI Union_Pow_eq Union_mono)
  by (metis set_mp)

lemma seq_cjs [intro]: "complete_join_semilattice seq_language"
  by unfold_locales (auto simp add: order.is_lub_simp[OF seq_ord])

lemma seq_cms [intro]: "complete_meet_semilattice seq_language"
  by (rule complete_join_semilattice.is_cms[OF seq_cjs])

lemma seq_cl [intro]: "complete_lattice seq_language"
  by (simp add: complete_lattice_def seq_cjs seq_cms)

abbreviation con_language :: "'a lan mult_ord" where
  "con_language \<equiv> \<lparr>carrier = UNIV, le = op \<subseteq>, one = 1, mult = op \<parallel>\<rparr>"

lemma "concurrent_ka language"
proof (simp add: concurrent_ka_def language_def, intro conjI allI)
  show "unital_quantale seq_language"
    apply (simp add: unital_quantale_def, intro conjI)
    apply (auto simp add: ftype_pred lan_product_def lan_one_def)
    apply (metis lan_one_def seq_cl)
    apply metis
    by (metis append_assoc)
next
  show "unital_quantale con_language"
    sorry
next
  fix a b c d
  show "a \<parallel> b \<bowtie> c \<parallel> d \<subseteq> (b \<bowtie> c) \<parallel> (a \<bowtie> d)"

datatype ('a, 'b) trace = tlink 'a 'b "('a, 'b) trace" | tend 'a

fun join :: "('a, 'b) trace \<Rightarrow> ('a, 'b) trace \<Rightarrow> ('a, 'b) trace" where
  "join (tlink u p \<sigma>) \<tau> = tlink u p (join \<sigma> \<tau>)"
| "join (tend u) \<tau> = \<tau>"

fun first :: "('a, 'b) trace \<Rightarrow> 'a" where
  "first (tlink u _ _) = u"
| "first (tend u)      = u"

fun last :: "('a, 'b) trace \<Rightarrow> 'a" where
  "last (tlink _ _ \<sigma>) = last \<sigma>"
| "last (tend u)      = u"

lemma join_last [simp]: "last (join \<sigma> \<tau>) = last \<tau>"
  by (induct \<sigma>, auto)

lemma join_first [simp]: "last \<sigma> = first \<tau> \<Longrightarrow> first (join \<sigma> \<tau>) = first \<sigma>"
  by (induct \<sigma>, auto)

lemma join_assoc: "join (join \<sigma> \<tau>) \<phi> = join \<sigma> (join \<tau> \<phi>)"
  by (induct \<sigma>, auto)

definition fusion_product :: "('a, 'b) trace set \<Rightarrow> ('a, 'b) trace set \<Rightarrow> ('a, 'b) trace set" (infixl "\<bowtie>" 70) where
  "X \<bowtie> Y = {Z. \<exists>\<sigma>\<in>X. \<exists>\<tau>\<in>Y. Z = join \<sigma> \<tau> \<and> last \<sigma> = first \<tau>}"

definition fusion_one :: "('a, 'b) trace set" where
  "fusion_one = tend ` UNIV"

no_notation
  Groups.one_class.one ("1")

notation
  fusion_one ("1")

lemma fusion_onel: "1 \<bowtie> X = X"
  by (simp add: fusion_product_def fusion_one_def)

lemma fusion_oner: "X \<bowtie> 1 = X"
proof (auto simp add: fusion_product_def fusion_one_def)
  fix \<sigma> :: "('a, 'b) trace" assume "\<sigma> \<in> X"
  thus "join \<sigma> (tend (last \<sigma>)) \<in> X"
    by (induct \<sigma> arbitrary: X, auto)
  from `\<sigma> \<in> X` show "\<exists>\<tau>\<in>X. \<sigma> = join \<tau> (tend (last \<tau>))"
    by (rule_tac x = \<sigma> in bexI, induct \<sigma> arbitrary: X, auto)
qed

lemma fusion_assoc:
  "(X \<bowtie> Y) \<bowtie> Z = X \<bowtie> (Y \<bowtie> Z)"
proof (auto simp add: fusion_product_def)
  fix \<sigma> \<tau> \<phi>
  assume \<sigma>X: "\<sigma> \<in> X" and \<tau>Y: "\<tau> \<in> Y " and \<phi>Z: "\<phi> \<in> Z"
  and \<tau>\<phi>: "last \<tau> = first \<phi>"
  and \<sigma>\<tau>: "last \<sigma> = first \<tau>"
  thus "\<exists>\<nu>\<in>X. \<exists>\<chi>. (\<exists>\<sigma>'\<in>Y. \<exists>\<tau>'\<in>Z. \<chi> = join \<sigma>' \<tau>' \<and> last \<sigma>' = first \<tau>')
                  \<and> join (join \<sigma> \<tau>) \<phi> = join \<nu> \<chi>
                  \<and> last \<nu> = first \<chi>"
    apply (rule_tac x = \<sigma> in bexI, auto)
    apply (rule_tac x = "join \<tau> \<phi>" in exI, auto)
    by (metis join_assoc)
  from \<sigma>X \<tau>Y \<phi>Z \<tau>\<phi> \<sigma>\<tau>
  show "\<exists>\<chi>. (\<exists>\<sigma>'\<in>X. \<exists>\<tau>'\<in>Y. \<chi> = join \<sigma>' \<tau>' \<and> last \<sigma>' = first \<tau>')
          \<and> (\<exists>\<nu>\<in>Z. join \<sigma> (join \<tau> \<phi>) = join \<chi> \<nu>
            \<and> last \<chi> = first \<nu>)"
    apply (rule_tac x = "join \<sigma> \<tau>" in exI, auto)
    apply (rule_tac x = \<phi> in bexI, auto)
    by (metis join_assoc)
qed

lemma fusion_inf_distl: "x \<bowtie> \<Union> Y = \<Union> {x \<bowtie> y|y. y \<in> Y}"
  by (auto simp add: fusion_product_def)

lemma fusion_inf_distr: "\<Union> X \<bowtie> y = \<Union> {x \<bowtie> y|x. x \<in> X}"
  by (auto simp add: fusion_product_def)

definition traces :: "('a, 'b) trace set mult_ord" where
  "traces \<equiv> \<lparr>carrier = UNIV, le = op \<subseteq>, one = fusion_one, mult = op \<bowtie>\<rparr>"

lemma traces_ord: "order traces"
  by (auto simp add: order_def traces_def)

lemma traces_lub [simp]: "\<Sigma>\<^bsub>traces\<^esub> X = \<Union> X"
  apply (simp add: order.lub_simp[OF traces_ord], rule the1I2)
  apply (simp_all add: traces_def)
  apply safe
  apply blast
  apply (metis PowI in_mono)
  apply (metis PowI in_mono)
  apply (metis PowI Sup_upper UnionI Union_Pow_eq Union_mono)
  by (metis set_mp)

lemma traces_cjs [intro]: "complete_join_semilattice traces"
  by unfold_locales (simp_all add: order.is_lub_simp[OF traces_ord], auto simp add: traces_def)

lemma traces_cms [intro]: "complete_meet_semilattice traces"
  by (rule complete_join_semilattice.is_cms[OF traces_cjs])

lemma traces_cl [intro]: "complete_lattice traces"
  by (simp add: complete_lattice_def traces_cjs traces_cms)

lemma traces_quantale: "unital_quantale traces"
  apply (simp add: unital_quantale_def, intro conjI)
  apply blast
  apply (simp_all add: traces_def ftype_pred fusion_assoc fusion_oner fusion_onel)
  by (auto simp add: fusion_product_def)

datatype unit = unit

fun interleave :: "('a, unit) trace \<Rightarrow> ('a, unit) trace \<Rightarrow> ('a, unit) trace set" where
  "interleave (tend u) (tend p) = {tlink u unit (tend p), tlink p unit (tend u)}"
| "interleave (tend u) (tlink p unit \<sigma>) = ({tlink u unit \<sigma>} \<union> (tlink p unit ` interleave (tend u) \<sigma>))"
| "interleave (tlink p unit \<sigma>) (tend u) = ({tlink u unit \<sigma>} \<union> (tlink p unit ` interleave (tend u) \<sigma>))"
| "interleave (tlink u unit \<sigma>) (tlink p unit \<tau>) =
     ((tlink u unit ` interleave \<sigma> (tlink p unit \<tau>)) \<union> (tlink p unit ` interleave (tlink u unit \<sigma>) \<tau>))"

definition interleaving :: "('a, unit) trace set \<Rightarrow> ('a, unit) trace set \<Rightarrow> ('a, unit) trace set" (infixl "\<parallel>" 75) where
  "X \<parallel> Y \<equiv> \<Union> {Z. \<exists>x\<in>X. \<exists>y\<in>Y. Z = interleave x y}"

lemma "1 \<parallel> x = x"
  apply (simp add: interleaving_def fusion_one_def)
  
