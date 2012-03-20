(*  Title:      Hoare_Examples.thy
    Author:     Tjark Weber, University of Cambridge
*)

header {* Hoare Logic: Examples *}

theory Hoare_Examples
imports "$ISABELLE_HOME/src/HOL/Hoare/Hoare_Logic" Relation_Model
begin

text {*
First, a correctness proof for the naive reachability algorithm
implemented using relations.  The proof uses both relational lemmas
and algebraic lemmas instantiated to the relational model.  Note that
{\tt sledgehammer} failed on the last verification condition.
*}

lemma relation_naive_reachability: "VARS w
 {True}
 w := V;
 WHILE \<not> (w O Y \<subseteq> w)
 INV {V \<subseteq> w \<and> w \<subseteq> V O Y^*}
 DO w := w \<union> w O Y OD
 {w = V O Y^*}"
proof (vcg_simp)
  show  "V \<subseteq> V O Y\<^sup>*"
  by (smt R_O_Id Relation_Model.star_ref equalityE rel_comp_mono subset_trans)

  next fix w
  show "V \<subseteq> w \<and> w \<subseteq> V O Y\<^sup>* \<and> \<not> w O Y \<subseteq> w \<Longrightarrow> V \<subseteq> w \<union> w O Y \<and> w O Y \<subseteq> V O Y\<^sup>*"
  by (smt le_supI1 O_assoc Relation_Model.star_ext Relation_Model.star_trans_eq order_refl rel_comp_mono sup_absorb1)+

  next fix w
  show "V \<subseteq> w \<and> w \<subseteq> V O Y\<^sup>* \<and> w O Y \<subseteq> w \<Longrightarrow> w = V O Y\<^sup>*"
  by (auto elim!: rtrancl_induct)
qed

text {*
Now, a purely algebraic correctness proof for the abstract (algebraic)
version of the same algorithm.
*}

lemma (in kleene_algebra) naive_reachability: "VARS w
 {True}
 w := V;
 WHILE \<not> (w \<cdot> Y \<le> w)
 INV {V \<le> w \<and> w \<le> V \<cdot> Y\<^sup>\<star>}
 DO w := w + w \<cdot> Y OD
 {w = V \<cdot> Y\<^sup>\<star>}"
proof (vcg_simp)
  show "V \<le> V \<cdot> Y\<^sup>\<star>"
  by (smt mult_isol mult_oner star_ref)

  next fix w
  show "V \<le> w \<and> w \<le> V \<cdot> Y\<^sup>\<star> \<and> \<not> w \<cdot> Y \<le> w \<Longrightarrow> V \<le> w + w \<cdot> Y \<and> w + w \<cdot> Y \<le> V \<cdot> Y\<^sup>\<star>"
  (* by (metis add_assoc add_lub leq_def mult_assoc mult_isol star_1l star_slide_var subdistr) -- {* takes several minutes *} *)
  proof
    assume A: "V \<le> w \<and> w \<le> V \<cdot> Y\<^sup>\<star> \<and> \<not> w \<cdot> Y \<le> w"
    show "V \<le> w + w \<cdot> Y"
      by (metis A add_ub order_trans)
    have "w \<le> V \<cdot> Y\<^sup>\<star>"
      by (metis A)
    thus "w + w \<cdot> Y \<le> V \<cdot> Y\<^sup>\<star>"
      by (metis add_lub min_def mult_assoc mult_double_iso opp_mult_def star_ext star_trans_eq)
  qed

  next fix w
  show "V \<le> w \<and> w \<le> V \<cdot> Y\<^sup>\<star> \<and> w \<cdot> Y \<le> w \<Longrightarrow> w = V \<cdot> Y\<^sup>\<star>"
  by (smt add_comm add_iso leq_def star_inductr)
qed

text {*
Since we previously proved that relations are Kleene algebras,
Isabelle automatically provides a relational version of {\tt
naive_reachability}.

However, note that this theorem is less general than {\tt
relation_naive_reachability}: the type of @{term V} and @{term Y} is
@{typ "('a * 'a) set"}, while in {\tt relation_naive_reachability},
@{term V} and @{term Y} are of type @{typ "('a * 'b) set"} and @{typ
"('b * 'b) set"}, respectively.
*}

end
