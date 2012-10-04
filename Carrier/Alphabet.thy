theory Alphabet
  imports Base
begin

record alphabet_tuple =
  alphabet_symbols :: "nat set"
  alphabet_arity :: "nat \<Rightarrow> nat"
  alphabet_funs :: "nat set"
  alphabet_rels :: "nat set"

definition binary_alphabet_tuple :: "alphabet_tuple" where
  "binary_alphabet_tuple = \<lparr> alphabet_symbols = {0, 1}
                           , alphabet_arity = (\<lambda>x. 0)
                           , alphabet_funs = {0}
                           , alphabet_rels = {1}
                           \<rparr>"

typedef alphabet = "{\<Sigma>::alphabet_tuple. finite (alphabet_symbols \<Sigma>)
                                      \<and> alphabet_funs \<Sigma> \<inter> alphabet_rels \<Sigma> = {}
                                      \<and> alphabet_funs \<Sigma> \<union> alphabet_rels \<Sigma> = alphabet_symbols \<Sigma>
                                      \<and> alphabet_funs \<Sigma> \<noteq> {} \<and> alphabet_rels \<Sigma> \<noteq> {}}"
  by (rule_tac x = "binary_alphabet_tuple" in exI, auto simp add: binary_alphabet_tuple_def)

definition symbols :: "alphabet \<Rightarrow> nat set" where
  "symbols = alphabet_symbols \<circ> Rep_alphabet"

definition arity :: "alphabet \<Rightarrow> nat \<Rightarrow> nat" where
  "arity = alphabet_arity \<circ> Rep_alphabet"

definition funs :: "alphabet \<Rightarrow> nat set" where
  "funs = alphabet_funs \<circ> Rep_alphabet"

definition rels :: "alphabet \<Rightarrow> nat set" where
  "rels = alphabet_rels \<circ> Rep_alphabet"

declare Rep_alphabet_inverse [simp]

(* TODO: These should hardly require sledgehammer to solve... *)

lemma symbols_finite: "finite (symbols \<Sigma>)"
  apply (simp add: symbols_def)
  apply (rule Abs_alphabet_induct)
  apply (auto simp add: alphabet_def)
  by (smt CollectE Rep_alphabet alphabet_def)

lemma funs_rels_disjoint: "funs \<Sigma> \<inter> rels \<Sigma> = {}"
  apply (simp add: funs_def rels_def)
  apply (rule Abs_alphabet_induct)
  apply (auto simp add: alphabet_def)
  by (smt Abs_alphabet_cases Abs_alphabet_inverse CollectI Collect_empty_eq Collect_mem_eq alphabet_def disjoint_iff_not_equal)

lemma symbol_fun_or_rel: "funs \<Sigma> \<union> rels \<Sigma> = symbols \<Sigma>"
  apply (simp add: funs_def rels_def symbols_def)
  apply (rule Abs_alphabet_induct)
  apply (auto simp add: alphabet_def)
  apply (smt Abs_alphabet_inverse CollectI Collect_empty_eq Collect_mem_eq UnI1 alphabet_def)
  apply (smt Abs_alphabet_inverse CollectI Collect_empty_eq Collect_mem_eq UnI2 alphabet_def)
  by (smt Abs_alphabet_cases Abs_alphabet_inverse CollectI Collect_empty_eq Collect_mem_eq UnE alphabet_def)

lemma funs_exist: "funs \<Sigma> \<noteq> {}"
  apply (simp add: funs_def)
  apply (rule Abs_alphabet_induct)
  apply (auto simp add: alphabet_def)
  by (smt CollectE Rep_alphabet alphabet_def)

lemma rels_exist: "rels \<Sigma> \<noteq> {}"
  apply (simp add: rels_def)
  apply (rule Abs_alphabet_induct)
  apply (auto simp add: alphabet_def)
  by (smt CollectE Rep_alphabet alphabet_def)

end
