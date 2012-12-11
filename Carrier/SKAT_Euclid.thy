theory SKAT_Euclid
  imports SKAT_Eval GCD
begin

datatype alph = mod_alph | plus_alph | nat_alph nat | eq_alph

lemma alph_UNIV: "UNIV = {mod_alph,eq_alph,plus_alph} \<union> (nat_alph ` UNIV)"
  by (auto simp add: image_def, metis alph.exhaust)

instantiation alph :: ranked_alphabet
begin

  fun arity_alph :: "alph \<Rightarrow> nat" where
    "arity_alph mod_alph = 2"
  | "arity_alph plus_alph = 2"
  | "arity_alph eq_alph = 2"
  | "arity_alph is_gcd_alph = 0"
  | "arity_alph (nat_alph _) = 0"

  definition funs_alph :: "alph set" where "funs_alph \<equiv> {mod_alph,plus_alph} \<union> (nat_alph ` UNIV)"

  definition rels_alph :: "alph set" where "rels_alph \<equiv> {eq_alph}"

  definition NULL_alph :: "alph" where "NULL_alph \<equiv> nat_alph 0"

  declare funs_alph_def [alphabet]
    and rels_alph_def [alphabet]
    and NULL_alph_def [alphabet]

  definition output_vars_alph :: "alph itself \<Rightarrow> nat set" where "output_vars_alph x \<equiv> {0}"

  declare output_vars_alph_def [alphabet]

  instance proof
    show "(funs :: alph set) \<inter> rels = {}"
      by (auto simp add: funs_alph_def rels_alph_def)

    show "(funs :: alph set) \<union> rels = UNIV"
      by (auto simp add: funs_alph_def rels_alph_def alph_UNIV)

    show "(funs :: alph set) \<noteq> {}"
      by (simp add: funs_alph_def)

    show "(rels :: alph set) \<noteq> {}"
      by (simp add: rels_alph_def)

    show "NULL \<in> (funs :: alph set)"
      by (simp add: NULL_alph_def funs_alph_def)

    show "arity (NULL::alph) = 0"
      by (simp add: NULL_alph_def)

    show "\<exists>x. x \<in> output_vars TYPE(alph)"
      by (metis (mono_tags) insertI1 output_vars_alph_def)

    show "finite (output_vars TYPE(alph))"
      by (metis (hide_lams, mono_tags) atLeastLessThan0 finite_atLeastLessThan finite_insert output_vars_alph_def)
  qed
end

definition MOD :: "alph trm \<Rightarrow> alph trm \<Rightarrow> alph trm" where
  "MOD a b \<equiv> (App mod_alph [a, b])"

definition PLUS :: "alph trm \<Rightarrow> alph trm \<Rightarrow> alph trm" where
  "PLUS a b = (App plus_alph [a, b])"

definition EQ :: "alph trm \<Rightarrow> alph trm \<Rightarrow> alph pred" where
  "EQ x y \<equiv> Pred eq_alph [x, y]"

definition NAT :: "nat \<Rightarrow> alph trm" where
  "NAT n \<equiv> App (nat_alph n) []"

declare MOD_def [skat_simp]
  and PLUS_def [skat_simp]
  and EQ_def [skat_simp]
  and NAT_def [skat_simp]

fun euclid_funs :: "alph \<Rightarrow> nat list \<Rightarrow> nat" where
  "euclid_funs mod_alph [x, y] = x mod y"
| "euclid_funs plus_alph [x, y] = x + y"
| "euclid_funs (nat_alph n) [] = n"
| "euclid_funs _ _ = 0"

inductive_set euclid_rels :: "alph \<Rightarrow> nat relation" for a :: "alph" where
  "a = eq_alph \<Longrightarrow> [x,x] \<in> euclid_rels a"

lemma [simp]: "[x, y] \<in> euclid_rels eq_alph \<longleftrightarrow> x = y"
  by (metis (lifting) euclid_rels.simps list.inject)

abbreviation EUCLID :: "(alph, nat) interp" where "EUCLID \<equiv> \<lparr>carrier = UNIV, mf = euclid_funs, mr = euclid_rels\<rparr>"

interpretation interp EUCLID done

definition SIMPLE_LOOP :: "alph skat" where
  "SIMPLE_LOOP \<equiv>
   WHILE !(pred (EQ (Var 0) (NAT 5))) DO
     0 := PLUS (Var 0) (NAT 1)
   WEND"

definition GCD :: "alph skat" where
  "GCD \<equiv>
   WHILE !(pred (EQ (Var 1) (NAT 0))) DO
     2 := Var 1;
     1 := MOD (Var 0) (Var 1);
     0 := Var 2
   WEND"

abbreviation hoare_triple_notation :: "nat mems \<Rightarrow> alph skat \<Rightarrow> nat mems \<Rightarrow> bool" ("_ \<lbrace> _ \<rbrace> _" [54,54,54] 53) where
  "hoare_triple_notation \<equiv> interp.hoare_triple EUCLID"

abbreviation module_notation :: "nat mems \<Rightarrow> alph skat \<Rightarrow> nat mems" (infix "\<Colon>" 75) where
  "module_notation \<Delta> x \<equiv> interp.module EUCLID \<Delta> x"

lemma helper: "\<lbrakk>\<And>x. P x = Q x\<rbrakk> \<Longrightarrow> {x. P x} = {x. Q x}"
  by auto

lemma "P \<lbrace> p \<rbrace> UNIV"
  by (metis hoare_triple_def top_greatest)

lemma "{} \<lbrace> p \<rbrace> P"
  by (metis bot_least hoare_triple_def interp.mod_empty)

lemma set_mem_UNIV [simp]: "set_mems x (\<lambda>mem. m) UNIV = {mem. m = mem x}"
  by (auto simp add: set_mems_def image_def set_mem_def) (rule_tac x = xa in exI, auto)

lemma satisfies_assign: "satisfies x (op = m) = UNIV \<Colon> x := NAT m"
  by (simp add: satisfies_def module_def NAT_def, transfer, simp add: assigns_def)

lemma skat_assign3_var: "r = t[x|s] \<Longrightarrow> (x := s \<cdot> x := t) = (x := r)"
  by (metis skat_assign3)

lemma variable_update: "satisfies x (op = n) \<lbrace> x := NAT m \<rbrace> satisfies x (op = m)"
  apply (simp add: satisfies_assign)
  apply (rule hoare_assignment'_var)
  apply (subst mod_mult[symmetric])
  apply (rule arg_cong) back
  apply (rule skat_assign3_var[symmetric])
  by (auto simp add: NAT_def)

  lemma while:
    assumes b_test: "b \<in> carrier tests"
    and Q_def: "Q = P \<inter> (UNIV \<Colon> !b)"
    and loop_condition: "P \<inter> (UNIV \<Colon> b) \<lbrace>p\<rbrace> P"
    shows "P \<lbrace> WHILE b DO p WEND \<rbrace> Q"
    by (metis (lifting) Q_def b_test interp.hoare_while loop_condition)

  lemma strengthen_precondition [consumes 1]: "\<lbrakk>P \<lbrace> p \<rbrace> Q; P' \<subseteq> P\<rbrakk> \<Longrightarrow> P' \<lbrace> p \<rbrace> Q"
    by (metis interp.hoare_weakening order_refl)

lemma [simp]: "satisfies x P \<subseteq> satisfies x Q \<longleftrightarrow> (\<forall>mem. P (mem x) \<longrightarrow> Q (mem x))"
  by (auto simp add: satisfies_def)

lemma [simp]: "UNIV \<Colon> pred_expr (BLeaf (EQ (Var n) (NAT m))) = satisfies n (op = m)"
  apply (simp add: module_def EQ_def NAT_def satisfies_def)
  apply transfer
  apply auto
  by (metis empty_iff singleton_iff)

lemma [simp]: "UNIV \<Colon> pred_expr (BNot (BLeaf (EQ (Var n) (NAT m)))) = satisfies n (op \<noteq> m)"
  apply (simp add: module_def EQ_def NAT_def satisfies_def)
  apply transfer
  apply auto
  by (metis empty_iff singleton_iff)

declare pred_to_expr [simp]
declare pred_expr_not [simp]

lemma [simp]: "pred_expr (BNot (BNot P)) = pred_expr P"
  sorry

declare pred_expr_closed [simp]

lemma weakening [consumes 1]: "\<lbrakk>P \<lbrace> p \<rbrace> Q; P' \<subseteq> P; Q \<subseteq> Q'\<rbrakk> \<Longrightarrow> P' \<lbrace> p \<rbrace> Q'"
  by (metis (lifting) hoare_weakening)

lemma simple_loop_example: "satisfies 0 (op = 0) \<lbrace> SIMPLE_LOOP \<rbrace> satisfies 0 (op = 5)"
proof -
  let ?invariant = "satisfies 0 (\<lambda>x. x \<le> 5)"

  have "?invariant \<lbrace> SIMPLE_LOOP \<rbrace> satisfies 0 (op = 5)"
  proof (simp add: SIMPLE_LOOP_def, rule while, simp_all)
    show "satisfies 0 (op = 5) = ?invariant \<inter> satisfies 0 (op = 5)"
      by (auto simp add: satisfies_def)

    have "satisfies 0 (\<lambda>y. y \<le> 4) \<lbrace> 0 := PLUS (Var 0) (NAT (Suc 0)) \<rbrace> satisfies 0 (\<lambda>y. 1 \<le> y \<and> y \<le> 5)"
      apply (rule hoare_assignment_var)
      apply (auto simp add: assigns_def PLUS_def NAT_def set_mems_def image_def set_mem_def satisfies_def)
      apply (rule_tac x = "\<lambda>v. if v = 0 then x 0 - 1 else x v" in exI)
      by auto

    thus "?invariant \<inter> satisfies 0 (\<lambda>y. y \<noteq> 5)
            \<lbrace> 0 := PLUS (Var 0) (NAT (Suc 0)) \<rbrace>
          ?invariant"
      by (rule weakening, auto simp add: satisfies_def)
  qed

  thus ?thesis
    by (rule strengthen_precondition, simp)
qed

fun initial_mem :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "initial_mem x y 0 = x"
| "initial_mem x y (Suc 0) = y"
| "initial_mem x y _ = 0"

declare pred_to_expr [simp]
declare pred_expr_not [simp]
declare Nat.One_nat_def [simp del]

no_notation
  dioid.one ("1\<index>") and
  dioid.zero ("0\<index>")

lemma (in interp) assignment: "P[x|s] \<subseteq> Q \<Longrightarrow> P \<lbrace> x := s \<rbrace> Q"
  by (metis hoare_triple_def mod_assign)

lemma euclids_algorithm: "{mem. mem 0 = x \<and> mem 1 = y} \<lbrace> GCD \<rbrace> {mem. mem 0 = gcd x y}"
proof -
  let ?invariant = "{mem. gcd (mem 0) (mem 1) = gcd x y}"

  have "?invariant \<lbrace> GCD \<rbrace> {mem. mem 0 = gcd x y \<and> mem 1 = 0}"
  proof (simp add: GCD_def, rule while, simp_all)
    show "{mem. mem 0 = gcd x y \<and> mem 1 = 0} = ?invariant \<inter> satisfies 1 (op = 0)"
      by (auto simp add: satisfies_def)

    show "{mem. gcd (mem 0) (mem 1) = gcd x y} \<inter> satisfies 1 (op < 0)
            \<lbrace> 2 := Var 1 ; 1 := MOD (Var 0) (Var 1) ; 0 := Var 2 \<rbrace>
          {mem. gcd (mem 0) (mem 1) = gcd x y}"
    proof (rule hoare_composition)+
      show "?invariant \<inter> satisfies 1 (op < 0) \<lbrace> 2 := Var 1 \<rbrace> ?invariant \<inter> satisfies 1 (op < 0) \<inter> {mem. mem 1 = mem 2}"
        apply (rule assignment)
        by (auto simp add: assigns_def set_mems_def image_def set_mem_def satisfies_def)

      show "?invariant \<inter> satisfies 1 (op < 0) \<inter> {mem. mem 1 = mem 2}
              \<lbrace> 1 := MOD (Var 0) (Var 1) \<rbrace>
            {mem. mem 1 = (mem 0) mod (mem 2)} \<inter> {mem. gcd (mem 0) (mem 2) = gcd x y} \<inter> satisfies 2 (op \<noteq> 0)"
        apply (rule assignment)
        by (auto simp add: assigns_def set_mems_def image_def set_mem_def satisfies_def MOD_def)

      have "{mem. mem 1 = (mem 0) mod (mem 2)} \<inter> {mem. gcd (mem 0) (mem 2) = gcd x y}
              \<lbrace> 0 := Var 2 \<rbrace>
            ?invariant \<inter> {mem. mem 0 = mem 2}"
        apply (rule assignment)
        apply (auto simp add: assigns_def set_mems_def image_def set_mem_def satisfies_def)
        by (metis gcd_red_nat)

      thus "{mem. mem 1 = (mem 0) mod (mem 2)} \<inter> {mem. gcd (mem 0) (mem 2) = gcd x y} \<inter> satisfies 2 (op \<noteq> 0)
              \<lbrace> 0 := Var 2 \<rbrace>
            ?invariant"
        by (rule weakening, auto)
    qed
  qed
  thus ?thesis
    by (rule weakening, auto)
qed

end
