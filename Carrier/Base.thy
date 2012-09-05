theory Base
  imports Main
begin

record 'a partial_object =
  carrier :: "'a set"

(* From HOL/SenSocialChoice/FSect.thy in AFP. By Peter Gammie *)
lemma finite_subset_induct_var [consumes 2, case_names empty insert]:
  assumes "finite F" and "F \<subseteq> A"
    and empty: "P {}"
    and insert: "\<And>a F. \<lbrakk>finite F; a \<in> A; F \<subseteq> A; a \<notin> F; P F\<rbrakk> \<Longrightarrow> P (insert a F)"
  shows "P F"
proof -
  from `finite F`
  have "F \<subseteq> A \<Longrightarrow> ?thesis"
  proof induct
    show "P {}" by fact
  next
    fix x F
    assume "finite F" and "x \<notin> F" and
      P: "F \<subseteq> A \<Longrightarrow> P F" and i: "insert x F \<subseteq> A"
    show "P (insert x F)"
    proof (rule insert)
      from i show "x \<in> A" by blast
      from i have "F \<subseteq> A" by blast
      with P show "P F" .
      show "finite F" by fact
      show "x \<notin> F" by fact
      show "F \<subseteq> A" by fact
    qed
  qed
  with `F \<subseteq> A` show ?thesis by blast
qed

text {* To talk about functions between structures with carrier sets,
we need some notion of a function's \emph {type}. *}

definition ftype :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<rightarrow>" 60) where
  "ftype A B \<equiv> {f. \<forall>x. x \<in> A \<longrightarrow> f x \<in> B}"

text {* We could also define \emph{ftype} as a predicate rather than
as a set. *}

lemma ftype_pred: "(f \<in> A \<rightarrow> B) = (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B)"
  by (simp add: ftype_def)

text {* Typing rules for composition and application can then be
derived, as well as the type of the identity function. *}

lemma typed_composition: "\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C\<rbrakk> \<Longrightarrow> g \<circ> f \<in> A \<rightarrow> C"
  by (simp add: ftype_def)

lemma typed_application: "\<lbrakk>x \<in> A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> f x \<in> B"
  by (simp add: ftype_def)

lemma typed_abstraction: "\<forall>x. f x \<in> A \<Longrightarrow> f \<in> UNIV \<rightarrow> A"
  by (simp add: ftype_def)

lemma typed_mapping: "\<lbrakk>f \<in> A \<rightarrow> B; X \<subseteq> A\<rbrakk> \<Longrightarrow> f ` X \<subseteq> B"
  by (metis ftype_pred image_subsetI set_mp)

lemma id_type: "id \<in> A \<rightarrow> A"
  by (simp add: ftype_def)

end
