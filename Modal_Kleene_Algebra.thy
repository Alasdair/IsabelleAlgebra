 header {* Modal Kleene Algebras *}

theory Modal_Kleene_Algebra
  imports Domain_Semiring Range_Semiring
begin

class modal_kleene_algebra = fmodal_kleene_algebra + bmodal_kleene_algebra +
assumes domrange: "d(r(x))=r(x)"
and rangedom: "r(d(x))=d(x)"

begin

text {* These axioms force that the domain algebra and the range algebra conicide *}

lemma domrangefix: "d(x)=x \<longleftrightarrow> r(x)=x"
  by (metis domrange rangedom)

lemma box_diamond_galois_1: "p=d(p) \<and> q=d(q) \<longrightarrow> (\<langle>x\<bar>p \<le> q \<longleftrightarrow> p \<le> \<bar>x]q)"
  by (metis domrangefix fbox_demodalisation3 rdemodalisation3)

lemma box_diamond_galois_2: "p=d(p) \<and> q=d(q) \<longrightarrow> (\<bar>x\<rangle>p \<le> q \<longleftrightarrow> p \<le> [x\<bar>q)"
  by (metis domrangefix bbox_demodalisation3 fdemodalisation3)

lemma diamond_conjugation_var_1: "p = d(p) \<and> q = d(q) \<longrightarrow> (\<bar>x\<rangle>q \<le> a(p) \<longleftrightarrow> \<langle>x\<bar>p \<le> a(q))"
  by (smt a_closure a_export antidomain_semiring_domain_def box_diamond_galois_1 domain_1 fbox_def fdia_fbox leq_def)

lemma diamond_conjugation: "p = d(p) \<and> q = d(q)  \<longrightarrow> (p\<cdot>(\<bar>x\<rangle>q) = 0 \<longleftrightarrow> q\<cdot>(\<langle>x\<bar>p) = 0)"
  by (metis diamond_conjugation_var_1 fdia_simp_2 bdia_simp_2 domrange d_d_zero dom_el_comm)

lemma box_conjugation:  "p = d(p) \<and> q = d(q) \<longrightarrow> (p \<le> [x\<bar>a(q) \<longleftrightarrow> q \<le> \<bar>x]a(p))"
  by (metis box_diamond_galois_2 a_closure diamond_conjugation_var_1  box_diamond_galois_1 antidomain_semiring_domain_def)

lemma box_diamond_cancellation_1:  "p=d(p)  \<longrightarrow>  p \<le> \<bar>x](\<langle>x\<bar>p)"
  by (metis bdiamond_def box_diamond_galois_1 domrange order_refl)

lemma box_diamond_cancellation_2:  "p=d(p)  \<longrightarrow>  p \<le> [x\<bar>(\<bar>x\<rangle>p)"
  by (metis box_diamond_galois_2 domain_invol fdiamond_def order_refl)

lemma box_diamond_cancellation_3:  "q=d(q) \<longrightarrow> \<bar>x\<rangle>([x\<bar>q) \<le> q"
  by (metis ar_closure box_diamond_galois_2 domrangefix dual.fbox_fdia order_refl)

lemma box_diamond_cancellation_4:  "q=d(q) \<longrightarrow> \<langle>x\<bar>(\<bar>x]q) \<le> q"
  by (metis a_closure box_diamond_galois_1 fbox_def order_refl)

end

end
