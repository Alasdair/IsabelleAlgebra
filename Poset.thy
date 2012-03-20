theory Poset
  imports Main
begin

(* From Isabelle's locale guide *)
locale poset =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
  and anti_sym [intro]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y"
  and trans [intro]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

locale galois_connection = poset +
  fixes F G :: "'a \<Rightarrow> 'a"
  assumes conn: "(F x \<sqsubseteq> y) = (x \<sqsubseteq> G y)"

begin
  lemma grefl: "F x \<sqsubseteq> F x" by (metis refl)

  lemma inflate: "x \<sqsubseteq> G (F x)" by (metis conn refl)

  lemma deflate: "F (G x) \<sqsubseteq> x" by (metis conn refl)

  lemma comm: "F (G x) \<sqsubseteq> G (F x)" by (metis deflate inflate trans)

  lemma prop1: "x \<sqsubseteq> y \<longrightarrow> x \<sqsubseteq> G (F y)" by (metis inflate trans)

  lemma monotone_F: "x \<sqsubseteq> y \<longrightarrow> F x \<sqsubseteq> F x" by (metis refl)
  lemma monotone_G: "x \<sqsubseteq> y \<longrightarrow> G x \<sqsubseteq> G x" by (metis refl)

  lemma prop2: "G x \<sqsubseteq> G (F (G x))" by (metis inflate)
  lemma prop3: "G (F (G x)) \<sqsubseteq> G x" by (metis conn deflate trans)
  lemma prop5: "G (F (G x)) = G x" by (metis prop2 prop3 anti_sym)

  lemma idempotent_FG: "F (G (F (G x))) = F (G x)" by (metis prop5)
end

