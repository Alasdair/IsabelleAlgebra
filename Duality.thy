theory Duality
  imports Main
begin

datatype 'a dual = dual 'a

primrec undual :: "'a dual \<Rightarrow> 'a" where
  undual_dual: "undual (dual x) = x"

lemma dual_undual [simp]: "dual (undual x) = x"
  by (metis dual.exhaust undual.simps)

lemma undual_dual_id [simp]: "dual \<circ> undual = id" by auto

lemma dual_undual_swap: "P (undual (dual x)) \<longleftrightarrow> P (dual (undual x))"
  by (metis dual_undual undual.simps)

lemma undual_equality [iff?]: "(undual x = undual y) \<longleftrightarrow> (x = y)"
  by (metis dual_undual)

lemma dual_equality [iff?]: "(dual x = dual y) \<longleftrightarrow> (x = y)"
  by (metis undual.simps)

lemma dual_ball [iff?]: "(\<forall>x\<in>A. P (dual x)) \<longleftrightarrow> (\<forall>x\<in> dual ` A. P x)"
  by (metis image_iff)

lemma range_dual [simp]: "surj dual"
  by (metis dual_undual surjI)

lemma dual_all [iff?]: "(\<forall>x. P (dual x)) \<longleftrightarrow> (\<forall>x. P x)"
  by (metis dual_undual)

lemma dual_ex: "(\<exists>x. P (dual x)) \<longleftrightarrow> (\<exists>x. P x)"
by (metis dual_undual)

lemma dual_collect: "{dual x | x. P (dual x)} = {y. P y}"
proof -
  have "{dual x|x. P (dual x)} = {y. \<exists>z. y = z \<and> P z}"
    by (simp only: dual_ex [symmetric])
  thus ?thesis by blast
qed

end
