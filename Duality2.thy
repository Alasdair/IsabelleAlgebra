theory Duality2
  imports Main
begin

typedef 'a dual = "{dual :: 'a \<Rightarrow> 'a. \<forall>x. dual (dual x) = x}"
apply (rule_tac x = id in exI)
by clarify (simp only: id_def)
