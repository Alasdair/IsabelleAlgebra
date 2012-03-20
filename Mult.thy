header {* Multiplication *}

theory Mult
  imports Main
begin

class mult =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 80)

end
