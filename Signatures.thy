header {* Signatures *}

theory Signatures

imports Main

begin

class mult_op =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 80)

class c_mult_op =
  fixes c_mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 80)

class star_op =
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)

class omega_op =
  fixes omega :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [101] 100)

class nabla_op =
  fixes nabla :: "'a \<Rightarrow> 'a" ("\<nabla>_" [90] 95)

class fdiamond_op =
  fixes fdiamond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<bar> _ \<rangle> _" [50,90] 95)

class fbox_op =
  fixes fbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<bar> _ ] _" [50,90] 95)

class bdiamond_op =
  fixes bdiamond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<langle> _ \<bar> _" [50,90] 95)

class bbox_op =
  fixes bbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("[ _ \<bar> _" [50,90] 95)

class a_op =
  fixes a :: "'a \<Rightarrow> 'a"

class d_op =
  fixes d :: "'a \<Rightarrow> 'a"

class r_op =
  fixes r :: "'a \<Rightarrow> 'a"

class ar_op =
  fixes ar :: "'a \<Rightarrow> 'a"

class pre_op =
  fixes pre :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<guillemotleft>" 55)

class ite_op =
  fixes ite :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<lhd> _ \<rhd> _" [58,58,58] 57)

class while_op =
  fixes while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<star>" 59)

class hoare_triple_op =
  fixes hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lbrace> _ \<rbrace> _" [54,54,54] 53)

class atomic_program =
  fixes Atomic_program :: "'a set"
  fixes Atomic_test :: "'a set"

class preimp_op =
  fixes preimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightarrow>" 60)

class postimp_op =
  fixes postimp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leftarrow>" 60)

class odot_op =
  fixes odot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 80)

class involution_op =
  fixes invol :: "'a \<Rightarrow> 'a" ("_\<^sup>\<circ>" [101] 100)

end

