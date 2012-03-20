header {* Local and Concurrent Monoids *}

theory LKA
  imports Signatures
begin

text{* The structures and theorems in this file correspond to those in
the forthcoming paper "On Locality and the Exchange Law for Concurrent
Processes". The pointers in this file are to facts from this paper. *}

declare [[ smt_solver = remote_z3]]
declare [[ smt_timeout = 60 ]]
declare [[ z3_options = "-memory:500" ]]

(**************************************************************************)

section {* Ordered Semigroups *}

text {* We start with the definitions of ordered semigroups and
ordered monoids. Some of these structures can be found in the Isabelle
library; we reimplemented them to make the formalisation
selfcontained. *}

class semigroup = mult_op + 
  assumes mult_assoc: "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"

text {* An ordered semigroup is a poset with a semigroup operation
that is left and right isotone. *}

class ordered_semigroup = semigroup + order +
  assumes mult_isor: "x \<le> y \<longrightarrow> z\<cdot>x \<le> z\<cdot>y"
  and  mult_isol: "x \<le> y \<longrightarrow> x\<cdot>z \<le> y\<cdot>z"

begin

text {* We now define Hoare and Plotkin triples (Definition 3.9). At
this level there is no distinction between programs and assertions. *}

definition hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace>" [54,54,54] 53)
  where "\<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> \<longleftrightarrow> x\<cdot>y \<le> z"

definition plotkin_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lparr> _ \<rparr> _ \<lparr>  _ \<rparr>" [54,54,54] 53)
  where "\<lparr>x\<rparr>y\<lparr>z\<rparr> \<longleftrightarrow> y\<cdot>x \<le> z"



lemma hoare_trivial: "\<lbrace>x\<rbrace>y\<lbrace>x\<cdot>y\<rbrace>"
by (smt hoare_triple_def order_refl) 

lemma plotkin_trivial: "\<lparr>x\<rparr>y\<lparr>y\<cdot>x\<rparr>"
by (smt order_refl plotkin_triple_def)

text {* We now derive some Hoare rules in ordered semigroups (Lemma
3.11). *}

lemma consequence_rule: "\<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> \<and> v \<le> x \<and> z \<le> w \<longrightarrow>  \<lbrace>v\<rbrace>y\<lbrace>w\<rbrace>"
  by (metis hoare_triple_def mult_isol order_trans)

lemma sequencing_rule_var:  "\<forall> v w y z . (\<exists> x . \<lbrace>v\<rbrace>w\<lbrace>x\<rbrace> \<and> \<lbrace>x\<rbrace>y\<lbrace>z\<rbrace>) \<longrightarrow>  \<lbrace>v\<rbrace>w\<cdot>y\<lbrace>z\<rbrace>"
  by (smt hoare_triple_def mult_assoc mult_isol order_trans)

lemma sequencing_rule:  "\<lbrace>v\<rbrace>w\<lbrace>x\<rbrace> \<and> \<lbrace>x\<rbrace>y\<lbrace>z\<rbrace> \<longrightarrow>  \<lbrace>v\<rbrace>w\<cdot>y\<lbrace>z\<rbrace>"
  by (smt hoare_triple_def mult_assoc mult_isol order_trans)

end

(**********************************************************************)

section {* Ordered Monoids *}

text {* We now add a unit to the semigroup. Later, the monoid
multiplication, which need not be commutative, is understood as serial
or sequential composition. The unit corresponds to skip. *}

class monoid = semigroup + 
  fixes skip :: "'a" ("s")
  assumes mult_skipl: "s\<cdot>x = x"
  and mult_skipr: "x\<cdot>s = x"

text {* s stands for skip *}

class ordered_monoid = ordered_semigroup + monoid

begin

text {* We can now prove another Hoare rule (Lemma 3.11). *}

lemma skip_rule: "\<lbrace>x\<rbrace>s\<lbrace>x\<rbrace>"
  by (smt hoare_triple_def mult_skipr order_refl)

end



(**********************************************************************)

section {* Ordered Bisemigroups *}

text {* Commutativity of concurrent composition is built into the
definition (Def. 3.1). *}

class bisemigroup = semigroup + c_mult_op +
  assumes c_mult_assoc: "(x\<otimes>y)\<otimes>z = x\<otimes>(y\<otimes>z)"
  assumes c_mult_comm: "x\<otimes>y = y\<otimes>x"

class ordered_bisemigroup = ordered_semigroup + bisemigroup +
  assumes c_mult_isor: "x \<le> y \<longrightarrow> z\<otimes>x \<le> z\<otimes>y"


begin

lemma c_mult_isol: "x \<le> y \<longrightarrow> x\<otimes>z \<le> y\<otimes>z"
  by (smt c_mult_comm c_mult_isor)

text {* We now relate the exchange laws of concurrent monoids and
concurrent Kleene algebras with rules of concurrent separation logic.

The next lemma shows that the concurrency rule of CSL is equivalent to
the exchange law of CKA (Lemma 3.12). *}

lemma concurrency_exchange:"
  (\<forall> u v w x y z. (\<lbrace>u\<rbrace>v\<lbrace>w\<rbrace> \<and> \<lbrace>x\<rbrace>y\<lbrace>z\<rbrace>) \<longrightarrow> \<lbrace>u\<otimes>x\<rbrace>v\<otimes>y\<lbrace>w\<otimes>z\<rbrace>) 
  \<longleftrightarrow> (\<forall> w x y z .(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>y)\<otimes>(x\<cdot>z))"
  by (smt c_mult_isol c_mult_isor hoare_triple_def hoare_trivial order_trans)

text {* The next two lemmas show that the two "small" exchange laws of
CKA are equivalent to the frame rules for Hoare and Plotkin triples in
CSL (Lemma 3.12). *}

lemma hoare_frame_exchange: 
  "(\<forall> x y z .(x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z)) \<longleftrightarrow> (\<forall> w x y z. \<lbrace>w\<rbrace>x\<lbrace>y\<rbrace> \<longrightarrow> \<lbrace>z\<otimes>w\<rbrace>x\<lbrace>z\<otimes>y\<rbrace>)"
  by (smt c_mult_comm c_mult_isol hoare_triple_def hoare_trivial order_trans)

lemma plotkin_frame_exchange: 
  "(\<forall> w x y z. \<lparr>w\<rparr>x\<lparr>y\<rparr> \<longrightarrow> \<lparr>w\<otimes>z\<rparr>x\<lparr>y\<otimes>z\<rparr>) \<longleftrightarrow> (\<forall> x y z . x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z)"
  by (smt c_mult_isol consequence_rule hoare_triple_def order_refl plotkin_triple_def)

text {* Finally we prove two further frame rules. In the algebraic
setting they are essentially isotonicity properties (Remark after
Lemma 3.12). *}

lemma futuristic_frame: "\<lparr>w\<rparr>x\<lparr>y\<rparr> \<longrightarrow> \<lparr>w\<cdot>z\<rparr>x\<lparr>y\<cdot>z\<rparr>"
  by (smt mult_assoc mult_isol plotkin_triple_def)

lemma archaic_frame:  "\<lbrace>w\<rbrace>x\<lbrace>y\<rbrace> \<longrightarrow> \<lbrace>z\<cdot>w\<rbrace>x\<lbrace>z\<cdot>y\<rbrace>"
  by (smt hoare_triple_def mult_assoc mult_isor)

end

(************************************************************************************)

section {* Ordered Bimonoids *}

text {* The definition of bimonoid given here differs from the one in
CKA. There are two different units instead of one single one. *}

class bimonoid = bisemigroup + monoid +
  fixes nothing :: "'a" ("n")
  assumes c_mult_nothingl: "n\<otimes>x = x"
  and c_mult_nothingr: "x\<otimes>n = x"

begin

subclass semigroup
proof qed

text {* Next we define local elements (Def. 4.2). *}

definition L :: "'a \<Rightarrow> 'a"
  where "L x = x\<otimes>s"

text {* L is called the localiser of the bimonoid. *}

definition local :: "'a \<Rightarrow> bool"
  where "local x \<longleftrightarrow> L x = x"

text {* Local elements are fixpoints of the localiser. *}

text {* The next statements are refutations. The counterexample
generator Nitpicck shows that there are models of bimonoids where skip
and nothing are not local. *}

(*
lemma skip_local: "local(s)"
nitpick -- 2-element counterexample found
*)

(*
lemma nothing_local: "local(n)"
nitpick -- 2-element counterexample found
*)

text {* Next we show that concurrent composition preserves locality
(Lemma 4.4). *}

lemma local_c_mult_closed:  "local x \<and> local y \<longrightarrow> local (x\<otimes>y)"
  by (smt L_def c_mult_assoc c_mult_comm local_def)

lemma weak_local_c_mult_closed:  "local x  \<longrightarrow> local (x\<otimes>y)"
  by (smt L_def c_mult_assoc c_mult_comm local_def)

text {* The next lemmas show that nothing is local iff every element
is local iff nothing and skip are equal Lemma 4.10). *}

lemma nothing_everything_loc: "local n \<longleftrightarrow> (\<forall> x . local x)"
  by (metis c_mult_nothingl weak_local_c_mult_closed)

lemma nothing_loc_skip: "local n \<longleftrightarrow> n = s"
  by (smt L_def c_mult_nothingl local_def)

lemma nothing_loc_skip_unit: "local n \<longleftrightarrow> (\<forall>x . x\<otimes>s = x)"
  by (smt L_def local_def nothing_everything_loc)

end

text {* (Def. 3.6) *}

class ordered_bimonoid = ordered_bisemigroup + bimonoid 

begin 

subclass ordered_bisemigroup
proof qed

text {* The following fact is part of the proof of Lemma
4.13. Essentially is says that the locaiser is isotone, which is a
rather trivial fact. *}

lemma local_iso: "x \<le> y \<longrightarrow> L(x) \<le> L(y)"
  by (smt L_def c_mult_isol)

end

(***********************************************************************************)

section {* Exchange monoids *}

text {* We now add the exchange law of CKA to ordered
bimonoids. Again, the main difference to the CKA case is that there
are two different units. *}

class exchange_monoid = ordered_bimonoid +
  assumes exchange: "(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>y)\<otimes>(x\<cdot>z)"

begin

text {* (Lemma 3.7) *}

lemma skip_le_nothing: "s \<le> n"
  by (metis c_mult_nothingr c_mult_nothingl mult_skipr mult_skipl exchange)

lemma nothing_subidem: "n \<le> n\<cdot>n"
  by (smt mult_isol mult_skipl skip_le_nothing)

lemma skip_supidem: "s\<otimes>s \<le> s"
  by (smt c_mult_isol c_mult_nothingl skip_le_nothing)

(*
lemma  "n \<le> s"
nitpick

lemma test: "x\<cdot>y \<le> x\<otimes>y"
nitpick

nitpick found 2-element counterexamples 
*)

text {* The next three lemmas show that local elements satisfy the
"small" exchange laws. *}

lemma loc_small_exchange_1: "local z \<longrightarrow> (x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z)"
  by (smt L_def c_mult_comm exchange local_def mult_skipr)

(*
lemma  "(x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z) \<longrightarrow> local z" 
nitpick

nitpick found 2-element counterexample
*)

lemma loc_small_exchange_2: "local x \<longrightarrow> x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z"
  by (metis L_def exchange local_def mult_skipl)

(*
lemma "x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z \<longrightarrow> local x"
nitpick 

nitpick found 2-element counterexample
*)

lemma loc_mult_le_c_mult: "local x \<and> local y \<longrightarrow> x\<cdot>y \<le> x\<otimes>y"
  by (smt L_def loc_small_exchange_1 local_def mult_skipl)

(*
lemma "x\<cdot>y \<le> x\<otimes>y \<longrightarrow> local x \<and> local y"
nitpick

nitpick found 2-element counterexample
*)

text {* The next two lemmas show that local elements satisfy the Hoare
and Plotkin frame rules (Lemma 4.3). *}

lemma loc_hoare_frame:  "local x \<and> \<lbrace>w\<rbrace>x\<lbrace>y\<rbrace> \<longrightarrow> \<lbrace>z\<otimes>w\<rbrace>x\<lbrace>z\<otimes>y\<rbrace>"
  by (smt L_def c_mult_comm concurrency_exchange exchange hoare_trivial local_def mult_skipr)

lemma loc_plotkin_frame:  "local x \<and>  \<lparr>w\<rparr>x\<lparr>y\<rparr> \<longrightarrow> \<lparr>w\<otimes>z\<rparr>x\<lparr>y\<otimes>z\<rparr>"
  by (smt c_mult_isol loc_small_exchange_2 order_trans plotkin_triple_def)

text {* The next lemma show locality is now also closed under serial
composition (this needs exchange), but skip and nothing need not be
local (Lemma 4.5). *}

lemma local_mult_closed: "local x \<and> local y \<longrightarrow> local (x\<cdot>y)"
  by (smt L_def antisym_conv c_mult_isor c_mult_nothingr loc_small_exchange_2 local_def skip_le_nothing)

(*
lemma "local s"
nitpick

nitpick found 3-element counterexample
*)

(*
lemma "local n"
nitpick

nitpick found 2-element counterexample
*)

end

(*****************************************************************************)

section {* Locality Monoids *}

text {* We still have two units, but require that skip is idempotent
with respect to concurrent composition (Def. 4.6). *}

class locality_monoid = exchange_monoid +
assumes skip_idem: "s\<otimes>s=s"

begin

lemma skip_local: "local s"
  by (smt L_def local_def skip_idem)

text {* (Lemma 4.7) *}

lemma local_closed: "local (L x)"
  by (smt L_def c_mult_assoc local_def skip_idem)

lemma local_closed_var: "L (L x) = L x"
  by (smt local_closed local_def)

text {* We can now show that L is the right adjoint of a Galois
connection (Lemma 4.14; the left adjoint is inclusion of the set of
local elements into the locality monoid). *}

lemma local_galois: "local x \<longrightarrow> (x \<le> y \<longleftrightarrow> x \<le> L(y))"
  by (smt L_def c_mult_comm c_mult_isor c_mult_nothingl local_def order_trans skip_le_nothing)

text {* The next rules strengthen the relationships between local
elements, exchange laws and frame rules in locality monoids. These
rules hold iff some elements are local (Lemma 4.15). *}

lemma loc_small_exchange_1_eq: "local z \<longleftrightarrow> (\<forall> x y . (x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z))"
  by (smt L_def c_mult_comm less_le less_le_not_le loc_small_exchange_1 local_closed local_galois mult_skipl skip_idem)

lemma loc_small_exchange_2: "local x \<longleftrightarrow> (\<forall> y z . x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z)"
  by (smt L_def antisym loc_small_exchange_2 local_closed local_galois mult_skipr skip_idem)

(*
lemma loc_mult_le_c_mult: "(local x \<and> local y) \<longleftrightarrow> x\<cdot>y \<le> x\<otimes>y"
nitpick

nitpick found 2-element counterexample 
*)

text {* The following two lemmas show that precisely the local
elements satisfy the Hoare and Plotkin frame rules. *}

lemma loc_hoare_frame:  "local x \<longleftrightarrow> (\<forall> w y z . \<lbrace>w\<rbrace>x\<lbrace>y\<rbrace> \<longrightarrow> \<lbrace>z\<otimes>w\<rbrace>x\<lbrace>z\<otimes>y\<rbrace>)"
  by (smt L_def c_mult_comm eq_iff hoare_triple_def loc_hoare_frame local_closed local_galois mult_skipl skip_idem)

lemma loc_plotkin_frame:  "local x \<longleftrightarrow> (\<forall> w y z .  \<lparr>w\<rparr>x\<lparr>y\<rparr> \<longrightarrow> \<lparr>w\<otimes>z\<rparr>x\<lparr>y\<otimes>z\<rparr>)"
  by (smt L_def c_mult_comm c_mult_isol c_mult_nothingl eq_iff loc_plotkin_frame local_def mult_skipr plotkin_triple_def skip_idem skip_le_nothing)

end

(************************************************************************************)

section {* Concurrent Monoids *}

text {* Finally, we define the concurrent monoids from CKA
(Def. 4.11). These structures have one single unit. In this setting,
the exchange law implies its "small" siblings (Lemma 3.8). *}

class concurrent_monoid = locality_monoid +
  assumes skip_eq_nothing: "s = n"

begin

lemma mult_incl_cmult: "x\<cdot>y \<le> x\<otimes>y"
  by (smt loc_mult_le_c_mult nothing_everything_loc skip_eq_nothing skip_local)

lemma exchange_var1: "(x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z)"
  by (smt loc_small_exchange_1 nothing_everything_loc skip_eq_nothing skip_local)

lemma exchange_var2: "x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z"
  by (smt loc_small_exchange_2 nothing_everything_loc skip_eq_nothing skip_local)

end


(************************************************************************)

class weak_exchange_bisemigroup = ordered_bisemigroup +
assumes e4: "(w\<otimes>x)\<cdot>(y\<otimes>z) \<le> (w\<cdot>x)\<otimes>(y\<cdot>z)"

begin

(*
lemma "e\<cdot>e = e & e\<otimes>e = e \<longrightarrow> (\<forall>x. e\<otimes>x = x \<longrightarrow> e\<otimes>x \<le> e\<cdot>x)"
nitpick -- 2-element counterexample


lemma "e\<cdot>e = e & e\<otimes>e = e \<longrightarrow> (\<forall>x. e\<cdot>x = x \<longrightarrow> e\<otimes>x \<le> e\<cdot>x)"
nitpick -- 2-element counterexample

lemma "e\<cdot>e = e & e\<otimes>e = e \<longrightarrow> (\<forall> x. e\<otimes>x = x \<longrightarrow> e\<cdot>(e\<otimes>x)= e\<otimes>x)"
nitpick -- 2-element counterexample

lemma "e\<cdot>e = e & e\<otimes>e = e \<longrightarrow> (\<forall> x. e\<cdot>x = x \<longrightarrow> e\<cdot>(e\<otimes>x)= e\<otimes>x)"
nitpick --- 3-element counterexample

lemma "e\<cdot>e = e & e\<otimes>e = e \<longrightarrow> (\<forall> x. \<forall> y. ((e\<cdot>x = x \<and> e\<cdot>y = y) \<longrightarrow> e\<otimes>(x\<cdot>y)= x\<cdot>y))"
nitpick -- 2-element counterexample
*)

lemma "e\<cdot>e = e & e\<otimes>e = e \<longrightarrow> (\<forall> x. \<forall> y. ((e\<otimes>x = x \<and> e\<otimes>y = y) \<longrightarrow> e\<otimes>(x\<cdot>y)= x\<cdot>y))"
nitpick -- 3-element counterexample

end

class exchange_bisemigroup = weak_exchange_bisemigroup +
assumes e1: "x\<cdot>y \<le> x\<otimes>y"
and e2: "x\<cdot>(y\<otimes>z) \<le> (x\<cdot>y)\<otimes>z"
and e3: "(x\<otimes>y)\<cdot>z \<le> x\<otimes>(y\<cdot>z)"

end

