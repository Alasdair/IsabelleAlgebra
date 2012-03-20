header {* Relation Algebra *}

theory Relation_Algebra
  imports My_Boolean_Algebra Domain_Semiring
begin

section{* Basic Relation Algebra *}

text {* We follow Tarski's original article and Maddux's book. We take
our own Boolean algebra, but any axioms would do. In contrast to
Schmidt and Str\"ohlein we do not assume that the Boolean algebra is
complete and we do not consider the Tarski rule in this section *}

text {* There are still some notation clashes we need to fix. They are due to the fact that notation from dioids and from Boolean algebras is overloaded. *}

class relation_algebra = boolean_algebra +
fixes composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl ";" 80)
fixes converse :: "'a \<Rightarrow> 'a" ("(_\<^sup>\<smile>)" [1000] 999)
fixes unit :: "'a" ("e")
assumes comp_assoc: "(x;y);z = x;(y;z)"
and comp_unitr: "x;e = x"
and comp_distr: "(x+y);z = x;z + y;z"
and conv_invol: "(x\<^sup>\<smile>)\<^sup>\<smile> = x"
and conv_add: "(x+y)\<^sup>\<smile> = x\<^sup>\<smile>+y\<^sup>\<smile>"
and conv_contrav: "(x;y)\<^sup>\<smile> = y\<^sup>\<smile>;x\<^sup>\<smile>"
and comp_res: "x\<^sup>\<smile>;(-(x;y)) \<le>  -y"

text {* We first show that every relation algebra is a dioid *}

sublocale relation_algebra < dioid_one_zero "op +" "op ;" "op \<le>" "op <" "e"
proof
fix x y z :: 'a
show "x ; y ; z = x ; (y ; z)"
  by (metis comp_assoc)
show "x + y + z = x + (y + z)"
 by (metis join_assoc)
show "x + y = y + x"
  by (metis join_comm)
show "(x + y) ; z = x ; z + y ; z"
  by (metis comp_distr)
show "x+x=x"
  by (metis join_idem)
show  "x;(y+z)=x;y+x;z"
  by (metis conv_invol conv_add conv_contrav comp_distr)
show "x;e=x"
  by (metis comp_unitr)
show "e;x=x"
  by (metis comp_unitr conv_contrav conv_invol)
show "0+x=x"
  by (metis leq_def zero_min)
show "x;0=0"
  by (metis comp_distr comp_res conv_contrav conv_invol leq_def one_plus zero_def zero_min zero_plus)
show "0;x=0"
  by (metis comp_distr comp_res conv_contrav conv_invol leq_def one_plus zero_def zero_min zero_plus)
show "(x \<le> y) = (x + y = y)"
  by (metis leq_def)
show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  by (metis strict_leq_def)
qed

context relation_algebra
begin

text {* We now show some simple lemmas about coversion*}

lemma conv_iso: "x \<le> y \<longleftrightarrow> x\<^sup>\<smile> \<le> y\<^sup>\<smile>"
  by (metis conv_add conv_invol leq_def)

lemma conv_zero: "0\<^sup>\<smile> = 0"
  by (metis antisym_conv conv_invol conv_iso zero_min)

lemma conv_one: "1\<^sup>\<smile> = 1"
  by (metis antisym_conv conv_invol conv_iso one_max)

lemma conv_compl: "(-x)\<^sup>\<smile> = -(x\<^sup>\<smile>)"
  by (metis antisym conv_add conv_invol conv_iso conv_one double_compl galois_aux meet_def one_def zero_def)

lemma  comp_res_aux: "(x\<^sup>\<smile>;(-(x;y)))\<cdot>y = 0"
  by (metis comp_res galois_aux)

lemma conv_e: "e\<^sup>\<smile> = e"
  by (metis comp_unitr conv_contrav conv_invol)

lemma conv_times: "(x\<cdot>y)\<^sup>\<smile> = x\<^sup>\<smile>\<cdot>y\<^sup>\<smile>"
  by (metis meet_def conv_compl conv_add)

lemma conv_self_conjugate: "x\<^sup>\<smile>\<cdot>y = 0 \<longleftrightarrow> x\<cdot>y\<^sup>\<smile> = 0"
  by (metis conv_invol conv_times conv_zero)

text {* The next lemma shows that conversion is self-conjugate *}
lemma conv_self_conjugate_var: "conjugation_p (\<lambda> x . x\<^sup>\<smile>) (\<lambda> x . x\<^sup>\<smile>)"
  by (metis conv_self_conjugate)

text {* The following lemmas link the relative product and meet *}

lemma comp_isor: "x \<le> y \<longrightarrow> x;z \<le> y;z"
  by (metis comp_distr leq_def)

lemma one_idem_mult: "1;1 = 1"
  by (metis comp_unitr leq_symm_intro one_max one_plus subdistl)

lemma mult_subdistl: "x;(y\<cdot>z) \<le> x;y"
  by (metis meet_lb mult_isol)

lemma mult_subdistr: "(x\<cdot>y);z \<le> x;z"
  by (metis comp_isor meet_lb)

lemma mult_subdistl_var: "x;(y\<cdot>z) \<le> (x;y)\<cdot>(x;z)"
  by (metis galois_2 meet_glb mult_isol mult_subdistl one_def one_max)

lemma mult_subdistr_var: "(x\<cdot>y);z \<le> (x;z)\<cdot>(y;z)"
  by (metis comp_isor leq_meet meet_glb meet_idem)


text {* The following lemmas deal with variants of the Peirce law, the Schr\"oder laws and the Dedekind law *}

text {* Some of these laws are obtained from Boolean algebras with
operators by instantiation, using conjugation properties *}

lemma peirce_1: "(x;y)\<cdot>z\<^sup>\<smile> = 0 \<longrightarrow> (y;z)\<cdot>x\<^sup>\<smile> = 0"
proof
  assume "(x;y)\<cdot>z\<^sup>\<smile> = 0"
  hence "z \<le> -(y\<^sup>\<smile>;x\<^sup>\<smile>)"
    by (metis conv_invol conv_iso galois_aux conv_compl comp_anti double_compl conv_contrav)
  thus "(y;z)\<cdot>x\<^sup>\<smile> = 0"
    by (metis mult_isol meet_iso comp_res_aux antisym_conv conv_invol zero_min)
qed

lemma peirce: "(x;y)\<cdot>z\<^sup>\<smile> = 0 \<longleftrightarrow> (y;z)\<cdot>x\<^sup>\<smile> = 0"
  by (metis peirce_1)

lemma schroeder_1: "(x;y)\<cdot>z = 0 \<longleftrightarrow> y\<cdot>(x\<^sup>\<smile>;z) = 0"
  by  (smt conv_invol peirce conv_zero conv_contrav conv_times meet_comm)

text {* The following conjugatio property is used for proving the modular law of relation algebra. *}
lemma schroeder_1_var: "conjugation_p (\<lambda>y . x;y) (\<lambda>y . x\<^sup>\<smile>;y)"
  by (metis schroeder_1)

lemma schroeder_2: "(y;x)\<cdot>z = 0 \<longleftrightarrow> y\<cdot>(z;x\<^sup>\<smile>) = 0"
  by (metis conv_invol peirce schroeder_1)

lemma schroeder_2_var: "conjugation_p (\<lambda>y . y;x)  (\<lambda>y . y;x\<^sup>\<smile>)"
  by (metis schroeder_2)

text {* These laws are dual with respect to conjugation/converse. This
could be exploited. *}

text {* A variant of the modular law for relation algebras can now
be instantiated from Boolean algebras with operators. *}
lemma modular_1_aux': "(x;(y\<cdot>(-(x\<^sup>\<smile>;z))))\<cdot>z = 0"
  by (metis schroeder_1_var modular_1_aux)

lemma modular_2_aux': "((y\<cdot>(-(z;x\<^sup>\<smile>)));x)\<cdot>z = 0"
(*  by (metis schroeder_2_var modular_1_aux) surprisingly this doesn't work *)
  by (metis galois_aux meet_comm meet_lb schroeder_2_var) 

text {* It is unclear why the second law couldn't be obtained by instantiation. But the next one can. *}

lemma modular_1': "(x;y)\<cdot>z = (x;(y\<cdot>(x\<^sup>\<smile>;z)))\<cdot>z"
  by (metis schroeder_1_var modular_1)

lemma modular_2':  "(y;x)\<cdot>z \<le> ((y\<cdot>(z;x\<^sup>\<smile>));x)\<cdot>z"
proof -
  have "(y;x)\<cdot>z = ((y\<cdot>(z;x\<^sup>\<smile>)+y\<cdot>(-(z;x\<^sup>\<smile>)));x)\<cdot>z"
    by (metis ba_3 meet_comm)
  thus ?thesis
    by (metis distr dist_1 meet_comm eq_iff modular_2_aux' zero_plus)
qed

lemma modular_1_var: "(x;y)\<cdot>z \<le> x;(y\<cdot>(x\<^sup>\<smile>;z))"
  by (metis modular_1' meet_lb)

lemma modular_2_var:  "(x;y)\<cdot>z \<le> (x\<cdot>(z;y\<^sup>\<smile>));y"
  by (metis modular_2' meet_lb order_trans)

lemma dedekind: "(x;y)\<cdot>z \<le>  (x\<cdot>(z;y\<^sup>\<smile>));(y\<cdot>(x\<^sup>\<smile>;z))"
proof -
  have "(x\<cdot>(z;y\<^sup>\<smile>));(y\<cdot>((x\<cdot>(z;y\<^sup>\<smile>))\<^sup>\<smile>;z)) \<le>  (x\<cdot>(z;y\<^sup>\<smile>));(y\<cdot>(x\<^sup>\<smile>;z))"
    by (metis mult_isol mult_isor conv_times meet_comm meet_iso meet_lb)
  hence "x\<cdot>(z;y\<^sup>\<smile>);y\<cdot>z \<le>  (x\<cdot>(z;y\<^sup>\<smile>));(y\<cdot>(x\<^sup>\<smile>;z))"
    by (metis modular_1_var order_trans)
  thus ?thesis by (metis modular_2' order_trans)
qed

lemma dedekind_var_1: "x;y \<le> (x\<cdot>(1;y\<^sup>\<smile>));(y\<cdot>(x\<^sup>\<smile>;1))"
  by (metis dedekind eq_iff meet_glb one_max order_trans)

lemma modular_var_2: "x;y \<le> x;(y\<cdot>(x\<^sup>\<smile>;1))"
  by (metis modular_1_var one_times)

lemma modular_var_3: "x;y \<le> (x\<cdot>(1;y\<^sup>\<smile>));y"
  by (metis modular_2_var one_times)

text {* Next we show some further properties. *}

lemma ra_1: "(x\<cdot>(y;1));z = (x;z)\<cdot>(y;1)"
proof -
 have  "(x\<cdot>(y;1));z \<le> (x;z)\<cdot>(y;1)"
   by (metis meet_glb mult_assoc mult_double_iso one_idem_mult one_max order_refl)
 moreover
 have  "(x;z)\<cdot>(y;1) \<le> (x\<cdot>(y;1));z"
   by (smt comp_assoc distl comp_isor dist_1 leq_def one_plus  modular_2_var order_trans)
 ultimately show ?thesis by auto
qed

lemma ra_2: "x;(z\<cdot>(y;1)) = (x\<cdot>(y;1)\<^sup>\<smile>);z"
proof -
  have "(x\<cdot>(1;(z\<cdot>(y;1))\<^sup>\<smile>));z \<le> (x\<cdot>(y;1)\<^sup>\<smile>);z"
    by (metis comp_isor conv_contrav conv_iso conv_one meet_comm meet_iso meet_lb ra_1)
  hence  "x;(z\<cdot>(y;1)) \<le>  (x\<cdot>(y;1)\<^sup>\<smile>);z"
  by (metis modular_var_3 mult_subdistl order_trans)
moreover
  have  five: "x;(z\<cdot>((x\<cdot>(y;1)\<^sup>\<smile>)\<^sup>\<smile>;1)) \<le> x;(z\<cdot>(y;1))"
    by (metis conv_invol conv_times meet_comm meet_lb ra_1 mult_isol meet_iso)
  hence  "x;(z\<cdot>(y;1)) \<ge> (x\<cdot>(y;1)\<^sup>\<smile>);z"
    by (metis modular_var_2 mult_subdistr order_trans)
  ultimately show ?thesis by auto
qed

lemma one_conv: "e\<cdot>(x;1) = e\<cdot>(x;x\<^sup>\<smile>)"
  by (metis comp_unitr meet_comm modular_1' one_times)

lemma one_compl: "-(x;1);1 = -(x;1)"
(*sledgehammer [isar_proof]*)
proof -
  have "\<forall>x\<^isub>1\<Colon>'a. (1\<Colon>'a) ; x\<^isub>1 = (1\<Colon>'a) ; ((1\<Colon>'a) ; x\<^isub>1)" by (metis mult_assoc one_idem_mult)
  hence "\<forall>x\<^isub>1\<Colon>'a. (1\<Colon>'a) ; (- ((1\<Colon>'a) ; x\<^isub>1)) = - ((1\<Colon>'a) ; x\<^isub>1)" by (metis comp_res comp_unitr conv_contrav conv_invol conv_iso conv_one join_comm leq_def' one_plus subdistl)
  hence "\<forall>x\<^isub>1\<Colon>'a. - (x\<^isub>1 ; (1\<Colon>'a)) = - (x\<^isub>1 ; (1\<Colon>'a)) ; (1\<Colon>'a)" by (metis conv_compl conv_contrav conv_invol conv_one)
  thus "- (x ; (1\<Colon>'a)) ; (1\<Colon>'a) = - (x ; (1\<Colon>'a))" by metis
qed

text {* Vectors *}

definition
  vector_p :: "'a \<Rightarrow> bool"
  where "vector_p(x) \<longleftrightarrow> x = x;1"

lemma vector_compl: "vector_p(x) \<longrightarrow>vector_p(-x)"
  by (metis one_compl vector_p_def)

lemma vector_add: "vector_p(x) \<longrightarrow> vector_p(y) \<longrightarrow> vector_p(x+y)"
  by (metis comp_distr vector_p_def)

lemma vector_mult: "vector_p(x) \<longrightarrow> vector_p(y) \<longrightarrow> vector_p(x\<cdot>y)"
  by (metis meet_def vector_add vector_compl)

lemma vector_comp: "vector_p(x) \<longrightarrow> vector_p(y) \<longrightarrow> vector_p(x;y)"
  by (metis comp_assoc vector_p_def)

lemma vector_1: "vector_p(y) \<longrightarrow> (x\<cdot>y);z = (x;z)\<cdot>y"
  by (metis meet_comm ra_1 vector_p_def)

lemma vector_2: "vector_p(y) \<longrightarrow> (x\<cdot>y\<^sup>\<smile>);z = x;(z\<cdot>y)"
  by (metis meet_comm ra_2 vector_p_def)

lemma vector_idem: "vector_p(x) \<longrightarrow> x;x =x"
  by (metis comp_assoc conv_one leq_meet modular_1_var meet_comm one_idem_mult one_times vector_1)

lemma vector_rectangle: "vector_p(x) \<longrightarrow> x;1;x = x"
  by (metis vector_idem vector_p_def)

lemma vector_3: "vector_p(x) \<longrightarrow> (x\<cdot>e);y = x\<cdot>y"
  by (metis meet_comm mult_onel vector_1)

section {* Tests *}

definition
  test_p :: "'a \<Rightarrow> bool"
  where "test_p(x) \<longleftrightarrow> x \<le> e"

lemma test_conv: "test_p(x) \<longrightarrow> test_p(x\<^sup>\<smile>)"
  by (metis conv_e conv_iso test_p_def)

lemma test_conv_var: "test_p(x) \<longrightarrow> x\<^sup>\<smile> \<le> e"
  by (metis test_conv test_p_def)

lemma test_eq_conv: "test_p(x) \<longrightarrow> x = x\<^sup>\<smile>"
proof
  assume hyp: "test_p(x)"
  hence  "x \<le> x;(e\<cdot>(x\<^sup>\<smile>;e))"
    by (metis comp_unitr leq_meet test_p_def_raw modular_1_var)
  hence "x \<le> (e\<cdot>(x\<^sup>\<smile>;e))" using hyp
    by (metis mult_onel leq_meet meet_comm meet_glb mult_subdistr test_p_def_raw)
  thus "x = x\<^sup>\<smile>"
    by (metis comp_unitr conv_e conv_times hyp leq_meet meet_comm test_p_def_raw conv_invol)
qed

lemma test_sum: "test_p(x) \<longrightarrow> test_p(y) \<longrightarrow> test_p(x+y)"
  by (metis add_lub test_p_def)

lemma test_prod: "test_p(x) \<longrightarrow> test_p(y) \<longrightarrow> test_p(x\<cdot>y)"
  by (metis add_comm ba_1 galois_2 leq_def one_def one_max  test_p_def) 

lemma test_comp: "test_p(x) \<longrightarrow> test_p(y) \<longrightarrow> test_p(x;y)"
  by (metis mult_isol comp_unitr order_trans test_p_def)

lemma test_comp_eq_mult: "(test_p(x) \<and> test_p(y)) \<longrightarrow> x;y = x\<cdot>y"
proof
  assume hyp:  "test_p(x) \<and> test_p(y)"
  hence "x;(e\<cdot>(x\<^sup>\<smile>;y)) \<le> x;y"
    by (metis mult_onel leq_meet meet_comm meet_glb mult_subdistr test_eq_conv test_p_def_raw)
  hence " x;y \<ge> x\<cdot>y"
    by (metis comp_unitr modular_1_var order_trans)
  moreover
  have  "x;(e\<cdot>(x\<^sup>\<smile>;y)) \<le> x;y" using hyp
    by (metis mult_onel leq_meet meet_comm meet_glb mult_subdistr test_eq_conv test_p_def_raw)
  hence " x;y \<ge> x\<cdot>y"
    by (metis comp_unitr modular_1_var order_trans)
  ultimately show " x;y = x\<cdot>y"
  by(metis antisym_conv distl comp_distr mult_onel comp_unitr hyp leq_def meet_glb test_p_def)
qed

lemma test_1: "test_p(x) \<longrightarrow> (x;1)\<cdot>y = x;y"
proof 
  assume hyp: "test_p(x)"
   hence  "(x;1)\<cdot>y \<le> x;y"
     by (smt modular_1' meet_comm one_times mult_assoc test_eq_conv  test_comp_eq_mult  meet_idem meet_lb)
   moreover
   have "(x;1)\<cdot>y \<ge> x;y"
     by (metis test_p_def_raw hyp mult_isor mult_onel  mult_isol one_max meet_glb)
   ultimately show  "(x;1)\<cdot>y = x;y" by auto
qed

lemma test_distr_1 : "test_p(x) \<and> test_p(y) \<longrightarrow> (x;z)\<cdot>(y;z) = (x\<cdot>y);z"
proof 
  assume "test_p(x) \<and> test_p(y)"
  hence "(x;z)\<cdot>(y;z) \<le> (x\<cdot>y);z" 
    by (metis meet_comm meet_iso mult_subdistl one_times test_1 mult_assoc test_comp_eq_mult) 
  moreover
  have  "(x\<cdot>y);z \<le> (x;z)\<cdot>(y;z)"
    by (metis meet_def mult_subdistr_var)
  ultimately  show "(x;z)\<cdot>(y;z) = (x\<cdot>y);z" by auto
qed


section {* Test Complements *}

definition
  test_compl :: "'a \<Rightarrow> 'a" ("(_\<inverse>)" [1000] 999)
  where "x\<inverse> = (e\<cdot>(-x))"

lemma test_compl_1: "test_p(x) \<longrightarrow> x+x\<inverse> = e"
  by (metis comp_anti compl double_compl leq_def meet_def test_compl_def_raw test_p_def_raw)

lemma test_compl_2: "test_p(x) \<longrightarrow> x\<cdot>x\<inverse> = 0"
  by (metis add_comm ba_1 de_morgan_1 double_compl one_def test_compl_def zero_def)

lemma test_test_compl: "test_p(x) \<longrightarrow> test_p(x\<inverse>)"
  by (metis meet_lb test_compl_def_raw test_p_def)

lemma test_compl_de_morgan_1: "(x+y)\<inverse> = x\<inverse>\<cdot>y\<inverse>"
  by (metis add_comm add_idem de_morgan_1 double_compl meet_assoc test_compl_def)

lemma test_compl_de_morgan_2: "(x\<cdot>y)\<inverse> = x\<inverse>+y\<inverse>"
  by (metis de_morgan_2 dist_1 test_compl_def)

lemma test_compl_three: "(((x::'a)\<inverse>)\<inverse>)\<inverse> = x\<inverse>"
proof -
  have F1: "\<forall>x\<^isub>1\<Colon>'a. x\<^isub>1 \<cdot> (- (- x\<^isub>1)) = x\<^isub>1" by (metis compl de_morgan_2 meet_comm meet_idem zero_meet)
  hence F2: "\<forall>x\<^isub>1\<Colon>'a. - (- x\<^isub>1) = x\<^isub>1" by (metis compl de_morgan_2 meet_comm meet_idem zero_meet)
  have "\<forall>x\<^isub>1\<Colon>'a. e \<cdot> (- x\<^isub>1) = e \<cdot> (- (e \<cdot> x\<^isub>1))" by (metis F1 compl de_morgan_2 meet_comm meet_idem test_compl_de_morgan_2 test_compl_def zero_meet)
  hence "e \<cdot> (- (e \<cdot> (- (e \<cdot> (- x))))) = e \<cdot> (- x)" by (metis F2)
  hence "e \<cdot> (- (e \<cdot> (- (e \<cdot> (- x))))) = x\<inverse>" by (metis test_compl_def)
  thus "((x\<inverse>)\<inverse>)\<inverse> = x\<inverse>" by (metis test_compl_def)
qed
 
lemma test_compl_double: "test_p(x) \<longrightarrow> (x\<inverse>)\<inverse> = x"
  by (metis comp_anti double_compl leq_def meet_def test_compl_def test_compl_three test_p_def_raw)

section {* Functions *}

definition
  p_fun_p :: "'a \<Rightarrow> bool"
  where "p_fun_p(x) \<longleftrightarrow> (x\<^sup>\<smile>;x \<le> e)"

definition
  total_p :: "'a => bool"
  where "total_p(x) \<longleftrightarrow> e \<le> x;x\<^sup>\<smile>"

definition
  map_p ::  "'a => bool"
  where "map_p(x) \<longleftrightarrow> p_fun_p(x) \<and> total_p(x)"

definition
  inj_p :: "'a => bool"
  where "inj_p(x) \<longleftrightarrow> x;x\<^sup>\<smile> \<le> e"

definition
  sur_p :: "'a => bool"
  where "sur_p(x) \<longleftrightarrow> e \<le> x\<^sup>\<smile>;x"

definition
  bij_p ::  "'a => bool"
  where "bij_p(x) \<longleftrightarrow> inj_p(x) \<and> sur_p(x)"

lemma inj_p_fun: "inj_p(x) \<longleftrightarrow> p_fun_p(x\<^sup>\<smile>)"
  by (metis conv_invol inj_p_def_raw p_fun_p_def)

lemma sur_total: "sur_p(x) \<longleftrightarrow> total_p(x\<^sup>\<smile>)"
  by (metis conv_invol sur_p_def_raw total_p_def)

lemma test_inj_p_fun: "test_p(x) \<longrightarrow> (p_fun_p(x) \<and> inj_p(x))"
  by (metis inj_p_def_raw meet_idem p_fun_p_def_raw test_comp_eq_mult test_eq_conv test_p_def_raw)

lemma p_fun_comp_var: "( x\<^sup>\<smile>;x \<le> e \<and>  y\<^sup>\<smile>;y \<le> e) \<longrightarrow> (x;y)\<^sup>\<smile>;(x;y) \<le> e"
  by (smt comp_assoc mult_isol comp_isor comp_unitr conv_contrav order_trans)


lemma p_fun_comp: "p_fun_p(x) \<longrightarrow> p_fun_p(y) \<longrightarrow> p_fun_p(x;y)"
by (metis p_fun_comp_var p_fun_p_def)

(*a problem? does isabelle expand defs? *)

lemma p_fun_mult_var: "x\<^sup>\<smile>;x \<le> e  \<longrightarrow> (x\<cdot>y)\<^sup>\<smile>;(x\<cdot>y) \<le> e"
  by (metis add_ub comp_distr compl conv_add de_morgan_2 double_compl mult_subdistl order_trans)

lemma inj_comp_var: "( x;x\<^sup>\<smile> \<le> e \<and>  y;y\<^sup>\<smile> \<le> e) \<longrightarrow>(x;y);(x;y)\<^sup>\<smile> \<le> e"
  by (metis conv_contrav conv_invol p_fun_comp_var)

lemma inj_mult_var: "x\<^sup>\<smile>;x \<le> e  \<longrightarrow> (x\<cdot>y)\<^sup>\<smile>;(x\<cdot>y) \<le> e"
  by (metis p_fun_mult_var)

lemma total_comp_var: "(e \<le> x;x\<^sup>\<smile> \<and> e \<le> y;y\<^sup>\<smile>) \<longrightarrow> e \<le> (x;y);(x;y)\<^sup>\<smile>"
proof
  assume hyp: "e \<le> x;x\<^sup>\<smile> \<and> e \<le> y;y\<^sup>\<smile>"
  have "(x;y);(x;y)\<^sup>\<smile> = x;(y;y\<^sup>\<smile>);x\<^sup>\<smile>"
    by (metis comp_assoc conv_contrav)
  hence "(x;y);(x;y)\<^sup>\<smile> \<ge>  x;x\<^sup>\<smile>" using hyp
    by (metis mult_isol comp_unitr conv_contrav conv_iso)
  thus "e \<le> (x;y);(x;y)\<^sup>\<smile>" using hyp
    by (metis comp_assoc order_trans)
qed

lemma total_add_var: "e \<le> x\<^sup>\<smile>;x  \<longrightarrow> e \<le> (x+y)\<^sup>\<smile>;(x+y)"
  by (metis add_ub distl comp_isor conv_iso order_trans)

lemma sur_comp_var: "(e \<le> x\<^sup>\<smile>;x \<and> e \<le> y\<^sup>\<smile>;y) \<longrightarrow> e \<le> (x;y)\<^sup>\<smile>;(x;y)"
  by (metis conv_contrav conv_invol total_comp_var)

lemma sur_sum_var: "e \<le> x\<^sup>\<smile>;x  \<longrightarrow> e \<le> (x+y)\<^sup>\<smile>;(x+y)"
  by (metis total_add_var)

lemma map_comp_var: "( x\<^sup>\<smile>;x \<le> e \<and>  y\<^sup>\<smile>;y \<le> e \<and> e \<le> x;x\<^sup>\<smile> \<and> e \<le> y;y\<^sup>\<smile>) \<longrightarrow> ((x;y)\<^sup>\<smile>;(x;y) \<le> e \<and> e \<le> (x;y);(x;y)\<^sup>\<smile>)"
  by (metis p_fun_comp_var total_comp_var)

lemma p_fun_distl: "x\<^sup>\<smile>;x \<le> e \<longrightarrow> x;(y\<cdot>z) = (x;y)\<cdot>(x;z)"
proof
  assume hyp: "x\<^sup>\<smile>;x \<le> e"
  hence "x;(z\<cdot>((x\<^sup>\<smile>;x);y)) \<le> x;(z\<cdot>y)"
    by (metis absorption1 add_idem add_lub mult_isol comp_isor mult_onel dist_2 meet_glb meet_lb)
  hence  "(x;y)\<cdot>(x;z) \<le> x;(z\<cdot>y)"
    by (smt comp_assoc modular_1_var meet_comm order_trans)
  thus "x;(y\<cdot>z) = (x;y)\<cdot>(x;z)"
    by (metis add_comm antisym_conv meet_def mult_subdistl_var)
qed

lemma p_fun_zero: "x\<^sup>\<smile>;x \<le> e \<longrightarrow> (x;y)\<cdot>(x;(-y)) = 0"
  by (metis annil p_fun_distl zero_meet)


lemma total_one: "e \<le> x;x\<^sup>\<smile> \<longrightarrow> x;1 =1"
  by (metis comp_assoc comp_isor comp_unitr conv_contrav conv_invol conv_one eq_iff one_max)

lemma total_1:  "e \<le> x;x\<^sup>\<smile> \<longrightarrow> (\<forall>y.(y;x = 0 \<longrightarrow> y = 0))"
  by (metis annir comp_unitr distl mult_assoc one_plus total_one zero_plus)

lemma surj_one: "e \<le> x\<^sup>\<smile>;x \<longrightarrow> 1;x =1"
  by (metis comp_assoc comp_isor comp_unitr conv_contrav conv_invol conv_one eq_iff one_max)

lemma surj_1:  "e \<le> x\<^sup>\<smile>;x \<longrightarrow> (\<forall>y.(x;y = 0 \<longrightarrow> y = 0))"
  by (metis comp_anti comp_res conv_contrav conv_one eq_iff surj_one zero_min zero_one)

lemma bij_map_prop: "(bij_p(x) \<and> map_p(x)) \<longrightarrow> (x\<^sup>\<smile>;x  = e \<and> x;x\<^sup>\<smile> = e)"
  by (metis bij_p_def eq_iff inj_p_def_raw map_p_def p_fun_p_def_raw sur_p_def_raw total_p_def_raw)

section {* Points and Rectangles *}

definition
  point_p :: "'a \<Rightarrow> bool"
  where "point_p(x) \<longleftrightarrow> (vector_p(x) \<and> inj_p(x) \<and> \<not>(x = 0))"

definition
  rectangle_p :: "'a \<Rightarrow> bool"
  where "rectangle_p(x) \<longleftrightarrow> x;1;x \<le> x"

lemma rectangle_eq: "rectangle_p(x) \<longleftrightarrow> x;1;x = x"
  by (metis comp_assoc conv_one dedekind eq_iff meet_comm one_idem_mult one_times rectangle_p_def_raw)

section {* Antidomain *}

definition
  antidom :: "'a \<Rightarrow> 'a" ("a")
  where "a(x) = e\<cdot>(-(x;1))"

definition
  dom :: "'a \<Rightarrow> 'a" ("d")
  where "d(x) = a(a(x))"

lemma antidom_test_comp: "a(x) = (x;1)\<inverse>"
  by (metis antidom_def test_compl_def)

lemma dom_def_aux: "d(x) = e\<cdot>(x;1)"
  by (metis antidom_def mult_onel dom_def_raw double_compl leq_def meet_def one_compl ra_1 zero_def zero_min)

lemma dom_def_aux_var: "d(x) = e\<cdot>(x;x\<^sup>\<smile>)"
  by (metis dom_def_aux one_conv)

lemma antidom_dom: "a(d(x)) = a(x)"
  by (metis antidom_test_comp mult_onel dom_def_aux double_compl leq_def meet_def ra_1 zero_def zero_min)

lemma dom_antidom: "d(a(x)) = a(x)"
  by (metis antidom_dom dom_def)

lemma a_1: "a(x);x = 0"
by (metis antidom_def comp_res_aux conv_compl conv_contrav conv_invol conv_one conv_self_conjugate_var meet_comm mult_onel one_compl ra_1)

lemma a_2: "a(x;y) = a(x;d(y))"
  by (metis antidom_def comp_assoc mult_onel dom_def_aux double_compl leq_def meet_def ra_1 zero_def zero_min)

lemma a_3: "a(x)+d(x) = e"
  by (metis antidom_def compl_1 dom_def_aux double_compl meet_def)

(* don't have to prove much more, show that this is subclass of dsemirings *)

lemma test_domain: "x = d(x) \<longleftrightarrow> x \<le>  e"
  by (metis dom_def_aux eq_iff meet_glb  test_eq_conv test_p_def_raw dom_def_aux_var test_comp_eq_mult meet_idem leq_meet meet_comm)
end

(* Name clash problem *)

(*
sublocale relation_algebra < boolean_domain_semiring "op +" "op ;" "e" "0" "a" "d" "op \<le>" "op <"

proof
  fix x y :: 'a
  show "a x ; x = (0\<Colon>'a)"
    by (metis antidom_test_comp conv_compl conv_contrav conv_times modular_2_aux meet_lb one_times test_compl_def test_eq_conv test_p_def zero_one)
  show "a (x ; y) + a (x ; a (a y)) = a (x ; a (a y))"
    by (metis a_2 dom_def join_idem)
  show "a (a x) + a x = e"
by (metis a_3 dom_def join_comm)

  show "(x \<le> y) = (x + y = y)"
by (metis join_comm leq_def')
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
by (metis strict_leq_def')
  show "d x = a (a x)"
by (metis dom_def)


qed

text {* In the presence of inverse we can explicitly link domain and range *}


lemma dom_one: "x;1 = d(x);1"
  by (metis mult_onel dom_def_aux meet_comm one_times ra_1)

lemma test_dom: "test_p(d(x))"
  by (metis dom_def_aux meet_lb test_p_def)

lemma p_fun_dom: "p_fun_p(d(x))"
  by (metis test_dom test_inj_p_fun)

lemma inj_dom: "inj_p(d(x))"
  by (metis test_dom test_inj_p_fun)

lemma total_alt_def: "total_p(x) \<longleftrightarrow> (d(x) = e)"
  by (metis dom_def_aux leq_meet one_conv total_p_def_raw)

section {* Relation Algebras with Reflexive Transitive Closure *}

class relation_algebra_rtc = relation_algebra +
fixes star :: "'a \<Rightarrow> 'a" ("(_*)" [1000] 999)
assumes rtc_unfoldl: "e+x;x* \<le> x*"
and rtc_inductl: "z+x;y \<le> y \<longrightarrow> x*;z \<le> y"
and rtc_inductr: "z+y;x \<le> y \<longrightarrow> z;x* \<le> y"

sublocale relation_algebra_rtc < kleene_algebra  "op +" "op ;" "op \<le>" "op <" "e" "0"
proof
fix x y z :: 'a
show "e + e = e"
  by (metis join_idem)
show "(x \<le> y) = (x + y = y)"
  by (metis leq_def')
show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  by (metis strict_leq_def')
show "e + x ; x* \<le> x*"
  by (metis rtc_unfoldl)
show "z + x ; y \<le> y \<longrightarrow> x* ; z \<le> y"
by (metis rtc_inductl)
show "z + y ; x \<le> y \<longrightarrow> z ; x* \<le> y"
by (metis rtc_inductr)
qed

(*
context relation_algebra
begin

subclass domain_semiring

end
*)

end
