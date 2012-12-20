theory SKAT_Trace
  imports SKAT_Term "Abstract-Rewriting/Abstract_Rewriting"
begin

datatype 'a event = Assign nat "'a trm"

inductive_set rewrites :: "'a::ranked_alphabet event list rel" where
  append_con: "(x, y) \<in> rewrites \<Longrightarrow> (a @ x @ b, a @ y @ b) \<in> rewrites"
| assign1: "\<lbrakk>y \<notin> FV s; y < x\<rbrakk> \<Longrightarrow> ([Assign x s, Assign y t], [Assign y (t[x|s]), Assign x s]) \<in> rewrites"
| assign2: "\<lbrakk>x \<notin> FV s; x < y\<rbrakk> \<Longrightarrow> ([Assign x s, Assign y t], [Assign x s, Assign y (t[x|s])]) \<in> rewrites"
| assign3: "([Assign x s, Assign x t], [Assign x (t[x|s])]) \<in> rewrites"

lemma WCR_symcl: "WCR (symcl S)"
  by (auto simp add: WCR_on_def join_def)

lemma CR_symcl: "CR (symcl S)"
  by (auto simp add: CR_on_def join_def) (metis Un_commute converse_Un converse_converse meetI meet_def)

lemma WN_rewrites: "WN rewrites"
  sorry

proof (auto simp add: WN_on_def normalizability_def)
  fix a
  show "\<exists>b. (a, b) \<in> rewrites\<^sup>* \<and> b \<in> NF rewrites"
    apply (induct a)
    apply auto
    

  
  
  
  
  

lemma "nf []"
proof (auto simp add: nf_def)
  fix x assume "[] \<mapsto> x" thus "False"
    by (rule rewrites.cases, auto)
qed

lemma "nf [x]"
proof (auto simp add: nf_def)
  fix y assume "[x] \<mapsto> y" thus "False"
    by (rule rewrites.cases, auto)
qed

lemma "nf x \<longleftrightarrow> \<not> reducible x"
  by (auto simp add: nf_def reducible_def)

fun interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
  "interleave [] x = {x}"
| "interleave x [] = {x}"
| "interleave (x#xs) (y#ys) = (op # x ` interleave xs (y#ys)) \<union> (op # y ` interleave (x#xs) ys)"

lemma interleave_comm: "interleave x y = interleave y x"
  by (induct rule: interleave.induct, metis interleave.simps(1) interleave.simps(2) list.exhaust, auto)

inductive event_con :: "'a::ranked_alphabet event list \<Rightarrow> 'a event list \<Rightarrow> bool" (infix "~" 50)
  where
  refl [intro]: "x ~ x"
| sym [sym]: "x ~ y \<Longrightarrow> y ~ x"
| trans [trans]: "x ~ y \<Longrightarrow> y ~ z \<Longrightarrow> x ~ z"

| append_compat: "x ~ y \<Longrightarrow> a @ x @ b ~ a @ y @ b"

| assign1: "\<lbrakk>x \<noteq> y; y \<notin> FV s\<rbrakk> \<Longrightarrow> [Assign x s, Assign y t] ~ [Assign y (t[x|s]), Assign x s]"
| assign2: "\<lbrakk>x \<noteq> y; x \<notin> FV s\<rbrakk> \<Longrightarrow> [Assign x s, Assign y t] ~ [Assign x s, Assign y (t[x|s])]"
| assign3: "[Assign x s, Assign x t] ~ [Assign x (t[x|s])]"

quotient_type 'a trace = "'a::ranked_alphabet event list" / event_con
  by (intro equivpI reflpI sympI transpI) (metis refl sym trans)+

lift_definition trace_append :: "'a::ranked_alphabet trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace" (infixr "\<cdot>" 70) is append
  by (metis append_Nil append_Nil2 append_compat equivp_def trace_equivp)

lemma trace_append_assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
  by transfer (metis append_assoc event_con.refl)

lift_definition trace_assign :: "nat \<Rightarrow> 'a::ranked_alphabet trm \<Rightarrow> 'a trace" (infix "::=" 100) is "\<lambda>x s. [Assign x s]"
  by (rule event_con.refl)

lemma trace_assign1: "\<lbrakk>x \<noteq> y; y \<notin> FV s\<rbrakk> \<Longrightarrow> x ::= s \<cdot> y ::= t = y ::= t[x|s] \<cdot> x ::= s"
  by (transfer, simp, rule event_con.assign1, assumption+)

lemma trace_assign2: "\<lbrakk>x \<noteq> y; x \<notin> FV s\<rbrakk> \<Longrightarrow> x ::= s \<cdot> y ::= t = x ::= s \<cdot> y ::= t[x|s]"
  by (transfer, simp, rule event_con.assign2, assumption+)

lemma trace_assign3: "(x ::= s \<cdot> x ::= t) = (x ::= t[x|s])"
  by (transfer, simp, rule event_con.assign3)

type_synonym 'a traces = "'a trace set"

definition traces_product :: "'a::ranked_alphabet traces \<Rightarrow> 'a traces \<Rightarrow> 'a traces" (infixl "\<bowtie>" 70) where
  "X \<bowtie> Y = {Z. \<exists>x\<in>X. \<exists>y\<in>Y. Z = x \<cdot> y}"

lemma "abs_trace (x#xs) = abs_trace [x] \<cdot> abs_trace xs"
  by transfer auto

definition trace_interleave :: "'a::ranked_alphabet trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace set" where
  "trace_interleave xs ys \<equiv> abs_trace ` (interleave (rep_trace xs) (rep_trace ys))"

lemma "trace_interleave xs ys = trace_interleave ys xs"
  by (simp add: trace_interleave_def) (metis interleave_comm)

type_synonym 'a mems = "(nat \<Rightarrow> 'a) set"

fun eval_events :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a event list \<Rightarrow> 'b mem \<Rightarrow> 'b mem" where
  "eval_events D [] mem = mem"
| "eval_events D (Assign x s # evs) mem = eval_events D evs (assign D x s mem)"

lemma eval_events_append: "eval_events D (append x y) mem = eval_events D y (eval_events D x mem)"
proof (induct x arbitrary: mem, auto)
  fix a :: "'b event" and x :: "'b event list" and mem :: "nat \<Rightarrow> 'a"
  assume "\<And>mem. eval_events D (append x y) mem = eval_events D y (eval_events D x mem)"
  moreover obtain z t where a_def: "a = Assign z t"
    by (metis event.exhaust)
  ultimately have "eval_events D (Assign z t # append x y) mem = eval_events D y (eval_events D (Assign z t # x) mem)"
    by auto
  thus "eval_events D (a # append x y) mem = eval_events D y (eval_events D (a # x) mem)"
    by (metis a_def)
qed

lemma event_con_eval: "x ~ y \<Longrightarrow> eval_events D x mem = eval_events D y mem"
  apply (induct arbitrary: mem rule: event_con.induct)
  apply auto
  apply (simp add: eval_events_append)
  apply (metis eval_assign1)
  apply (metis eval_assign2)
  by (metis eval_assign3)

lift_definition eval_trace :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'a trace \<Rightarrow> 'b mem \<Rightarrow> 'b mem" is eval_events
  by (rule ext, rule event_con_eval, assumption)

(*
lemma "\<lbrakk>eval_trace D t1 emp = mem; eval_trace D t2 emp = mem\<rbrakk> \<Longrightarrow> t1 = t2"
*)

end
