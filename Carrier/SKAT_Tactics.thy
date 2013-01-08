theory SKAT_Tactics
  imports SKAT
begin

lemma skat_star_elim:
  assumes "x \<notin> touches t"
  shows "(x := s \<cdot> \<lfloor>t\<rfloor>)\<^sup>\<star> \<cdot> x := null = \<lfloor>t\<rfloor>\<^sup>\<star> \<cdot> x := null"
  apply (subst ska.star_elim[symmetric,simplified])
  apply (metis skat_null_zero)
  apply skat_comm
  apply (metis assms set_mp touch_atoms)
  apply (metis skat_null_zero)
  by auto

definition seq :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "seq xs \<equiv> foldl op \<cdot> \<one> xs"

definition SEQ :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "SEQ \<equiv> seq"

definition qes :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "qes xs \<equiv> seq (rev xs)"

definition QES :: "'a::ranked_alphabet skat list \<Rightarrow> 'a skat" where
  "QES \<equiv> qes"

lemma seq_to_qes: "seq xs = qes (rev xs)"
  by (simp add: qes_def)

ML {*
fun seq_select_tac s ctxt n =
  simp_tac (HOL_basic_ss addsimps @{thms SEQ_def[symmetric]}) n
  THEN EqSubst.eqsubst_tac ctxt [s] @{thms SEQ_def} n

fun seq_deselect_tac n =
  simp_tac (HOL_basic_ss addsimps @{thms SEQ_def QES_def}) n

fun qes_select_tac s ctxt n =
  simp_tac (HOL_basic_ss addsimps @{thms QES_def[symmetric]}) n
  THEN EqSubst.eqsubst_tac ctxt [s] @{thms QES_def} n

fun qes_deselect_tac n =
  simp_tac (HOL_basic_ss addsimps @{thms QES_def}) n

fun seq_reverse_tac s ctxt n =
  seq_select_tac s ctxt n
  THEN simp_tac (HOL_basic_ss addsimps @{thms seq_to_qes rev.simps append.simps}) n
  THEN seq_deselect_tac n

fun qes_reverse_tac s ctxt n =
  qes_select_tac s ctxt n
  THEN simp_tac (HOL_basic_ss addsimps @{thms qes_def rev.simps append.simps}) n
  THEN qes_deselect_tac n

*}

method_setup seq_select = {*
Scan.lift (Scan.optional Parse.nat 0) >>
  (fn s => fn ctxt => SIMPLE_METHOD (seq_select_tac s ctxt 1))
*}

method_setup seq_deselect = {*
Scan.succeed (fn _ => SIMPLE_METHOD (seq_deselect_tac 1))
*}

method_setup qes_select = {*
Scan.lift (Scan.optional Parse.nat 0) >>
  (fn s => fn ctxt => SIMPLE_METHOD (qes_select_tac s ctxt 1))
*}

method_setup qes_deselect = {*
Scan.succeed (fn _ => SIMPLE_METHOD (qes_deselect_tac 1))
*}

method_setup seq_rev = {*
Scan.lift (Scan.optional Parse.nat 0) >>
  (fn s => fn ctxt => seq_reverse_tac s ctxt |> SIMPLE_METHOD')
*}

method_setup qes_rev = {*
Scan.lift (Scan.optional Parse.nat 0) >>
  (fn s => fn ctxt => qes_reverse_tac s ctxt |> SIMPLE_METHOD')
*}

lemmas mult_oner = skd.mult_oner[simplified]
  and mult_onel = skd.mult_onel[simplified]

declare mult_oner [skat_simp]
  and mult_onel [skat_simp]
  and seq_def [skat_simp]
  and qes_def [skat_simp]
  and foldl.simps [skat_simp]
  and rev.simps [skat_simp]
  and append.simps [skat_simp]

lemma seq_singleton [simp]: "seq [x] = x" by skat_reduce
lemma qes_singleton [simp]: "qes [x] = x" by skat_reduce

lemma foldl_step: "foldl op \<cdot> \<one> (x#xs) = x \<cdot> foldl op \<cdot> \<one> xs"
  by (induct xs arbitrary: x, auto, skat_reduce, metis skd.mult_assoc)

lemma foldl_is_foldr: "foldl op \<cdot> \<one> xs = foldr op \<cdot> xs \<one>"
  by (induct xs, auto, metis foldl_Cons foldl_step)

lemma seq_foldr: "seq xs = foldr op \<cdot> xs \<one>"
  by (simp add: seq_def foldl_is_foldr)

lemma seq_mult: "seq (xs @ ys) = seq xs \<cdot> seq ys"
  apply (induct xs)
  apply (simp add: seq_foldr)
  apply (metis skd.mult_onel)
  apply (simp add: seq_foldr)
  by (metis skd.mult_assoc)

lemma seq_cut: "seq xs = seq (take n xs) \<cdot> seq (drop n xs)"
  by (subst seq_mult[symmetric], simp)

lemma seq_zip: "seq xs = qes (rev (take n xs)) \<cdot> seq (drop n xs)"
  by (metis seq_cut seq_to_qes)

method_setup cut = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat >>
  (fn (s, c) => fn ctxt =>
    let
      val ct = nat_cterm c
    in
      seq_select_tac s ctxt 1
      THEN EqSubst.eqsubst_tac ctxt [0] [Drule.instantiate' [] [NONE, SOME ct] @{thm seq_cut}] 1
      THEN simp_tac (HOL_basic_ss addsimps @{thms Nat.nat.cases take.simps drop.simps}) 1
      THEN seq_deselect_tac 1
      |> SIMPLE_METHOD
    end)
*}

ML {*
fun zip_tac s c ctxt n =
  let
    val ct = nat_cterm c
  in
    seq_select_tac s ctxt n
    THEN EqSubst.eqsubst_tac ctxt [0] [Drule.instantiate' [] [NONE, SOME ct] @{thm seq_zip}] n
    THEN simp_tac (HOL_basic_ss addsimps @{thms rev.simps append.simps Nat.nat.cases take.simps drop.simps}) n
  end
*}

method_setup zip = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat >>
  (fn (s, c) => fn ctxt => SIMPLE_METHOD (zip_tac s c ctxt 1))
*}

lemma zip_right: "qes (x#xs) \<cdot> seq ys = qes xs \<cdot> seq (x#ys)"
  by (metis (no_types) foldl_step qes_def rev.simps(2) seq_def seq_mult seq_singleton skd.mult_assoc)

lemmas zip_left = zip_right[symmetric]

lemma zip_comm: "x\<cdot>y = y\<cdot>x \<Longrightarrow> qes (x#xs) \<cdot> seq (y#ys) = qes (y#xs) \<cdot> seq (x#ys)"
  by (metis (no_types) qes_def rev.simps(2) seq_mult seq_singleton skd.mult_assoc zip_left)

lemma unzip: "qes xs \<cdot> seq ys = seq (rev xs @ ys)"
  by (metis qes_def seq_mult)

ML {*
fun unzip_tac ctxt n =
  EqSubst.eqsubst_tac ctxt [0] @{thms unzip} n
  THEN simp_tac (HOL_basic_ss addsimps @{thms rev.simps append.simps}) n
*}

method_setup unzip = {*
Scan.succeed (fn ctxt => unzip_tac ctxt |> SIMPLE_METHOD')
*}

ML {*
fun NTIMES 0 _ = all_tac
  | NTIMES n tac = tac THEN (NTIMES (n - 1) tac)

fun commr_tac s c m = Subgoal.FOCUS (fn {context, ...} =>
  let
    val move_right_tac = EVERY
      [ EqSubst.eqsubst_tac context [0] @{thms zip_comm} 1
      , skat_comm_tac simp_solver context 1
      , EqSubst.eqsubst_tac context [0] @{thms zip_left} 1
      ]
  in
    DETERM (zip_tac s c context 1)
    THEN (if m = 0
          then (CHANGED (REPEAT move_right_tac))
          else (NTIMES m move_right_tac))
    THEN unzip_tac context 1
    THEN seq_deselect_tac 1
  end)
*}

method_setup commr1 = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat -- Scan.lift (Scan.optional Parse.nat 0) >>
  (fn ((s, c), m) => fn ctxt => SIMPLE_METHOD' (commr_tac s c m ctxt))
*}

method_setup comml1 = {*
Scan.lift Parse.nat  -- Scan.lift Parse.nat -- Scan.lift (Scan.optional Parse.nat 0) >>
  (fn ((s, c), m) => fn ctxt =>
    let
      val move_left_tac = EVERY
        [ EqSubst.eqsubst_tac ctxt [0] @{thms zip_comm} 1
        , skat_comm_tac simp_solver ctxt 1
        , EqSubst.eqsubst_tac ctxt [0] @{thms zip_right} 1
        ]
    in
      DETERM (zip_tac s (c - 1) ctxt 1)
      THEN (if m = 0
            then (CHANGED (REPEAT move_left_tac))
            else (NTIMES m move_left_tac))
      THEN unzip_tac ctxt 1
      THEN seq_deselect_tac 1
      |> SIMPLE_METHOD
    end)
*}

inductive comms :: "'a::ranked_alphabet skat \<Rightarrow> 'a skat list \<Rightarrow> bool" where
  comms_nil: "comms x []"
| comms_cons: "\<lbrakk>x\<cdot>y = y\<cdot>x; comms x ys\<rbrakk> \<Longrightarrow> comms x (y#ys)"

lemma comms_comm: "comms x xs \<Longrightarrow> x \<cdot> seq xs = seq xs \<cdot> x"
  apply (induct xs)
  apply (metis foldl_step seq_def seq_singleton skd.mult_onel)
  by (metis (hide_lams, no_types) comms.simps foldl_step list.inject list.simps(3) seq_def skd.mult_assoc)

lemma break: "i < length xs \<Longrightarrow> xs = take i xs @ xs ! i # tl (drop i xs)"
  apply (induct xs arbitrary: i)
  apply simp
  apply auto
  by (metis add_0_right add_Suc_right append_take_drop_id list.size(4) nth_drop' tl.simps(2))

lemma comm_step:
  assumes
  "\<exists>i. nth ys i = x \<and> i < length ys \<and> comms x (take i ys) \<and> seq xs = seq (take i ys @ tl (drop i ys))"
  shows "seq (x#xs) = seq ys"
proof -
  obtain i where asm1: "ys ! i = x"
  and asm2: "i < length ys"
  and asm3: "comms x (take i ys)"
  and asm4: "seq xs = seq (take i ys @ tl (drop i ys))"
    by (metis assms)

  have "seq (x#xs) = x \<cdot> seq xs"
    by (metis append_Cons append_Nil seq_mult seq_singleton)
  also have "... = x \<cdot> seq (take i ys @ tl (drop i ys))"
    by (metis asm4)
  also have "... = x \<cdot> seq (take i ys) \<cdot> seq (tl (drop i ys))"
    by (metis append_Cons append_Nil seq_mult seq_singleton asm4)
  also have "... = seq (take i ys) \<cdot> x \<cdot> seq (tl (drop i ys))"
    by (metis comms_comm asm3)
  also have "... = seq (take i ys) \<cdot> ys ! i \<cdot> seq (tl (drop i ys))"
    by (metis asm1)
  also have "... = seq (take i ys @ [ys ! i] @ tl (drop i ys))"
    by (metis (lifting) append_assoc seq_mult seq_singleton)
  also have "... = seq ys"
    by (metis (lifting) append_Cons append_self_conv2 break asm2)
  finally show ?thesis .
qed

ML {*
fun seq_comm_step_tac ctxt n =
  rtac @{thm conjI} n THEN simp_tac (simpset_of ctxt) n
  THEN rtac @{thm conjI} n THEN simp_tac (simpset_of ctxt) n
  THEN REPEAT (rtac @{thm comms_cons} n THEN skat_comm_tac simp_solver ctxt n)
  THEN rtac @{thm comms_nil} n
  THEN simp_tac (simpset_of ctxt) n

fun destroy [] = (fn x => x)
  | destroy (f::fs) = f o Thm.dest_comb #> destroy fs

fun safe_dest_comb ctrm = SOME (Thm.dest_comb ctrm)
  handle CTERM _ => NONE

fun safe_destroy [] ctrm = SOME ctrm
  | safe_destroy (f::fs) ctrm =
    case (safe_dest_comb ctrm) of
      NONE => NONE
    | SOME x => safe_destroy fs (f x);

fun ml_list ctrm =
  case (safe_destroy [fst, snd] ctrm) of
    NONE => []
  | SOME x => x :: ml_list (destroy [snd] ctrm);

fun find_index _ [] = 0
  | find_index x (y::ys) =
    (if x aconvc y then 0 else 1 + find_index x ys)

fun seq_comm_get_index concl =
  let
    val ys = concl |> destroy [snd, snd, snd] |> ml_list
    val xs = concl |> destroy [snd, fst, snd, snd] |> ml_list
  in
    find_index (hd xs) ys
  end

val seq_comm1_tac = Subgoal.FOCUS (fn {concl, context, ...} =>
  let
    val index = nat_cterm (seq_comm_get_index concl)
    val exI_index = Drule.instantiate' [SOME @{ctyp "nat"}] [NONE, SOME index] @{thm exI}
  in
    EVERY [rtac @{thm comm_step} 1, rtac exI_index 1, seq_comm_step_tac context 1]
    ORELSE commr_tac 1 1 0 context 1
  end
  handle CTERM _ => no_tac)

val seq_comm_tac = Subgoal.FOCUS (fn {context, ...} =>
  REPEAT1 (seq_comm1_tac context 1))
*}

method_setup seq_comm = {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (seq_comm_tac ctxt)) *}

lemma seq_cong: "seq xs = seq ys \<Longrightarrow> seq (x#xs) = seq (x#ys)"
  by (skat_simp, metis SKAT_Tactics.mult_onel foldl_Cons foldl_step)

lemma qes_cong: "qes xs = qes ys \<Longrightarrow> qes (x#xs) = qes (x#ys)"
  by skat_simp

method_setup cong = {*
Scan.succeed (fn ctxt =>
  REPEAT (rtac @{thm seq_cong} 1)
  THEN simp_tac (HOL_basic_ss addsimps @{thms seq_to_qes rev.simps append.simps}) 1
  THEN REPEAT (rtac @{thm qes_cong} 1)
  THEN simp_tac (HOL_basic_ss addsimps @{thms qes_def rev.simps append.simps}) 1
  |> CHANGED |> SIMPLE_METHOD)
*}

method_setup congl = {*
Scan.succeed (fn ctxt =>
  REPEAT (rtac @{thm seq_cong} 1) |> CHANGED |> SIMPLE_METHOD)
*}

method_setup congr = {*
Scan.succeed (fn ctxt =>
  simp_tac (HOL_basic_ss addsimps @{thms seq_to_qes rev.simps append.simps}) 1
  THEN (REPEAT (rtac @{thm qes_cong} 1))
  THEN simp_tac (HOL_basic_ss addsimps @{thms qes_def rev.simps append.simps}) 1
  |> CHANGED |> SIMPLE_METHOD)
*}

lemma seq_head_eq [intro]: "\<lbrakk>x = y; seq xs = seq ys\<rbrakk> \<Longrightarrow> seq (x#xs) = seq (y#ys)"
  by (metis seq_cong)

lemma seq_head_plus [intro]: "seq xs = seq ys + seq zs \<Longrightarrow> seq (x#xs) = seq (x#ys) + seq (x#zs)"
  by (metis append_Cons eq_Nil_appendI seq_mult skd.distl)

lemma seq_head_elim [simp,elim]: "x \<in> carrier tests \<Longrightarrow> seq (x#xs) + seq (!x#xs) = seq xs"
proof -
  assume "x \<in> carrier tests"
  hence "(x + !x) \<cdot> seq xs = seq xs"
    by (metis complement_one skd.mult_onel)
  hence "x \<cdot> seq xs + !x \<cdot> seq xs = seq xs"
    by (metis skd.distr)
  thus ?thesis
    by (metis append_Cons append_Nil seq_mult seq_singleton)
qed

lemma seq_head_elim_var [simp,elim]: "x \<in> carrier tests \<Longrightarrow> seq (!x#xs) + seq (x#xs) = seq xs"
  by (metis seq_head_elim skd.add_comm)

lemma zip_zero: "x\<cdot>y = \<zero> \<Longrightarrow> qes (x#xs) \<cdot> seq (y#ys) = \<zero>"
  by (metis fold_Cons_rev foldl_step seq_def skd.mult_assoc skd.mult_zerol skd.mult_zeror zip_left)

lemma zip_zero1: "x \<in> carrier tests \<Longrightarrow> qes (x#xs) \<cdot> seq (!x#ys) = \<zero>"
  by (metis complement_zero foldl_step seq_def skd.mult_assoc skd.mult_zerol skd.mult_zeror zip_left)

lemma zip_zero2: "x \<in> carrier tests \<Longrightarrow> qes (!x#xs) \<cdot> seq (x#ys) = \<zero>"
  by (metis not_closed skt.test_mult_comm zip_comm zip_zero1)

lemma zippify: "seq xs \<cdot> seq ys = qes (rev xs) \<cdot> seq ys"
  by (simp add: qes_def)

method_setup zero = {*
Scan.succeed (fn ctxt =>
  EqSubst.eqsubst_tac ctxt [0] @{thms zippify} 1
  THEN simp_tac (HOL_basic_ss addsimps @{thms rev.simps append.simps}) 1
  THEN EqSubst.eqsubst_tac ctxt [0] @{thms zip_zero1 zip_zero2} 1
  |> SIMPLE_METHOD)
*}

lemma seq_cons: "seq (x#xs) = x \<cdot> seq xs"
  by (metis foldl_step seq_def)

lemma qes_snoc: "qes (x#xs) = qes xs \<cdot> x"
  by (simp add: qes_def seq_mult)

lemma seq_empty [simp]: "seq [] = \<one>" by skat_reduce
lemma qes_empty [simp]: "qes [] = \<one>" by skat_reduce

end
