theory apply_tree
  imports Main fix_handle
begin

(* User Program *)

datatype op =
  OGetBlobData nat
  | OGetTreeData nat nat
  | OCreateBlob nat
  | OCreateTree "nat list"
  | OCreateThunk nat
  | OCreateEncode nat
  | ORunInternal
  | OReturn nat

record state =
  hs :: "handle list"
  ds :: "raw list"

type_synonym userprog = "op list"

consts get_prog :: "raw \<Rightarrow> userprog"

(* User program state helper *)

definition hpush :: "state \<Rightarrow> handle \<Rightarrow> state" where
  "hpush s h \<equiv> s \<lparr>hs := h # hs s\<rparr>"

definition dpush :: "state \<Rightarrow> raw \<Rightarrow> state" where
  "dpush s d \<equiv> s \<lparr>ds := d # ds s\<rparr>"

(* Deterministic internal procedure: operates on the 
 * list of available data *)

consts internal :: "raw list \<Rightarrow> raw list"
definition run_internal :: "state \<Rightarrow> state" where
  "run_internal s \<equiv> s \<lparr>ds := internal (ds s)\<rparr>"

lemma run_internal_hs[simp]: "hs (run_internal s) = hs s"
  by (simp add: run_internal_def)

lemma run_internal_ds_equiv:
  assumes "ds s1 = ds s2"
  shows "ds (run_internal s1) = ds (run_internal s2)"
  using assms by (simp add: run_internal_def)

(* Step semantics *)

datatype step_result =
  Continue state
  | Return handle

fun step :: "op \<Rightarrow> state \<Rightarrow> step_result option" where
  "step (OGetBlobData i) s = 
      (if i < length (hs s) then
         (case (hs s ! i) of
          HBlobHandle b \<Rightarrow> Some (Continue (dpush s (get_blob_data b)))
        | _ \<Rightarrow> None)
       else None)"
| "step (OGetTreeData i j) s =
      (if i < length (hs s) then
         (case (hs s ! i) of
          HTreeHandle t \<Rightarrow> (if (j < get_tree_size t) 
                            then Some (Continue (hpush s (get_tree_data t j))) 
                            else None)
          | _ \<Rightarrow> None)
       else None)"
| "step (OCreateBlob i) s =
      (if i < length (ds s) then
         Some (Continue (hpush s (HBlobHandle (create_blob (ds s ! i)))))
       else None)"
| "step (OCreateThunk i) s =
      (if i < length (hs s) then
         case (hs s ! i) of
         HTreeHandle t \<Rightarrow> Some (Continue (hpush s (HThunkHandle (create_thunk t))))
         | _ \<Rightarrow> None
       else None)"
| "step (OCreateTree xs) s =
      (if (\<forall>i\<in>set xs. i < length (hs s)) then
        (let hlist = map (\<lambda>i. hs s ! i) xs in
         Some (Continue (hpush s (HTreeHandle (create_tree hlist)))))
      else None)"
| "step (OCreateEncode i) s =
      (if i < length (hs s) then
         case (hs s ! i) of
         HThunkHandle t \<Rightarrow> Some (Continue (hpush s (HEncodeHandle (create_encode t))))
         | _ \<Rightarrow> None
      else None)"
| "step (OReturn i) s =
      (if i < length (hs s) then Some (Return (hs s ! i)) else None)"
| "step (ORunInternal) s = Some (Continue (run_internal s))"

fun exec :: "userprog \<Rightarrow> state \<Rightarrow> handle option"
  where
    "exec [] s = None"
  | "exec (i # xs) s =
   (case (step i s) of
   None \<Rightarrow> None
   | Some (Return r) \<Rightarrow> Some r
   | Some (Continue s') \<Rightarrow> exec xs s')"

(* Application Thunk evaluation *)
definition state_init :: "TreeHandle \<Rightarrow> state" where
  "state_init tree \<equiv> \<lparr> hs = [HTreeHandle tree], ds = [] \<rparr>"

definition get_tree_prog :: "TreeHandle \<Rightarrow> userprog option" where
  "get_tree_prog tree \<equiv> if (get_tree_size tree > 0) then
                   (case (get_tree_data tree 0) of
                     HBlobHandle b \<Rightarrow> Some (get_prog (get_blob_data b))
                   | _ \<Rightarrow> None)
                   else None"

definition apply_tree :: "TreeHandle \<Rightarrow> handle option" where
  "apply_tree tree \<equiv> case (get_tree_prog tree) of
                      Some prog \<Rightarrow> exec prog (state_init tree)
                    | _ \<Rightarrow> None"

fun rel_opt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "rel_opt X None None = True"
| "rel_opt X (Some h1) (Some h2) = X h1 h2"
| "rel_opt X _ _ = False"

(*We call two program states related by X if each handle in the handle lists are pair-wise X
 *and each data in the data lists is pair-wise equal*)
definition rel_state :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "rel_state X s1 s2 \<equiv>
     list_all2 (\<lambda>h1 h2. X h1 h2) (hs s1) (hs s2) \<and> ds s1 = ds s2"

(*We call two step results equivalent if either they step to equivalent states or they returns
 *eq handles*)

definition rel_step :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> step_result \<Rightarrow> step_result \<Rightarrow> bool" where
  "rel_step X x1 x2 \<equiv>
   case (x1, x2) of
   (Continue s1, Continue s2) \<Rightarrow> rel_state X s1 s2
  |(Return r1, Return r2) \<Rightarrow> X r1 r2
  | _ \<Rightarrow> False"

definition rel_step_result :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> step_result option \<Rightarrow> step_result option \<Rightarrow> bool" where
  "rel_step_result X r1 r2 \<equiv> rel_opt (rel_step X) r1 r2"

(* 1. Useful lemmas for operations on two states that are equivalent *)

lemma list_all2_append:
  assumes "list_all2 P xs ys"
    and "P x y"
  shows   "list_all2 P (xs @ [x]) (ys @ [y])"
  using assms
  by (induction arbitrary: x y rule: list_all2_induct) simp_all

lemma rel_state_hpush:
  assumes "rel_state X s1 s2" and "X h1 h2"
  shows "rel_state X (hpush s1 h1) (hpush s2 h2)"
  using assms unfolding rel_state_def hpush_def
  by (auto simp: list_all2_append)

lemma rel_state_hpush_self:
  assumes "\<And> x. X x x"
  assumes "rel_state X s1 s2"
  shows "rel_state X (hpush s1 h) (hpush s2 h)"
  using assms
proof -
  have "X h h" using assms(1) by auto
  then show ?thesis using rel_state_hpush assms by blast
qed

lemma rel_dpush:
  assumes "rel_state X s1 s2" and "d1 = d2"
  shows "rel_state X (dpush s1 d1) (dpush s2 d2)"
  using assms unfolding rel_state_def dpush_def by auto

lemma rel_state_hs:
  "rel_state X s1 s2 \<Longrightarrow> list_all2 (\<lambda>h1 h2. X h1 h2) (hs s1) (hs s2)"
  by (simp add: rel_state_def)

lemma rel_state_ds:
  "rel_state X s1 s2 \<Longrightarrow> (ds s1) = (ds s2)"
  by (simp add: rel_state_def)

lemma rel_state_hs_same_length:
  assumes "rel_state X s1 s2"
  shows "length (hs s1) = length (hs s2)"
  using rel_state_hs[OF assms]
  by (simp add: list_all2_lengthD)

lemma rel_state_hs_nth:
  assumes "rel_state X s1 s2" "i < length (hs s1)"
  shows "X ((hs s1) ! i) ((hs s2)! i) \<and> i < length (hs s2)"
  using rel_state_hs[OF assms(1)] assms(2)
  by (simp add: list_all2_conv_all_nth)

lemma create_tree_same_typed: 
  assumes "list_all2 same_typed_handle xs ys"
  shows "same_typed_handle (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
  using assms by force

lemma get_tree_same_typed: 
  assumes "same_typed_handle (HTreeHandle t1) (HTreeHandle t2)"
  assumes "i < length (get_tree_raw t1)"
  shows "same_typed_handle (get_tree_data t1 i) (get_tree_data t2 i)"
  by (metis assms(1,2) get_tree_data_def handle.distinct(1,7,9) handle.inject(2) list_all2_nthD same_typed_handle.cases same_typed_tree.cases)

lemma step_X:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes get_blob_data_cong: "\<And>b1 b2. X (HBlobHandle b1) (HBlobHandle b2) 
                               \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes get_tree_size_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2)
                               \<Longrightarrow> get_tree_size t1 = get_tree_size t2"
  assumes get_tree_data_cong: "\<And>t1 t2 j. X (HTreeHandle t1) (HTreeHandle t2)
                               \<Longrightarrow> j < get_tree_size t1
                               \<Longrightarrow> X (get_tree_data t1 j) (get_tree_data t2 j)"
  assumes create_blob_cong: "\<And>d1 d2. d1 = d2
                             \<Longrightarrow> X (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
  assumes create_tree_cong: "\<And>xs ys. list_all2 X xs ys
                             \<Longrightarrow> X (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
  assumes create_encode_cong: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2)
                               \<Longrightarrow> X (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"
  assumes create_thunk_cong: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes S: "rel_state X s1 s2 \<and> rel_state same_typed_handle s1 s2"
  shows   "rel_step_result X (step op s1) (step op s2) \<and> rel_step_result same_typed_handle (step op s1) (step op s2)"
proof -
  have L: "length (hs s1) = length (hs s2)" 
    using rel_state_hs_same_length S
    by blast
  have D: "(ds s1) = (ds s2)" using rel_state_ds S by blast

  show ?thesis
  proof (cases op)
    case (OGetBlobData i)
      then show ?thesis 
      proof (cases "i < length (hs s1)")
        case False
        then show ?thesis using OGetBlobData False L rel_step_result_def by auto
      next
        case True
        have rel: "X (hs s1 ! i) (hs s2 ! i)" 
          using S rel_state_hs_nth True by auto
        have same_type: "same_typed_handle (hs s1 ! i) (hs s2 ! i)"
          using S rel_state_hs_nth True by auto
        then show ?thesis
          using get_blob_data_cong rel OGetBlobData True L S rel_dpush rel_step_result_def rel_step_def
          by (cases "(hs s1 ! i)") auto
      qed
   next
    case (OCreateBlob i)
    then show ?thesis
    proof (cases "i < length (ds s1)")
      case True
      then have EQD: "ds s1 ! i = ds s2 ! i" using D by simp
      then show ?thesis 
        using OCreateBlob True S create_blob_cong EQD rel_step_result_def D rel_state_hpush rel_step_def same_typed_tree_same_typed_handle.blob_handle by auto
    next
      case False
      then show ?thesis using OCreateBlob D rel_step_result_def by auto
    qed
  next
    case (OGetTreeData i j)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      have rel: "X (hs s1 ! i) (hs s2 ! i)" 
        using S rel_state_hs_nth True by auto
      have same_type: "same_typed_handle (hs s1 ! i) (hs s2 ! i)"
        using S rel_state_hs_nth True by auto
      then show ?thesis
      proof (cases "(hs s1 ! i)")
        case (blob_handle b1 b2)
        then show ?thesis 
          using rel_step_result_def OGetTreeData by simp
      next 
        case (thunk_handle t1 t2)
        then show ?thesis 
          using rel_step_result_def OGetTreeData by simp
      next
        case (encode_handle e1 e2)
        then show ?thesis
          using rel_step_result_def OGetTreeData by simp
      next
        case (tree_handle t1 t2)
        then show ?thesis
        proof -
          consider (True') "j < get_tree_size t1"
            |      (False') "\<not> j < get_tree_size t1"
            by blast
          then show ?thesis
          proof cases
            case True'
            have 1: "X (get_tree_data t1 j) (get_tree_data t2 j)"
              using get_tree_data_cong rel True' tree_handle by auto
            have 2: "same_typed_handle (get_tree_data t1 j) (get_tree_data t2 j)"
              using get_tree_same_typed rel True' tree_handle same_type get_tree_size_def by auto
            show ?thesis
              using  rel_step_result_def OGetTreeData True' True tree_handle get_tree_size_cong L rel rel_state_hpush S           1 2 rel_step_def
              by simp
          next
            case False'
            then show ?thesis
              using OGetTreeData True False' L tree_handle rel_step_result_def rel get_tree_size_cong by auto
          qed
        qed
      qed
    next
      case False
      then show ?thesis using OGetTreeData L rel_step_result_def by auto
    qed
  next
    case (OCreateThunk i)
      then show ?thesis 
      proof (cases "i < length (hs s1)")
        case False
        then show ?thesis 
          using OCreateThunk False L rel_step_result_def by auto
      next
        case True
        have rel: "X (hs s1 ! i) (hs s2 ! i)" 
          using S rel_state_hs_nth True by auto
        have same_type: "same_typed_handle (hs s1 ! i) (hs s2 ! i)"
          using S rel_state_hs_nth True by auto
        then show ?thesis
          using create_thunk_cong rel OCreateThunk True L S rel_state_hpush rel_step_result_def rel_step_def same_typed_tree_same_typed_handle.thunk_handle
          by (cases "(hs s1 ! i)") auto
      qed
  next
    case (OCreateEncode i)
      then show ?thesis 
      proof (cases "i < length (hs s1)")
        case False
        then show ?thesis 
          using OCreateEncode False L rel_step_result_def by auto
      next
        case True
        have rel: "X (hs s1 ! i) (hs s2 ! i)" 
          using S rel_state_hs_nth True by auto
        have same_type: "same_typed_handle (hs s1 ! i) (hs s2 ! i)"
          using S rel_state_hs_nth True by auto
        then show ?thesis
          using create_encode_cong rel OCreateEncode True L S rel_state_hpush rel_step_result_def rel_step_def same_typed_tree_same_typed_handle.encode_handle
          by (cases "(hs s1 ! i)") auto
      qed
  next
    case (OCreateTree xs)
  then show ?thesis
    proof (cases "\<forall>i \<in> set xs. i < length (hs s1)")
      case True
      let ?hlist1 = "map (\<lambda>i. hs s1 ! i) xs"
      let ?hlist2 = "map (\<lambda>i. hs s2 ! i) xs"

      have "list_all2 X ?hlist1 ?hlist2"
      proof -
        have "\<forall>i \<in> set xs. X (hs s1 ! i) (hs s2 ! i)"
          using True L rel_state_hs_nth S
          by blast
        then show ?thesis by (induction xs) auto
      qed
      then have "X (HTreeHandle (create_tree ?hlist1)) (HTreeHandle (create_tree ?hlist2))"
        using create_tree_cong by auto

      moreover have "list_all2 same_typed_handle ?hlist1 ?hlist2"
      proof -
        have "\<forall>i \<in> set xs. same_typed_handle (hs s1 ! i) (hs s2 ! i)"
          using True L rel_state_hs_nth S
          by blast
        then show ?thesis by (induction xs) auto
      qed
      then have "same_typed_handle (HTreeHandle (create_tree ?hlist1)) (HTreeHandle (create_tree ?hlist2))"
        using create_tree_same_typed by auto

      ultimately show ?thesis using OCreateTree True L assms rel_state_hpush rel_step_result_def rel_step_def by auto
    next
      case False
      then show ?thesis using OCreateTree L rel_step_result_def by auto
    qed
  next
    case (ORunInternal)
    show ?thesis using ORunInternal rel_step_result_def rel_state_def assms run_internal_def rel_step_def by auto
  next
    case (OReturn i)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      have rel: "X (hs s1 ! i) (hs s2 ! i)" 
        using S rel_state_hs_nth True by auto
      have same_type: "same_typed_handle (hs s1 ! i) (hs s2 ! i)"
        using S rel_state_hs_nth True by auto
      then show ?thesis 
        using OReturn True L rel_step_result_def rel_state_hs_nth S rel rel_step_def by auto
    next
      case False
      then show ?thesis using OReturn L rel_step_result_def by auto
    qed
  qed
qed

lemma exec_X:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes get_blob_data_cong: "\<And>b1 b2. X (HBlobHandle b1) (HBlobHandle b2) 
                               \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes get_tree_size_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2)
                               \<Longrightarrow> get_tree_size t1 = get_tree_size t2"
  assumes get_tree_data_cong: "\<And>t1 t2 j. X (HTreeHandle t1) (HTreeHandle t2)
                               \<Longrightarrow> j < get_tree_size t1
                               \<Longrightarrow> X (get_tree_data t1 j) (get_tree_data t2 j)"
  assumes create_blob_cong: "\<And>d1 d2. d1 = d2
                             \<Longrightarrow> X (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
  assumes create_tree_cong: "\<And>xs ys. list_all2 X xs ys
                             \<Longrightarrow> X (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
  assumes create_encode_cong: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2)
                               \<Longrightarrow> X (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"
  assumes create_thunk_cong: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  shows "rel_state X s1 s2 \<and> rel_state same_typed_handle s1 s2 \<Longrightarrow> rel_opt X (exec p s1) (exec p s2) \<and> rel_opt same_typed_handle (exec p s1) (exec p s2)"
proof (induction p arbitrary: s1 s2)
  case Nil
  then show ?case by auto
next
  case (Cons i xs)
  assume S: "rel_state X s1 s2 \<and> rel_state same_typed_handle s1 s2"
  show "rel_opt X (exec (i # xs) s1) (exec (i # xs) s2) \<and> rel_opt same_typed_handle (exec (i # xs) s1) (exec (i # xs) s2)"
  proof (cases "step i s1")
    case None
    then show ?thesis 
      using step_X[OF assms S] Cons rel_step_result_def rel_step_def
      by (metis (lifting) exec.simps(2) option.simps(4) rel_opt.elims(2) rel_opt.simps(1,4))
  next
    case (Some r1)
    then obtain r2 where Some': "step i s2 = Some r2"
                     and rel_step: "rel_step X r1 r2"
                     and rel_same_typed: "rel_step same_typed_handle r1 r2"
      using step_X[OF assms S] rel_step_result_def 
      by (metis option.exhaust rel_opt.simps(2,3))

    show ?thesis
    proof (cases r1)
      case (Continue x1)
      then obtain x2 where "rel_state X x1 x2"
                       and "rel_state same_typed_handle x1 x2"
                       and Continue': "r2 = Continue x2"
        using rel_step rel_same_typed
        by (metis (no_types, lifting) old.prod.case rel_step_def step_result.exhaust step_result.simps(5,6))

      then have "rel_opt X (exec xs x1) (exec xs x2) \<and> rel_opt same_typed_handle (exec xs x1) (exec xs x2)"
        using Cons.IH[of x1 x2]
        by simp

      then show ?thesis 
        using Cons Some Continue Some' Continue' by auto
    next
      case (Return x1)
      then obtain x2 where Return': "r2 = Return x2"
                       and "X x1 x2" 
                       and "same_typed_handle x1 x2"
        using rel_step rel_same_typed
        by (metis (no_types, lifting) old.prod.case rel_step_def step_result.exhaust step_result.simps(5,6))

      then show ?thesis
        using Cons Some Return Some' Return' by auto
    qed
  qed
qed

lemma state_init_X:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes "X (HTreeHandle t1) (HTreeHandle t2) \<and> same_typed_handle (HTreeHandle t1) (HTreeHandle t2)"
  shows "rel_state X (state_init t1) (state_init t2) \<and> rel_state same_typed_handle (state_init t1) (state_init t2)"
  using assms
  unfolding state_init_def rel_state_def
  by simp

lemma get_prog_X:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes get_blob_data_cong: "\<And>b1 b2. X (HBlobHandle b1) (HBlobHandle b2) 
                               \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes get_tree_size_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2)
                               \<Longrightarrow> get_tree_size t1 = get_tree_size t2"
  assumes get_tree_data_cong: "\<And>t1 t2 j. X (HTreeHandle t1) (HTreeHandle t2)
                               \<Longrightarrow> j < get_tree_size t1
                               \<Longrightarrow> X (get_tree_data t1 j) (get_tree_data t2 j)"
  assumes H: "X (HTreeHandle t1) (HTreeHandle t2) \<and> same_typed_handle (HTreeHandle t1) (HTreeHandle t2)"
  shows "rel_opt (\<lambda>t1 t2. t1 = t2) (get_tree_prog t1) (get_tree_prog t2)"
proof (cases "0 < get_tree_size t1")
  case False
  then have "0 = get_tree_size t1" and "0 = get_tree_size t2"
    using get_tree_size_cong H
    by auto
  then show ?thesis
    unfolding get_tree_prog_def
    by simp
next
  case True
  then have True': "0 < get_tree_size t2"
    using get_tree_size_cong H
    by auto

  have rel: "X (get_tree_data t1 0) (get_tree_data t2 0)"
    using get_tree_data_cong True True' H by auto
  have "same_typed_handle (get_tree_data t1 0) (get_tree_data t2 0)"
    using True True' H get_tree_same_typed get_tree_size_def by auto

  then show ?thesis
  proof (cases "get_tree_data t1 0")
    case encode_handle
    then show ?thesis unfolding get_tree_prog_def using True True' by auto
  next
    case thunk_handle
    then show ?thesis unfolding get_tree_prog_def using True True' by auto
  next
    case tree_handle
    then show ?thesis unfolding get_tree_prog_def using True True' by auto
  next
    case (blob_handle b1 b2)
    then show ?thesis
      using rel get_blob_data_cong True True'
      unfolding get_tree_prog_def
      by auto
  qed
qed

lemma apply_tree_X:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes get_blob_data_cong: "\<And>b1 b2. X (HBlobHandle b1) (HBlobHandle b2) 
                               \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes get_tree_size_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2)
                               \<Longrightarrow> get_tree_size t1 = get_tree_size t2"
  assumes get_tree_data_cong: "\<And>t1 t2 j. X (HTreeHandle t1) (HTreeHandle t2)
                               \<Longrightarrow> j < get_tree_size t1
                               \<Longrightarrow> X (get_tree_data t1 j) (get_tree_data t2 j)"
  assumes create_blob_cong: "\<And>d1 d2. d1 = d2
                             \<Longrightarrow> X (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
  assumes create_tree_cong: "\<And>xs ys. list_all2 X xs ys
                             \<Longrightarrow> X (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
  assumes create_encode_cong: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2)
                               \<Longrightarrow> X (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"
  assumes create_thunk_cong: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes H: "X (HTreeHandle t1) (HTreeHandle t2) \<and> same_typed_handle (HTreeHandle t1) (HTreeHandle t2)"
  shows "rel_opt X (apply_tree t1) (apply_tree t2) \<and> rel_opt same_typed_handle (apply_tree t1) (apply_tree t2)"
proof (cases "get_tree_prog t1")
  case None
  then have "get_tree_prog t2 = None"
    using get_prog_X[of X t1 t2, OF get_blob_data_cong get_tree_size_cong get_tree_data_cong H]
    using rel_opt.elims(2) by auto

  then show ?thesis unfolding apply_tree_def
    using None by auto
next
  case (Some p1)
  then obtain p2 where "get_tree_prog t2 = Some p2"
                   and "p1 = p2"
    using get_prog_X[of X t1 t2, OF get_blob_data_cong get_tree_size_cong get_tree_data_cong H]
    using rel_opt.elims(2) by fastforce

  then show ?thesis
    using exec_X[of X "state_init t1" "state_init t2", OF get_blob_data_cong get_tree_size_cong get_tree_data_cong create_blob_cong create_tree_cong create_encode_cong create_thunk_cong state_init_X[of X t1 t2, OF H]] Some
    unfolding apply_tree_def 
    by simp
qed

end

