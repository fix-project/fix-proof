theory eqqqnew
  imports Main
begin

typedecl BlobHandle
typedecl TreeHandle
datatype ThunkHandle = HThunkHandle TreeHandle
datatype EncodeHandle = HEncodeHandle ThunkHandle

datatype handle = 
  HBlobHandle BlobHandle
  | HTreeHandle TreeHandle
  | HThunkHandle ThunkHandle
  | HEncodeHandle EncodeHandle

typedecl raw
type_synonym BlobData = "raw"
type_synonym TreeData = "handle list"

(* Fixpoint APIs *)

consts 
  get_blob_data :: "BlobHandle \<Rightarrow> BlobData"
  get_tree_raw :: "TreeHandle \<Rightarrow> handle list"
  get_thunk_tree :: "ThunkHandle \<Rightarrow> TreeHandle"
  get_encode_thunk :: "EncodeHandle \<Rightarrow> ThunkHandle"

create_blob :: "BlobData \<Rightarrow> BlobHandle"
create_tree :: "TreeData \<Rightarrow> TreeHandle"
create_thunk :: "TreeHandle \<Rightarrow> ThunkHandle"
create_encode :: "ThunkHandle \<Rightarrow> EncodeHandle"

definition get_tree_data :: "TreeHandle \<Rightarrow> nat \<Rightarrow> handle" where
  "get_tree_data t i \<equiv> (get_tree_raw t) ! i"

definition get_tree_size :: "TreeHandle \<Rightarrow> nat" where
  "get_tree_size t \<equiv> length (get_tree_raw t)"

(* Blob/Tree creation rules *)

axiomatization where
  get_blob_data_create_blob[simp]:
  "get_blob_data (create_blob x) = x"
  and
  get_tree_raw_create_tree[simp]:
  "get_tree_raw (create_tree xs) = xs"
  and
  create_tree_get_tree_raw[simp]:
  "create_tree (get_tree_raw tree) = tree"
  and
  get_thunk_tree_create_thunk[simp]:
  "get_thunk_tree (create_thunk th) = th"
  and
  create_thunk_get_thunk_tree[simp]:
  "create_thunk (get_thunk_tree t) = t"
  and
  create_encode_get_thunk_encode[simp]:
  "create_encode (get_encode_thunk e) = e"
  and
  get_thunk_encode_create_encode[simp]:
  "get_encode_thunk (create_encode thunk) = thunk"

fun get_type :: "handle \<Rightarrow> nat" where
  "get_type (HBlobHandle _ ) = 0"
| "get_type (HTreeHandle _ ) = 1"
| "get_type (HThunkHandle _ ) = 2"
| "get_type (HEncodeHandle _) = 3"

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

consts get_prog :: "TreeHandle \<Rightarrow> userprog"

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

(* Thunk evaluation *)

definition state_init :: "TreeHandle \<Rightarrow> state" where
  "state_init tree \<equiv> \<lparr> hs = [HTreeHandle tree], ds = [] \<rparr>"

definition apply_tree :: "TreeHandle \<Rightarrow> handle option" where
  "apply_tree tree \<equiv> exec (get_prog tree) (state_init tree)"

fun rel_opt :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> handle option \<Rightarrow> handle option \<Rightarrow> bool" where
  "rel_opt X None None = True"
| "rel_opt X (Some h1) (Some h2) = X h1 h2"
| "rel_opt X _ _ = False"

(*We call two program states equivalent if each handle in the handle lists are pair-wise eq
 *and each data in the data lists is pair-wise equal*)
definition rel_state :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "rel_state X s1 s2 \<equiv>
     list_all2 (\<lambda>h1 h2. X h1 h2) (hs s1) (hs s2) \<and> ds s1 = ds s2"

(*We call two step results equivalent if either they step to equivalent states or they returns
 *eq handles*)
definition rel_step_result :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> step_result option \<Rightarrow> step_result option \<Rightarrow> bool" where
  "rel_step_result X r1 r2 \<equiv> 
   (case (r1, r2) of
     (Some (Continue s1), Some (Continue s2)) \<Rightarrow> rel_state X s1 s2
   | (Some (Return r1), Some (Return r2)) \<Rightarrow>  X r1 r2
   | (None, None) \<Rightarrow> True
   | (_, _) \<Rightarrow> False)"

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

lemma step_fun_eq:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes S: "rel_state X s1 s2"
  shows   "rel_step_result X (step op s1) (step op s2)"
proof -
  have L: "length (hs s1) = length (hs s2)" using rel_state_hs_same_length[OF S] .
  have D: "(ds s1) = (ds s2)" using rel_state_ds[OF S] .

  show ?thesis
  proof (cases op)
    case (OGetBlobData i)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S rel_state_hs_nth by auto
      then show ?thesis
      proof (cases "(hs s1 ! i)")
        case (HBlobHandle b1)
        then obtain b2 where BLOB2: "hs s2 ! i = HBlobHandle b2" using EQ X_preserve_blob by auto
        then have EQD: "get_blob_data b1 = get_blob_data b2"
          using HBlobHandle get_blob_data_cong EQ by auto  
        have S1: "step op s1 = Some(Continue (dpush s1 (get_blob_data b1)))"
             and  S2: "step op s2 = Some(Continue (dpush s2 (get_blob_data b2)))"
          using OGetBlobData True L HBlobHandle BLOB2 by auto
        have "rel_state X (dpush s1 (get_blob_data b1)) (dpush s2 (get_blob_data b2))"
          using True HBlobHandle L S rel_dpush get_blob_data_cong EQ BLOB2
          by auto
        then show ?thesis using S1 S2 rel_step_result_def by auto
      next
        case (HTreeHandle t1)
        then obtain t2 where TREE2: "hs s2 ! i = HTreeHandle t2" using EQ X_preserve_tree by auto
        then show ?thesis using OGetBlobData HTreeHandle True rel_step_result_def by auto
      next
        case (HThunkHandle th1)
        then obtain th2 where "hs s2 ! i = HThunkHandle th2" using EQ X_preserve_thunk by auto
        then show ?thesis using OGetBlobData HThunkHandle True rel_step_result_def by auto
      next
        case (HEncodeHandle e1)
        then obtain e2 where "hs s2 ! i = HEncodeHandle e2" using EQ X_preserve_encode by auto
        then show ?thesis using OGetBlobData HEncodeHandle True rel_step_result_def by auto
      qed
    next
      case False
      then show ?thesis using OGetBlobData False L rel_step_result_def by auto
    qed
  next
    case (OGetTreeData i j)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S rel_state_hs_nth by auto
      then show ?thesis
      proof (cases "(hs s1 ! i)")
        case (HBlobHandle)
        then obtain b2 where BLOB2: "hs s2 ! i = HBlobHandle b2"
          using X_preserve_blob EQ by auto
        then show ?thesis using OGetTreeData True L HBlobHandle rel_step_result_def 
          by auto
      next
        case (HTreeHandle t1)
        then obtain t2 where TREE2: "hs s2 ! i = HTreeHandle t2" 
          using S X_preserve_tree EQ by auto
        then have EQN: "X (HTreeHandle t1) (HTreeHandle t2)"
          using HTreeHandle EQ by simp
        then show ?thesis
        proof -
          consider (True') "j < get_tree_size t1"
            | (False') "\<not> j < get_tree_size t1"
            by blast
          then show ?thesis
          proof cases
            case True'
            have EQCHILD: "X (get_tree_data t1 j) (get_tree_data t2 j)"
              using get_tree_data_cong[OF EQN True'] by auto
            then have EQRES: "rel_state X (hpush s1 (get_tree_data t1 j)) (hpush s2 (get_tree_data t2 j))"
              using S rel_state_hpush by auto

            have "j < get_tree_size t2" 
              using  True' EQN get_tree_size_cong
              by simp
            then have S2: "step op s2 = Some (Continue (hpush s2 (get_tree_data t2 j)))"
              using OGetTreeData TREE2 True L by auto

            have "step op s1 = Some (Continue (hpush s1 (get_tree_data t1 j)))"
              using OGetTreeData True True' HTreeHandle by auto
            then show ?thesis using S2 EQRES rel_step_result_def by auto
          next
            case False'
            then have "\<not> j < get_tree_size t2"
              using EQN get_tree_size_cong
              by simp
            then show ?thesis 
              using OGetTreeData True False' L HTreeHandle TREE2 rel_step_result_def by auto
          qed
        qed
      next
        case (HThunkHandle th1)
        then obtain th2 where "hs s2 ! i = HThunkHandle th2" using EQ X_preserve_thunk by auto
        then show ?thesis using OGetTreeData HThunkHandle True rel_step_result_def by auto
      next
        case (HEncodeHandle e1)
        then obtain e2 where "hs s2 ! i = HEncodeHandle e2" using EQ X_preserve_encode by auto
        then show ?thesis using OGetTreeData HEncodeHandle True rel_step_result_def by auto
      qed
    next
      case False
      then show ?thesis using OGetTreeData rel_step_result_def L by auto
    qed
  next
    case (OCreateBlob i)
    then show ?thesis
    proof (cases "i < length (ds s1)")
      case True
      then have EQD: "ds s1 ! i = ds s2 ! i" using D by simp
      then show ?thesis 
        using OCreateBlob True rel_state_hpush_self[OF X_self S] create_blob_cong[OF EQD] rel_step_result_def D by auto
    next
      case False
      then show ?thesis using OCreateBlob D rel_step_result_def by auto
    qed
  next
    case (OCreateThunk i)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S rel_state_hs_nth by auto
      then show ?thesis
      proof (cases "hs s1 ! i")
        case (HBlobHandle b1)
        then obtain b2 where BLOB2: "hs s2 ! i = HBlobHandle b2"
          using X_preserve_blob EQ by auto
        then show ?thesis using OCreateThunk True HBlobHandle  rel_step_result_def by auto
      next
        case (HTreeHandle t1)
        then obtain t2 where TREE2: "hs s2 ! i = HTreeHandle t2"
          using X_preserve_tree EQ by auto
        have "X (HTreeHandle t1) (HTreeHandle t2) "using EQ HTreeHandle TREE2 by simp
        then have "X (HTreeHandle (get_thunk_tree (create_thunk t1))) (HTreeHandle (get_thunk_tree (create_thunk t2)))"
          by simp

        then have "X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
          using X_tree_to_thunk by auto
        then show ?thesis 
          using OCreateThunk True HTreeHandle TREE2 S rel_state_hpush rel_step_result_def L by auto
      next
        case (HThunkHandle th1)
        then obtain th2 where "hs s2 ! i = HThunkHandle th2" using EQ X_preserve_thunk by auto
        then show ?thesis using OCreateThunk HThunkHandle rel_step_result_def by auto
      next
        case (HEncodeHandle e1)
        then obtain e2 where "hs s2 ! i = HEncodeHandle e2" using EQ X_preserve_encode by auto
        then show ?thesis using OCreateThunk HEncodeHandle True rel_step_result_def by auto
      qed
    next
      case False
      then show ?thesis using OCreateThunk L rel_step_result_def by auto
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
          using True L rel_state_hs_nth[OF S] by auto
        then show ?thesis by (induction xs) auto
      qed
      then have "list_all2 X (get_tree_raw (create_tree ?hlist1)) (get_tree_raw (create_tree ?hlist2))"
        by simp
      then have "X (HTreeHandle (create_tree ?hlist1)) (HTreeHandle (create_tree ?hlist2))"
        using create_tree_cong by auto
      then show ?thesis using OCreateTree True L assms rel_state_hpush rel_step_result_def by auto
    next
      case False
      then show ?thesis using OCreateTree L rel_step_result_def by auto
    qed
  next
    case (OCreateEncode i)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S rel_state_hs_nth by auto
      then show ?thesis
      proof (cases "hs s1 ! i")
        case (HBlobHandle b1)
        then obtain b2 where BLOB2: "hs s2 ! i = HBlobHandle b2"
          using X_preserve_blob EQ by auto
        then show ?thesis using OCreateEncode True HBlobHandle rel_step_result_def by auto
      next
        case (HTreeHandle t1)
        then obtain t2 where TREE2: "hs s2 ! i = HTreeHandle t2"
          using X_preserve_tree EQ by auto
        then show ?thesis using OCreateEncode True HTreeHandle rel_step_result_def by auto
      next
        case (HEncodeHandle e1)
        then obtain e2 where "hs s2 ! i = HEncodeHandle e2" using EQ X_preserve_encode by auto
        then show ?thesis using OCreateEncode HEncodeHandle rel_step_result_def by auto
      next
        case (HThunkHandle t1)
        then obtain t2 where Thunk2: "hs s2 ! i = HThunkHandle t2" using EQ X_preserve_thunk by auto
        
        have "X (HThunkHandle t1) (HThunkHandle t2) "using EQ HThunkHandle Thunk2 by simp
        then have "X (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"
          using create_encode_cong by auto
        then show ?thesis 
          using OCreateEncode True HThunkHandle Thunk2 S rel_state_hpush rel_step_result_def L by auto
      qed
    next
      case False
      then show ?thesis using OCreateEncode L rel_step_result_def by auto
    qed
  next
    case (ORunInternal)
    have "rel_state X (run_internal s1) (run_internal s2)"
      using assms run_internal_def rel_state_def by auto
    then show ?thesis using ORunInternal rel_step_result_def by auto
  next
    case (OReturn i)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S rel_state_hs_nth by auto
      then show ?thesis using OReturn True L rel_step_result_def by auto
    next
      case False
      then show ?thesis using OReturn L rel_step_result_def by auto
    qed
  qed
qed

corollary step_eq_none:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes S: "rel_state X s1 s2"
     and S1: "step op s1 = None"
   shows "step op s2 = None"
proof -
  have "rel_step_result X (step op s1) (step op s2)"
    using step_fun_eq assms by blast
  then show ?thesis using S1 using rel_step_result_def by (cases "step op s2") auto
qed

corollary step_eq_return:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes S: "rel_state X s1 s2"
    and S1: "step op s1 = Some (Return h1)"
  shows "\<exists>h2. step op s2 = Some (Return h2) \<and> X h1 h2"
proof -
  have H: "rel_step_result X (step op s1) (step op s2)"
    using step_fun_eq assms by blast
  then show ?thesis using assms(2) rel_step_result_def 
  proof (cases "step op s2")
    case None
    then show ?thesis using H rel_step_result_def S1 by auto
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Continue)
      then show ?thesis using H rel_step_result_def S1 Some by auto
    next
      case (Return x)
      then have "X h1 x" using H rel_step_result_def S1 Some by auto
      then have "step op s2 = Some (Return x) \<and> X h1 x"
        using Some Return by blast
      then show ?thesis by auto
    qed
  qed
qed

corollary step_eq_continue:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes S: "rel_state X s1 s2"
    and S1: "step op s1 = Some (Continue s1')"
  shows "\<exists>s2'. step op s2 = Some (Continue s2') \<and> rel_state X s1' s2'"
proof -
  have H: "rel_step_result X (step op s1) (step op s2)"
    using step_fun_eq assms by blast
  then show ?thesis using S rel_step_result_def 
  proof (cases "step op s2")
    case None
    then show ?thesis using H rel_step_result_def S1 by auto
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Return)
      then show ?thesis using H rel_step_result_def S1 Some by auto
    next
      case (Continue x)
      then have "rel_state X s1' x" using H rel_step_result_def S1 Some by auto
      then have "step op s2 = Some (Continue x) \<and> rel_state X s1' x"
        using Some Continue by blast
      then show ?thesis by auto 
    qed
  qed
qed

(* 5. Given eq_state s1 s2, and some program p, execing them either both returns None or returns
equivalent handles *)

lemma exec_eq:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  shows "rel_state X s1 s2 \<Longrightarrow> rel_opt X (exec p s1) (exec p s2)"
proof (induction p arbitrary: s1 s2)
  case Nil
  then show ?case by auto
next
  case (Cons i xs)
  assume S: "rel_state X s1 s2"

  show "rel_opt X (exec (i # xs) s1) (exec (i # xs) s2)"
  proof (cases "step i s1")
    case None
    have "step i s2 = None"
      using step_eq_none assms Cons.prems None by blast
    then show ?thesis using Cons None  by auto
  next
    case (Some a)
    then show ?thesis 
    proof (cases a)
      case (Continue s1')
      have S1: "step i s1 = Some (Continue s1')" using Some Continue by simp
      have Ex: "\<exists>s2'. step i s2 = Some (Continue s2') \<and> rel_state X s1' s2'"
        using step_eq_continue[OF assms S S1] by assumption
      then obtain s2' where S2: "step i s2 = Some (Continue s2')"
                        and EQ': "rel_state X s1' s2'"
        by auto
      have "rel_opt X (exec xs s1') (exec xs s2')"
        using Cons.IH EQ' by blast
      then show ?thesis using Cons Some Continue S2 by auto
    next
      case (Return h1)
      have S1: "step i s1 = Some (Return h1)" using Some Return by simp
      have Ex: "\<exists>h2. step i s2 = Some (Return h2) \<and>  X h1 h2"
        using step_eq_return[OF assms S S1] .
      then obtain h2 where S2: "step i s2 = Some (Return h2)"
                       and EQ': "X h1 h2"
        by auto
      then show ?thesis using Cons S1 by auto
    qed
  qed
qed
  
corollary exec_eq_some:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
      and S: "rel_state X s1 s2"
      and S1: "exec p s1 = Some h1"
    shows "\<exists>h2. exec p s2 = Some h2 \<and> X h1 h2"
proof -
  have H: "rel_opt X (exec p s1) (exec p s2)"
    using exec_eq[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                  create_blob_cong create_tree_cong create_encode_cong X_preserve_blob
                  X_preserve_tree X_preserve_thunk X_preserve_encode X_tree_to_thunk
                  X_self S] .
  then show ?thesis
    using S1 by (cases "exec p s2") auto
qed
  
corollary exec_eq_none:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
      and S: "rel_state X s1 s2"
      and S1: "exec p s1 = None"
    shows "exec p s2 = None"
proof -
 have H: "rel_opt X (exec p s1) (exec p s2)"
    using exec_eq[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                  create_blob_cong create_tree_cong create_encode_cong X_preserve_blob
                  X_preserve_tree X_preserve_thunk X_preserve_encode X_tree_to_thunk
                  X_self S] .
  then show ?thesis
    using S1 by (cases "exec p s2") auto
qed

(* 6. Given two equivalent trees, thinking them for one step either both returns None, or
returns equivalent handles*)

lemma state_init_eq:
  assumes "X (HTreeHandle t1) (HTreeHandle t2)"
  shows "rel_state X (state_init t1) (state_init t2)"
  using assms
  unfolding state_init_def rel_state_def
  by simp

lemma apply_tree_eq:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
    and S: "X (HTreeHandle t1) (HTreeHandle t2)"
    shows "rel_opt X (apply_tree t1) (apply_tree t2)"
proof -
  let ?s1 = "state_init t1"
  let ?s2 = "state_init t2"
  have EQSTATE: "rel_state X ?s1 ?s2"
    using state_init_eq S
    by auto
  have SAMEPROG: "get_prog (get_thunk_tree (create_thunk t1)) = get_prog (get_thunk_tree (create_thunk t2))"
    using get_prog_cong S
    by auto

  show ?thesis
  proof (cases "apply_tree t1")
    case None
    then have "apply_tree t2 = None"
      using SAMEPROG exec_eq_none[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                  create_blob_cong create_tree_cong create_encode_cong X_preserve_blob
                  X_preserve_tree X_preserve_thunk X_preserve_encode X_tree_to_thunk
                  X_self EQSTATE] apply_tree_def by auto
    then show ?thesis using None by auto
  next
    case (Some h1)
    then have SOME1: "exec (get_prog t1) ?s1 = Some h1"
      using apply_tree_def by auto
    have "\<exists>h2. exec (get_prog t1) ?s2 = Some h2 \<and> X h1 h2"
      using exec_eq_some[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                  create_blob_cong create_tree_cong create_encode_cong X_preserve_blob
                  X_preserve_tree X_preserve_thunk X_preserve_encode X_tree_to_thunk
                  X_self EQSTATE SOME1] .
    then obtain h2 where "exec (get_prog t2) ?s2 = Some h2 \<and> X h1 h2"
      using SAMEPROG by auto
    then show ?thesis using Some apply_tree_def by auto
  qed
qed

corollary apply_tree_eq_some:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes S: "X (HTreeHandle t1) (HTreeHandle t2)"
  assumes S1: "apply_tree t1 = Some r1"
    shows "\<exists>r2. apply_tree t2 = Some r2 \<and> X r1 r2"
proof -
  have R: "rel_opt X (apply_tree t1) (apply_tree t2)"
    using get_blob_data_cong get_tree_size_cong get_tree_data_cong create_blob_cong
          create_tree_cong create_encode_cong 
          X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode X_tree_to_thunk
          X_self get_prog_cong S
    by (rule apply_tree_eq[of X t1 t2])
  then show ?thesis using S1 by (cases "apply_tree t2") auto
qed


corollary apply_tree_eq_some_rev:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes S: "X (HTreeHandle t1) (HTreeHandle t2)"
  assumes S1: "apply_tree t2 = Some r2"
    shows "\<exists>r1. apply_tree t1 = Some r1 \<and> X r1 r2"
proof -
  have R: "rel_opt X (apply_tree t1) (apply_tree t2)"
    using get_blob_data_cong get_tree_size_cong get_tree_data_cong create_blob_cong
          create_tree_cong create_encode_cong 
          X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode X_tree_to_thunk
          X_self get_prog_cong S
    by (rule apply_tree_eq[of X t1 t2])
  then show ?thesis using S1 by (cases "apply_tree t1") auto
qed

corollary apply_tree_eq_none:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes S: "X (HTreeHandle t1) (HTreeHandle t2)"
     and S1: "apply_tree t1 = None"
   shows "apply_tree t2 = None"
proof -
  have R: "rel_opt X (apply_tree t1) (apply_tree t2)"
    using get_blob_data_cong get_tree_size_cong get_tree_data_cong create_blob_cong
          create_tree_cong create_encode_cong X_preserve_blob X_preserve_tree X_preserve_thunk 
          X_preserve_encode X_tree_to_thunk
          X_self get_prog_cong S
    by (rule apply_tree_eq[of X t1 t2])
  then show ?thesis using S1 by (cases "apply_tree t2") auto
qed

fun is_thunk :: "handle \<Rightarrow> bool" where
  "is_thunk (HThunkHandle _) = True"
| "is_thunk _ = False"

fun think_with_fuel :: "nat \<Rightarrow> ThunkHandle \<Rightarrow> handle option"
and force_with_fuel :: "nat \<Rightarrow> ThunkHandle \<Rightarrow> handle option"
and execute_with_fuel :: "nat \<Rightarrow> EncodeHandle \<Rightarrow> handle option"
and eval_with_fuel :: "nat \<Rightarrow> handle \<Rightarrow> handle option"
and eval_tree_with_fuel :: "nat \<Rightarrow> TreeHandle \<Rightarrow> TreeHandle option"
and eval_list_with_fuel :: "nat \<Rightarrow> handle list \<Rightarrow> handle list option" where
  "think_with_fuel 0 thunk = None"
| "think_with_fuel (Suc n) thunk = 
   (case (eval_tree_with_fuel n (get_thunk_tree thunk)) of
      None \<Rightarrow> None
    | Some t' \<Rightarrow> apply_tree t')"
| "force_with_fuel 0 thunk = None"
| "force_with_fuel (Suc n) thunk =
   (case (think_with_fuel n thunk) of
      None \<Rightarrow> None
    | Some h \<Rightarrow> (case h of
                 HBlobHandle _ \<Rightarrow> Some h
               | HTreeHandle _ \<Rightarrow> Some h
               | HThunkHandle thunk' \<Rightarrow> force_with_fuel n thunk'
               | HEncodeHandle encode' \<Rightarrow> force_with_fuel n (get_encode_thunk encode')))"
| "execute_with_fuel n encode = force_with_fuel n (get_encode_thunk encode)"
| "eval_list_with_fuel n [] = Some []"
| "eval_list_with_fuel n (x # xs) =
   (case (eval_with_fuel n x) of
    None \<Rightarrow> None
  | Some y \<Rightarrow> (case (eval_list_with_fuel n xs) of
               None \<Rightarrow> None
             | Some ys \<Rightarrow> Some (y # ys)))"
| "eval_tree_with_fuel n tree =
   (case (eval_list_with_fuel n (get_tree_raw tree)) of
    None \<Rightarrow> None
  | Some xs \<Rightarrow> Some (create_tree xs))"
| "eval_with_fuel 0 h =
   (case h of
    HThunkHandle _ \<Rightarrow> Some h
  | HBlobHandle _ \<Rightarrow> Some h
  | _ \<Rightarrow> None)"
| "eval_with_fuel (Suc n) h =
    (case h of
    HThunkHandle _ \<Rightarrow> Some h
  | HBlobHandle _ \<Rightarrow> Some h
  | HTreeHandle tree \<Rightarrow> (case (eval_tree_with_fuel n tree) of
                         None \<Rightarrow> None
                       | Some tree' \<Rightarrow> Some (HTreeHandle tree'))
  | HEncodeHandle encode \<Rightarrow> (case (execute_with_fuel n encode) of
                             None \<Rightarrow> None
                           | Some h \<Rightarrow> eval_with_fuel n h))"

definition thinks_to :: "ThunkHandle \<Rightarrow> handle \<Rightarrow> bool" where
  "thinks_to h h1 \<equiv> (\<exists>fuel. think_with_fuel fuel h = Some h1)"

definition forces_to :: "ThunkHandle \<Rightarrow> handle \<Rightarrow> bool" where
  "forces_to h h1 \<equiv> (\<exists>fuel. force_with_fuel fuel h = Some h1)"

definition executes_to :: "EncodeHandle \<Rightarrow> handle \<Rightarrow> bool" where
  "executes_to h h1 \<equiv> (\<exists>fuel. execute_with_fuel fuel h = Some h1)"

definition evals_tree_to :: "TreeHandle \<Rightarrow> TreeHandle \<Rightarrow> bool" where
  "evals_tree_to h h1 \<equiv> (\<exists>fuel. eval_tree_with_fuel fuel h = Some h1)"

definition evals_to :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  "evals_to h h1 \<equiv> (\<exists>fuel. eval_with_fuel fuel h = Some h1)"

(* Determinism *)
lemma force_with_fuel_not_thunk:
  assumes "force_with_fuel n h = Some r"
  shows "(\<exists>b. r = HBlobHandle b) \<or> (\<exists>t. r = HTreeHandle t)"
  using assms
proof (induction n arbitrary: h)
  case 0
  then show ?thesis by auto
next
  case (Suc n')
  then show ?case
  proof (cases "think_with_fuel n' h")
    case None
    then show ?thesis using Suc.prems by auto
  next
    case (Some r')
    then show ?thesis using Suc Some by (cases r') auto
  qed
qed

lemma eval_list_to_list_all:
  "eval_list_with_fuel f xs = Some ys \<Longrightarrow> list_all2 (\<lambda>x y. eval_with_fuel f x = Some y) xs ys"
proof (induction xs arbitrary: ys)
  case Nil
  then have "ys = []" by auto
  then show ?case using Nil by auto
next
  case (Cons x xs')
  then obtain y  where Head: "eval_with_fuel f x = Some y"
    by (cases "eval_with_fuel f x") auto
  then obtain ys' where X: "eval_list_with_fuel f xs' = Some ys'"
                  and  Consy: "(y # ys') = ys"
    using Cons
    by (cases "eval_list_with_fuel f xs'") auto

  have Tail:"(list_all2 (\<lambda>x y. eval_with_fuel f x = Some y)  xs' ys')"
     using Cons.IH X by blast 
  show ?case using Head Tail Consy by auto
qed


lemma list_all_to_eval_list:
  "list_all2 (\<lambda>x y. eval_with_fuel f x = Some y) xs ys \<Longrightarrow> eval_list_with_fuel f xs = Some ys"
proof (induction xs arbitrary: ys)
  case Nil
  then have "ys = []" by auto
  then show ?case using Nil by auto
next
  case (Cons x xs')
  then obtain y ys' where "list_all2 (\<lambda>x y. eval_with_fuel f x = Some y) (x # xs') (y # ys')"
                    and Consy: "ys = y # ys'"
    by (cases "ys") auto
  then have Tail: "list_all2 (\<lambda>x y. eval_with_fuel f x = Some y) xs' ys'"
       and  Head: "eval_with_fuel f x = Some y"
    by auto

  have "eval_list_with_fuel f xs' = Some ys'"
    using Cons.IH Tail by auto
  then have "eval_list_with_fuel f (x # xs') = Some (y # ys')" using Head by auto
  then show ?case using Consy by auto
qed

lemma fuel_padding:
 fixes f k :: nat
  shows
    "(\<forall>th r. think_with_fuel f th = Some r \<longrightarrow> think_with_fuel (f + k) th = Some r)
  \<and> (\<forall>h v. force_with_fuel f h = Some v \<longrightarrow> force_with_fuel (f + k) h = Some v)
  \<and> (\<forall>h v. execute_with_fuel f h = Some v \<longrightarrow> execute_with_fuel (f + k) h = Some v)
  \<and> (\<forall>xs ys. eval_list_with_fuel f xs = Some ys \<longrightarrow> eval_list_with_fuel (f + k) xs = Some ys)
  \<and> (\<forall>h v. eval_tree_with_fuel f h = Some v \<longrightarrow> eval_tree_with_fuel (f + k) h = Some v)
  \<and> (\<forall>h v. eval_with_fuel f h = Some v \<longrightarrow> eval_with_fuel (f + k) h = Some v)"
proof (induction f arbitrary: h)
  case 0
  then show ?case
  proof -
    have P1: "\<forall>th r.
       think_with_fuel 0 th = Some r \<longrightarrow>
       think_with_fuel (0 + k) th = Some r"
      by auto
    have P2: "\<forall>h v. force_with_fuel 0 h = Some v \<longrightarrow>
          force_with_fuel (0 + k) h = Some v" by auto
    have P3: "\<forall>h v. execute_with_fuel 0 h = Some v \<longrightarrow> execute_with_fuel (0 + k) h = Some v" 
      by auto

    have P6: "\<forall>h v. eval_with_fuel 0 h = Some v \<longrightarrow> eval_with_fuel (0 + k) h = Some v"
    proof (intro allI impI)
      fix h v
      assume ASSM: "eval_with_fuel 0 h = Some v"
      show "eval_with_fuel (0 + k) h = Some v"
      proof (cases h)
        case (HBlobHandle b)
        then show ?thesis using ASSM by (cases k) auto
      next
        case (HThunkHandle th)
        then show ?thesis using ASSM by (cases k) auto
      next
        case (HTreeHandle t)
        then show ?thesis using ASSM by auto
      next
        case (HEncodeHandle e)
        then show ?thesis using ASSM by auto
      qed
    qed

    have P4: "\<forall>xs ys. eval_list_with_fuel 0 xs = Some ys \<longrightarrow> eval_list_with_fuel (0 + k) xs = Some ys"
    proof (intro allI impI)
      fix xs ys
      assume ASSM: "eval_list_with_fuel 0 xs = Some ys"
      have "list_all2 (\<lambda>x y. eval_with_fuel 0 x = Some y) xs ys" 
        using eval_list_to_list_all[OF ASSM] .
      then have "list_all2 (\<lambda>x y. eval_with_fuel (0 + k) x = Some y) xs ys" 
      proof (rule list_all2_mono)
        fix xs ys
        assume "eval_with_fuel 0 xs = Some ys"
        then show "eval_with_fuel (0 + k) xs = Some ys"
          using P6 by auto
      qed
      then show "eval_list_with_fuel (0 + k) xs = Some ys"
        using list_all_to_eval_list by auto
    qed

    have P5: "\<forall>h v. eval_tree_with_fuel 0 h = Some v \<longrightarrow> eval_tree_with_fuel (0 + k) h = Some v"
    proof (intro allI impI)
      fix h v
      assume "eval_tree_with_fuel 0 h = Some v"
      then obtain xs where "eval_list_with_fuel 0 (get_tree_raw h) = Some xs" and V: "v = create_tree xs" 
        by (cases "eval_list_with_fuel 0 (get_tree_raw h)") auto
      then have "eval_list_with_fuel (0 + k) (get_tree_raw h) = Some xs" using P4 by auto
      then show "eval_tree_with_fuel (0 + k) h = Some v" using V by auto
    qed

    show ?case using P1 P2 P3 P4 P5 P6 by blast
  qed
next
  case (Suc f)

  have P1: "\<forall>th r.
       think_with_fuel (Suc f) th = Some r \<longrightarrow>
       think_with_fuel (Suc f + k) th = Some r"
  proof (intro allI impI)
    fix th r
    assume "think_with_fuel (Suc f) th = Some r"
    then obtain t' where "eval_tree_with_fuel f (get_thunk_tree th) = Some t'"
                     and  APPLY: "apply_tree t' = Some r"
      by (cases "eval_tree_with_fuel f (get_thunk_tree th)") auto
    then have "eval_tree_with_fuel (f + k) (get_thunk_tree th) = Some t'"
      using Suc.IH by auto
    then show "think_with_fuel (Suc f + k) th = Some r" using APPLY by auto
  qed
        
  have P2: "\<forall>h v. force_with_fuel (Suc f) h = Some v \<longrightarrow>
          force_with_fuel (Suc f + k) h = Some v"
  proof (intro allI impI)
    fix h v
    assume assm1: "force_with_fuel (Suc f) h = Some v"
    show "force_with_fuel (Suc f + k) h = Some v"
    proof -
      obtain h' where Think: "think_with_fuel f h = Some h'" using assm1 
        by (cases "think_with_fuel f h") auto
      then have ThinkIH: "think_with_fuel (f + k) h = Some h'"
        using Suc.IH by auto

      show "force_with_fuel (Suc f+ k) h = Some v"
      proof (cases h')
        case (HBlobHandle b)
        then show ?thesis using Think ThinkIH assm1 by auto
      next
        case (HTreeHandle t)
        then show ?thesis using Think ThinkIH assm1 by auto
      next
        case (HThunkHandle thunk')
        then have "force_with_fuel f thunk' = Some v" using Think assm1 by auto
        then have "force_with_fuel (f + k) thunk' = Some v" using Suc.IH by auto
        then show ?thesis using ThinkIH HThunkHandle by auto
      next
        case (HEncodeHandle encode')
        then have "force_with_fuel f (get_encode_thunk encode') = Some v" 
          using Think assm1 by auto
        then have "force_with_fuel (f + k) (get_encode_thunk encode') = Some v" 
          using Suc.IH by auto
        then show ?thesis using ThinkIH HEncodeHandle by auto
      qed
    qed
  qed
      
  have P3: "\<forall>h v. execute_with_fuel (Suc f) h = Some v \<longrightarrow> execute_with_fuel (Suc f + k) h = Some v"
  proof (intro allI impI)
    fix h v
    assume "execute_with_fuel (Suc f) h = Some v"
    then show "execute_with_fuel (Suc f + k) h = Some v" using P2 by auto
  qed

  have P6: "\<forall>h v. eval_with_fuel (Suc f) h = Some v \<longrightarrow> eval_with_fuel (Suc f + k) h = Some v"
  proof (intro allI impI)
    fix h v
    assume ASSM: "eval_with_fuel (Suc f) h = Some v"
    show "eval_with_fuel (Suc f + k) h = Some v"
    proof (cases h)
      case (HBlobHandle b)
      then show ?thesis using ASSM by (cases k) auto
    next
      case (HThunkHandle th)
      then show ?thesis using ASSM by (cases k) auto
    next
      case (HTreeHandle t)
      then obtain tree' where "eval_tree_with_fuel f t = Some tree'"
                        and V: "v = HTreeHandle tree'"
        using ASSM
        by (cases "eval_tree_with_fuel f t") auto
      then have "eval_tree_with_fuel (f + k) t = Some tree'"
        using Suc.IH by auto
      then show ?thesis using V HTreeHandle by auto
    next
      case (HEncodeHandle e)
      then obtain h' where "execute_with_fuel f e = Some h'"
                       and "eval_with_fuel f h' = Some v"
        using ASSM
        by (cases "execute_with_fuel f e") auto
      then have "execute_with_fuel (f + k) e = Some h'"
           and  "eval_with_fuel (f + k) h' = Some v"
        using Suc.IH by auto
      then show ?thesis using HEncodeHandle by auto
    qed
  qed

  have P4: "\<forall>xs ys. eval_list_with_fuel (Suc f) xs = Some ys \<longrightarrow> eval_list_with_fuel (Suc f + k) xs = Some ys"
  proof (intro allI impI)
    fix xs ys
    assume ASSM: "eval_list_with_fuel (Suc f) xs = Some ys"
    have "list_all2 (\<lambda>x y. eval_with_fuel (Suc f) x = Some y) xs ys" 
      using eval_list_to_list_all[OF ASSM] .
    then have "list_all2 (\<lambda>x y. eval_with_fuel (Suc f + k) x = Some y) xs ys" 
    proof (rule list_all2_mono)
      fix xs ys
      assume "eval_with_fuel (Suc f) xs = Some ys"
      then show "eval_with_fuel (Suc f + k) xs = Some ys"
        using P6 by auto
    qed
    then show "eval_list_with_fuel (Suc f + k) xs = Some ys"
      using list_all_to_eval_list by auto
  qed

  have P5: "\<forall>h v. eval_tree_with_fuel (Suc f) h = Some v \<longrightarrow> eval_tree_with_fuel (Suc f + k) h = Some v"
  proof (intro allI impI)
    fix h v
    assume "eval_tree_with_fuel (Suc f) h = Some v"
    then obtain xs where "eval_list_with_fuel (Suc f) (get_tree_raw h) = Some xs" and V: "v = create_tree xs" 
      by (cases "eval_list_with_fuel (Suc f) (get_tree_raw h)") auto
    then have "eval_list_with_fuel (Suc f + k) (get_tree_raw h) = Some xs" using P4 by auto
    then show "eval_tree_with_fuel (Suc f + k) h = Some v" using V by auto
  qed

  show ?case using P1 P2 P3 P4 P5 P6 by blast
qed

lemma think_with_fuel_padding:
  assumes "think_with_fuel f h = Some h1"
  shows "think_with_fuel (f + k) h = Some h1"
  using assms fuel_padding by auto

lemma force_with_fuel_padding:
  assumes "force_with_fuel f h = Some h1"
  shows "force_with_fuel (f + k) h = Some h1"
  using assms fuel_padding by auto

lemma execute_with_fuel_padding:
  assumes "execute_with_fuel f h = Some h1"
  shows "execute_with_fuel (f + k) h = Some h1"
  using assms fuel_padding by auto

lemma eval_with_fuel_padding:
  assumes "eval_with_fuel f h = Some h1"
  shows "eval_with_fuel (f + k) h = Some h1"
  using assms fuel_padding by auto

lemma eval_tree_with_fuel_padding:
  assumes "eval_tree_with_fuel f h = Some h1"
  shows "eval_tree_with_fuel (f + k) h = Some h1"
  using assms fuel_padding by auto

lemma eval_list_with_fuel_padding:
  assumes "eval_list_with_fuel f h = Some h1"
  shows "eval_list_with_fuel (f + k) h = Some h1"
  using assms fuel_padding by auto

lemma evals_to_tree_to:
  assumes "list_all2 (\<lambda>x y. evals_to x y) xs ys"
  shows "\<exists>fuel. eval_list_with_fuel fuel xs = Some ys"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  then have "eval_list_with_fuel 0 [] = Some []" by auto
  then show ?case by auto
next
  case (Cons x xs y ys)
  then obtain fuel where T: "eval_list_with_fuel fuel xs = Some ys" by auto
  obtain fuel' where H: "eval_with_fuel fuel' x = Some y" using evals_to_def Cons by auto

  let ?f = "max fuel fuel'"
  let ?f1 = "?f - fuel"
  let ?f2 = "?f - fuel'"
  have "eval_list_with_fuel (fuel + ?f1) xs = Some ys" using eval_list_with_fuel_padding[OF T] .
  then have T: "list_all2 (\<lambda>x y. eval_with_fuel ?f x = Some y) xs ys" 
    using eval_list_to_list_all by auto
  have "eval_with_fuel (fuel' + ?f2) x = Some y"  using eval_with_fuel_padding[OF H] .
  then have "list_all2 (\<lambda>x y. eval_with_fuel ?f x = Some y) (x # xs) (y # ys)" using T by auto
  then have "eval_list_with_fuel ?f (x # xs) = Some (y # ys)" using list_all_to_eval_list by auto
  then show ?case by auto
qed

lemma thinks_to_deterministic:
  assumes "thinks_to h h1" and "thinks_to h h2"
  shows "h1 = h2"
  using assms
proof -
  obtain f1 where A: "think_with_fuel f1 h = Some h1"
    using assms(1) unfolding thinks_to_def by auto
  obtain f2 where B: "think_with_fuel f2 h = Some h2"
    using assms(2) unfolding thinks_to_def by auto
  let ?F = "max f1 f2"
  let ?k1 = "?F - f1"
  let ?k2 = "?F - f2"
  have "think_with_fuel (f1 + ?k1) h = Some h1"
    using think_with_fuel_padding[OF A] .
  then have AA: "think_with_fuel ?F h = Some h1" by simp
  have "think_with_fuel (f2 + ?k2) h = Some h2" 
    using think_with_fuel_padding[OF B] .
  then have BB: "think_with_fuel ?F h = Some h2" by simp
  show ?thesis using AA BB by simp
qed

lemma forces_to_deterministic:
  assumes "forces_to h h1" and "forces_to h h2"
  shows "h1 = h2"
  using assms
proof -
  obtain f1 where A: "force_with_fuel f1 h = Some h1"
    using assms(1) unfolding forces_to_def by auto
  obtain f2 where B: "force_with_fuel f2 h = Some h2"
    using assms(2) unfolding forces_to_def by auto
  let ?F = "max f1 f2"
  let ?k1 = "?F - f1"
  let ?k2 = "?F - f2"
  have "force_with_fuel (f1 + ?k1) h = Some h1"
    using force_with_fuel_padding[OF A] .
  then have AA: "force_with_fuel ?F h = Some h1" by simp
  have "force_with_fuel (f2 + ?k2) h = Some h2" 
    using force_with_fuel_padding[OF B] .
  then have BB: "force_with_fuel ?F h = Some h2" by simp
  show ?thesis using AA BB by simp
qed

lemma executes_to_deterministic:
  assumes "executes_to h h1" and "executes_to h h2"
  shows "h1 = h2"
  using assms
proof -
  obtain f1 where A: "execute_with_fuel f1 h = Some h1"
    using assms(1) unfolding executes_to_def by auto
  obtain f2 where B: "execute_with_fuel f2 h = Some h2"
    using assms(2) unfolding executes_to_def by auto
  let ?F = "max f1 f2"
  let ?k1 = "?F - f1"
  let ?k2 = "?F - f2"
  have "execute_with_fuel (f1 + ?k1) h = Some h1"
    using execute_with_fuel_padding[OF A] .
  then have AA: "execute_with_fuel ?F h = Some h1" by simp
  have "execute_with_fuel (f2 + ?k2) h = Some h2" 
    using execute_with_fuel_padding[OF B] .
  then have BB: "execute_with_fuel ?F h = Some h2" by simp
  show ?thesis using AA BB by simp
qed

lemma evals_tree_to_deterministic:
  assumes "evals_tree_to h h1" and "evals_tree_to h h2"
  shows "h1 = h2"
  using assms
proof -
  obtain f1 where A: "eval_tree_with_fuel f1 h = Some h1"
    using assms(1) unfolding evals_tree_to_def by auto
  obtain f2 where B: "eval_tree_with_fuel f2 h = Some h2"
    using assms(2) unfolding evals_tree_to_def by auto
  let ?F = "max f1 f2"
  let ?k1 = "?F - f1"
  let ?k2 = "?F - f2"
  have "eval_tree_with_fuel (f1 + ?k1) h = Some h1"
    using eval_tree_with_fuel_padding[OF A] .
  then have AA: "eval_tree_with_fuel ?F h = Some h1" by simp
  have "eval_tree_with_fuel (f2 + ?k2) h = Some h2" 
    using eval_tree_with_fuel_padding[OF B] .
  then have BB: "eval_tree_with_fuel ?F h = Some h2" by simp
  show ?thesis using AA BB by simp
qed
lemma evals_to_deterministic:
  assumes "evals_to h h1" and "evals_to h h2"
  shows "h1 = h2"
  using assms
proof -
  obtain f1 where A: "eval_with_fuel f1 h = Some h1"
    using assms(1) unfolding evals_to_def by auto
  obtain f2 where B: "eval_with_fuel f2 h = Some h2"
    using assms(2) unfolding evals_to_def by auto
  let ?F = "max f1 f2"
  let ?k1 = "?F - f1"
  let ?k2 = "?F - f2"
  have "eval_with_fuel (f1 + ?k1) h = Some h1"
    using eval_with_fuel_padding[OF A] .
  then have AA: "eval_with_fuel ?F h = Some h1" by simp
  have "eval_with_fuel (f2 + ?k2) h = Some h2" 
    using eval_with_fuel_padding[OF B] .
  then have BB: "eval_with_fuel ?F h = Some h2" by simp
  show ?thesis using AA BB by simp
qed

lemma forces_to_not_thunk:
  assumes "forces_to h r"
  shows "(\<exists>b. r = HBlobHandle b) \<or> (\<exists>t. r = HTreeHandle t)"
  using assms force_with_fuel_not_thunk
  unfolding forces_to_def
  by auto

definition endpoint :: "('a \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> handle option" where
  "endpoint f h \<equiv>
     (if (\<exists>v. f h v)
      then Some (THE v. f h v)
      else None)"

definition think :: "ThunkHandle \<Rightarrow> handle option" where
  "think h = endpoint thinks_to h"

definition force :: "ThunkHandle \<Rightarrow> handle option" where
  "force h = endpoint forces_to h"

definition execute :: "EncodeHandle \<Rightarrow> handle option" where
  "execute h = endpoint executes_to h"

definition eval :: "handle \<Rightarrow> handle option" where
  "eval h = endpoint evals_to h"

lemma endpoint_some:
  assumes H: "endpoint f h = Some h1"
  and f_deterministic: "\<And>h h1 h2. f h h1 \<Longrightarrow> f h h2 \<Longrightarrow> h1 = h2"
  shows "f h h1"
  using assms
  unfolding endpoint_def
proof -
  have ex: "\<exists>x. f h x"
    using assms unfolding endpoint_def by (auto split: if_splits)
  have ex1: "\<exists>!x. f h x"
    using ex f_deterministic by (auto)
  have "f h (THE x. f h x)"
    using ex1 by (rule theI')
  moreover have "h1 = (THE x. f h x)"
    using assms ex unfolding endpoint_def by (auto split: if_splits)
  ultimately show ?thesis by simp
qed

lemma think_some:
  assumes "think h = Some h1"
  shows "thinks_to h h1"
proof -
  have "endpoint thinks_to h = Some h1"
    using assms think_def by auto
  then show ?thesis using endpoint_some[of thinks_to h h1] thinks_to_deterministic by auto
qed

lemma force_some:
  assumes "force h = Some h1"
  shows "forces_to h h1"
proof -
  have "endpoint forces_to h = Some h1"
    using assms force_def by auto
  then show ?thesis using endpoint_some[of forces_to h h1] forces_to_deterministic by auto
qed

lemma force_not_thunk:
  assumes "force h = Some r"
  shows "(\<exists>b. r = HBlobHandle b) \<or> (\<exists>t. r = HTreeHandle t)"
  using  forces_to_not_thunk force_some[OF assms]
  by auto

lemma execute_some:
  assumes "execute h = Some h1"
  shows "executes_to h h1"
proof -
  have "endpoint executes_to h = Some h1"
    using assms execute_def by auto
  then show ?thesis using endpoint_some[of executes_to h h1] executes_to_deterministic by auto
qed

lemma eval_some:
  assumes "eval h = Some h1"
  shows "evals_to h h1"
proof -
  have "endpoint evals_to h = Some h1"
    using assms eval_def by auto
  then show ?thesis using endpoint_some[of evals_to h h1] evals_to_deterministic by auto
qed

lemma endpoint_unique:
  assumes "f h h1"
  and f_deterministic: "\<And>h h1 h2. f h h1 \<Longrightarrow> f h h2 \<Longrightarrow> h1 = h2"
  shows "endpoint f h = Some h1"
  using assms
proof -
  have ex: "\<exists>x. f h x" using assms by blast
  have ex1: "\<exists>!y. f h y"
    using assms f_deterministic by auto
  have the_eq: "(THE x. f h x) = h1"
    using assms ex1 by auto
  show ?thesis
    unfolding endpoint_def using ex the_eq by simp
qed

lemma think_unique:
  assumes "thinks_to h h1"
  shows "think h = Some h1"
proof -
  show ?thesis unfolding think_def using endpoint_unique[of thinks_to h h1] assms thinks_to_deterministic by auto
qed

lemma force_unique:
  assumes "forces_to h h1"
  shows "force h = Some h1"
proof -
  show ?thesis unfolding force_def using endpoint_unique[of forces_to h h1] assms forces_to_deterministic by auto
qed

lemma eval_unique:
  assumes "evals_to h h1"
  shows "eval h = Some h1"
proof -
  show ?thesis unfolding eval_def using endpoint_unique[of evals_to h h1] assms evals_to_deterministic by auto
qed

lemma execute_unique:
  assumes "executes_to h h1"
  shows "execute h = Some h1"
proof -
  show ?thesis unfolding execute_def using endpoint_unique[of executes_to h h1] assms executes_to_deterministic by auto
qed

lemma force_deterministic:
  assumes "force h = Some h1"
      and "force h = Some h2"
    shows "h1 = h2"
  using force_some forces_to_deterministic assms(1) assms(2)
  by auto

lemma think_deterministic:
  assumes "think h = Some h1"
      and "think h = Some h2"
    shows "h1 = h2"
  using think_some thinks_to_deterministic assms(1) assms(2)
  by auto

lemma execute_deterministic:
  assumes "execute h = Some h1"
      and "execute h = Some h2"
    shows "h1 = h2"
  using execute_some executes_to_deterministic assms(1) assms(2)
  by auto

lemma eval_deterministic:
  assumes "eval h = Some h1"
      and "eval h = Some h2"
    shows "h1 = h2"
  using eval_some evals_to_deterministic assms(1) assms(2)
  by auto

coinductive eq :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  EqBlob:
  "(get_blob_data b1 = get_blob_data b2) 
   \<Longrightarrow> eq (HBlobHandle b1) (HBlobHandle b2)"
| EqTree:
  "list_all2 eq (get_tree_raw t1) (get_tree_raw t2) 
   \<Longrightarrow> eq (HTreeHandle t1) (HTreeHandle t2)"
| EqThunkNone:
  "think t1 = None \<Longrightarrow> 
   think t2 = None \<Longrightarrow>
   eq (HThunkHandle t1) (HThunkHandle t2)"
| EqThunkSingleStep:
  "think t1 = Some (HThunkHandle t2) \<Longrightarrow>
   eq (HThunkHandle t1) (HThunkHandle t2)"
| EqThunkSingleStepEncode:
  "think t1 = Some (HEncodeHandle t2) \<Longrightarrow>
   eq (HThunkHandle t1) (HThunkHandle (get_encode_thunk t2))"
| EqThunkSomeRes:
  "think t1 = Some r1 \<Longrightarrow>
   think t2 = Some r2 \<Longrightarrow>
   eq r1 r2 \<Longrightarrow>
   eq (HThunkHandle t1) (HThunkHandle t2)"
| EqEncode:
  "eq (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow>
   eq (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"
| EqSelf:
   "eq h h"

(* 2. eq handles are of the same type, and if LHS is BlobHandle/TreeHandle/ThunkHandle, there
exists a BlobHandle/TreeHandle/ThunkHandle for the RHS. *)

theorem eq_same_type:
  assumes "eq h1 h2"
  shows "get_type h1 = get_type h2"
  using assms
  by (cases rule: eq.cases) auto 

lemma eq_same_kind_blob:
  assumes "eq (HBlobHandle b1) h2"
  shows "\<exists>b2. h2 = HBlobHandle b2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_blob_rev:
  assumes "eq h1 (HBlobHandle b2)"
  shows "\<exists>b1. h1 = HBlobHandle b1"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_tree:
  assumes "eq (HTreeHandle t1) h2"
  shows "\<exists>t2. h2 = HTreeHandle t2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_tree_rev:
  assumes "eq h1 (HTreeHandle t2)"
  shows "\<exists>t1. h1 = HTreeHandle t1"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_thunk:
  assumes "eq (HThunkHandle th1) h2"
  shows "\<exists>th2. h2 = HThunkHandle th2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_thunk_rev:
  assumes "eq h1 (HThunkHandle th2)"
  shows "\<exists>th1. h1 = HThunkHandle th1"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_encode:
  assumes "eq (HEncodeHandle th1) h2"
  shows "\<exists>th2. h2 = HEncodeHandle th2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_encode_rev:
  assumes "eq h1 (HEncodeHandle th2)"
  shows "\<exists>th1. h1 = HEncodeHandle th1"
  using assms
  by (cases rule: eq.cases) auto

(* 3. API functions respect eq *)

theorem get_blob_data_eq:
  assumes "eq (HBlobHandle b1) (HBlobHandle b2)"
  shows "get_blob_data b1 = get_blob_data b2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_refl: "eq h h" 
  by (rule eq.EqSelf)

lemma eq_tree_children:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
  shows "list_all2 eq (get_tree_raw t1) (get_tree_raw t2)"
  using assms
proof (cases rule: eq.cases)
  case EqTree
  then show ?thesis by auto
next
  case (EqSelf)
  then have "get_tree_raw t1 = get_tree_raw t2" by simp
  then show ?thesis  
    by (simp add: list_all2_refl eq_refl)
qed

theorem get_tree_size_eq:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
  shows   "get_tree_size t1 = get_tree_size t2"
  using eq_tree_children[OF assms]
  by (simp add: get_tree_size_def list_all2_lengthD)

theorem get_tree_data_eq:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)" and "i < get_tree_size t1"
  shows "eq (get_tree_data t1 i) (get_tree_data t2 i)"
proof -
  have A: "i < length (get_tree_raw t1)" using assms(2) get_tree_size_def by auto
  have "list_all2 eq (get_tree_raw t1) (get_tree_raw t2)" 
    using eq_tree_children[OF assms(1)] .
  then have "eq ((get_tree_raw t1) ! i) ((get_tree_raw t2) ! i)" 
    using list_all2_nthD[OF _ A] by auto
  then show ?thesis by (simp add: get_tree_data_def[symmetric]) 
qed

theorem create_blob_eq:
  assumes "d1 = d2"
  shows "eq (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
proof -
  have "get_blob_data (create_blob d1) = get_blob_data (create_blob d2)" 
    using assms by simp_all
  then show ?thesis by (rule eq.EqBlob) 
qed

theorem create_tree_eq:
  assumes "list_all2 eq xs ys"
  shows "eq (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
proof -
  have "list_all2 eq (get_tree_raw (create_tree xs)) (get_tree_raw (create_tree ys))"
    using assms by simp_all
  then show ?thesis by (rule eq.EqTree)
qed

theorem create_encode_eq:
  assumes "eq (HThunkHandle t1) (HThunkHandle t2)"
  shows "eq (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"
  using assms by (rule eq.EqEncode)

theorem get_encode_thunk_eq:
  assumes "eq (HEncodeHandle e1) (HEncodeHandle e2)"
  shows "eq (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
  using assms 
proof (cases rule: eq.cases)
  case (EqEncode th1 th2)
  then show ?thesis by auto
next
  case EqSelf
  have "eq (HThunkHandle (get_encode_thunk e1))
           (HThunkHandle (get_encode_thunk e1))" 
    by (rule eq.EqSelf)
  then show ?thesis using EqSelf by auto
qed

theorem run_internal_X:
  assumes "rel_state X s1 s2"
  shows "rel_state X (run_internal s1) (run_internal s2)"
proof -
  have "list_all2 X (hs s1) (hs s2)" using assms unfolding rel_state_def by simp_all
  then have HS: "list_all2 X (hs (run_internal s1)) (hs (run_internal s2))" 
    using run_internal_hs 
    by simp

  have DS: "ds s1 = ds s2" using assms unfolding rel_state_def by simp_all
  have DS': "ds (run_internal s1) = ds (run_internal s2)"
    using run_internal_ds_equiv[OF DS]
    by assumption

  show ?thesis using HS DS' rel_state_def by auto
qed

lemma X_preserve_blob_rev:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  and H: "X h (HBlobHandle b)"
shows "\<exists>b'. h = HBlobHandle b'"
  using H
proof (cases h)
  case (HBlobHandle b) then show ?thesis by auto
next
  case (HTreeHandle t) then show ?thesis using X_preserve_tree H by auto
next
  case (HThunkHandle th) then show ?thesis using X_preserve_thunk H by auto
next
  case (HEncodeHandle e) then show ?thesis using X_preserve_encode H by auto
qed

lemma X_preserve_tree_rev:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  and H: "X h (HTreeHandle b)"
shows "\<exists>b'. h = HTreeHandle b'"
  using H
proof (cases h)
  case (HBlobHandle b) then show ?thesis using X_preserve_blob H by auto
next
  case (HTreeHandle t) then show ?thesis using X_preserve_tree H by auto
next
  case (HThunkHandle th) then show ?thesis using X_preserve_thunk H by auto
next
  case (HEncodeHandle e) then show ?thesis using X_preserve_encode H by auto
qed

lemma X_preserve_thunk_rev:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  and H: "X h (HThunkHandle b)"
shows "\<exists>b'. h = HThunkHandle b'"
  using H
proof (cases h)
  case (HBlobHandle b) then show ?thesis using X_preserve_blob H by auto
next
  case (HTreeHandle t) then show ?thesis using X_preserve_tree H by auto
next
  case (HThunkHandle th) then show ?thesis using X_preserve_thunk H by auto
next
  case (HEncodeHandle e) then show ?thesis using X_preserve_encode H by auto
qed

lemma X_preserve_encode_rev:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  and H: "X h (HEncodeHandle b)"
shows "\<exists>b'. h = HEncodeHandle b'"
  using H
proof (cases h)
  case (HBlobHandle b) then show ?thesis using X_preserve_blob H by auto
next
  case (HTreeHandle t) then show ?thesis using X_preserve_tree H by auto
next
  case (HThunkHandle th) then show ?thesis using X_preserve_thunk H by auto
next
  case (HEncodeHandle e) then show ?thesis using X_preserve_encode H by auto
qed

lemma eq_tree_eval_fuel_n:
 fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes create_tree_cong: "\<And>xs ys. list_all2 X xs ys
                             \<Longrightarrow> X (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
  assumes X_tree_reasons: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
    list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes eval_cong_n: "\<And>h1 h2. X h1 h2 \<Longrightarrow>
      (\<forall>v1. eval_with_fuel n h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
     \<and>
      (\<forall>v2. eval_with_fuel n h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))"
  assumes E: "X (HTreeHandle t1) (HTreeHandle t2)"
  shows "(\<forall>v1. eval_tree_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. evals_tree_to t2 v2 \<and> X (HTreeHandle v1) (HTreeHandle v2)))
      \<and>
        (\<forall>v2. eval_tree_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. evals_tree_to t1 v1 \<and> X (HTreeHandle v1) (HTreeHandle v2)))"
proof -
  have LHS: "(\<forall>v1. eval_tree_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. evals_tree_to t2 v2 \<and> X (HTreeHandle v1) (HTreeHandle v2)))"
  proof (intro allI impI)
    fix v1

    let ?raw1 = "get_tree_raw t1"
    let ?raw2 = "get_tree_raw t2"
    let ?out1 = "get_tree_raw v1"

    assume "eval_tree_with_fuel n t1 = Some v1"
    then have eval_raw1: "eval_list_with_fuel n ?raw1 = Some ?out1" 
      by (cases "eval_list_with_fuel n ?raw1") auto

    have ASSM: "list_all2 (\<lambda>x y. X x y) ?raw1 ?raw2" 
      using X_tree_reasons E by auto

    have "\<exists>ys' fuel. eval_list_with_fuel fuel ?raw2 = Some ys' \<and> list_all2 X ?out1 ys'"
      using ASSM eval_raw1
    proof (induction arbitrary: v1 rule: list_all2_induct)
      case Nil
      then have "get_tree_raw v1 = []" by (cases ?out1) auto
      then have "eval_list_with_fuel 0 [] = Some []" and "list_all2 X (get_tree_raw v1) []"
        by auto
      then show ?case by blast
    next
      case (Cons x xs y ys)

      then have "eval_list_with_fuel n (x # xs) = Some (get_tree_raw v1)" by auto
      then have "list_all2 (\<lambda>x y. eval_with_fuel n x = Some y) (x # xs) (get_tree_raw v1)" 
        using eval_list_to_list_all by auto
      then obtain z zs' where Tail: "list_all2 (\<lambda>x y. eval_with_fuel n x = Some y) xs zs'"
                        and   Head: "eval_with_fuel n x = Some z"
                        and   V1Z: "get_tree_raw v1 = (z # zs')"
        by (cases "get_tree_raw v1") auto
       
      have "eval_list_with_fuel n xs = Some (get_tree_raw (create_tree zs'))" 
        using Tail list_all_to_eval_list by auto
      then obtain ys' fuel where F1: "eval_list_with_fuel fuel ys = Some ys'"
                           and "list_all2 X (get_tree_raw (create_tree zs')) ys'"
        using Cons.IH[of "create_tree zs'"] by auto
      then have EQT: "list_all2 X zs' ys'" by simp

      have "\<exists>v2. evals_to y v2 \<and> X z v2"
        using Head eval_cong_n Cons.hyps(1) by auto
      then obtain v2 where "evals_to y v2" and EQH: "X z v2" by auto
      then obtain fuel' where F2: "eval_with_fuel fuel' y = Some v2" using evals_to_def by auto

      let ?f = "max fuel fuel'"
      let ?f1 = "?f - fuel"
      let ?f2 = "?f - fuel'"
      have "eval_list_with_fuel (fuel + ?f1) ys = Some ys'" using eval_list_with_fuel_padding[OF F1] .
      then have F1: "list_all2 (\<lambda>x y. eval_with_fuel ?f x = Some y) ys ys'"
        using eval_list_to_list_all by auto
      have "eval_with_fuel (fuel' + ?f2) y = Some v2" using eval_with_fuel_padding[OF F2] .
      then have "list_all2 (\<lambda>x y. eval_with_fuel ?f x = Some y) (y # ys) (v2 # ys')" 
        using F1 by auto
      then have X: "eval_list_with_fuel ?f (y # ys) = Some (v2 # ys')" 
        using list_all_to_eval_list by auto

      have "list_all2 X (z # zs') (v2 # ys')" using EQT EQH by auto
      then have "list_all2 X (get_tree_raw v1) (v2 # ys')" using V1Z by auto
      then show ?case using X by blast
    qed
    then obtain ys' fuel where EV: "eval_list_with_fuel fuel ?raw2 = Some ys'"
                         and   EQ: "list_all2 X ?out1 ys'"
      by auto

    let ?v2 = "create_tree ys'"
    let ?out2 = "get_tree_raw (create_tree ys')"

    have "eval_tree_with_fuel fuel t2 = Some ?v2" using EV
      by auto
    then have LHS: "evals_tree_to t2 ?v2" using evals_tree_to_def by auto

    have "list_all2 X (get_tree_raw v1) (get_tree_raw (create_tree ys'))" using EQ by auto
    then have "X (HTreeHandle (create_tree (get_tree_raw v1))) 
                 (HTreeHandle (create_tree (get_tree_raw (create_tree ys'))))" 
      using create_tree_cong[of "get_tree_raw v1" "get_tree_raw(create_tree ys')"] by auto
    then have RHS: "X (HTreeHandle v1) (HTreeHandle ?v2)" by auto

    then show "(\<exists>v2. evals_tree_to t2 v2 \<and> X (HTreeHandle v1) (HTreeHandle v2))" using LHS by auto
  qed

  have RHS: "(\<forall>v2. eval_tree_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. evals_tree_to t1 v1 \<and> X (HTreeHandle v1) (HTreeHandle v2)))"
  proof (intro allI impI)
    fix v2

    let ?raw1 = "get_tree_raw t1"
    let ?raw2 = "get_tree_raw t2"
    let ?out2 = "get_tree_raw v2"

    assume "eval_tree_with_fuel n t2 = Some v2"
    then have eval_raw2: "eval_list_with_fuel n ?raw2 = Some ?out2" 
      by (cases "eval_list_with_fuel n ?raw2") auto

    have ASSM: "list_all2 (\<lambda>x y. X x y) ?raw1 ?raw2" 
      using X_tree_reasons E by auto

    have "\<exists>xs' fuel. eval_list_with_fuel fuel ?raw1 = Some xs' \<and> list_all2 X xs' ?out2"
      using ASSM eval_raw2
    proof (induction arbitrary: v2 rule: list_all2_induct)
      case Nil
      then have "get_tree_raw v2 = []" by (cases ?out2) auto
      then have "eval_list_with_fuel 0 [] = Some []" and "list_all2 X [] (get_tree_raw v2)"
        by auto
      then show ?case by blast
    next
      case (Cons x xs y ys)

      then have "eval_list_with_fuel n (y # ys) = Some (get_tree_raw v2)" by auto
      then have "list_all2 (\<lambda>x y. eval_with_fuel n x = Some y) (y # ys) (get_tree_raw v2)" 
        using eval_list_to_list_all by auto
      then obtain z zs' where Tail: "list_all2 (\<lambda>x y. eval_with_fuel n x = Some y) ys zs'"
                        and   Head: "eval_with_fuel n y = Some z"
                        and   V1Z: "get_tree_raw v2 = (z # zs')"
        by (cases "get_tree_raw v2") auto
       
      have "eval_list_with_fuel n ys = Some (get_tree_raw (create_tree zs'))" 
        using Tail list_all_to_eval_list by auto
      then obtain xs' fuel where F1: "eval_list_with_fuel fuel xs = Some xs'"
                           and "list_all2 X xs' (get_tree_raw (create_tree zs'))"
        using Cons.IH[of "create_tree zs'"] by auto
      then have EQT: "list_all2 X xs' zs'" by simp

      have "\<exists>v1. evals_to x v1 \<and> X v1 z"
        using Head eval_cong_n Cons.hyps(1) by auto
      then obtain v1 where "evals_to x v1" and EQH: "X v1 z" by auto
      then obtain fuel' where F2: "eval_with_fuel fuel' x = Some v1" using evals_to_def by auto

      let ?f = "max fuel fuel'"
      let ?f1 = "?f - fuel"
      let ?f2 = "?f - fuel'"
      have "eval_list_with_fuel (fuel + ?f1) xs = Some xs'" using eval_list_with_fuel_padding[OF F1] .
      then have F1: "list_all2 (\<lambda>x y. eval_with_fuel ?f x = Some y) xs xs'"
        using eval_list_to_list_all by auto
      have "eval_with_fuel (fuel' + ?f2) x = Some v1" using eval_with_fuel_padding[OF F2] .
      then have "list_all2 (\<lambda>x y. eval_with_fuel ?f x = Some y) (x # xs) (v1 # xs')" 
        using F1 by auto
      then have X: "eval_list_with_fuel ?f (x # xs) = Some (v1 # xs')" 
        using list_all_to_eval_list by auto

      have "list_all2 X (v1 # xs') (z # zs')" using EQT EQH by auto
      then have "list_all2 X (v1 # xs') (get_tree_raw v2) " using V1Z by auto
      then show ?case using X by blast
    qed
    then obtain xs' fuel where EV: "eval_list_with_fuel fuel ?raw1 = Some xs'"
                         and   EQ: "list_all2 X xs' ?out2"
      by auto

    let ?v1 = "create_tree xs'"
    let ?out1 = "get_tree_raw (create_tree xs')"

    have "eval_tree_with_fuel fuel t1 = Some ?v1" using EV
      by auto
    then have LHS: "evals_tree_to t1 ?v1" using evals_tree_to_def by auto

    have "list_all2 X (get_tree_raw (create_tree xs')) ?out2" using EQ by auto
    then have "X (HTreeHandle ?v1) (HTreeHandle v2)" 
      using create_tree_cong[of "get_tree_raw(create_tree xs')" "get_tree_raw v2"] by auto
    then show "(\<exists>v1. evals_tree_to t1 v1 \<and> X (HTreeHandle v1) (HTreeHandle v2))" using LHS by auto
  qed

  then show ?thesis using LHS RHS by blast
qed

lemma execute_with_fuel_n:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes get_encode_thunk_cong: "\<And>e1 e2. X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
  assumes force_with_fuel_cong_n: "\<And>h1 h2. X h1 h2 \<Longrightarrow>
     ((\<exists>t1. h1 = handle.HThunkHandle t1) \<longrightarrow>
     (\<exists>t1 t2. h1 = handle.HThunkHandle t1 \<and> h2 = handle.HThunkHandle t2 
     \<and> (\<forall>v1. force_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2))))
 \<and>
    ((\<exists>t2. h2 = handle.HThunkHandle t2) \<longrightarrow>
     (\<exists>t1 t2. h1 = handle.HThunkHandle t1 \<and> h2 = handle.HThunkHandle t2 
     \<and> (\<forall>v2. force_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1 v2))))"
  assumes E: "X (HEncodeHandle e1) (HEncodeHandle e2)"
  shows "(\<forall>v1. execute_with_fuel n e1 = Some v1 \<longrightarrow> (\<exists>v2. executes_to e2 v2 \<and> X v1 v2))
      \<and>
        (\<forall>v2. execute_with_fuel n e2 = Some v2 \<longrightarrow> (\<exists>v1. executes_to e1 v1 \<and> X v1 v2))"
proof -
  let ?th1 = "get_encode_thunk e1"
  let ?th2 = "get_encode_thunk e2"
  have EQT: "X (HThunkHandle ?th1) (HThunkHandle ?th2)" using get_encode_thunk_cong E by auto

  have LHS: "\<forall>v1. execute_with_fuel n e1 = Some v1 \<longrightarrow> (\<exists>v2. executes_to e2 v2 \<and> X v1 v2)"
  proof (intro allI impI)
    fix v1
    assume "execute_with_fuel n e1 = Some v1"
    then have Force1: "force_with_fuel n ?th1 = Some v1" by auto
    obtain v2 where "forces_to ?th2 v2" and EQRES:" X v1 v2" 
      using force_with_fuel_cong_n EQT Force1 by blast
    then obtain fuel where "force_with_fuel fuel ?th2 = Some v2" using forces_to_def by auto
    then have "execute_with_fuel fuel e2 = Some v2" by auto
    then show "\<exists>v2. executes_to e2 v2 \<and> X v1 v2" using executes_to_def EQRES by auto
  qed

  have RHS: "(\<forall>v2. execute_with_fuel n e2 = Some v2 \<longrightarrow> (\<exists>v1. executes_to e1 v1 \<and> X v1 v2))"
  proof (intro allI impI)
    fix v2
    assume "execute_with_fuel n e2 = Some v2"
    then have Force2: "force_with_fuel n ?th2 = Some v2" by auto
    obtain v1 where "forces_to ?th1 v1" and EQRES: "X v1 v2" 
      using force_with_fuel_cong_n EQT Force2 by blast
    then obtain fuel where "force_with_fuel fuel ?th1 = Some v1" using forces_to_def by auto
    then have "execute_with_fuel fuel e1 = Some v1" by auto
    then show "\<exists>v1. executes_to e1 v1 \<and> X v1 v2" using executes_to_def EQRES by auto
  qed

  show ?thesis using LHS RHS by auto
qed
      
lemma eq_forces_to_induct:
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
  assumes get_encode_thunk_cong: "\<And>e1 e2. X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes X_tree_reasons: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
    list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_thunk_reasons: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow> (
     X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  assumes X_thunk_single_step: "\<And>t1 t2. think t1 = Some (HThunkHandle t2) \<Longrightarrow>
                               X (HThunkHandle t1) (HThunkHandle t2)" 
  assumes E: "X h1 h2"
  shows
    "(
       ((\<exists>t1. h1 = HThunkHandle t1) \<longrightarrow>
        (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v1. think_with_fuel n t1 = Some v1 \<longrightarrow> ((\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)))))
      \<and>
       ((\<exists>t2. h2 = HThunkHandle t2) \<longrightarrow>
        (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v2. think_with_fuel n t2 = Some v2 \<longrightarrow> ((\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2))))))
      \<and>
       ((\<exists>t1. h1 = HThunkHandle t1) \<longrightarrow>
        (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v1. force_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2))))
      \<and>
       ((\<exists>t2. h2 = HThunkHandle t2) \<longrightarrow>
        (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v2. force_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1 v2))))
      \<and> 
        (\<forall>v1. eval_with_fuel n h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
      \<and>
        (\<forall>v2. eval_with_fuel n h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))
  )"
  using E
proof (induction n arbitrary: h1 h2)
  case 0

  thm X_thunk_reasons


  have P1: "((\<exists>t1. h1 = HThunkHandle t1) \<longrightarrow> (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v1. think_with_fuel 0 t1 = Some v1 \<longrightarrow> (\<exists>v2. thinks_to t2 v2 \<and> X v1 v2))))"
  proof
    assume ASSM: "\<exists>t1. h1 = HThunkHandle t1" 
    show "\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v1. think_with_fuel 0 t1 = Some v1 \<longrightarrow> (\<exists>v2. thinks_to t2 v2 \<and> X v1 v2))"
    proof -
      obtain t1 where T1: "h1 = HThunkHandle t1"
        using ASSM by auto
      then obtain t2 where T2: "h2 = HThunkHandle t2"
        using 0 T1 X_preserve_thunk by auto
      then show ?thesis using T1 T2 by auto
    qed
  qed

  have P2: "((\<exists>t2. h2 = HThunkHandle t2) \<longrightarrow> (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v2. think_with_fuel 0 t2 = Some v2 \<longrightarrow> (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2))))"
  proof
    assume ASSM: "\<exists>t2. h2 = HThunkHandle t2" 
    show "\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v2. think_with_fuel 0 t2 = Some v2 \<longrightarrow> (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2))"
    proof -
      obtain t2 where T2: "h2 = HThunkHandle t2"
        using ASSM by auto
      then have "\<exists>t1. h1 = HThunkHandle t1"
        using 0 X_preserve_thunk_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] by auto
      then obtain t1 where T1: "h1 = HThunkHandle t1" by auto
      then show ?thesis using T1 T2 by auto
    qed
  qed

  have P3: "(\<exists>t1. h1 = HThunkHandle t1) \<longrightarrow> (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v1. force_with_fuel 0 t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2)))"
  proof
    assume ASSM: "\<exists>t1. h1 = HThunkHandle t1" 
    show "\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v1. force_with_fuel 0 t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2))"
    proof -
      obtain t1 where T1: "h1 = HThunkHandle t1"
        using ASSM by auto
      then obtain t2 where T2: "h2 = HThunkHandle t2"
        using 0 T1 X_preserve_thunk by auto
      then show ?thesis using T1 T2 by auto
    qed
  qed

  have P4: "(\<exists>t2. h2 = handle.HThunkHandle t2) \<longrightarrow> (\<exists>t1 t2. h1 = handle.HThunkHandle t1 \<and> h2 = handle.HThunkHandle t2 \<and> (\<forall>v2. force_with_fuel 0 t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1 v2)))"
  proof
    assume ASSM: "\<exists>t2. h2 = HThunkHandle t2" 
    show "\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v2. force_with_fuel 0 t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1 v2))"
    proof -
      obtain t2 where T2: "h2 = HThunkHandle t2"
        using ASSM by auto
      then have "\<exists>t1. h1 = HThunkHandle t1"
        using 0 T2 X_preserve_thunk_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] by auto
      then obtain t1 where T1: "h1 = HThunkHandle t1" by auto
      then show ?thesis using T1 T2 by auto
    qed
  qed

  have P5: "\<forall>v1. eval_with_fuel 0 h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2)"
  proof (intro allI impI)
    fix v1
    assume ASSM: "eval_with_fuel 0 h1 = Some v1"
    show "(\<exists>v2. evals_to h2 v2 \<and> X v1 v2)"
      using ASSM
    proof (cases h1)
      case (HBlobHandle b1)
      then obtain b2 where B2: "h2 = HBlobHandle b2" using X_preserve_blob 0 by auto
      then have "eval_with_fuel 0 h2 = Some h2" by auto
      then have E2: "evals_to h2 h2" using evals_to_def by blast

      have "v1 = h1" using ASSM HBlobHandle by auto
      then have "X v1 h2" using 0 by auto
      then show ?thesis using E2 by auto
    next
      case (HThunkHandle t1)
      then obtain t2 where T2: "h2 = HThunkHandle t2" using X_preserve_thunk 0 by auto
      then have "eval_with_fuel 0 h2 = Some h2" by auto
      then have E2: "evals_to h2 h2" using evals_to_def by blast

      have "v1 = h1" using ASSM HThunkHandle by auto
      then have "X v1 h2" using 0 by auto
      then show ?thesis using E2 by auto
    next
      case (HTreeHandle t)
      then show ?thesis using ASSM by auto
    next
      case (HEncodeHandle t)
      then show ?thesis using ASSM by auto
    qed
  qed

  have P6: "(\<forall>v2. eval_with_fuel 0 h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))"
  proof (intro allI impI)
    fix v2
    assume ASSM: "eval_with_fuel 0 h2 = Some v2"
    show "(\<exists>v1. evals_to h1 v1 \<and> X v1 v2)"
      using ASSM
    proof (cases h2)
      case (HBlobHandle b2)
      then have "\<exists>b1. h1 = HBlobHandle b1"
        using 0 X_preserve_blob_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] by auto
      then obtain b1 where B1: "h1 = HBlobHandle b1" by auto
      then have "eval_with_fuel 0 h1 = Some h1" by auto
      then have E1: "evals_to h1 h1" using evals_to_def by blast

      have "v2 = h2" using ASSM HBlobHandle by auto
      then have "X h1 v2" using 0 by auto
      then show ?thesis using E1 by auto
    next
      case (HThunkHandle t2)
      then have "\<exists>t1. h1 = HThunkHandle t1"
        using 0 X_preserve_thunk_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] by auto
      then obtain t1 where T1: "h1 = HThunkHandle t1" by auto
      then have "eval_with_fuel 0 h1 = Some h1" by auto
      then have E1: "evals_to h1 h1" using evals_to_def by blast

      have "v2 = h2" using ASSM HThunkHandle by auto
      then have "X h1 v2" using 0 by auto
      then show ?thesis using E1 by auto
    next
      case (HTreeHandle t)
      then show ?thesis using ASSM by auto
    next
      case (HEncodeHandle e)
      then show ?thesis using ASSM by auto
    qed
  qed

  show ?case using P1 P2 P3 P4 P5 P6 by auto
next
  case (Suc f')
  have eval_cong_f': "\<And>h1 h2. X h1 h2 \<Longrightarrow>
      (\<forall>v1. eval_with_fuel f' h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
     \<and>
      (\<forall>v2. eval_with_fuel f' h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))"
    using Suc.IH by blast

    have relevant_IH_think:
      "\<And>h1 h2. X h1 h2 \<Longrightarrow>
       ((\<exists>t1. h1 = HThunkHandle t1) \<longrightarrow>
         (\<exists>t1 t2.
             h1 = HThunkHandle t1 \<and>
             h2 = HThunkHandle t2 \<and>
             (\<forall>v1. think_with_fuel f' t1 = Some v1 \<longrightarrow>
                   (\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or>
                   v1 = HThunkHandle t2 
                   \<or> v1 = HEncodeHandle (create_encode t2)))) \<and>
        ((\<exists>t2. h2 = HThunkHandle t2) \<longrightarrow>
         (\<exists>t1 t2.
             h1 = HThunkHandle t1 \<and>
             h2 = HThunkHandle t2 \<and>
             (\<forall>v2. think_with_fuel f' t2 = Some v2 \<longrightarrow>
                   (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or>
                   thinks_to t1 (HThunkHandle t2)
                   \<or> thinks_to t1 (HEncodeHandle (create_encode t2)))))"
      using Suc.IH by blast

    have relevant_IH_force:
      "\<And>h1 h2. X h1 h2 \<Longrightarrow>
      ((\<exists>t1. h1 = handle.HThunkHandle t1) \<longrightarrow>
         (\<exists>t1 t2.
             h1 = handle.HThunkHandle t1 \<and>
             h2 = handle.HThunkHandle t2 \<and>
             (\<forall>v1. force_with_fuel f' t1 =
                   Some v1 \<longrightarrow>
                   (\<exists>v2. forces_to t2 v2 \<and>
                         X v1 v2)))) \<and>
        ((\<exists>t2. h2 = handle.HThunkHandle t2) \<longrightarrow>
         (\<exists>t1 t2.
             h1 = handle.HThunkHandle t1 \<and>
             h2 = handle.HThunkHandle t2 \<and>
             (\<forall>v2. force_with_fuel f' t2 =
                   Some v2 \<longrightarrow>
                   (\<exists>v1. forces_to t1 v1 \<and>
                         X v1 v2))))"
      using Suc.IH by blast

  from Suc show ?case
  apply (intro conjI)
  proof
    assume ASSM: "X h1 h2"
    show "\<exists>t1. h1 = handle.HThunkHandle t1 \<Longrightarrow>
    \<exists>t1 t2.
       h1 = handle.HThunkHandle t1 \<and>
       h2 = handle.HThunkHandle t2 \<and>
       (\<forall>v1. think_with_fuel (Suc f') t1 = Some v1 \<longrightarrow> ((\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)))"
    proof -
      assume "\<exists>t1. h1 = handle.HThunkHandle t1"
      then obtain t1 where T1: "h1 = HThunkHandle t1" by auto
      then obtain t2 where T2: "h2 = HThunkHandle t2" using ASSM X_preserve_thunk by auto
      then have ASSM: "X (HThunkHandle t1) (HThunkHandle t2)" using T1 ASSM by auto
      
      have ASSM: "X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
                  (think t1 = None \<and> think t2 = None) \<or>
                  (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
                  (think t1 = Some (HThunkHandle t2)) \<or>
                  (think t1 = Some (HEncodeHandle (create_encode t2)))"
        using X_thunk_reasons[of t1 t2] ASSM  by blast

      let ?case1 = "X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2))"
      let ?case2 = "think t1 = None \<and> think t2 = None"
      let ?case3 = "\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2"
      let ?case4 = "think t1 = Some (HThunkHandle t2)"
      let ?case5 = "think t1 = Some (HEncodeHandle (create_encode t2))"
      let ?endgoal = "\<forall>v1. think_with_fuel (Suc f') t1 = Some v1 \<longrightarrow> ((\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2))"

      have "?endgoal"
        using ASSM
      proof
        assume EQTREE: "?case1"
        show "?endgoal"
        proof (intro allI impI)
          fix v1
          assume "think_with_fuel (Suc f') t1 = Some v1"
          then obtain tree' where "eval_tree_with_fuel f' (get_thunk_tree t1) = Some tree'"
                            and   Apply1: "apply_tree tree' = Some v1"
            by (cases "eval_tree_with_fuel f' (get_thunk_tree t1)") auto
          then obtain tree2' where EVTree2: "evals_tree_to (get_thunk_tree t2) tree2'"
                             and  EQApplyTree: "X (HTreeHandle tree') (HTreeHandle tree2')"
            using eq_tree_eval_fuel_n[OF create_tree_cong X_tree_reasons eval_cong_f' EQTREE] 
            by auto

          have "\<exists>v2. apply_tree tree2' = Some v2 \<and> X v1 v2"
            using apply_tree_eq_some[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                                     create_blob_cong create_tree_cong create_encode_cong
                                     X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode
                                     X_tree_to_thunk X_self get_prog_cong EQApplyTree Apply1] .
          then obtain v2 where Apply2: "apply_tree tree2' = Some v2" and EQOUT: "X v1 v2" by auto

          obtain f'' where "eval_tree_with_fuel f'' (get_thunk_tree t2) = Some tree2'"
            using EVTree2 evals_tree_to_def by auto
          then have "think_with_fuel (Suc f'') t2 = Some v2" using Apply2 by auto
          then have "\<exists>v2. thinks_to t2 v2 \<and> X v1 v2" using EQOUT thinks_to_def by blast
          then show "(\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)" by blast
        qed
      next
        assume "?case2 \<or> ?case3 \<or> ?case4 \<or> ?case5"
        then show ?endgoal
        proof
          assume ?case2
          then have None: "think t1 = None" by auto
         
          show ?endgoal
          proof (intro allI impI)
            fix v1
            assume "think_with_fuel (Suc f') t1 = Some v1"
            then have "thinks_to t1 v1" using thinks_to_def by blast
            then have "think t1 = Some v1" using think_unique by auto
            then show "(\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)" using None by auto
          qed
        next 
          assume "?case3 \<or> ?case4 \<or> ?case5"
          then show ?endgoal
          proof
            assume ?case3
            then obtain r1 r2 where T1: "think t1 = Some r1" 
                              and T2: "think t2 = Some r2" 
                              and Xout: "X r1 r2"
              by auto

            show ?endgoal
            proof (intro allI impI)
              fix v1
              assume "think_with_fuel (Suc f') t1 = Some v1"
              then have "think t1 = Some v1" using thinks_to_def think_unique by blast
              then have "v1 = r1" using T1 think_deterministic by auto
              then have Xout: "X v1 r2" using Xout by auto

              have "thinks_to t2 r2" using T2 think_some by auto
              then show "(\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)" using Xout by blast
            qed
          next
            assume "?case4 \<or> ?case5"
            then show ?endgoal
            proof
              assume ?case4
              then have X: "think t1 = Some (HThunkHandle t2)"  by auto

              show ?endgoal
              proof (intro allI impI)
                fix v1
                assume "think_with_fuel (Suc f') t1 = Some v1"
                then have "think t1 = Some v1" using thinks_to_def think_unique by blast
                then have "v1 = HThunkHandle t2" using X by auto
                then show "(\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)" by blast
              qed
            next
              assume ?case5
              then have X: "think t1 = Some (HEncodeHandle (create_encode t2))" by auto

              show ?endgoal
              proof (intro allI impI)
                fix v1
                assume "think_with_fuel (Suc f') t1 = Some v1"
                then have "think t1 = Some v1" using thinks_to_def think_unique by blast
                then have "v1 = HEncodeHandle (create_encode t2)" using X by auto
                then show "(\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)" by blast
              qed
            qed
          qed
        qed
      qed

      then show "\<exists>t1 t2.
       h1 = handle.HThunkHandle t1 \<and>
       h2 = handle.HThunkHandle t2 \<and>
       (\<forall>v1. think_with_fuel (Suc f') t1 = Some v1 \<longrightarrow> ((\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)))"
        using T1 T2 by auto
    qed
  next
    assume ASSM: "X h1 h2"
    show "(\<exists>t2. h2 = HThunkHandle t2) \<longrightarrow>
    (\<exists>t1 t2.
        h1 = HThunkHandle t1 \<and>
        h2 = HThunkHandle t2 \<and>
        (\<forall>v2. think_with_fuel (Suc f') t2 = Some v2 \<longrightarrow> (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2))))"
    proof (intro impI)
      assume "\<exists>t2. h2 = HThunkHandle t2"
      then obtain t2 where T2: "h2 = HThunkHandle t2" by auto
      then have "\<exists>t1. h1 = HThunkHandle t1" 
        using ASSM X_preserve_thunk_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode]
        by auto
      then obtain t1 where T1: "h1 = HThunkHandle t1" by auto
      then have ASSM: "X (HThunkHandle t1) (HThunkHandle t2)" using T1 T2 ASSM by simp

      let ?case1 = "X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2))"
      let ?case2 = "think t1 = None \<and> think t2 = None"
      let ?case3 = "\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2"
      let ?case4 = "think t1 = Some (HThunkHandle t2)"
      let ?case5 = "think t1 = Some (HEncodeHandle (create_encode t2))"
      let ?endgoal = "(\<forall>v2. think_with_fuel (Suc f') t2 = Some v2 \<longrightarrow> (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2)))"

      have ASSM: "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4 \<or> ?case5"
        using X_thunk_reasons[of t1 t2] ASSM by blast

      have ?endgoal
        using ASSM
      proof
        assume EQTREE: ?case1
        show ?endgoal
        proof (intro allI impI)
          fix v2
          assume "think_with_fuel (Suc f') t2 = Some v2"
          then obtain tree2' where "eval_tree_with_fuel f' (get_thunk_tree t2) = Some tree2'"
                             and Apply2: "apply_tree tree2' = Some v2"
            by (cases "eval_tree_with_fuel f' (get_thunk_tree t2)") auto
          then obtain tree' where EVTree1: "evals_tree_to (get_thunk_tree t1) tree'" 
                            and   EQApplyTree: "X (HTreeHandle tree') (HTreeHandle tree2')"
            using eq_tree_eval_fuel_n[OF create_tree_cong X_tree_reasons eval_cong_f' EQTREE]
            by auto

          have "\<exists>v1. apply_tree tree' = Some v1 \<and> X v1 v2"
            using apply_tree_eq_some_rev[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                                create_blob_cong create_tree_cong create_encode_cong X_preserve_blob
                                X_preserve_tree X_preserve_thunk X_preserve_encode X_tree_to_thunk
                                X_self get_prog_cong EQApplyTree Apply2] by auto
          then obtain v1 where Apply1: "apply_tree tree' = Some v1" and EQOUT: "X v1 v2" by auto

          obtain f'' where "eval_tree_with_fuel f'' (get_thunk_tree t1) = Some tree'"
            using EVTree1 evals_tree_to_def by auto
          then have "think_with_fuel (Suc f'') t1 = Some v1" using Apply1 by auto
          then have "\<exists>v1. thinks_to t1 v1 \<and> X v1 v2" using EQOUT thinks_to_def by blast
          then show "(\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2))" by blast
        qed
      next
        assume "?case2 \<or> ?case3 \<or> ?case4 \<or> ?case5"
        then show ?endgoal
        proof
          assume ?case2
          then have None: "think t2 = None" by auto
          show ?endgoal
          proof (intro allI impI)
            fix v2
            assume "think_with_fuel (Suc f') t2 = Some v2"
            then have "think t2 = Some v2" using thinks_to_def think_unique by blast
            then show "(\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2))" 
              using None by auto
          qed
        next
          assume "?case3 \<or> ?case4 \<or> ?case5"
          then show ?endgoal
          proof
            assume ?case3
            then obtain r1 r2 where T1: "think t1 = Some r1"
                              and   T2: "think t2 = Some r2"
                              and   Xout: "X r1 r2"
              by auto
            show ?endgoal
            proof (intro allI impI)
              fix v2
              assume "think_with_fuel (Suc f') t2 = Some v2"
              then have "think t2 = Some v2" using thinks_to_def think_unique by blast
              then have "v2 = r2" using T2 think_deterministic by auto
              then have Xout: "X r1 v2" using Xout by auto

              have "thinks_to t1 r1" using T1 think_some by auto
              then show "(\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2))" 
                using Xout by auto
            qed
          next
            assume "?case4 \<or> ?case5"
            then show ?endgoal
            proof
              assume ?case4
              then have X: "thinks_to t1 (HThunkHandle t2)" using think_some by auto
            
              show ?endgoal
              proof (intro allI impI)
                fix v2
                assume "think_with_fuel (Suc f') t2 = Some v2"
                then show "(\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2))" 
                  using X by auto
              qed
            next
              assume ?case5
              then have X: "thinks_to t1 (HEncodeHandle (create_encode t2))" using think_some by auto

              show ?endgoal
              proof (intro allI impI)
                fix v2
                assume "think_with_fuel (Suc f') t2 = Some v2"
                then show "(\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2))" 
                  using X by auto
              qed
            qed
          qed
        qed
      qed
     
      then show " \<exists>t1 t2.
        h1 = HThunkHandle t1 \<and>
        h2 = HThunkHandle t2 \<and>
        (\<forall>v2. think_with_fuel (Suc f') t2 = Some v2 \<longrightarrow> (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2)))"
        using T1 T2 by auto
    qed
  next
    assume ASSM: "X h1 h2"
    show "(\<exists>t1. h1 = handle.HThunkHandle t1) \<longrightarrow>
    (\<exists>t1 t2.
        h1 = handle.HThunkHandle t1 \<and>
        h2 = handle.HThunkHandle t2 \<and>
        (\<forall>v1. force_with_fuel (Suc f') t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2)))"
    proof (intro impI)
      assume "\<exists>t1. h1 = handle.HThunkHandle t1"
      then have "(\<exists>t1 t2.
             h1 = handle.HThunkHandle t1 \<and>
             h2 = handle.HThunkHandle t2 \<and>
             (\<forall>v1. think_with_fuel f' t1 = Some v1 \<longrightarrow>
                   (\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or>
                   v1 = handle.HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)))"
        using relevant_IH_think[OF ASSM] by auto
      then obtain t1 t2 where T1: "h1 = HThunkHandle t1" 
                        and   T2: "h2 = HThunkHandle t2"
                        and   relevant_IH:  "(\<forall>v1. think_with_fuel f' t1 = Some v1 \<longrightarrow>
                                             (\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or>
                                             v1 = handle.HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2))"
        by auto
      then have ASSM: "X (HThunkHandle t1) (HThunkHandle t2)" using T1 ASSM by auto

      let ?endgoal = "\<forall>v1. force_with_fuel (Suc f') t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2)"

      have ?endgoal
      proof (intro allI impI)
        fix v1
        assume F1: "force_with_fuel (Suc f') t1 = Some v1"
        then obtain t1' where T1: "think_with_fuel f' t1 = Some t1'"
          by (cases "think_with_fuel f' t1") auto

        let ?case1 = "\<exists>v2. thinks_to t2 v2 \<and> X t1' v2"
        let ?case2 = "t1' = HThunkHandle t2"
        let ?case3 = "t1' = HEncodeHandle (create_encode t2)"
        let ?endgoal = "\<exists>v2. forces_to t2 v2 \<and> X v1 v2"

        have "?case1 \<or> ?case2 \<or> ?case3"
          using relevant_IH T1 T2 ASSM by auto

        then show ?endgoal
        proof
          assume ?case1
          then obtain t2' where T2: "thinks_to t2 t2'" and EQOUT: "X t1' t2'" by auto

          show ?endgoal
          proof (cases t1')
            case (HBlobHandle b1)
            then have EQV1: "v1 = t1'" using F1 T1 by auto
            obtain b2 where Blob2: "t2' = HBlobHandle b2" using EQOUT X_preserve_blob HBlobHandle by auto
            then obtain fuel where "think_with_fuel fuel t2 = Some t2'" using T2 thinks_to_def by auto
            then have "force_with_fuel (Suc fuel) t2 = Some t2'" using Blob2 by auto
            then have "forces_to t2 t2'" using forces_to_def by blast
            then show ?thesis using EQOUT EQV1 by blast
          next
            case (HTreeHandle t1)
            then have EQV1: "v1 = t1'" using F1 T1 by auto
            obtain b2 where Tree2: "t2' = HTreeHandle b2" using EQOUT X_preserve_tree HTreeHandle by auto
            then obtain fuel where "think_with_fuel fuel t2 = Some t2'" using T2 thinks_to_def by auto
            then have "force_with_fuel (Suc fuel) t2 = Some t2'" using Tree2 by auto
            then have "forces_to t2 t2'" using forces_to_def by blast
            then show ?thesis using EQOUT EQV1 by blast
          next
            case (HThunkHandle th1)  
            then obtain th1 th2 where Th1: "t1' = HThunkHandle th1"
                                and   Th2: "t2' = HThunkHandle th2"
                                and   OUT: "\<forall>v1. force_with_fuel f' th1 = Some v1 \<longrightarrow> 
                                           (\<exists>v2. forces_to th2 v2 \<and> X v1 v2)"
              using relevant_IH_force[OF EQOUT] HThunkHandle by auto

            have "force_with_fuel f' th1 = Some v1" using F1 T1 Th1 by auto
            then obtain v2 where "forces_to th2 v2" and EQV: "X v1 v2"
              using OUT by auto
            then obtain fuel where Fuel1: "force_with_fuel fuel th2 = Some v2" 
              using forces_to_def by auto
            obtain fuel' where Fuel2: "think_with_fuel fuel' t2 = Some t2'" 
              using T2 thinks_to_def by auto

            let ?f = "max fuel fuel'"
            let ?f1 = "?f - fuel"
            let ?f2 = "?f - fuel'"

            have Fuel1: "force_with_fuel (fuel + ?f1) th2 = Some v2" 
              using force_with_fuel_padding[OF Fuel1] .
            have Fuel2: "think_with_fuel (fuel' + ?f2) t2 = Some t2'"
              using think_with_fuel_padding[OF Fuel2] .
            have "force_with_fuel (Suc ?f) t2 = Some v2"
              using Fuel2 Th2 Fuel1 by auto
            then show ?thesis using EQV forces_to_def by blast
          next
            case (HEncodeHandle e1)
            then obtain e2 where Encode2: "t2' = HEncodeHandle e2" 
              using EQOUT X_preserve_encode by auto

            let ?th1 = "HThunkHandle (get_encode_thunk e1)"
            let ?th2 = "HThunkHandle (get_encode_thunk e2)"
            have EQT: "X ?th1 ?th2" using get_encode_thunk_cong HEncodeHandle Encode2 EQOUT by auto
            then obtain th1 th2 where Th1: "?th1 = HThunkHandle th1"
                                and   Th2: "?th2 = HThunkHandle th2"
                                and   OUT: "\<forall>i. force_with_fuel f' th1 = Some v1 \<longrightarrow> 
                                           (\<exists>v2. forces_to th2 v2 \<and> X v1 v2)"
              using relevant_IH_force[OF EQT] by auto
            
            have "force_with_fuel f' th1 = Some v1" using F1 HEncodeHandle T1 Th1 by auto
            then obtain v2 where "forces_to th2 v2" and EQV: "X v1 v2"
              using OUT by auto
            then obtain fuel where Fuel1: "force_with_fuel fuel th2 = Some v2" 
              using forces_to_def by auto
            obtain fuel' where Fuel2: "think_with_fuel fuel' t2 = Some t2'" 
              using T2 thinks_to_def by auto

            let ?f = "max fuel fuel'"
            let ?f1 = "?f - fuel"
            let ?f2 = "?f - fuel'"

            have Fuel1: "force_with_fuel (fuel + ?f1) th2 = Some v2" 
              using force_with_fuel_padding[OF Fuel1] .
            have Fuel2: "think_with_fuel (fuel' + ?f2) t2 = Some t2'"
              using think_with_fuel_padding[OF Fuel2] .
            have "force_with_fuel (Suc ?f) t2 = Some v2"
              using Fuel2 Encode2 Th2 Fuel1 by auto
            then show ?thesis using EQV forces_to_def by blast
          qed
        next
          assume "?case2 \<or> ?case3"
          then show ?endgoal
          proof
            assume ?case2
            then have Step: "t1' = HThunkHandle t2" .
            then have "force_with_fuel f' t2 = Some v1" using F1 T1 by auto
            then have "forces_to t2 v1" and "X v1 v1" using forces_to_def X_self by auto
            then show ?endgoal by auto
          next
            assume ?case3
            then have Step: "t1' = HEncodeHandle (create_encode t2)" .
            then have "force_with_fuel f' t2 = Some v1" using F1 T1 by auto
            then have "forces_to t2 v1" and "X v1 v1" using forces_to_def X_self by auto
            then show ?endgoal by auto
          qed
        qed
      qed
      then show "  (\<exists>t1 t2.
        h1 = handle.HThunkHandle t1 \<and>
        h2 = handle.HThunkHandle t2 \<and>
        (\<forall>v1. force_with_fuel (Suc f') t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2)))"
        using T1 T2 by auto
    qed
  next
    assume ASSM: "X h1 h2"
    let ?LHS = " (\<exists>t2. h2 = HThunkHandle t2)"
    let ?RHS = " (\<exists>t1 t2. h1 = handle.HThunkHandle t1 \<and> h2 = handle.HThunkHandle t2 
                \<and> (\<forall>v2. force_with_fuel (Suc f') t2 = Some v2 
               \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1 v2)))"
    show "?LHS \<longrightarrow> ?RHS"
    proof (intro impI)
      assume ?LHS
      then obtain t1 t2 where T1: "h1 = HThunkHandle t1"
                        and   T2: "h2 = HThunkHandle t2"
                        and   relevant_IH: "\<forall>v2. think_with_fuel f' t2 = Some v2 \<longrightarrow>
                                           (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or>
                                           thinks_to t1 (HEncodeHandle (create_encode t2))"
        using relevant_IH_think[OF ASSM] by auto
      then have ASSM: "X (HThunkHandle t1) (HThunkHandle t2)" using ASSM by auto

      let ?endgoal = "(\<forall>v2. force_with_fuel (Suc f') t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1
      v2))"

      have ?endgoal
      proof (intro allI impI)
        fix v2
        assume F2: "force_with_fuel (Suc f') t2 = Some v2"
        then obtain t2' where T2: "think_with_fuel f' t2 = Some t2'"
          by (cases "think_with_fuel f' t2") auto

        let ?case1 = "\<exists>v1. thinks_to t1 v1 \<and> X v1 t2'"
        let ?case2 = "thinks_to t1 (HThunkHandle t2)"
        let ?case3 = "thinks_to t1 (HEncodeHandle (create_encode t2))"
        let ?endgoal = "\<exists>v1. forces_to t1 v1 \<and> X v1 v2"

        have "?case1 \<or> ?case2 \<or> ?case3" using relevant_IH T2  by auto
        then show ?endgoal
        proof 
          assume ?case1 
          then obtain t1' where T1: "thinks_to t1 t1'" and EQOUT: "X t1' t2'" by auto

          show ?endgoal
          proof (cases t2')
            case (HBlobHandle b2)
            then have EQV: "v2 = t2'" using F2 T2 by auto
            then have "\<exists>b1. t1' = HBlobHandle b1" using X_preserve_blob_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] EQOUT HBlobHandle by auto
            then obtain b1 where Blob1: "t1' = HBlobHandle b1" by auto
            then obtain fuel where "think_with_fuel fuel t1 = Some t1'" 
              using T1 thinks_to_def by auto
            then have "force_with_fuel (Suc fuel) t1 = Some t1'" using Blob1 by auto
            then show ?thesis using forces_to_def EQOUT EQV by blast
          next
            case (HTreeHandle t2)
            then have EQV: "v2 = t2'" using F2 T2 by auto
            then have "\<exists>b1. t1' = HTreeHandle b1" using X_preserve_tree_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] EQOUT HTreeHandle by auto
            then obtain b1 where Tree1: "t1' = HTreeHandle b1" by auto
            then obtain fuel where "think_with_fuel fuel t1 = Some t1'" 
              using T1 thinks_to_def by auto
            then have "force_with_fuel (Suc fuel) t1 = Some t1'" using Tree1 by auto
            then show ?thesis using forces_to_def EQOUT EQV by blast
          next
            case (HThunkHandle th2)
            then obtain th1 th2 where Th1: "t1' = HThunkHandle th1"
                                and   Th2: "t2' = HThunkHandle th2"
                                and   OUT: "\<forall>v2. force_with_fuel f' th2 = Some v2 \<longrightarrow> 
                                           (\<exists>v1. forces_to th1 v1 \<and> X v1 v2)"
              using relevant_IH_force[OF EQOUT] HThunkHandle by auto

            have "force_with_fuel f' th2 = Some v2" using F2 T2 Th2 by auto
            then obtain v1 where "forces_to th1 v1" and EQV: "X v1 v2" using OUT by auto
            then obtain fuel where Fuel1: "force_with_fuel fuel th1 = Some v1" 
              using forces_to_def by auto
            obtain fuel' where Fuel2: "think_with_fuel fuel' t1 = Some t1'"
              using T1 thinks_to_def by auto

            let ?f = "max fuel fuel'"
            let ?f1 = "?f - fuel"
            let ?f2 = "?f - fuel'"

            have Fuel1: "force_with_fuel (fuel + ?f1) th1 = Some v1"
              using force_with_fuel_padding[OF Fuel1] .
            have Fuel2: "think_with_fuel (fuel' + ?f2) t1 = Some t1'"
              using think_with_fuel_padding[OF Fuel2] .
            have "force_with_fuel (Suc ?f) t1 = Some v1"
              using Fuel2 Th1 Fuel1 by auto
            then show ?thesis using EQV forces_to_def by blast
          next
            case (HEncodeHandle e2)
            then have "\<exists>e1. t1' = HEncodeHandle e1" using EQOUT X_preserve_encode_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] by auto
            then obtain e1 where Encode1: "t1' = HEncodeHandle e1" by auto

            let ?th1 = "HThunkHandle (get_encode_thunk e1)"
            let ?th2 = "HThunkHandle (get_encode_thunk e2)"
            have EQT: "X ?th1 ?th2" 
              using get_encode_thunk_cong HEncodeHandle Encode1 EQOUT by auto
            then obtain th1 th2 where Th1: "?th1 = HThunkHandle th1"
                                and   Th2: "?th2 = HThunkHandle th2"
                                and   OUT: "\<forall>v2. force_with_fuel f' th2 = Some v2 \<longrightarrow> 
                                           (\<exists>v1. forces_to th1 v1 \<and> X v1 v2)"
              using relevant_IH_force[OF EQT] by auto

            have "force_with_fuel f' th2 = Some v2" using F2 HEncodeHandle T2 Th2 by auto
            then obtain v1 where "forces_to th1 v1" and EQV: "X v1 v2" using OUT by auto
            then obtain fuel where Fuel1: "force_with_fuel fuel th1 = Some v1" 
              using forces_to_def by auto
            obtain fuel' where Fuel2: "think_with_fuel fuel' t1 = Some t1'"
              using T1 thinks_to_def by auto

            let ?f = "max fuel fuel'"
            let ?f1 = "?f - fuel"
            let ?f2 = "?f - fuel'"

            have Fuel1: "force_with_fuel (fuel + ?f1) th1 = Some v1"
              using force_with_fuel_padding[OF Fuel1] .
            have Fuel2: "think_with_fuel (fuel' + ?f2) t1 = Some t1'"
              using think_with_fuel_padding[OF Fuel2] .
            have "force_with_fuel (Suc ?f) t1 = Some v1"
              using Fuel2 Encode1 Th1 Fuel1 by auto
            then show ?thesis using EQV forces_to_def by blast
          qed
        next
          assume "?case2 \<or> ?case3"
          then show ?endgoal
          proof
            assume ?case2
            then have Step: "thinks_to t1 (HThunkHandle t2)" .
            then obtain fuel where Fuel1: "think_with_fuel fuel t1 = Some (HThunkHandle t2)"
              using thinks_to_def by auto
          
            let ?f = "max fuel (Suc f')"
            let ?f1 = "?f - fuel"
            let ?f2 = "?f - (Suc f')"
          
            have Fuel1: "think_with_fuel (fuel + ?f1) t1 = Some (HThunkHandle t2)"
              using think_with_fuel_padding[OF Fuel1] .
            have Fuel2: "force_with_fuel ((Suc f') + ?f2) t2 = Some v2"
              using force_with_fuel_padding[OF F2] .
            have "force_with_fuel (Suc ?f) t1 = Some v2" using Fuel1 Fuel2 by auto
            then show ?thesis using forces_to_def X_self by blast
          next
            assume ?case3
            then have Step: "thinks_to t1 (HEncodeHandle (create_encode t2))" .
            then obtain fuel where Fuel1: "think_with_fuel fuel t1 = Some (HEncodeHandle (create_encode t2))"
              using thinks_to_def by auto
          
            let ?f = "max fuel (Suc f')"
            let ?f1 = "?f - fuel"
            let ?f2 = "?f - (Suc f')"
          
            have Fuel1: "think_with_fuel (fuel + ?f1) t1 = Some (HEncodeHandle (create_encode t2))"
              using think_with_fuel_padding[OF Fuel1] .
            have Fuel2: "force_with_fuel ((Suc f') + ?f2) t2 = Some v2"
              using force_with_fuel_padding[OF F2] .
            have "force_with_fuel (Suc ?f) t1 = Some v2" using Fuel1 Fuel2 by auto
            then show ?thesis using forces_to_def X_self by blast
          qed
        qed
      qed
      then show ?RHS using T1 T2 by auto
    qed
  next
    assume EQH: "X h1 h2"

    let ?RHS = " \<forall>v1. eval_with_fuel (Suc f') h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2)"
    show "?RHS"
    proof (intro allI impI)
      fix v1
      assume ASSM: "eval_with_fuel (Suc f') h1 = Some v1"
      show "\<exists>v2. evals_to h2 v2 \<and> X v1 v2"
        using ASSM
      proof (cases h1)
        case (HBlobHandle b1)
        then obtain b2 where "h2 = HBlobHandle b2" using X_preserve_blob EQH by blast
        then have "eval_with_fuel 0 h2 = Some h2" by auto
        then have "evals_to h2 h2" using evals_to_def by blast
        then show ?thesis using ASSM EQH HBlobHandle by auto
      next
        case (HThunkHandle t1)
        then obtain t2 where "h2 = HThunkHandle t2" using X_preserve_thunk EQH by blast
        then have "eval_with_fuel 0 h2 = Some h2" by auto
        then have "evals_to h2 h2" using evals_to_def by blast
        then show ?thesis using ASSM EQH HThunkHandle by auto
      next
        case (HTreeHandle t1)
        then obtain t2 where T2: "h2 = HTreeHandle t2" using X_preserve_tree EQH by blast
        then have EQTREE: "X (HTreeHandle t1) (HTreeHandle t2)" using EQH HTreeHandle by auto

        obtain tree' where "eval_tree_with_fuel f' t1 = Some tree'"
                     and   V1: "v1 = HTreeHandle tree'"
          using ASSM HTreeHandle by (cases "eval_tree_with_fuel f' t1") auto
        then obtain tree2' where "evals_tree_to t2 tree2'"
                           and   EQTREE: "X (HTreeHandle tree') (HTreeHandle tree2')"
          using eq_tree_eval_fuel_n[OF create_tree_cong X_tree_reasons eval_cong_f' EQTREE]
          by auto
        then obtain fuel where "eval_tree_with_fuel fuel t2 = Some tree2'" 
          using evals_tree_to_def by auto
        then have "eval_with_fuel (Suc fuel) h2 = Some (HTreeHandle tree2')" using T2 by auto
        then have "evals_to h2 (HTreeHandle tree2')" using evals_to_def by blast
        then show ?thesis using V1 EQTREE by auto
      next
        case (HEncodeHandle e1)
        then obtain e2 where E2: "h2 = HEncodeHandle e2" using X_preserve_encode EQH by blast
        then have EQENCODE: "X (HEncodeHandle e1) (HEncodeHandle e2)" 
          using EQH HEncodeHandle by auto

        obtain h1' where "execute_with_fuel f' e1 = Some h1'"
                   and   Eval1: "eval_with_fuel f' h1' = Some v1"
          using ASSM HEncodeHandle
          by (cases "execute_with_fuel f' e1") auto
        then obtain h2' where "executes_to e2 h2'"
                        and   EQ': "X h1' h2'"
          using execute_with_fuel_n[OF get_encode_thunk_cong relevant_IH_force EQENCODE] 
          by blast
        then obtain fuel where Fuel1: "execute_with_fuel fuel e2 = Some h2'" 
          using executes_to_def by auto

        obtain v2 where "evals_to h2' v2" and EQRES: "X v1 v2"
          using Suc.IH EQ' Eval1 by blast
        then obtain fuel' where Fuel2: "eval_with_fuel fuel' h2' = Some v2" 
          using evals_to_def by auto

        let ?f = "max fuel fuel'"
        let ?f1 = "?f - fuel"
        let ?f2 = "?f - fuel'"

        have Fuel1: "execute_with_fuel (fuel + ?f1) e2 = Some h2'"
          using execute_with_fuel_padding[OF Fuel1] .
        have Fuel2: "eval_with_fuel (fuel' + ?f2) h2' = Some v2"
          using eval_with_fuel_padding[OF Fuel2] .
        have "eval_with_fuel (Suc ?f) h2 = Some v2" using Fuel1 Fuel2 E2 by auto
        then show ?thesis using evals_to_def EQRES by blast
      qed
    qed
  next
    assume EQH: "X h1 h2"

    let ?RHS = " \<forall>v2. eval_with_fuel (Suc f') h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2)"
    show ?RHS
    proof (intro allI impI)
      fix v2
      assume ASSM: "eval_with_fuel (Suc f') h2 = Some v2"
      show "\<exists>v1. evals_to h1 v1 \<and> X v1 v2"
        using ASSM
      proof (cases h2)
        case (HBlobHandle b2)
        then have "\<exists>b1. h1 = HBlobHandle b1"
          using X_preserve_blob_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] EQH by auto
        then obtain b1 where "h1 = HBlobHandle b1" by auto
        then have "eval_with_fuel 0 h1 = Some h1" by auto
        then have "evals_to h1 h1" using evals_to_def by blast
        then show ?thesis using ASSM EQH HBlobHandle by auto
      next
        case (HThunkHandle t2)
        then have "\<exists>t1. h1 = HThunkHandle t1"
          using X_preserve_thunk_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] EQH by auto
        then obtain t1 where "h1 = HThunkHandle t1" by auto
        then have "eval_with_fuel 0 h1 = Some h1" by auto
        then have "evals_to h1 h1" using evals_to_def by blast
        then show ?thesis using ASSM EQH HThunkHandle by auto
      next
        case (HTreeHandle t2)
        then have "\<exists>t1. h1 = HTreeHandle t1"
          using X_preserve_tree_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] EQH by auto
        then obtain t1 where T1: "h1 = HTreeHandle t1" by auto
        then have EQTREE: "X (HTreeHandle t1) (HTreeHandle t2)" using EQH HTreeHandle by auto

        obtain tree2' where "eval_tree_with_fuel f' t2 = Some tree2'"
                     and   V2: "v2 = HTreeHandle tree2'"
          using ASSM HTreeHandle by (cases "eval_tree_with_fuel f' t2") auto
        then obtain tree1' where "evals_tree_to t1 tree1'"
                           and   EQTREE: "X (HTreeHandle tree1') (HTreeHandle tree2')"
          using eq_tree_eval_fuel_n[OF create_tree_cong X_tree_reasons eval_cong_f' EQTREE]
          by auto
        then obtain fuel where "eval_tree_with_fuel fuel t1 = Some tree1'" 
          using evals_tree_to_def by auto
        then have "eval_with_fuel (Suc fuel) h1 = Some (HTreeHandle tree1')" using T1 by auto
        then have "evals_to h1 (HTreeHandle tree1')" using evals_to_def by blast
        then show ?thesis using V2 EQTREE by auto
      next
        case (HEncodeHandle e2)
        then have "\<exists>e1. h1 = HEncodeHandle e1"
          using X_preserve_encode_rev[OF X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode] EQH by auto
        then obtain e1 where E1: "h1 = HEncodeHandle e1" by auto
        then have EQENCODE: "X (HEncodeHandle e1) (HEncodeHandle e2)" 
          using EQH HEncodeHandle by auto

        obtain h2' where "execute_with_fuel f' e2 = Some h2'"
                   and   Eval2: "eval_with_fuel f' h2' = Some v2"
          using ASSM HEncodeHandle
          by (cases "execute_with_fuel f' e2") auto
        then obtain h1' where "executes_to e1 h1'"
                        and   EQ': "X h1' h2'"
          using execute_with_fuel_n[OF get_encode_thunk_cong relevant_IH_force EQENCODE] 
          by blast
        then obtain fuel where Fuel1: "execute_with_fuel fuel e1 = Some h1'" 
          using executes_to_def by auto

        obtain v1 where "evals_to h1' v1" and EQRES: "X v1 v2"
          using Suc.IH EQ' Eval2 by blast
        then obtain fuel' where Fuel2: "eval_with_fuel fuel' h1' = Some v1" 
          using evals_to_def by auto

        let ?f = "max fuel fuel'"
        let ?f1 = "?f - fuel"
        let ?f2 = "?f - fuel'"

        have Fuel1: "execute_with_fuel (fuel + ?f1) e1 = Some h1'"
          using execute_with_fuel_padding[OF Fuel1] .
        have Fuel2: "eval_with_fuel (fuel' + ?f2) h1' = Some v1"
          using eval_with_fuel_padding[OF Fuel2] .
        have "eval_with_fuel (Suc ?f) h1 = Some v1" using Fuel1 Fuel2 E1 by auto
        then show ?thesis using evals_to_def EQRES by blast
      qed
    qed
  qed
qed

lemma forces_X:
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
  assumes get_encode_thunk_cong: "\<And>e1 e2. X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes X_tree_reasons: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
    list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_thunk_reasons: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow> (
     X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  assumes X_thunk_single_step: "\<And>t1 t2. think t1 = Some (HThunkHandle t2) \<Longrightarrow>
                               X (HThunkHandle t1) (HThunkHandle t2)" 
  assumes E: "X (HThunkHandle h1) (HThunkHandle h2)"
  shows "rel_opt X (force h1) (force h2)"
proof -
  have force_all_n: "\<And>h1 h2 n. X h1 h2 \<Longrightarrow>
       ((\<exists>t1. h1 = HThunkHandle t1) \<longrightarrow>
        (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v1. force_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2))))
      \<and>
       ((\<exists>t2. h2 = HThunkHandle t2) \<longrightarrow>
        (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v2. force_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1 v2))))"
      using eq_forces_to_induct[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
           create_blob_cong create_tree_cong create_encode_cong get_encode_thunk_cong
           X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode
           X_tree_to_thunk X_self
           get_prog_cong X_tree_reasons X_thunk_reasons X_thunk_single_step] by auto

    show ?thesis
    proof (cases "force h1")
      case None
      then have None1: "force h1 = None" by auto
      
      then show ?thesis
      proof (cases "force h2")
        case None
        then show ?thesis using None1 by auto
      next
        case (Some v2)
        then have "forces_to h2 v2" using force_some by auto
        then obtain n2 where F2: "force_with_fuel n2 h2 = Some v2"
          using forces_to_def by auto

        obtain v1 where "forces_to h1 v1" and "X v1 v2"
          using force_all_n[of "HThunkHandle h1" "HThunkHandle h2"] E F2 by blast
        then have "force h1 = Some v1" using force_unique by auto
        then show ?thesis using None1 by auto
      qed
    next
      case (Some v1)
      then have Some1: "forces_to h1 v1" using force_some by auto
      then obtain n1 where F1: "force_with_fuel n1 h1 = Some v1"
        using forces_to_def by blast

      obtain v2 where "forces_to h2 v2" and EQRES: "X v1 v2"
        using force_all_n[of "HThunkHandle h1" "HThunkHandle h2"] E F1 by blast
      then have "force h2 = Some v2" using force_unique by auto
      then show ?thesis using EQRES Some by auto
    qed
  qed

lemma evals_X:
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
  assumes get_encode_thunk_cong: "\<And>e1 e2. X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes X_tree_reasons: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
    list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_thunk_reasons: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow> (
     X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  assumes X_thunk_single_step: "\<And>t1 t2. think t1 = Some (HThunkHandle t2) \<Longrightarrow>
                               X (HThunkHandle t1) (HThunkHandle t2)" 
  assumes E: "X h1 h2"
  shows "rel_opt X (eval h1) (eval h2)"
proof -
  have eval_all_n: "\<And>h1 h2 n. X h1 h2 \<Longrightarrow>
        (\<forall>v1. eval_with_fuel n h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
      \<and>
        (\<forall>v2. eval_with_fuel n h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))"
      using eq_forces_to_induct[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
           create_blob_cong create_tree_cong create_encode_cong get_encode_thunk_cong
           X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode
           X_tree_to_thunk X_self
           get_prog_cong X_tree_reasons X_thunk_reasons X_thunk_single_step] by auto

    show ?thesis
    proof (cases "eval h1")
      case None
      then have None1: "eval h1 = None" by auto
      
      then show ?thesis
      proof (cases "eval h2")
        case None
        then show ?thesis using None1 by auto
      next
        case (Some v2)
        then have "evals_to h2 v2" using eval_some by auto
        then obtain n2 where F2: "eval_with_fuel n2 h2 = Some v2"
          using evals_to_def by auto

        obtain v1 where "evals_to h1 v1" and "X v1 v2"
          using eval_all_n[of "h1" "h2"] E F2 by blast
        then have "eval h1 = Some v1" using eval_unique by auto
        then show ?thesis using None1 by auto
      qed
    next
      case (Some v1)
      then have Some1: "evals_to h1 v1" using eval_some by auto
      then obtain n1 where F1: "eval_with_fuel n1 h1 = Some v1"
        using evals_to_def by blast

      obtain v2 where "evals_to h2 v2" and EQRES: "X v1 v2"
        using eval_all_n[of "h1" "h2"] E F1 by blast
      then have "eval h2 = Some v2" using eval_unique by auto
      then show ?thesis using EQRES Some by auto
    qed
  qed

lemma think_X:
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
  assumes get_encode_thunk_cong: "\<And>e1 e2. X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_preserve_encode: "\<And>e h. X (HEncodeHandle e) h \<Longrightarrow> \<exists>e'. h = (HEncodeHandle e')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes X_tree_reasons: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
    list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_thunk_reasons: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow> (
     X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  assumes X_thunk_single_step: "\<And>t1 t2. think t1 = Some (HThunkHandle t2) \<Longrightarrow>
                               X (HThunkHandle t1) (HThunkHandle t2)" 
  assumes E: "X (HThunkHandle h1) (HThunkHandle h2)"
  shows "rel_opt X (think h1) (think h2) \<or> (think h1 = Some (HThunkHandle h2)) \<or> (think h1 = Some (HEncodeHandle (create_encode h2)))"
proof -
  have think_all_n: "\<And>h1 h2 n. X h1 h2 \<Longrightarrow>
      ((\<exists>t1. h1 = HThunkHandle t1) \<longrightarrow>
        (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v1. think_with_fuel n t1 = Some v1 \<longrightarrow> ((\<exists>v2. thinks_to t2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle t2 \<or> v1 = HEncodeHandle (create_encode t2)))))
      \<and>
       ((\<exists>t2. h2 = HThunkHandle t2) \<longrightarrow>
        (\<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> (\<forall>v2. think_with_fuel n t2 = Some v2 \<longrightarrow> ((\<exists>v1. thinks_to t1 v1 \<and> X v1 v2) \<or> thinks_to t1 (HThunkHandle t2) \<or> thinks_to t1 (HEncodeHandle (create_encode t2))  ))))"
      using eq_forces_to_induct[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
           create_blob_cong create_tree_cong create_encode_cong get_encode_thunk_cong
           X_preserve_blob X_preserve_tree X_preserve_thunk X_preserve_encode
           X_tree_to_thunk X_self
           get_prog_cong X_tree_reasons X_thunk_reasons X_thunk_single_step] by auto

    show ?thesis
    proof (cases "think h1")
      case None
      then have None1: "think h1 = None" by auto
      
      then show ?thesis
      proof (cases "think h2")
        case None
        then show ?thesis using None1 by auto
      next
        case (Some v2)
        then have "thinks_to h2 v2" using think_some by auto
        then obtain n2 where F2: "think_with_fuel n2 h2 = Some v2"
          using thinks_to_def by auto

        have "(\<exists>v1. thinks_to h1 v1 \<and> X v1 v2) \<or> thinks_to h1 (HThunkHandle h2) \<or> thinks_to h1 (HEncodeHandle (create_encode h2))"
          using think_all_n[of "HThunkHandle h1" "HThunkHandle h2"] E F2 by blast

        then show ?thesis
        proof
          assume "\<exists>v1. thinks_to h1 v1 \<and> X v1 v2"
          then obtain v1 where "thinks_to h1 v1" and "X v1 v2" by auto
          then have "think h1 = Some v1" using think_unique by auto
          then show ?thesis using None1 by auto
        next
          assume "thinks_to h1 (HThunkHandle h2) \<or> thinks_to h1 (HEncodeHandle (create_encode h2))"
          then show ?thesis
          proof
            assume "thinks_to h1 (HThunkHandle h2)"
            then show ?thesis using think_unique by auto
          next
            assume "thinks_to h1 (HEncodeHandle (create_encode h2))"
            then have "think h1 = Some (HEncodeHandle (create_encode h2))" using think_unique by auto
            then show ?thesis using think_unique by blast
          qed
        qed
      qed
    next
      case (Some v1)
      then have Some1: "thinks_to h1 v1" using think_some by auto
      then obtain n1 where F1: "think_with_fuel n1 h1 = Some v1"
        using thinks_to_def by blast

      have "(\<exists>v2. thinks_to h2 v2 \<and> X v1 v2) \<or> v1 = HThunkHandle h2 \<or> v1 = HEncodeHandle (create_encode h2)"
        using think_all_n[of "HThunkHandle h1" "HThunkHandle h2"] E F1 by blast

      then show ?thesis
      proof
        assume "\<exists>v2. thinks_to h2 v2 \<and> X v1 v2"
        then obtain v2 where "thinks_to h2 v2" and EQRES: "X v1 v2" by auto
        then have "think h2 = Some v2" using think_unique by auto
        then show ?thesis using EQRES Some by auto
      next
        assume "v1 = HThunkHandle h2 \<or> v1 = HEncodeHandle (create_encode h2)"
        then show ?thesis
        proof
          assume "v1 = HThunkHandle h2"
          then have "thinks_to h1 (HThunkHandle h2)" using Some1 by auto
          then show ?thesis using think_unique by auto
        next
          assume "v1 = HEncodeHandle (create_encode h2)"
          then have "thinks_to h1 (HEncodeHandle (create_encode h2))" using Some1 by auto
          then show ?thesis using think_unique by auto
        qed
      qed
    qed
  qed

(* 7. Given two equivalent handles, if forcing the first one gives some output handle,
forcing the second one gives an equivalent output handle*)
                          
coinductive R :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  R_from_eq:
    "eq h1 h2 \<Longrightarrow> R h1 h2"
| RTree_strong:
    "list_all2 (\<lambda>x y. R x y \<or> eq x y) (get_tree_raw t1) (get_tree_raw t2)
     \<Longrightarrow> R (HTreeHandle t1) (HTreeHandle t2)"
| R_tree_to_thunk:
    "R (HTreeHandle t1) (HTreeHandle t2)
     \<Longrightarrow> R (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
| R_thunk_some_res:
  "think t1 = Some r1 \<Longrightarrow>
   think t2 = Some r2 \<Longrightarrow>
   R r1 r2 \<Longrightarrow>
   R (HThunkHandle t1) (HThunkHandle t2)"
| R_encode:
  "R (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow>
   R (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"

lemma list_all2_RorEq_to_eq:
  assumes IH: "\<And>x y. R x y \<Longrightarrow> eq x y"
  assumes L:  "list_all2 (\<lambda>x y. R x y \<or> eq x y) xs ys"
  shows       "list_all2 eq xs ys"
  using L
  by (rule list_all2_mono) (auto dest: IH)

lemma eq_to_R:
  assumes "eq x y"
  shows "R x y"
  using assms
  by (rule R.R_from_eq)

lemma RorEq_to_eq:
  assumes "R x y \<or> eq x y"
  shows "R x y"
proof -
  from assms show "R x y"
  proof
    assume "R x y" then show "R x y" by assumption
  next
    assume "eq x y" then show "R x y" by (rule R.R_from_eq) 
  qed
qed

lemma list_all2_RorEq_to_R:
  assumes "list_all2 (\<lambda>x y. R x y \<or> eq x y) xs ys"
  shows   "list_all2 R xs ys"
  using assms
  by (rule list_all2_mono) (auto intro: RorEq_to_eq)

lemma list_all2_Eq_to_R:
  assumes "list_all2 (\<lambda>x y. eq x y) xs ys"
  shows   "list_all2 R xs ys"
  using assms
  by (rule list_all2_mono) (auto intro: eq_to_R)

lemma list_all2_eq_imp_RorEq:
  assumes H: "list_all2 eq xs ys"
  shows "list_all2 (\<lambda>x y. R x y \<or> eq x y) xs ys"
proof -
  have step: "\<And>x y. eq x y \<Longrightarrow> (R x y \<or> eq x y)"
    by (intro disjI2)
  from H show ?thesis
    by (rule list_all2_mono[OF _ step])
qed

lemma list_all2_R_imp_RorEq:
  assumes "list_all2 R xs ys"
  shows "list_all2 (\<lambda>x y. R x y \<or> eq x y) xs ys"
  using assms
  by (induction xs ys rule: list_all2_induct) auto

lemma R_refl: "R h h"
  using eq_refl
  by (rule R.R_from_eq)

lemma list_all2_R_self:
"list_all2 R xs xs"
  using R_refl
  by (induction xs) auto

lemma get_blob_data_cong_R:
  assumes "R (HBlobHandle b1) (HBlobHandle b2)"
  shows "get_blob_data b1 = get_blob_data b2"
  using assms
  using get_blob_data_eq
  by (cases rule: R.cases) auto

lemma R_tree_children:
  assumes "R (HTreeHandle t1) (HTreeHandle t2)"
  shows "list_all2 R (get_tree_raw t1) (get_tree_raw t2)"
  using assms 
proof (cases rule: R.cases)  
  case R_from_eq
  then show ?thesis using eq_tree_children list_all2_Eq_to_R by auto 
next
  case RTree_strong
  then show ?thesis using list_all2_RorEq_to_R by auto
qed

lemma get_tree_size_cong_R:
  assumes "R (HTreeHandle t1) (HTreeHandle t2)"
  shows "get_tree_size t1 = get_tree_size t2"
  using R_tree_children[OF assms]
  by (simp add: get_tree_size_def list_all2_lengthD)

lemma get_tree_data_cong_R:
  assumes "R (HTreeHandle t1) (HTreeHandle t2)" and "i < get_tree_size t1"
  shows "R (get_tree_data t1 i) (get_tree_data t2 i)"
proof -
  have A: "i < length (get_tree_raw t1)" using assms(2) get_tree_size_def by auto
  have "list_all2 R (get_tree_raw t1) (get_tree_raw t2)" 
    using R_tree_children[OF assms(1)] .
  then have "R ((get_tree_raw t1) ! i) ((get_tree_raw t2) ! i)" 
    using list_all2_nthD[OF _ A] by auto
  then show ?thesis by (simp add: get_tree_data_def[symmetric]) 
qed

lemma create_blob_cong_R:
  assumes "d1 = d2"
  shows "R (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
  using create_blob_eq[OF assms]
  by (rule R.R_from_eq)

lemma create_tree_cong_R:
  assumes "list_all2 R xs ys"
  shows "R (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
proof -
  have X: "list_all2 R (get_tree_raw (create_tree xs)) (get_tree_raw (create_tree ys))"
    using assms by simp_all
  then have "list_all2 (\<lambda>x y. R x y \<or> eq x y)  (get_tree_raw (create_tree xs)) (get_tree_raw (create_tree ys))"
    using list_all2_R_imp_RorEq[OF X] by simp
  then show ?thesis by (rule R.RTree_strong)
qed

lemma create_encode_cong_R:
  assumes "R (HThunkHandle th1) (HThunkHandle th2)"
  shows "R (HEncodeHandle (create_encode th1)) (HEncodeHandle (create_encode th2))"
  using assms by (rule R.R_encode)

lemma get_encode_thunk_cong_R:
  assumes "R (HEncodeHandle e1) (HEncodeHandle e2)"
  shows "R (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
  using assms
proof (cases rule: R.cases)
  case R_from_eq
  then have "eq (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
    using get_encode_thunk_eq by auto
  then show ?thesis by (rule R.R_from_eq)
next
  case (R_encode t1 t2)
  then show ?thesis by auto
qed

lemma R_preserve_blob:
  assumes "R (HBlobHandle b) h"
  shows "\<exists>b'. h = (HBlobHandle b')"
  using assms
proof (cases rule: R.cases)
  case R_from_eq
  then show ?thesis using eq_same_kind_blob by simp
qed

lemma R_preserve_tree:
  assumes "R (HTreeHandle t1) h2"
  shows "\<exists>t2. h2 = HTreeHandle t2"
  using assms
proof (cases rule: R.cases)
  case R_from_eq
  then show ?thesis using eq_same_kind_tree by simp
next
  case RTree_strong
  then show ?thesis by simp
qed

lemma R_preserve_thunk:
  assumes "R (HThunkHandle th1) h2"
  shows "\<exists>th2. h2 = HThunkHandle th2"
  using assms
proof (cases rule: R.cases)
  case R_from_eq
  then show ?thesis using eq_same_kind_thunk[OF local.R_from_eq] by auto
next
  case R_tree_to_thunk
  then show ?thesis by simp
next
  case R_thunk_some_res
  then show ?thesis by simp
qed

lemma R_preserve_encode:
  assumes "R (HEncodeHandle th1) h2"
  shows "\<exists>th2. h2 = HEncodeHandle th2"
  using assms
proof (cases rule: R.cases)
  case R_from_eq
  then show ?thesis using eq_same_kind_encode[OF local.R_from_eq] by auto
next
  case R_encode
  then show ?thesis by auto
qed

lemma R_tree_reasons:
  assumes "R (HTreeHandle t1) (HTreeHandle t2)"
  shows "list_all2 R (get_tree_raw t1) (get_tree_raw t2)"
  using assms R_tree_children
  by auto

lemma eq_thunk_reasons:
"\<And>t1 t2.
       eq (handle.HThunkHandle t1)
        (handle.HThunkHandle
          t2) \<Longrightarrow>
       (eq (HTreeHandle
             (get_thunk_tree t1))
         (HTreeHandle
           (get_thunk_tree t2)) \<or>
        think t1 = None \<and>
        think t2 = None \<or>
        (\<exists>r1 r2.
            think t1 = Some r1 \<and>
            think t2 = Some r2 \<and>
            eq r1 r2) \<or>
        think t1 =
        Some
         (handle.HThunkHandle
           t2)) \<or>
       think t1 =
       Some
        (handle.HEncodeHandle
          (create_encode t2))"
  using eq_refl
proof -
  fix t1 t2
  assume ASSM: "eq (HThunkHandle t1) (HThunkHandle t2)"
  show "(eq (HTreeHandle
             (get_thunk_tree t1))
         (HTreeHandle
           (get_thunk_tree t2)) \<or>
        think t1 = None \<and>
        think t2 = None \<or>
        (\<exists>r1 r2.
            think t1 = Some r1 \<and>
            think t2 = Some r2 \<and>
            eq r1 r2) \<or>
        think t1 =
        Some
         (handle.HThunkHandle
           t2)) \<or>
       think t1 =
       Some
        (handle.HEncodeHandle
          (create_encode t2))"
    using ASSM eq_refl
    by (cases rule: eq.cases) auto
qed

lemma R_thunk_reasons:
  assumes "R (HThunkHandle t1) (HThunkHandle t2)"
  shows "R (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
        (think t1 = None \<and> think t2 = None) \<or>
        (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> R r1 r2) \<or>
        (think t1 = Some (HThunkHandle t2)) \<or>
        (think t1 = Some (HEncodeHandle (create_encode t2)))"
  using assms
proof (cases rule: R.cases)
  case R_from_eq
  then show ?thesis using eq_thunk_reasons eq_to_R by blast
next
  case R_tree_to_thunk
  then show ?thesis by auto
next
  case R_thunk_some_res
  then show ?thesis by auto
qed

lemma eq_thunk_single_step:
  assumes "think t1 = Some (HThunkHandle t2)"
  shows "eq (HThunkHandle t1) (HThunkHandle t2)"
  using assms
  by (rule eq.EqThunkSingleStep)

lemma R_thunk_single_step:
  assumes "think t1 = Some (HThunkHandle t2)"
  shows "R (HThunkHandle t1) (HThunkHandle t2)"
  using eq_thunk_single_step[OF assms]
  by (rule R.R_from_eq)

(* TODO: remove this axiom with real get_prog definition *) 
axiomatization where
  get_prog_R:
    "R (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"

axiomatization where
  get_prog_eq:
    "eq (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"

lemma R_impl_eq:
  assumes"R h1 h2"
  shows "eq h1 h2"
  using assms
proof (coinduction arbitrary: h1 h2 rule: eq.coinduct)
  case eq
  then show ?case
  proof (cases rule: R.cases)
    case R_from_eq
    then show ?thesis using list_all2_eq_imp_RorEq by (cases rule: eq.cases) auto
  next
    case (RTree_strong t1 t2)
    then have "list_all2 (\<lambda>h1 h2. (\<exists>h1' h2'. h1 = h1' \<and> h2 = h2' \<and> R h1' h2') \<or> eq h1 h2) (get_tree_raw t1)
       (get_tree_raw t2)"
      by auto
    then show ?thesis using RTree_strong by auto
  next
    case (R_thunk_some_res t1 r1 t2 r2)
    then show ?thesis by auto
  next
    case (R_tree_to_thunk t1 t2)

    let ?th1 = "create_thunk t1" 
    let ?th2 = "create_thunk t2"
    have Lastgoal: "R (HThunkHandle ?th1) (HThunkHandle ?th2)" using eq R_tree_to_thunk by auto

    have TH: "rel_opt R (think ?th1) (think ?th2) \<or> think ?th1 = Some (HThunkHandle ?th2) \<or> think ?th1 = Some (HEncodeHandle (create_encode ?th2))"
    proof (rule_tac X=R in think_X)
      fix b1 b2
      assume "R (HBlobHandle b1) (HBlobHandle b2)"
      then show "get_blob_data b1 = get_blob_data b2" 
        using get_blob_data_cong_R by auto
    next
      fix t1 t2
      assume "R (HTreeHandle t1) (HTreeHandle t2)"
      then show "get_tree_size t1 = get_tree_size t2" 
        using get_tree_size_cong_R by auto
    next
      fix t1 t2 j
      assume "R (HTreeHandle t1) (HTreeHandle t2)"
      and "j < get_tree_size t1"
      then show "R (get_tree_data t1 j) (get_tree_data t2 j)" 
        using get_tree_data_cong_R by auto
    next
      fix d1 d2 :: raw
      assume "d1 = d2"
      then show "R (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
        using create_blob_cong_R by auto
    next
      fix xs ys
      assume "list_all2 R xs ys"
      then show "R (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
        using create_tree_cong_R by auto
    next
      fix b h
      assume "R (HBlobHandle b) h"
      then show "\<exists>b'. h = HBlobHandle b'"
        using R_preserve_blob by auto
    next
      fix t h
      assume "R (HTreeHandle t) h"
      then show "\<exists>t'. h = HTreeHandle t'"
        using R_preserve_tree by auto
    next
      fix t h
      assume "R (HThunkHandle t) h"
      then show "\<exists>t'. h = HThunkHandle t'"
        using R_preserve_thunk by auto
    next
      fix t1 t2
      assume "R (HThunkHandle t1) (HThunkHandle t2)"
      then show "R (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"
        using create_encode_cong_R by auto
    next
      fix e1 e2
      assume "R (HEncodeHandle e1) (HEncodeHandle e2)"
      then show "R (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
        using get_encode_thunk_cong_R by auto
    next
      fix e h
      assume "R (HEncodeHandle e) h"
      then show "\<exists>e'. h = HEncodeHandle e'"
        using R_preserve_encode by auto
    next
      fix t1 t2
      assume "R (HTreeHandle t1) (HTreeHandle t2)"
      then show "R (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
        by (rule R.R_tree_to_thunk) 
    next
      fix h
      show "R h h"
        using R_refl .
    next
      fix t1 t2
      show "R (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
        using get_prog_R .
    next
      fix t1 t2
      assume "R (HTreeHandle t1) (HTreeHandle t2)"
      then show "list_all2 R (get_tree_raw t1) (get_tree_raw t2)"
        using R_tree_reasons by auto
    next 
      fix t1 t2
      assume "R (HThunkHandle t1) (HThunkHandle t2)"
      then show "(
     R (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> R r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
        using R_thunk_reasons by auto
    next
      fix t1 t2
      assume "think t1 = Some (HThunkHandle t2)"
      then show "R (HThunkHandle t1) (HThunkHandle t2)"
        using R_thunk_single_step by auto
    next
      show "R (HThunkHandle ?th1) (HThunkHandle ?th2)"
        using Lastgoal .
    qed

    then show ?thesis
    proof
      assume TH: "rel_opt R (think (create_thunk t1)) (think (create_thunk t2))"
      then show ?thesis
      proof (cases "think (create_thunk t1)")
        case None
        have "think (create_thunk t2) = None" 
          using TH None by (cases "think (create_thunk t2)") auto
        then show ?thesis using None R_tree_to_thunk by auto
      next
        case (Some r1)
        then obtain r2 where SOME2: "think (create_thunk t2) = Some r2"
                         and RRES: "R r1 r2"
          using TH by (cases "think (create_thunk t2)") auto
        have ROREQ: "R r1 r2 \<or> eq r1 r2" using RRES by auto
        then show ?thesis using Some SOME2 RRES R_tree_to_thunk  by blast
      qed
    next
      assume "think (create_thunk t1) = Some (HThunkHandle (create_thunk t2)) \<or> think (create_thunk t1) = Some (HEncodeHandle (create_encode (create_thunk t2)))"
      then show ?thesis 
      proof 
        assume "think (create_thunk t1) = Some (HThunkHandle (create_thunk t2))"
        then show ?thesis using R_tree_to_thunk by auto
      next
        assume "think (create_thunk t1) = Some (HEncodeHandle (create_encode (create_thunk t2)))"
        then show ?thesis using R_tree_to_thunk by auto
      qed
    qed
  next
    case (R_encode t1 t2)
    then show ?thesis by blast
  qed
qed

lemma eq_tree_to_thunk:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
  shows "eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
proof -
  have "R (HTreeHandle t1) (HTreeHandle t2)" using assms by (rule R.R_from_eq)
  then have "R (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))" by (rule R.R_tree_to_thunk)
  then show ?thesis using R_impl_eq by auto
qed

lemma force_eq:
  assumes "eq (HThunkHandle h1) (HThunkHandle h2)"
  shows "rel_opt eq (force h1) (force h2)"
proof -
  show ?thesis
    using forces_X[OF get_blob_data_eq get_tree_size_eq get_tree_data_eq create_blob_eq
                   create_tree_eq create_encode_eq get_encode_thunk_eq eq_same_kind_blob
                   eq_same_kind_tree eq_same_kind_thunk eq_same_kind_encode eq_tree_to_thunk
                   eq_refl get_prog_eq eq_tree_children eq_thunk_reasons eq_thunk_single_step assms]
    by auto
qed

lemma eval_eq:
  assumes "eq h1 h2"
  shows "rel_opt eq (eval h1) (eval h2)"
proof -
  show ?thesis
    using evals_X[OF get_blob_data_eq get_tree_size_eq get_tree_data_eq create_blob_eq
                   create_tree_eq create_encode_eq get_encode_thunk_eq eq_same_kind_blob
                   eq_same_kind_tree eq_same_kind_thunk eq_same_kind_encode eq_tree_to_thunk
                   eq_refl get_prog_eq eq_tree_children eq_thunk_reasons eq_thunk_single_step assms]
    by auto
qed

lemma list_all2_eq_refl:
  "list_all2 eq xs xs"
  using eq_refl
  by (induction xs) auto

lemma eq_tree_update1:
  assumes "eq a b"
  shows
    "eq (HTreeHandle (create_tree (pre @ a # post)))
        (HTreeHandle (create_tree (pre @ b # post)))"
proof -
  have H0: "list_all2 eq post post"
    using list_all2_eq_refl
    by auto
  then have H1: "list_all2 eq (a # post) (b # post)"
    using list_all2_append assms by auto

  have H2: "list_all2 eq pre pre" 
    using list_all2_eq_refl by auto
  thm list_all2_append

  have "list_all2 eq (pre @ a # post) (pre @ b # post)"
  proof (induction pre)
    case Nil
    then show ?case using H1 by auto
  next
    case (Cons x xs)
    have "eq x x" using eq_refl by auto
    then show ?case using Cons by auto
  qed

  then have "list_all2 eq (get_tree_raw (create_tree (pre @ a # post)))
                          (get_tree_raw (create_tree (pre @ b # post)))"
    by simp
  then show ?thesis by (rule eq.EqTree)
qed

lemma equivclp_tree_update1:
  assumes "equivclp eq a b"
  shows "equivclp eq (HTreeHandle (create_tree (pre @ (a # post))))
                     (HTreeHandle (create_tree (pre @ (b # post))))"
  using assms
proof (induction rule: equivclp_induct)
  case base 
  then show ?case by (rule equivclp_refl) 
next
  case (step y z)
  have X: "eq y z \<or> eq z y" using step by auto

  from X show ?case
  proof 
    assume "eq y z"
    then have "eq (HTreeHandle (create_tree (pre @ y # post)))
        (HTreeHandle (create_tree (pre @ z # post)))"
      using eq_tree_update1 by auto
    then have Y: "equivclp eq (HTreeHandle (create_tree (pre @ y # post)))
        (HTreeHandle (create_tree (pre @ z # post)))" by (rule r_into_equivclp)
   
    show ?case using equivclp_trans[OF step.IH Y] by auto
  next
    assume "eq z y"
    then have "eq (HTreeHandle (create_tree (pre @ z # post)))
        (HTreeHandle (create_tree (pre @ y # post)))"
      using eq_tree_update1 by auto
    then have Y: "equivclp eq (HTreeHandle (create_tree (pre @ y # post)))
        (HTreeHandle (create_tree (pre @ z # post)))" by (rule converse_r_into_equivclp)
    show ?case using equivclp_trans[OF step.IH Y] by auto
  qed
qed

lemma equivclp_tree_list_all2_prefix:
  assumes LA: "list_all2 (equivclp eq) xs ys"
  shows
    "equivclp eq (HTreeHandle (create_tree (pre @ xs)))
                 (HTreeHandle (create_tree (pre @ ys)))"
  using LA
proof (induction xs ys arbitrary: pre rule: list_all2_induct)
  case Nil
  then show ?case by (rule equivclp_refl)
next
  case (Cons x xs y ys)
  have head_step:
    "equivclp eq (HTreeHandle (create_tree (pre @ x # xs)))
                 (HTreeHandle (create_tree (pre @ y # xs)))"
    using Cons.hyps(1)
    by (rule equivclp_tree_update1[where post=xs])

  have tail_steps:
    "equivclp eq (HTreeHandle (create_tree ((pre @ [y]) @ xs)))
                 (HTreeHandle (create_tree ((pre @ [y]) @ ys)))"
    using Cons.IH[of "pre @ [y]"]
    by simp

  have tail_steps':
    "equivclp eq (HTreeHandle (create_tree (pre @ y # xs)))
                 (HTreeHandle (create_tree (pre @ y # ys)))"
    using tail_steps by simp

  show ?case
    using head_step tail_steps'
    by (rule equivclp_trans)
qed

lemma equivclp_tree_list_all2:
  assumes "list_all2 (equivclp eq) xs ys"
  shows   "equivclp eq (HTreeHandle (create_tree xs))
                       (HTreeHandle (create_tree ys))"
  using equivclp_tree_list_all2_prefix[where pre="[]", OF assms]
  by simp

lemma equivclp_thunk:
  assumes H: "equivclp eq h1 h2"
  shows "\<exists>t1. h1 = HTreeHandle t1 \<Longrightarrow> 
         \<exists>t1 t2. h1 = HTreeHandle t1 \<and> h2 = HTreeHandle t2 \<and> equivclp eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  using H
proof (induction rule: equivclp_induct)
  case base
  obtain t1 where T1: "h1 = HTreeHandle t1" using base by auto
  obtain t2 where T2: "h1 = HTreeHandle t2" using base by auto
  have "t1 = t2" using T1 T2 by simp
  then have "eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
    using eq_refl by auto
  then show ?case using T1 T2 r_into_equivclp by auto
next
  case (step y z)
  obtain t1 t2 where T1: "h1 = HTreeHandle t1"
               and   T2: "y = HTreeHandle t2"
               and  LHS: "equivclp eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
    using step.IH step.prems by auto

  have X: "eq y z \<or> eq z y" using step by auto
  from X show ?case
  proof
    assume Y: "eq y z"
    then obtain t3 where T3: "z = HTreeHandle t3" using eq_same_kind_tree T2 by auto

    have "eq (HThunkHandle (create_thunk t2)) (HThunkHandle (create_thunk t3))"
      using Y T2 T3 eq_tree_to_thunk by auto
    then have RHS: "equivclp eq (HThunkHandle (create_thunk t2)) (HThunkHandle (create_thunk t3))"
      using r_into_equivclp by auto

    have "equivclp eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t3))"
      using equivclp_trans[OF LHS RHS] by auto
    then show ?thesis using T1 T3 by auto
  next
    assume Y: "eq z y"
    then obtain t3 where T3: "z = HTreeHandle t3" using eq_same_kind_tree_rev T2 by auto

    have "eq (HThunkHandle (create_thunk t3)) (HThunkHandle (create_thunk t2))"
      using Y T2 T3 eq_tree_to_thunk by auto
    then have RHS: "equivclp eq (HThunkHandle (create_thunk t2)) (HThunkHandle (create_thunk t3))"
      using r_into_equivclp by auto

    have "equivclp eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t3))"
      using equivclp_trans[OF LHS RHS] by auto
    then show ?thesis using T1 T3 by auto
  qed
qed

lemma force_equivclp:
  assumes H: "equivclp eq h1 h2"
  shows "\<exists>t1. h1 = HThunkHandle t1 \<Longrightarrow> 
  \<exists>t1 t2. h1 = HThunkHandle t1 \<and> h2 = HThunkHandle t2 \<and> rel_opt (equivclp eq) (force t1) (force t2)"
  using H
proof (induction rule: equivclp_induct)
  case base
  then obtain t1 where T1: "h1 = HThunkHandle t1" by auto
  then obtain t2 where T2: "h1 = HThunkHandle t2" and "t1 = t2" by auto
  then have "rel_opt eq (force t1) (force t2)"
    using eq_refl by (cases "force t1") auto
  then show ?case using T1 T2 r_into_equivclp by (cases "force t1") auto
next
  case (step y z)
  then obtain t1 t2 where H1: "h1 = HThunkHandle t1"
                    and   Y: "y = HThunkHandle t2"
                    and   Rel: "rel_opt (equivclp eq) (force t1) (force t2)"
    by auto
  have X: "eq y z \<or> eq z y" using step by auto

  show ?case
  proof (cases "force t1")
    case None 
    then have None1: "force t1 = None" .
    then have None2: "force t2 = None" using Rel by (cases "force t2") auto

    from X have "\<exists>t3. z = HThunkHandle t3"
      using Y eq_same_kind_thunk eq_same_kind_thunk_rev by auto
    then obtain t3 where Z: "z = HThunkHandle t3" by auto

    from X have "force t3 = None"
    proof
      assume "eq y z"
      then have "rel_opt eq (force t2) (force t3)" using Y Z force_eq by auto
      then show ?thesis using None2 by (cases "force t3") auto
    next
      assume "eq z y"
      then have "rel_opt eq (force t3) (force t2)" using Y Z force_eq by auto
      then show ?thesis using None2 by (cases "force t3") auto
    qed
    then show ?thesis using H1 Z None1 by auto
  next
    case (Some a1)
    then obtain a2 where Some2: "force t2 = Some a2"
                     and EQ1: "equivclp eq a1 a2"
      using Rel by (cases "force t2") auto

    from X have "\<exists>t3. z = HThunkHandle t3"
      using Y eq_same_kind_thunk eq_same_kind_thunk_rev by auto
    then obtain t3 where Z: "z = HThunkHandle t3" by auto

    from X have "\<exists>a3. force t3 = Some a3 \<and> equivclp eq a2 a3"
    proof
      assume "eq y z"
      then have "rel_opt eq (force t2) (force t3)" using Y Z force_eq by auto
      then obtain a3 where "force t3 = Some a3 \<and> eq a2 a3" using Some2 by (cases "force t3") auto
      then have "force t3 = Some a3 \<and> equivclp eq a2 a3" using r_into_equivclp by blast
      then show ?thesis by auto
    next
      assume "eq z y"
      then have "rel_opt eq (force t3) (force t2)" using Y Z force_eq by auto
      then obtain a3 where "force t3 = Some a3 \<and> eq a3 a2" using Some2 by (cases "force t3") auto
      then have "force t3 = Some a3 \<and> equivclp eq a2 a3" using r_into_equivclp by blast
      then show ?thesis by auto
    qed
    then obtain a3 where Some3: "force t3 = Some a3"
                     and EQ2: "equivclp eq a2 a3"
      by auto

    show ?thesis using Some Some3 EQ1 EQ2 equivclp_trans H1 Z by auto
  qed
qed

lemma force_with_fuel_to_equivclp_eq:
  "\<And>t h. force_with_fuel n t = Some h 
        \<Longrightarrow> \<exists>t'. think t' = Some h \<and> equivclp eq (HThunkHandle t) (HThunkHandle t')"
proof (induction n)
  case 0
  have "force_with_fuel 0 t = None" by auto
  then show ?case using 0 by auto
next
  case (Suc n')
  then show ?case
  proof (cases "think_with_fuel n' t")
    case None
    then have "force_with_fuel (Suc n') t = None" by auto
    then show ?thesis using Suc by auto
  next
    case (Some r)
    then show ?thesis
    proof (cases r)
      case (HBlobHandle)
      then have "think_with_fuel n' t = Some h" 
        using Suc Some by auto
      then have RES: "think t = Some h" using thinks_to_def think_unique by blast

      have "equivclp eq (HThunkHandle t) (HThunkHandle t)"
        using eq_refl r_into_equivclp by auto
      then show ?thesis using RES by auto
    next
      case (HTreeHandle)
      then have "think_with_fuel n' t = Some h"
        using Suc Some by auto
      then have RES: "think t = Some h" using thinks_to_def think_unique by blast

      have "equivclp eq (HThunkHandle t) (HThunkHandle t)"
        using eq_refl r_into_equivclp by auto
      then show ?thesis using RES by auto
    next
      case (HThunkHandle thunk)
      then have "force_with_fuel n' thunk = Some h"
        using Suc Some by auto
      then obtain t' where Think: "think t' = Some h"
                     and  Tail: "equivclp eq (HThunkHandle thunk) (HThunkHandle t')"
        using Suc.IH by auto

      have "think t = Some (HThunkHandle thunk)"
        using Some HThunkHandle thinks_to_def think_unique by blast
      then have "eq (HThunkHandle t) (HThunkHandle thunk)" by (rule eq.EqThunkSingleStep)
      then have "equivclp eq (HThunkHandle t) (HThunkHandle t')"
        using equivclp_trans[of "eq" "HThunkHandle t" "HThunkHandle thunk" "HThunkHandle t'"] Tail by auto
      then show ?thesis using Think by blast
    next
      case (HEncodeHandle encode)

      let ?thunk = "get_encode_thunk encode"
      have "force_with_fuel n' ?thunk = Some h"
        using Suc Some HEncodeHandle by auto
      then obtain t' where Think: "think t' = Some h"
                     and  Tail: "equivclp eq (HThunkHandle ?thunk) (HThunkHandle t')"
        using Suc.IH by auto

      have "think t = Some (HEncodeHandle encode)"
        using Some HEncodeHandle thinks_to_def think_unique by blast
      then have "eq (HThunkHandle t) (HThunkHandle ?thunk)" by (rule eq.EqThunkSingleStepEncode)
      then have "equivclp eq (HThunkHandle t) (HThunkHandle t')"
        using equivclp_trans[of "eq" "HThunkHandle t" "HThunkHandle ?thunk" "HThunkHandle t'"] Tail by auto
      then show ?thesis using Think by blast
    qed
  qed
qed

axiomatization where
  thunk_for_all_blob:
    "\<exists>b. h = HBlobHandle b \<Longrightarrow> \<exists>th. think th = Some h"

axiomatization where
  thunk_for_all_tree:
    "\<exists>t. h = HTreeHandle t \<Longrightarrow> \<exists>th. think th = Some h"

lemma equivclp_eq_same_kind:
  assumes "equivclp eq r1 r2"
  shows "get_type r1 = get_type r2"
  using assms eq_same_type
  by (induction rule: equivclp_induct) auto

corollary equivclp_eq_preserve_blob:
  assumes "equivclp eq (HBlobHandle b1) r2"
  shows "\<exists>b2. r2 = HBlobHandle b2"
  using equivclp_eq_same_kind[OF assms]
  by (cases r2) auto

corollary equivclp_eq_preserve_tree:
  assumes "equivclp eq (HTreeHandle t1) r2"
  shows "\<exists>t2. r2 = HTreeHandle t2"
  using equivclp_eq_same_kind[OF assms]
  by (cases r2) auto

lemma equivclp_eq_thunk_some_res:
  assumes "equivclp eq r1 r2"
  shows "\<And>t1 t2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> ((\<exists>b1. r1 = HBlobHandle b1) \<or> (\<exists>t1. r1 = HTreeHandle t1)) \<longrightarrow> equivclp eq (HThunkHandle t1) (HThunkHandle t2)"
  using assms
proof (induction rule: equivclp_induct)
  case base
  then show ?case
  proof (intro impI)
    assume "think t1 = Some r1 \<and> think t2 = Some r1 \<and> ((\<exists>b1. r1 = HBlobHandle b1) \<or> (\<exists>t1. r1 = HTreeHandle t1))"
    then have "think t1 = Some r1" and "think t2 = Some r1" and "eq r1 r1" using eq_refl by auto
    then have "eq (HThunkHandle t1) (HThunkHandle t2)" by (rule eq.EqThunkSomeRes)
    then show "equivclp eq (HThunkHandle t1) (HThunkHandle t2)" using r_into_equivclp by auto
  qed
next
  case (step y z)
  then show ?case
  proof (intro impI)
    assume "think t1 = Some r1 \<and> think t2 = Some z \<and> ((\<exists>b1. r1 = HBlobHandle b1) \<or> (\<exists>t1. r1 = HTreeHandle t1))"
    then have T1: "think t1 = Some r1"
          and T2: "think t2 = Some z"
          and H: "(\<exists>b1. r1 = HBlobHandle b1) \<or> (\<exists>t1. r1 = HTreeHandle t1)"
      by auto

    have H': "get_type r1 = get_type y"  using step.hyps(1) equivclp_eq_same_kind by auto
    have "(\<exists>b2. y = HBlobHandle b2) \<or> (\<exists>t2. y = HTreeHandle t2)"
      using H
    proof
      assume "\<exists>b1. r1 = HBlobHandle b1"
      then show ?thesis using H' by (cases y) auto
    next
      assume "\<exists>t1. r1 = HTreeHandle t1"
      then show ?thesis using H' by (cases y) auto
    qed
    then obtain t3 where T3: "think t3 = Some y" using thunk_for_all_blob thunk_for_all_tree by auto
    then have E13: "equivclp eq (HThunkHandle t1) (HThunkHandle t3)" using T1 step.IH H by auto

    have "eq (HThunkHandle t3) (HThunkHandle t2) \<or> eq (HThunkHandle t2) (HThunkHandle t3)"
      using step.hyps(2) eq.EqThunkSomeRes T2 T3 by auto
    then have E32: "equivclp eq (HThunkHandle t3) (HThunkHandle t2)" by auto

    show "equivclp eq (HThunkHandle t1) (HThunkHandle t2)"
      using E13 E32 equivclp_trans[of eq "(HThunkHandle t1)" "(HThunkHandle t3)" "(HThunkHandle t2)"] by auto
  qed
qed

lemma force_to_equivclp_eq:
  assumes F1: "force t1 = Some r1"
      and F2: "force t2 = Some r2"
      and H: "equivclp eq r1 r2"
    shows "equivclp eq (HThunkHandle t1) (HThunkHandle t2)"
proof -
  obtain f1 where "force_with_fuel f1 t1 = Some r1"
    using F1 force_some forces_to_def by blast
  then obtain t1' where T1: "think t1' = Some r1"
                    and E1: "equivclp eq (HThunkHandle t1) (HThunkHandle t1')"
    using force_with_fuel_to_equivclp_eq by blast

  obtain f2 where "force_with_fuel f2 t2 = Some r2"
    using F2 force_some forces_to_def by blast
  then obtain t2' where T2: "think t2' = Some r2"
                    and E2: "equivclp eq (HThunkHandle t2) (HThunkHandle t2')"
    using force_with_fuel_to_equivclp_eq by blast


  have "equivclp eq (HThunkHandle t1') (HThunkHandle t2')"
    using H T1 T2 force_not_thunk[OF F1] equivclp_eq_thunk_some_res by auto
  then have "equivclp eq (HThunkHandle t1) (HThunkHandle t2')"
    using E1 equivclp_trans[of eq] by auto
  then show ?thesis using equivclp_sym[OF E2] equivclp_trans[of eq] by auto
qed

lemma equivclp_eq_thunk_to_encode:
  assumes H: "equivclp eq h1 h2"
      and "\<exists>th1. h1 = HThunkHandle th1"
  shows "\<exists>th1 th2. h1 = (HThunkHandle th1) \<and> h2 = (HThunkHandle th2) \<and> equivclp eq (HEncodeHandle (create_encode th1)) (HEncodeHandle (create_encode th2))"
  using assms
proof (induction rule: equivclp_induct)
  case base
  then show ?case using eq.EqSelf by auto 
next
  case (step y z)
  then obtain th1 th2 where TH1: "h1 = HThunkHandle th1"
                        and TH2: "y = HThunkHandle th2"
                        and EQ: "equivclp eq (HEncodeHandle (create_encode th1))
                                         (HEncodeHandle (create_encode th2))"
    by auto

  have "get_type y = get_type z"
    using step.hyps(2) equivclp_eq_same_kind by blast
  then obtain th3 where TH3: "z = HThunkHandle th3"
    using TH2 by (cases z) auto
  then have EQ1: "equivclp eq (HEncodeHandle (create_encode th2)) (HEncodeHandle (create_encode th3))"
    using eq.EqEncode TH2 step.hyps(2) r_into_equivclp by auto
  show ?case using equivclp_trans[OF EQ EQ1] TH1 TH3 by auto
qed

inductive coupon_force :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_storage :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_eq :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  CouponForce:
  "force t = Some r \<Longrightarrow> coupon_force (HThunkHandle  t) r"
| CouponStorage:
  "(get_blob_data b1 = get_blob_data b2) \<Longrightarrow>
   coupon_storage (HBlobHandle b1) (HBlobHandle b2)"
| CouponBlob:
  "coupon_storage h1 h2 \<Longrightarrow> coupon_eq h1 h2"
| CouponTree:
  "list_all2 (\<lambda>h1 h2. coupon_eq h1 h2) (get_tree_raw t1) (get_tree_raw t2) 
   \<Longrightarrow> coupon_eq (HTreeHandle t1) (HTreeHandle t2)"
| CouponThunk:
  "coupon_force h1 r1 \<Longrightarrow>
   coupon_force h2 r2 \<Longrightarrow>
   coupon_eq r1 r2 \<Longrightarrow>
   coupon_eq h1 h2"
| CouponThunkTree:
  "coupon_eq (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
   coupon_eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
| CouponThunkForce:
  "coupon_eq h1 h2 \<Longrightarrow>
   coupon_force h1 r1 \<Longrightarrow>
   coupon_force h2 r2 \<Longrightarrow>
   coupon_eq r1 r2"
| CouponEncode:
  "coupon_eq (HThunkHandle th1) (HThunkHandle th2) \<Longrightarrow>
   coupon_eq (HEncodeHandle (create_encode th1)) (HEncodeHandle (create_encode th2))"
| CouponSelf:
   "coupon_eq h h"
| CouponSym:
   "coupon_eq h1 h2 \<Longrightarrow> coupon_eq h2 h1"
| CouponTrans:
   "coupon_eq h1 h2 \<Longrightarrow> coupon_eq h2 h3 \<Longrightarrow> coupon_eq h1 h3"

lemma coupon_sound:
  "(coupon_force h r \<longrightarrow> (\<exists>th. h = HThunkHandle th \<and> force th = Some r)) \<and> (coupon_storage h1 h2 \<longrightarrow> (\<exists>b1 b2. h1 = HBlobHandle b1 \<and> h2 = HBlobHandle b2 \<and> get_blob_data b1 = get_blob_data b2)) \<and> (coupon_eq h1 h2 \<longrightarrow> equivclp eq h1 h2)"
proof (induction rule: coupon_force_coupon_storage_coupon_eq.induct)
  case (CouponForce th r)
  then show ?case by auto
next
  case (CouponStorage b1 b2)
  then show ?case by auto
next
  case (CouponBlob h1 h2)
  obtain b1 b2 where "h1 = HBlobHandle b1"
                 and "h2 = HBlobHandle b2"
                 and "get_blob_data b1 = get_blob_data b2"
    using CouponBlob.IH
    by auto
  then show ?case using eq.EqBlob[of b1 b2] r_into_equivclp[of eq "HBlobHandle b1" "HBlobHandle b2"] by auto
next
  case (CouponTree t1 t2)
  let ?t1 = "get_tree_raw t1"
  let ?t2 = "get_tree_raw t2"
  have "list_all2 (equivclp eq) ?t1 ?t2" using CouponTree list_all2_mono by auto
  then show ?case using equivclp_tree_list_all2[of ?t1 ?t2] by auto
next
  case (CouponThunk th1 r1 th2 r2)
  then show ?case using CouponThunk.IH force_to_equivclp_eq by auto
next
  case (CouponThunkTree t1 t2)
  then show ?case using equivclp_thunk by auto
next
  case (CouponThunkForce h1 h2 r1 r2)
  then obtain th1 th2 where "h1 = HThunkHandle th1" and F1: "force th1 = Some r1" and "h2 = HThunkHandle th2" and F2: "force th2 = Some r2" by auto
  then have "rel_opt (equivclp eq) (force th1) (force th2)" using CouponThunkForce force_equivclp by blast
  then show ?case using F1 F2 by auto
next 
  case (CouponEncode th1 th2)
  then show ?case using equivclp_eq_thunk_to_encode by auto
next
  case (CouponSelf h)
  then show ?case using eq_refl r_into_equivclp by auto
next
  case (CouponSym h1 h2)
  then show ?case using equivclp_sym[of eq h1 h2] by auto
next
  case (CouponTrans h1 h2 h3)
  then show ?case using equivclp_trans[of eq h1 h2 h3] by auto
qed

lemma equivclp_eq_eval:
  assumes H: "equivclp eq h1 h2"
  shows "rel_opt (equivclp eq) (eval h1) (eval h2)"
  using H
proof (induction rule: equivclp_induct)
  case base
  then show ?case by (cases "eval h1") auto
next
  case (step y z)
  have "(rel_opt eq (eval y) (eval z)) \<or> (rel_opt eq (eval z) (eval y))" 
    using eval_eq step.hyps(2) by auto
  then have "rel_opt (equivclp eq) (eval y) (eval z)" 
    using r_into_equivclp by (cases "eval y"; cases "eval z") auto
  then show ?case using local.step(3) equivclp_trans 
    by (cases "eval h1"; cases "eval y"; cases "eval z") auto
qed

lemma equivclp_eq_same_data:
  assumes H: "equivclp eq h1 h2"
      and "\<exists>b1. h1 = HBlobHandle b1"
    shows "\<exists>b1 b2. h1 = HBlobHandle b1 \<and> h2 = HBlobHandle b2 \<and> get_blob_data b1 = get_blob_data b2"
  using H
proof (induction rule: equivclp_induct)
  case base
  then show ?case using assms(2) by auto
next
  case (step y z)
  then obtain b1 b2 where B1: "h1 = HBlobHandle b1"
                      and B2: "y = HBlobHandle b2"
                      and EQD: "get_blob_data b1 = get_blob_data b2"
    by auto

  have "get_type y = get_type z" using eq_same_type step.hyps(2) by auto
  then obtain b3 where B3: "z = HBlobHandle b3" using B2 by (cases z) auto
  then have "get_blob_data b2 = get_blob_data b3" using B2 step.hyps(2) get_blob_data_eq by auto
  then have "get_blob_data b1 = get_blob_data b3" using EQD by auto
  then show ?case using B1 B3 by auto
qed

corollary coupon_eq_blob_same_data:
  assumes "coupon_eq (HBlobHandle b1) (HBlobHandle b2)"
  shows "get_blob_data b1 = get_blob_data b2"
proof -
  let ?h1 = "HBlobHandle b1"
  let ?h2 = "HBlobHandle b2"
  have "equivclp eq ?h1 ?h2" using assms coupon_sound by auto
  then show "get_blob_data b1 = get_blob_data b2" using equivclp_eq_same_data by auto
qed

datatype coupon_type =
  Force | Storage | Eq

datatype request_type =
  Blob | Tree | Thunk | ThunkTree | ThunkForce | Encode | Self | Sym | Trans

record coupon = 
  type :: coupon_type
  lhs :: handle
  rhs :: handle

fun get_coupon_type :: "coupon \<Rightarrow> nat" where
  "get_coupon_type c =
   (case (type c) of
    Force \<Rightarrow> 0
  | Storage \<Rightarrow> 1
  | Eq \<Rightarrow> 2)"


definition is_force_coupon :: "coupon \<Rightarrow> bool" where
  "is_force_coupon c \<equiv> (get_coupon_type c = 0)"

definition is_storage_coupon :: "coupon \<Rightarrow> bool" where
  "is_storage_coupon c \<equiv> (get_coupon_type c = 1)"

definition is_eq_coupon :: "coupon \<Rightarrow> bool" where
  "is_eq_coupon c \<equiv> (get_coupon_type c = 2)"

fun make_coupon :: "request_type \<Rightarrow> coupon list \<Rightarrow> handle option \<Rightarrow> coupon option" where
  "make_coupon Blob ([c]) None = 
    (if (is_storage_coupon c) then Some (\<lparr> type = Eq, lhs = (lhs c), rhs = (rhs c) \<rparr>)
     else None)"
| "make_coupon Tree xs None =
    (if (\<forall>c \<in> set xs. is_eq_coupon c) then
     (let llist = map (\<lambda>c. lhs c) xs in
      let rlist = map (\<lambda>c. rhs c) xs in
      Some (\<lparr> type = Eq, lhs = (HTreeHandle (create_tree llist)), rhs = (HTreeHandle (create_tree rlist))\<rparr>))
     else None)"
| "make_coupon Thunk (f1 # f2 # e # []) None =
    (if ((is_force_coupon f1) \<and> (is_force_coupon f2) \<and> (is_eq_coupon e) \<and> (rhs f1 = lhs e) \<and> (rhs f2 = rhs e)) then
     Some (\<lparr> type = Eq, lhs = lhs f1, rhs = lhs f2 \<rparr>) 
    else None)"
| "make_coupon ThunkTree (e # []) None =
    (case (type e) of
      Eq \<Rightarrow> (case (lhs e) of
              HTreeHandle t1 \<Rightarrow>
               (case (rhs e) of
                HTreeHandle t2 \<Rightarrow> Some (\<lparr> type = Eq, lhs = (HThunkHandle (create_thunk t1)), rhs = (HThunkHandle (create_thunk t2)) \<rparr>)
               | _ \<Rightarrow> None)
              | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
| "make_coupon ThunkForce (e # f1 # f2 # []) None =
   (if ((is_eq_coupon e) \<and> (is_force_coupon f1) \<and> (is_force_coupon f2) \<and> (lhs f1 = lhs e) \<and> (lhs f2 = rhs e)) then
    Some( \<lparr> type = Eq, lhs = rhs f1, rhs = rhs f2 \<rparr>)
    else None)"
| "make_coupon Encode (e # []) None =
   (if (is_eq_coupon e) then
    (case (lhs e) of
      HThunkHandle t1 \<Rightarrow>
       (case (rhs e) of
         HThunkHandle t2 \<Rightarrow> Some ( \<lparr> type = Eq, lhs = (HEncodeHandle (create_encode t1)), rhs = (HEncodeHandle (create_encode t2)) \<rparr>)
        | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)
   else None)"
| "make_coupon Self [] (Some h) =
   Some ( \<lparr> type = Eq, lhs = h, rhs = h \<rparr> )"
| "make_coupon Sym (e # []) None =
   (if (is_eq_coupon e) then
    Some ( \<lparr> type = Eq, lhs = rhs e, rhs = lhs e \<rparr>)
   else None)"
| "make_coupon Trans (e1 # e2 # []) None =
   (if ((is_eq_coupon e1) \<and> (is_eq_coupon e2) \<and> (rhs e1 = lhs e2))
    then Some (\<lparr> type = Eq, lhs = lhs e1, rhs = rhs e2 \<rparr>)
    else None)"
| "make_coupon _ _ _ = None"

definition coupon_ok :: "coupon \<Rightarrow> bool" where
  "coupon_ok c =
   (case (type c) of
    Eq \<Rightarrow> coupon_eq (lhs c) (rhs c)
  | Force \<Rightarrow> coupon_force (lhs c) (rhs c)
  | Storage \<Rightarrow> coupon_storage (lhs c) (rhs c))"

lemma coupon_ok_eq:
  assumes OK: "coupon_ok c"
      and H: "is_eq_coupon c"
  shows "coupon_eq (lhs c) (rhs c)"
  using OK H coupon_ok_def is_eq_coupon_def
  by (cases "type c") auto

lemma make_coupon_sound:
  assumes All: "list_all coupon_ok coupons"
      and H: "make_coupon op coupons handles = Some c"
    shows "coupon_ok c"
proof (cases op)
  case Blob
  then obtain c' xs
    where "coupons = c' # xs" using H by (cases coupons) auto
  then have LS: "coupons = [c']" using Blob H by (cases xs) auto
  then have handles_nil: "handles = None" using H by (cases handles) auto
  then have Storage: "type c' = Storage" using H Blob LS handles_nil H is_storage_coupon_def by (cases "type c'") auto
  then have Cdef: "c = \<lparr> type = Eq, lhs = (lhs c'), rhs = (rhs c') \<rparr>" 
    using H Blob LS handles_nil H Storage is_storage_coupon_def by auto
  have "coupon_ok c'" using All LS by auto
  then have "coupon_storage (lhs c') (rhs c')" using coupon_ok_def Storage by auto
  then have "coupon_eq (lhs c') (rhs c')" using coupon_force_coupon_storage_coupon_eq.CouponBlob by auto
  then show ?thesis using Cdef coupon_ok_def by auto
next
  case Tree

  have handles_nil: "handles = None" using H Tree by (cases handles) auto
  then show ?thesis  using H Tree handles_nil 
  proof (cases "\<forall>c \<in> set coupons. is_eq_coupon c") 
    case False
    then have "make_coupon op coupons handles = None" using Tree handles_nil by auto
    then show ?thesis using H Tree handles_nil by auto
  next
    case True
    let ?llist = "map (\<lambda>c. lhs c) coupons"
    let ?rlist = "map (\<lambda>c. rhs c) coupons"
    let ?ltree = "HTreeHandle (create_tree ?llist)"
    let ?rtree = "HTreeHandle (create_tree ?rlist)"

    have "list_all2 coupon_eq ?llist ?rlist" 
      using True All coupon_ok_eq by (induction coupons) auto
    then have EQ: "coupon_eq ?ltree ?rtree"
      using coupon_force_coupon_storage_coupon_eq.CouponTree by auto

    have Cdef: "c = \<lparr> type = Eq, lhs = ?ltree, rhs = ?rtree \<rparr>" using H Tree handles_nil True by auto
    then show ?thesis using coupon_ok_def Cdef EQ by auto
  qed
next
  case Thunk
  then obtain f1 xs
    where "coupons = f1 # xs" using H by (cases coupons) auto
  then obtain f2 xs
    where "coupons = f1 # f2 # xs" using H Thunk by (cases xs) auto
  then obtain e xs
    where "coupons = f1 # f2 # e # xs" using H Thunk by (cases xs) auto
  then have LS: "coupons = f1 # f2 # e # []" using H Thunk by (cases xs) auto

  have handles_nil: "handles = None" using H Thunk by (cases handles) auto

  then have X: "((is_force_coupon f1) \<and> (is_force_coupon f2) \<and> (is_eq_coupon e) \<and> (rhs f1 = lhs e) \<and> (rhs f2 = rhs e))" using H Thunk LS by (cases "((is_force_coupon f1) \<and> (is_force_coupon f2) \<and> (is_eq_coupon e) \<and> (rhs f1 = lhs e) \<and> (rhs f2 = rhs e))") auto

  have "coupon_ok f1" using All LS by auto
  then have F1: "coupon_force (lhs f1) (rhs f1)" using X coupon_ok_def is_force_coupon_def by (cases "type f1") auto
  have "coupon_ok f2" using All LS by auto
  then have F2: "coupon_force (lhs f2) (rhs f2)" using X coupon_ok_def is_force_coupon_def by (cases "type f2") auto
  have "coupon_ok e" using All LS by auto
  then have E: "coupon_eq (lhs e) (rhs e)" using X coupon_ok_def is_eq_coupon_def by (cases "type e") auto

  then have EQ: "coupon_eq (lhs f1) (lhs f2)" using F1 F2 E X coupon_force_coupon_storage_coupon_eq.CouponThunk by auto

  have Cdef: "c = \<lparr> type = Eq, lhs = (lhs f1), rhs = (lhs f2) \<rparr>" 
    using H Thunk handles_nil LS X by auto
  then show ?thesis using coupon_ok_def EQ by auto
next
  case ThunkTree
  then obtain c' xs
    where "coupons = c' # xs" using H by (cases coupons) auto
  then have LS: "coupons = [c']" using ThunkTree H by (cases xs) auto
  then have OK: "coupon_ok c'" using All by auto
  have handles_nil: "handles = None" using H LS by (cases handles) auto

  have Eq: "type c' = Eq" using H ThunkTree LS handles_nil by (cases "type c'") auto
  then obtain t1 t2 where T1: "lhs c' = HTreeHandle t1" and T2: "rhs c' = HTreeHandle t2"
    using H ThunkTree LS handles_nil by (cases "lhs c'"; cases "rhs c'") auto
  then have EQ: "coupon_eq (HTreeHandle t1) (HTreeHandle t2)" using OK Eq coupon_ok_def by auto

  let ?lhs = "HThunkHandle (create_thunk t1)"
  let ?rhs = "HThunkHandle (create_thunk t2)"

  have EQ:"coupon_eq ?lhs ?rhs" using EQ coupon_force_coupon_storage_coupon_eq.CouponThunkTree by auto

  have "c = \<lparr> type = Eq, lhs = ?lhs, rhs = ?rhs \<rparr>" 
    using H ThunkTree handles_nil LS Eq T1 T2 by auto
  then show ?thesis using EQ coupon_ok_def by auto
next
  case ThunkForce
  then obtain e xs
    where "coupons = e # xs" using H by (cases coupons) auto
  then obtain f1 xs
    where "coupons = e # f1 # xs" using H ThunkForce by (cases xs) auto
  then obtain f2 xs
    where "coupons = e # f1 # f2 # xs" using H ThunkForce by (cases xs) auto
  then have LS: "coupons = e # f1 # f2 # []" using H ThunkForce by (cases xs) auto
  then have Eok: "coupon_ok e" and F1ok: "coupon_ok f1" and F2ok: "coupon_ok f2" using All by auto

  have handles_nil: "handles = None" using H ThunkForce by (cases handles) auto

  have X: "(is_eq_coupon e) \<and> (is_force_coupon f1) \<and> (is_force_coupon f2) \<and> (lhs f1 = lhs e) \<and> (lhs f2 = rhs e)" using LS handles_nil ThunkForce H by (cases "(is_eq_coupon e) \<and> (is_force_coupon f1) \<and> (is_force_coupon f2) \<and> (lhs f1 = lhs e) \<and> (lhs f2 = rhs e)") auto
  have E: "coupon_eq (lhs e) (rhs e)" using coupon_ok_def Eok X is_eq_coupon_def by (cases "type e") auto
  have F1: "coupon_force (lhs f1) (rhs f1)" using coupon_ok_def F1ok X is_force_coupon_def by (cases "type f1") auto
  have F2: "coupon_force (lhs f2) (rhs f2)" using coupon_ok_def F2ok X is_force_coupon_def by (cases "type f2") auto
  have EQ: "coupon_eq (rhs f1) (rhs f2)" using E F1 F2 X coupon_force_coupon_storage_coupon_eq.CouponThunkForce by auto

  have "c = \<lparr> type = Eq, lhs = (rhs f1), rhs = (rhs f2) \<rparr>" using H ThunkForce handles_nil LS X by auto
  then show ?thesis using EQ coupon_ok_def by auto
next
  case Encode
  then obtain c' xs
    where "coupons = c' # xs" using H by (cases coupons) auto
  then have LS: "coupons = [c']" using Encode H by (cases xs) auto
  then have OK: "coupon_ok c'" using All by auto
  have handles_nil: "handles = None" using H LS by (cases handles) auto

  have Eq: "type c' = Eq" using H Encode LS handles_nil is_eq_coupon_def by (cases "type c'") auto
  then obtain t1 t2 where T1: "lhs c' = HThunkHandle t1" and T2: "rhs c' = HThunkHandle t2"
    using H Encode LS handles_nil is_eq_coupon_def by (cases "lhs c'"; cases "rhs c'") auto
  then have EQ: "coupon_eq (HThunkHandle t1) (HThunkHandle t2)" using OK Eq coupon_ok_def by auto

  let ?lhs = "HEncodeHandle (create_encode t1)"
  let ?rhs = "HEncodeHandle (create_encode t2)"

  have EQ:"coupon_eq ?lhs ?rhs" using EQ coupon_force_coupon_storage_coupon_eq.CouponEncode by auto

  have "c = \<lparr> type = Eq, lhs = ?lhs, rhs = ?rhs \<rparr>" 
    using H Encode handles_nil LS Eq T1 T2 is_eq_coupon_def by auto
  then show ?thesis using EQ coupon_ok_def by auto
next
  case Self
  then obtain h
    where handles_some: "handles = Some h" using H by (cases handles) auto
  then have coupons_nil: "coupons = []" using H by (cases coupons) auto
  then have Cdef: "c = \<lparr> type = Eq, lhs = h, rhs = h \<rparr>" using handles_some Self H by auto

  have "coupon_eq h h" using coupon_force_coupon_storage_coupon_eq.CouponSelf by auto
  then show ?thesis using coupon_ok_def Cdef by auto
next
  case Sym
  then obtain c' xs
    where "coupons = c' # xs" using H by (cases coupons) auto
  then have LS: "coupons = [c']" using Sym H by (cases xs) auto
  then have OK: "coupon_ok c'" using All by auto
  have handles_nil: "handles = None" using H LS by (cases handles) auto

  have Eq: "type c' = Eq" using H Sym LS handles_nil is_eq_coupon_def by (cases "type c'") auto
  then have "coupon_eq (lhs c') (rhs c')" using OK coupon_ok_def by auto
  then have EQ: "coupon_eq (rhs c') (lhs c')" using coupon_force_coupon_storage_coupon_eq.CouponSym by auto

  have "c = \<lparr> type = Eq, lhs = (rhs c'), rhs = (lhs c') \<rparr>" using H Sym LS handles_nil Eq is_eq_coupon_def by auto
  then show ?thesis using EQ coupon_ok_def by auto
next
  case Trans
  then obtain e1 xs
    where "coupons = e1 # xs" using H by (cases coupons) auto
  then obtain e2 xs
    where "coupons = e1 # e2 # xs" using H Trans by (cases xs) auto
  then have LS: "coupons = e1 # e2 # []" using H Trans by (cases xs) auto
  then have Ok1: "coupon_ok e1" and Ok2: "coupon_ok e2" using All by auto

  have handles_nil: "handles = None" using H Trans by (cases handles) auto

  have X: "(is_eq_coupon e1) \<and> (is_eq_coupon e2) \<and> (rhs e1 = lhs e2)"
    using H Trans LS handles_nil
    by (cases "(is_eq_coupon e1) \<and> (is_eq_coupon e2) \<and> (rhs e1 = lhs e2)")  auto
  have E1: "coupon_eq (lhs e1) (rhs e1)" using X Ok1 coupon_ok_def is_eq_coupon_def by (cases "type e1") auto
  have E2: "coupon_eq (lhs e2) (rhs e2)" using X Ok2 coupon_ok_def is_eq_coupon_def by (cases "type e2") auto
  have EQ: "coupon_eq (lhs e1) (rhs e2)" using E1 E2 X coupon_force_coupon_storage_coupon_eq.CouponTrans by auto

  have "c = \<lparr> type = Eq, lhs = (lhs e1), rhs = (rhs e2) \<rparr>"
    using H Trans handles_nil LS X by auto
  then show ?thesis using EQ coupon_ok_def by auto
qed 

(* make_coupon related api functions *)

consts
  (* coupon-related ones *)
  is_coupon :: "handle \<Rightarrow> bool"
  create_eq_coupon :: "handle \<Rightarrow> handle \<Rightarrow> handle"
  get_coupon_lhs :: "handle \<Rightarrow> handle option"
  get_coupon_rhs :: "handle \<Rightarrow> handle option"
  get_coupon_type_api :: "handle \<Rightarrow> nat"

  (* typeless Fix apis *)
  get_type_api :: "handle \<Rightarrow> nat"
  get_tree_size_api :: "handle \<Rightarrow> nat option"
  get_tree_data_api :: "handle \<Rightarrow> nat \<Rightarrow> handle option"
  create_thunk_api :: "handle \<Rightarrow> handle option"
  create_encode_api :: "handle \<Rightarrow> handle option"

  is_equal :: "handle \<Rightarrow> handle \<Rightarrow> bool"

axiomatization where
  create_coupon_is_coupon[simp]:
  "is_coupon (create_eq_coupon l r) = True"
and
  get_coupon_lhs[simp]:
  "get_coupon_lhs (create_eq_coupon l r) = Some l"
and
  get_coupon_rhs[simp]:
  "get_coupon_rhs (create_eq_coupon l r) = Some r"
and
  get_coupon_type_eq[simp]:
  "get_coupon_type_api (create_eq_coupon l r) = 2"

definition is_force_coupon_api :: "handle \<Rightarrow> bool" where
  "is_force_coupon_api c \<equiv> (is_coupon c \<and> get_coupon_type_api c = 0)"

definition is_storage_coupon_api :: "handle \<Rightarrow> bool" where
  "is_storage_coupon_api c \<equiv> (is_coupon c \<and> get_coupon_type_api c = 1)"

definition is_eq_coupon_api :: "handle \<Rightarrow> bool" where
  "is_eq_coupon_api c \<equiv> (is_coupon c \<and> get_coupon_type_api c = 2)"

axiomatization where
  get_type_match[simp]:
  "get_type_api h = get_type h"
and
  get_tree_data_api_match[simp]:
  "get_tree_data_api (HTreeHandle t) i = (if i < length (get_tree_raw t) then Some (get_tree_data t i) else None)"
and
  get_tree_size_api_match[simp]:
  "get_tree_size_api (HTreeHandle t) = Some (get_tree_size t)"
and
  get_tree_data_api_blob[simp]:
  "get_tree_data_api (HBlobHandle b) i = None"
and
  get_tree_data_api_encode[simp]:
  "get_tree_data_api (HEncodeHandle e) i = None"
and
  get_tree_data_api_thunk[simp]:
  "get_tree_data_api (HThunkHandle th) i = None"
and
  get_tree_size_api_blob[simp]:
  "get_tree_size_api (HBlobHandle b) = None"
and
  get_tree_size_api_encode[simp]:
  "get_tree_size_api (HEncodeHandle e) = None"
and
  get_tree_size_api_thunk[simp]:
  "get_tree_size_api (HThunkHandle th) = None"
and
  create_thunk_api_match[simp]:
  "create_thunk_api (HTreeHandle t) = Some (HThunkHandle (create_thunk t))"
and
  create_thunk_api_blob[simp]:
  "create_thunk_api (HBlobHandle b) = None"
and
  create_thunk_api_encode[simp]:
  "create_thunk_api (HEncodeHandle e) = None"
and
  create_thunk_api_thunk[simp]:
  "create_thunk_api (HThunkHandle th) = None"
and
  create_encode_api_match[simp]:
  "create_encode_api (HThunkHandle th) = Some (HEncodeHandle (create_encode th))"
and
  create_encode_api_blob[simp]:
  "create_encode_api (HBlobHandle b) = None"
and
  create_encode_api_tree[simp]:
  "create_encode_api (HTreeHandle t) = None"
and
  create_encode_api_encode[simp]:
  "create_encode_api (HEncodeHandle e) = None"
and
  is_equal_match [simp]:
  "is_equal h1 h2 = (h1 = h2)"

definition raw_coupon_ok :: "handle \<Rightarrow> bool" where
  "raw_coupon_ok h =
   (if (is_coupon h) then
    (case (get_coupon_lhs h, get_coupon_rhs h) of
       (Some l, Some r) \<Rightarrow> 
        (if (is_force_coupon_api h) then
           coupon_force l r
         else if (is_storage_coupon_api h) then
           coupon_storage l r
         else if (is_eq_coupon_api h) then
           coupon_eq l r
         else False)
      | _ \<Rightarrow> False)
   else False)"

fun make_coupon_self :: "handle \<Rightarrow> handle option" where
  "make_coupon_self h = Some (create_eq_coupon h h)"

lemma those_length:
  "those (map f xs) = Some ys \<Longrightarrow> length xs = length ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons h t)
  then obtain x' where H: "f h = Some x'" by (cases "f h") auto
  then obtain xs' where T: "those (map f t) = Some xs'" using Cons by auto
  then have Consys: "ys = x' # xs'" using H T Cons by auto

  have "length xs' = length t" using Cons.IH T by auto
  then have "length ys = length (h # t)" using Consys by auto
  then show ?case using Cons by auto
qed

lemma those_nth:
  "those (map f xs) = Some ys \<Longrightarrow> i < length xs \<Longrightarrow> Some (ys ! i) = f (xs ! i)"
proof (induction xs arbitrary: ys i)
  case Nil
  then show ?case by auto
next
  case (Cons h t)
  then obtain x' where H: "f h = Some x'" by (cases "f h") auto
  then obtain xs' where T: "those (map f t) = Some xs'" using Cons by auto
  then have Consys: "ys = x' # xs'" using H T Cons by auto
  then show ?case using H T Cons Consys by (cases "i") auto
qed

(* make_coupon_raw: request_type \<Rightarrow> premises \<Rightarrow> lhs \<Rightarrow> rhs \<Rightarrow> handle option *)
fun make_coupon_raw :: "request_type \<Rightarrow> handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_coupon_raw Blob ([c]) l r =
   (if (is_storage_coupon_api c) 
    then (case (get_coupon_lhs c, get_coupon_rhs c) of
     (Some l', Some r') \<Rightarrow> (if ( is_equal l l' \<and> is_equal r r') then Some (create_eq_coupon l r)
                                                                else None)
    | _ \<Rightarrow> None)
    else None)"
| "make_coupon_raw Tree xs l r =
   (if (\<forall>c \<in> set xs. is_eq_coupon_api c) then
    (let lhs = those (map (\<lambda>c. get_coupon_lhs c) xs) in
     let rhs = those (map (\<lambda>c. get_coupon_rhs c) xs) in
     (case (lhs, rhs) of
      (Some llist, Some rlist) \<Rightarrow> 
        (if (get_tree_size_api l = Some (length llist) \<and> get_tree_size_api r = Some (length rlist))   then
          (if (\<forall>i. (i < length llist \<longrightarrow>
              (case (get_tree_data_api l i, get_tree_data_api r i) of
                 (Some h1, Some h2) \<Rightarrow> (is_equal h1 (llist ! i)) \<and> is_equal h2 (rlist ! i)
                | _ \<Rightarrow> False))) then
            Some (create_eq_coupon l r)
          else None)
        else None)
     | _ \<Rightarrow> None))
    else None)"
| "make_coupon_raw Thunk (f1 # f2 # e # []) l r =
   (if ((is_force_coupon_api f1) \<and> (is_force_coupon_api f2) \<and> (is_eq_coupon_api e)) 
    then
     (case (get_coupon_lhs f1, get_coupon_rhs f1, get_coupon_lhs f2, get_coupon_rhs f2,  get_coupon_lhs e, get_coupon_rhs e) of
      (Some f1l, Some f1r, Some f2l, Some f2r, Some el, Some er) \<Rightarrow>
         (if (is_equal f1r el \<and> is_equal f2r er) then
          (if (is_equal f1l l \<and> is_equal f2l r) then Some (create_eq_coupon l r) else None)
          else None)
     | _ \<Rightarrow> None)
    else None)"
| "make_coupon_raw ThunkTree ([e]) l r =
   (if (is_eq_coupon_api e) then
    (case (get_coupon_lhs e, get_coupon_rhs e) of
     (Some l', Some r') \<Rightarrow> 
       (case (create_thunk_api l', create_thunk_api r') of
         (Some l'', Some r'') \<Rightarrow> 
         (if (is_equal l l'' \<and> is_equal r r'') then Some(create_eq_coupon l r) else None)
        | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)
   else None)"
| "make_coupon_raw ThunkForce (e # f1 # f2 # []) l r =
   (if ((is_eq_coupon_api e) \<and> (is_force_coupon_api f1) \<and> (is_force_coupon_api f2))
    then
    (case (get_coupon_lhs e, get_coupon_rhs e, get_coupon_lhs f1, get_coupon_rhs f1, get_coupon_lhs f2, get_coupon_rhs f2) of
     (Some el, Some er, Some f1l, Some f1r, Some f2l, Some f2r) \<Rightarrow>
        (if (is_equal f1l el \<and> is_equal f2l er \<and> is_equal f1r l \<and> is_equal f2l r) then
         Some (create_eq_coupon l r)
        else None)
     | _ \<Rightarrow> None)
   else None)"
| "make_coupon_raw Encode (e # []) l r =
   (if (is_eq_coupon_api e) then
     (case (get_coupon_lhs e, get_coupon_rhs e) of 
       (Some l, Some r) \<Rightarrow>
        (case (create_encode_api l, create_encode_api r) of
          (Some l', Some r') \<Rightarrow> 
            (if (is_equal l l' \<and> is_equal r r') then Some (create_eq_coupon l' r') else None)
        | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)
    else None)"
| "make_coupon_raw Sym (e # []) l r =
   (if (is_eq_coupon_api e) then
     (case (get_coupon_lhs e, get_coupon_rhs e) of
      (Some l', Some r') \<Rightarrow> 
        (if (is_equal r' l \<and> is_equal l' r) then Some (create_eq_coupon l r) else None)
     | _ \<Rightarrow> None)
   else None)"
| "make_coupon_raw Trans (e1 # e2 # []) l r =
   (if (is_eq_coupon_api e1 \<and> is_eq_coupon_api e2) then
     (case (get_coupon_lhs e1, get_coupon_rhs e1, get_coupon_lhs e2, get_coupon_rhs e2) of
       (Some e1l, Some e1r, Some e2l, Some e2r) \<Rightarrow>
         (if (is_equal e1r e2l \<and> is_equal l e1l \<and> is_equal r e2r) then
           Some (create_eq_coupon l r)
          else None)
      | _ \<Rightarrow> None)
    else None)"
| "make_coupon_raw Self [] l r =
   (if (is_equal l r) then Some (create_eq_coupon l r) else None)"
| "make_coupon_raw _ _ _ _ = None"

lemma make_coupon_raw_sound:
  assumes All: "list_all raw_coupon_ok coupons"
      and   H: "make_coupon_raw op coupons l r = Some c"
    shows "raw_coupon_ok c"
proof (cases op)
  case Blob
  then obtain c' xs where "coupons = c' # xs" using H by (cases coupons) auto
  then have LS: "coupons = [c']" using Blob H by (cases xs) auto
  then have ISS: "is_storage_coupon_api c'" using Blob H by (cases "is_storage_coupon_api c'") auto
  then have ISC: "is_coupon c'" using is_storage_coupon_api_def by auto

  have NOTF: "\<not> is_force_coupon_api c'" using ISS is_storage_coupon_api_def is_force_coupon_api_def by auto

  have Ok: "raw_coupon_ok c'" using All LS by auto
  then have "\<exists>l r. (get_coupon_lhs c', get_coupon_rhs c') = (Some l, Some r)" using ISS ISC raw_coupon_ok_def by (cases "get_coupon_lhs c'"; cases "get_coupon_rhs c'") auto
  then obtain l' r' where Some1: "get_coupon_lhs c' = Some l'" and Some2: "get_coupon_rhs c' = Some r'" by blast
  then have "coupon_storage l' r'" using ISS ISC NOTF Ok raw_coupon_ok_def by auto
  then have EQ: "coupon_eq l' r'" using coupon_force_coupon_storage_coupon_eq.CouponBlob by auto

  have "is_equal l l' \<and> is_equal r r'" using H Blob LS ISS Some1 Some2 by (cases "is_equal l l' \<and> is_equal r r'") auto
  then have "c = create_eq_coupon l r" and EQ: "coupon_eq l r" using H Blob LS ISS Some1 Some2 EQ by auto

  then have "is_coupon c" and "is_eq_coupon_api c" and "\<not>is_force_coupon_api c" and "\<not>is_storage_coupon_api c" and "get_coupon_lhs c = Some l" and "get_coupon_rhs c = Some r" using is_eq_coupon_api_def is_force_coupon_api_def is_storage_coupon_api_def by auto
  then show ?thesis using EQ raw_coupon_ok_def by auto
next
  case Tree
  then have A: "(\<forall>c \<in> set coupons. is_eq_coupon_api c)" 
    using H by (cases "\<forall>c \<in> set coupons. is_eq_coupon_api c") auto 
  then obtain llist rlist where S1: "those (map (\<lambda>c. get_coupon_lhs c) coupons) = Some llist"
                            and S2: "those (map (\<lambda>c. get_coupon_rhs c) coupons) = Some rlist"
    using H Tree by (cases "(those (map (\<lambda>c. get_coupon_lhs c) coupons))";
                     cases "those (map (\<lambda>c. get_coupon_rhs c) coupons)") auto


  have LEN: "get_tree_size_api l = Some (length llist) \<and> get_tree_size_api r = Some (length rlist)"
    using Tree A S1 S2 H
    by (cases "get_tree_size_api l = Some (length llist) \<and> get_tree_size_api r = Some (length rlist)") auto

  then have EQUAL: "\<forall>i<length llist.
                case get_tree_data_api l i of None \<Rightarrow> False
                | Some h1 \<Rightarrow>
                    case get_tree_data_api r i of None \<Rightarrow> False
                    | Some h2 \<Rightarrow> is_equal h1 (llist ! i) \<and> is_equal h2 (rlist ! i)"
    using Tree A S1 S2 H by (cases "\<forall>i<length llist.
                case get_tree_data_api l i of None \<Rightarrow> False
                | Some h1 \<Rightarrow>
                    case get_tree_data_api r i of None \<Rightarrow> False
                    | Some h2 \<Rightarrow> is_equal h1 (llist ! i) \<and> is_equal h2 (rlist ! i)") auto

  then have OUTPUT: "c = create_eq_coupon l r" using Tree A S1 S2 H LEN by auto

  obtain t1 t2 where Tree1: "l = HTreeHandle t1" and Tree2: "r = HTreeHandle t2" 
    using LEN by (cases l; cases r) auto
  then have LEN: "get_tree_size t1 = length llist" and LEN2: "get_tree_size t2 = length rlist" 
    using LEN by auto

  have L: "length coupons = length llist" using S1 those_length by auto
  have "length coupons = length rlist" using S2 those_length by auto
  then have L': "length llist = length rlist" using L by auto

  let ?l = "length llist"
  have L1: "get_tree_size t1 = ?l" 
   and L2: "length rlist = ?l" 
   and L3: "length coupons = ?l"  using LEN L L' 
    by auto
  then have L1: "length (get_tree_raw t1) = ?l"
        and L4: "length (get_tree_raw t2) = ?l" using LEN2 get_tree_size_def by auto

  have "\<forall>i<?l. coupon_eq (get_tree_data t1 i) (get_tree_data t2 i)"
  proof (intro allI impI)
    fix i
    assume VL: "i < ?l"
    then have OK: "raw_coupon_ok (coupons ! i)" 
      using All L3 list_all_length[of raw_coupon_ok coupons] by auto

    have ISE: "is_eq_coupon_api (coupons ! i)" using VL A L3 by auto
    then obtain l' r' where LHS: "get_coupon_lhs (coupons ! i) = Some l'" 
                        and RHS: "get_coupon_rhs (coupons ! i) =  Some r'" 
      using raw_coupon_ok_def is_eq_coupon_api_def OK 
      by (cases "get_coupon_lhs (coupons ! i)"; cases "get_coupon_rhs (coupons ! i)") auto
    then have EQ: "coupon_eq l' r'" 
      using raw_coupon_ok_def is_eq_coupon_api_def is_force_coupon_api_def is_storage_coupon_api_def OK ISE by auto

    have LI: "llist ! i = l'" using LHS S1 VL those_nth[of get_coupon_lhs coupons llist i] L3 by auto
    have RI: "rlist ! i = r'" using RHS S2 VL those_nth[of get_coupon_rhs coupons rlist i] L3 by auto

    obtain l'' r'' where "get_tree_data_api l i = Some l''"
                     and "get_tree_data_api r i = Some r''"
                     and EQUAL1: "is_equal l'' (llist ! i)"
                     and EQUAL2: "is_equal r'' (rlist ! i)"
      using EQUAL VL by (cases "get_tree_data_api l i"; cases "get_tree_data_api r i") auto
    then have "get_tree_data t1 i =  l''" and "get_tree_data t2 i = r''" 
      using VL Tree1 Tree2 L1 L4 by auto
    then show "coupon_eq (get_tree_data t1 i) (get_tree_data t2 i)"
      using EQ EQUAL1 EQUAL2 LI RI by auto
  qed

  then have "list_all2 coupon_eq (get_tree_raw t1) (get_tree_raw t2)" 
    using L1 L4 get_tree_data_def list_all2_all_nthI[of "get_tree_raw t1" "get_tree_raw t2"] by auto
  then have "coupon_eq l r" using Tree1 Tree2 coupon_force_coupon_storage_coupon_eq.CouponTree
    by auto
  then show ?thesis using OUTPUT raw_coupon_ok_def is_eq_coupon_api_def is_storage_coupon_api_def is_force_coupon_api_def by auto
next
  case Thunk
  then obtain f1 xs
    where "coupons = f1 # xs" using H by (cases coupons) auto
  then obtain f2 xs
    where "coupons = f1 # f2 # xs" using H Thunk by (cases xs) auto
  then obtain e xs
    where "coupons = f1 # f2 # e # xs" using H Thunk by (cases xs) auto
  then have LS: "coupons = f1 # f2 # e # []" using H Thunk by (cases xs) auto

  have COUPON: "(is_force_coupon_api f1) \<and> (is_force_coupon_api f2) \<and> (is_eq_coupon_api e)"
    using H Thunk LS
    by (cases "(is_force_coupon_api f1) \<and> (is_force_coupon_api f2) \<and> (is_eq_coupon_api e)") auto

  then obtain f1l f1r f2l f2r el er where L1: "get_coupon_lhs f1 = Some f1l"
                                      and R1: "get_coupon_rhs f1 = Some f1r"
                                      and L2: "get_coupon_lhs f2 = Some f2l"
                                      and R2: "get_coupon_rhs f2 = Some f2r"
                                      and LE: "get_coupon_lhs e = Some el"
                                      and RE: "get_coupon_rhs e = Some er"
    using H Thunk LS
    by (cases "get_coupon_lhs f1"; cases "get_coupon_rhs f1"; cases "get_coupon_lhs f2"; cases "get_coupon_rhs f2"; cases "get_coupon_lhs e"; cases "get_coupon_rhs e") auto

  then have EQL: "is_equal f1r el \<and> is_equal f2r er"
    using H Thunk LS COUPON
    by (cases "is_equal f1r el \<and> is_equal f2r er") auto
  then have EQIN: "is_equal f1l l \<and> is_equal f2l r"
    using H Thunk LS COUPON L1 R1 L2 R2 LE RE
    by (cases "is_equal f1l l \<and> is_equal f2l r") auto
  then have OUTPUT: "c = create_eq_coupon l r" 
    using H Thunk LS COUPON L1 R1 L2 R2 LE RE EQL by auto

  have "raw_coupon_ok f1" using All LS by auto
  then have F1: "coupon_force f1l f1r" 
    using COUPON raw_coupon_ok_def is_force_coupon_api_def L1 R1 by auto

  have "raw_coupon_ok f2" using All LS by auto
  then have F2: "coupon_force f2l f2r"
    using COUPON raw_coupon_ok_def is_force_coupon_api_def L2 R2 by auto

  have "raw_coupon_ok e" using All LS by auto
  then have E: "coupon_eq f1r f2r"
    using COUPON raw_coupon_ok_def is_force_coupon_api_def is_storage_coupon_api_def is_eq_coupon_api_def LE RE EQL by auto

  have "coupon_eq f1l f2l" using coupon_force_coupon_storage_coupon_eq.CouponThunk[OF F1 F2 E] by auto
  then have "coupon_eq l r" using EQIN by auto
  then show ?thesis 
    using raw_coupon_ok_def is_force_coupon_api_def is_storage_coupon_api_def is_eq_coupon_api_def OUTPUT by auto
next
  case ThunkTree
  then obtain e xs
    where "coupons = e # xs" using H by (cases coupons) auto
  then have LS: "coupons = [e]" using ThunkTree H by (cases xs) auto

  have EQC: "is_eq_coupon_api e" using H ThunkTree LS by (cases "is_eq_coupon_api e") auto
  then obtain l' r' where L: "get_coupon_lhs e = Some l'"
                      and R: "get_coupon_rhs e = Some r'"
    using H ThunkTree LS by (cases "get_coupon_lhs e"; cases "get_coupon_rhs e") auto
  then obtain l'' r'' where L'': "create_thunk_api l' = Some l''"
                        and R'': "create_thunk_api r' = Some r''"
    using H ThunkTree LS EQC by (cases "create_thunk_api l'"; cases "create_thunk_api r'") auto
  then have EQO: "is_equal l l'' \<and> is_equal r r''"
    using H ThunkTree LS EQC L R by (cases "is_equal l l'' \<and> is_equal r r''") auto
  then have OUTPUT: "c = create_eq_coupon l r"
    using H ThunkTree LS EQC L R L'' R'' by auto

  obtain t1 where TreeL: "l' = HTreeHandle t1" and ThunkL: "l'' = HThunkHandle (create_thunk t1)"
    using L'' by (cases l') auto
  obtain t2 where TreeR: "r' = HTreeHandle t2" and ThunkR: "r'' = HThunkHandle (create_thunk t2)"
    using R'' by (cases r') auto

  have "coupon_eq l' r'" 
    using All LS EQC L R raw_coupon_ok_def is_force_coupon_api_def is_storage_coupon_api_def is_eq_coupon_api_def by auto
  then have "coupon_eq l'' r''" 
    using TreeL ThunkL TreeR ThunkR coupon_force_coupon_storage_coupon_eq.CouponThunkTree by auto
  then show ?thesis 
    using OUTPUT EQO raw_coupon_ok_def is_force_coupon_api_def is_storage_coupon_api_def is_eq_coupon_api_def OUTPUT by auto
next
  case ThunkForce
  then show ?thesis sorry
next
  case Encode
  then show ?thesis sorry
next
  case Self
  then show ?thesis sorry
next
  case Sym
  then show ?thesis sorry
next
  case Trans
  then show ?thesis sorry
qed