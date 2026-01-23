theory eqqqnew
  imports Main
begin

typedecl BlobHandle
typedecl TreeHandle
datatype ThunkHandle = HThunkHandle TreeHandle

datatype handle = 
  HBlobHandle BlobHandle
  | HTreeHandle TreeHandle
  | HThunkHandle ThunkHandle

typedecl raw
type_synonym BlobData = "raw"
type_synonym TreeData = "handle list"

(* Fixpoint APIs *)

consts 
  get_blob_data :: "BlobHandle \<Rightarrow> BlobData"
  get_tree_raw :: "TreeHandle \<Rightarrow> handle list"
  get_thunk_tree :: "ThunkHandle \<Rightarrow> TreeHandle"

create_blob :: "BlobData \<Rightarrow> BlobHandle"
create_tree :: "TreeData \<Rightarrow> TreeHandle"
create_thunk :: "TreeHandle \<Rightarrow> ThunkHandle"

definition get_tree_data :: "TreeHandle \<Rightarrow> nat \<Rightarrow> handle" where
  "get_tree_data t i \<equiv> (get_tree_raw t) ! i"

definition get_tree_size :: "TreeHandle \<Rightarrow> nat" where
  "get_tree_size t \<equiv> length (get_tree_raw t)"

fun get_type :: "handle \<Rightarrow> nat" where
  "get_type (HBlobHandle _ ) = 0"
| "get_type (HTreeHandle _ ) = 1"
| "get_type (HThunkHandle _ ) = 2"

(* User Program *)

datatype op =
  OGetBlobData nat
  | OGetTreeData nat nat
  | OCreateBlob nat
  | OCreateTree "nat list"
  | OCreateThunk nat
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

definition state_init :: "ThunkHandle \<Rightarrow> state" where
  "state_init thunk \<equiv> \<lparr> hs = [HTreeHandle (get_thunk_tree thunk)], ds = [] \<rparr>"

definition think :: "ThunkHandle \<Rightarrow> handle option" where
  "think th \<equiv> exec (get_prog (get_thunk_tree th)) (state_init th)" 

fun is_thunk :: "handle \<Rightarrow> bool" where
  "is_thunk (HThunkHandle _) = True"
| "is_thunk _ = False"

fun force_with_fuel :: "nat \<Rightarrow> handle \<Rightarrow> handle option" where
  "force_with_fuel n h =
     (case h of
        HThunkHandle th \<Rightarrow>
          (case n of
             0 \<Rightarrow> None
           | Suc n' \<Rightarrow>
               (case think th of
                  None \<Rightarrow> None
                | Some h1 \<Rightarrow> force_with_fuel n' h1))
       | _ \<Rightarrow> Some h)"

definition forces_to :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  "forces_to h h1 \<equiv> (\<exists>fuel. force_with_fuel fuel h = Some h1 \<and> \<not> is_thunk h1)"

(* Determinism *)

lemma force_with_fuel_pad:
  assumes "force_with_fuel f h = Some h1" and "\<not> is_thunk h1"
  shows "force_with_fuel (f + k) h = Some h1"
  using assms
proof (induction f arbitrary: h)
  case 0 then show ?case by (cases h) auto
next
  case (Suc f')
  then show ?case 
  proof (cases h) 
    case (HBlobHandle b)
    then have "force_with_fuel (Suc f') h = Some h" by simp_all
    then have "h1 = h" using Suc.prems(1) by auto
    then show ?thesis using HBlobHandle by auto
  next
    case (HTreeHandle t)
    then have "force_with_fuel (Suc f') h = Some h" by simp_all
    then have "h1 = h" using Suc.prems(1) by auto
    then show ?thesis using HTreeHandle by auto
  next
    case (HThunkHandle th)
    from Suc.prems(1) HThunkHandle obtain h2 where
      A: "think th = Some h2"
      and B: "force_with_fuel f' h2 = Some h1" by (simp split: option.splits)

    have "force_with_fuel (f' + k) h2 = Some h1" using B Suc.IH Suc.prems(2) by auto
    then show ?thesis using HThunkHandle A by simp_all
  qed
qed

lemma forces_to_deterministic:
  assumes "forces_to h h1" and "forces_to h h2"
  shows "h1 = h2"
  using assms
proof -
  obtain f1 where A: "force_with_fuel f1 h = Some h1" and NT1: "\<not> is_thunk h1"
    using assms(1) unfolding forces_to_def by auto
  obtain f2 where B: "force_with_fuel f2 h = Some h2" and NT2: "\<not> is_thunk h2"
    using assms(2) unfolding forces_to_def by auto
  let ?F = "max f1 f2"
  let ?k1 = "?F - f1"
  let ?k2 = "?F - f2"
  have "force_with_fuel (f1 + ?k1) h = Some h1"
    using force_with_fuel_pad[OF A NT1] .
  then have AA: "force_with_fuel ?F h = Some h1" by simp
  have "force_with_fuel (f2 + ?k2) h = Some h2" 
    using force_with_fuel_pad[OF B NT2] .
  then have BB: "force_with_fuel ?F h = Some h2" by simp
  show ?thesis using AA BB by simp
qed

lemma forces_to_not_thunk:
  assumes "forces_to h h1"
  shows "\<not> is_thunk h1"
  using assms
  unfolding forces_to_def
  by auto

definition force :: "handle \<Rightarrow> handle option" where
  "force h =
     (if (\<exists>v. forces_to h v)
      then Some (THE v. forces_to h v)
      else None)"

lemma force_some:
  assumes "force h = Some h1"
  shows "forces_to h h1"
  using assms
  unfolding force_def
proof -
  have ex: "\<exists>x. forces_to h x"
    using assms unfolding force_def by (auto split: if_splits)
  have ex1: "\<exists>!x. forces_to h x"
    using ex forces_to_deterministic by (auto)
  have "forces_to h (THE x. forces_to h x)"
    using ex1 by (rule theI')
  moreover have "h1 = (THE x. forces_to h x)"
    using assms ex unfolding force_def by (auto split: if_splits)
  ultimately show ?thesis by simp
qed

lemma force_unique:
  assumes "forces_to h h1"
  shows "force h = Some h1"
  using assms
proof -
  have ex: "\<exists>x. forces_to h x" using assms by blast
  have ex1: "\<exists>!y. forces_to h y"
    using assms forces_to_deterministic by auto
  have the_eq: "(THE x. forces_to h x) = h1"
    using assms ex1 by auto
  show ?thesis
    unfolding force_def using ex the_eq by simp
qed

lemma force_deterministic:
  assumes "force h = Some h1"
      and "force h = Some h2"
    shows "h1 = h2"
  using force_some forces_to_deterministic assms(1) assms(2)
  by auto

(* Blob/Tree creation rules *)

axiomatization where
  get_blob_data_create_blob[simp]:
  "get_blob_data (create_blob x) = x"
  and
  get_tree_raw_create_tree[simp]:
  "get_tree_raw (create_tree xs) = xs"
  and
  get_thunk_tree_create_thunk[simp]:
  "get_thunk_tree (create_thunk th) = th"
  and
  create_thunk_get_thunk_tree[simp]:
  "create_thunk (get_thunk_tree t) = t"

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
| EqThunkSomeRes:
  "think t1 = Some r1 \<Longrightarrow>
   think t2 = Some r2 \<Longrightarrow>
   \<not> is_thunk r1 \<Longrightarrow>
   \<not> is_thunk r2 \<Longrightarrow>
   eq r1 r2 \<Longrightarrow>
   eq (HThunkHandle t1) (HThunkHandle t2)"
| EqThunkSymm:
  "eq (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow>
   eq (HThunkHandle t2) (HThunkHandle t1)"
| EqThunkTrans:
  "eq (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow>
   eq (HThunkHandle t2) (HThunkHandle t3) \<Longrightarrow>
   eq (HThunkHandle t1) (HThunkHandle t3)"
| EqSelf:
   "eq h h"

fun rel_opt :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> handle option \<Rightarrow> handle option \<Rightarrow> bool" where
  "rel_opt X None None = True"
| "rel_opt X (Some h1) (Some h2) = X h1 h2"
| "rel_opt X _ _ = False"

(*We call two program states equivalent if each handle in the handle lists are pair-wise eq
 *and each data in the data lists is pair-wise equal*)
definition eq_state_rel :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "eq_state_rel X s1 s2 \<equiv>
     list_all2 (\<lambda>h1 h2. X h1 h2) (hs s1) (hs s2) \<and> ds s1 = ds s2"

(*We call two step results equivalent if either they step to equivalent states or they returns
 *eq handles*)
definition eq_step_result_rel :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> step_result option \<Rightarrow> step_result option \<Rightarrow> bool" where
  "eq_step_result_rel X r1 r2 \<equiv> 
   (case (r1, r2) of
     (Some (Continue s1), Some (Continue s2)) \<Rightarrow> eq_state_rel X s1 s2
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

lemma eq_state_hpush:
  assumes "eq_state_rel X s1 s2" and "X h1 h2"
  shows "eq_state_rel X (hpush s1 h1) (hpush s2 h2)"
  using assms unfolding eq_state_rel_def hpush_def
  by (auto simp: list_all2_append)

lemma eq_state_hpush_self:
  assumes "\<And> x. X x x"
  assumes "eq_state_rel X s1 s2"
  shows "eq_state_rel X (hpush s1 h) (hpush s2 h)"
  using assms
proof -
  have "X h h" using assms(1) by auto
  then show ?thesis using eq_state_hpush assms by blast
qed

lemma eq_dpush:
  assumes "eq_state_rel X s1 s2" and "d1 = d2"
  shows "eq_state_rel X (dpush s1 d1) (dpush s2 d2)"
  using assms unfolding eq_state_rel_def dpush_def by auto

lemma eq_state_hs:
  "eq_state_rel X s1 s2 \<Longrightarrow> list_all2 (\<lambda>h1 h2. X h1 h2) (hs s1) (hs s2)"
  by (simp add: eq_state_rel_def)

lemma eq_state_ds:
  "eq_state_rel X s1 s2 \<Longrightarrow> (ds s1) = (ds s2)"
  by (simp add: eq_state_rel_def)

lemma eq_state_hs_same_length:
  assumes "eq_state_rel X s1 s2"
  shows "length (hs s1) = length (hs s2)"
  using eq_state_hs[OF assms]
  by (simp add: list_all2_lengthD)

lemma eq_state_hs_nth:
  assumes "eq_state_rel X s1 s2" "i < length (hs s1)"
  shows "X ((hs s1) ! i) ((hs s2)! i) \<and> i < length (hs s2)"
  using eq_state_hs[OF assms(1)] assms(2)
  by (simp add: list_all2_conv_all_nth)

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

lemma eq_not_blob:
  assumes "eq h1 h2"
  shows "(\<forall>b. h1 \<noteq> HBlobHandle b) \<Longrightarrow> (\<forall>b. h2 \<noteq> HBlobHandle b)"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_tree:
  assumes "eq (HTreeHandle t1) h2"
  shows "\<exists>t2. h2 = HTreeHandle t2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_not_tree:
  assumes "eq h1 h2"
  shows "(\<forall>t. h1 \<noteq> HTreeHandle t) \<Longrightarrow> (\<forall>t. h2 \<noteq> HTreeHandle t)"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_thunk:
  assumes "eq (HThunkHandle th1) h2"
  shows "\<exists>th2. h2 = HThunkHandle th2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_not_thunk:
  assumes "eq h1 h2" and "\<not> is_thunk h1"
  shows   "\<not> is_thunk h2"
  using assms
  by (cases h1) auto

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

theorem run_internal_X:
  assumes "eq_state_rel X s1 s2"
  shows "eq_state_rel X (run_internal s1) (run_internal s2)"
proof -
  have "list_all2 X (hs s1) (hs s2)" using assms unfolding eq_state_rel_def by simp_all
  then have HS: "list_all2 X (hs (run_internal s1)) (hs (run_internal s2))" 
    using run_internal_hs 
    by simp

  have DS: "ds s1 = ds s2" using assms unfolding eq_state_rel_def by simp_all
  have DS': "ds (run_internal s1) = ds (run_internal s2)"
    using run_internal_ds_equiv[OF DS]
    by assumption

  show ?thesis using HS DS' eq_state_rel_def by auto
qed

(* 4. Given eq_state s1 s2, and some operation op, stepping them gives equivalent step results *)

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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes S: "eq_state_rel X s1 s2"
  shows   "eq_step_result_rel X (step op s1) (step op s2)"
proof -
  have L: "length (hs s1) = length (hs s2)" using eq_state_hs_same_length[OF S] .
  have D: "(ds s1) = (ds s2)" using eq_state_ds[OF S] .

  show ?thesis
  proof (cases op)
    case (OGetBlobData i)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S eq_state_hs_nth by auto
      then show ?thesis
      proof (cases "(hs s1 ! i)")
        case (HBlobHandle b1)
        then obtain b2 where BLOB2: "hs s2 ! i = HBlobHandle b2" using EQ X_preserve_blob by auto
        then have EQD: "get_blob_data b1 = get_blob_data b2"
          using HBlobHandle get_blob_data_cong EQ by auto  
        have S1: "step op s1 = Some(Continue (dpush s1 (get_blob_data b1)))"
             and  S2: "step op s2 = Some(Continue (dpush s2 (get_blob_data b2)))"
          using OGetBlobData True L HBlobHandle BLOB2 by auto
        have "eq_state_rel X (dpush s1 (get_blob_data b1)) (dpush s2 (get_blob_data b2))"
          using True HBlobHandle L S eq_dpush get_blob_data_cong EQ BLOB2
          by auto
        then show ?thesis using S1 S2 eq_step_result_rel_def by auto
      next
        case (HTreeHandle t1)
        then obtain t2 where TREE2: "hs s2 ! i = HTreeHandle t2" using EQ X_preserve_tree by auto
        then show ?thesis using OGetBlobData HTreeHandle True eq_step_result_rel_def by auto
      next
        case (HThunkHandle th1)
        then obtain th2 where "hs s2 ! i = HThunkHandle th2" using EQ X_preserve_thunk by auto
        then show ?thesis using OGetBlobData HThunkHandle True eq_step_result_rel_def by auto
      qed
    next
      case False
      then show ?thesis using OGetBlobData False L eq_step_result_rel_def by auto
    qed
  next
    case (OGetTreeData i j)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S eq_state_hs_nth by auto
      then show ?thesis
      proof (cases "(hs s1 ! i)")
        case (HBlobHandle)
        then obtain b2 where BLOB2: "hs s2 ! i = HBlobHandle b2"
          using X_preserve_blob EQ by auto
        then show ?thesis using OGetTreeData True L HBlobHandle eq_step_result_rel_def 
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
            then have EQRES: "eq_state_rel X (hpush s1 (get_tree_data t1 j)) (hpush s2 (get_tree_data t2 j))"
              using S eq_state_hpush by auto

            have "j < get_tree_size t2" 
              using  True' EQN get_tree_size_cong
              by simp
            then have S2: "step op s2 = Some (Continue (hpush s2 (get_tree_data t2 j)))"
              using OGetTreeData TREE2 True L by auto

            have "step op s1 = Some (Continue (hpush s1 (get_tree_data t1 j)))"
              using OGetTreeData True True' HTreeHandle by auto
            then show ?thesis using S2 EQRES eq_step_result_rel_def by auto
          next
            case False'
            then have "\<not> j < get_tree_size t2"
              using EQN get_tree_size_cong
              by simp
            then show ?thesis 
              using OGetTreeData True False' L HTreeHandle TREE2 eq_step_result_rel_def by auto
          qed
        qed
      next
        case (HThunkHandle th1)
        then obtain th2 where "hs s2 ! i = HThunkHandle th2" using EQ X_preserve_thunk by auto
        then show ?thesis using OGetTreeData HThunkHandle True eq_step_result_rel_def by auto
      qed
    next
      case False
      then show ?thesis using OGetTreeData eq_step_result_rel_def L by auto
    qed
  next
    case (OCreateBlob i)
    then show ?thesis
    proof (cases "i < length (ds s1)")
      case True
      then have EQD: "ds s1 ! i = ds s2 ! i" using D by simp
      then show ?thesis 
        using OCreateBlob True eq_state_hpush_self[OF X_self S] create_blob_cong[OF EQD] eq_step_result_rel_def D by auto
    next
      case False
      then show ?thesis using OCreateBlob D eq_step_result_rel_def by auto
    qed
  next
    case (OCreateThunk i)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S eq_state_hs_nth by auto
      then show ?thesis
      proof (cases "hs s1 ! i")
        case (HBlobHandle b1)
        then obtain b2 where BLOB2: "hs s2 ! i = HBlobHandle b2"
          using X_preserve_blob EQ by auto
        then show ?thesis using OCreateThunk True HBlobHandle  eq_step_result_rel_def by auto
      next
        case (HTreeHandle t1)
        then obtain t2 where TREE2: "hs s2 ! i = HTreeHandle t2"
          using X_preserve_tree EQ by auto
        have "X (HTreeHandle (get_thunk_tree (create_thunk t1))) (HTreeHandle (get_thunk_tree (create_thunk t2)))"
          using EQ HTreeHandle TREE2 by simp

        then have "X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
          using X_tree_to_thunk by auto
        then show ?thesis 
          using OCreateThunk True HTreeHandle TREE2 S eq_state_hpush eq_step_result_rel_def L by auto
      next
        case (HThunkHandle th1)
        then obtain th2 where "hs s2 ! i = HThunkHandle th2" using EQ X_preserve_thunk by auto
        then show ?thesis using OCreateThunk HThunkHandle  eq_step_result_rel_def by auto
      qed
    next
      case False
      then show ?thesis using OCreateThunk L eq_step_result_rel_def by auto
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
          using True L eq_state_hs_nth[OF S] by auto
        then show ?thesis by (induction xs) auto
      qed
      then have "list_all2 X (get_tree_raw (create_tree ?hlist1)) (get_tree_raw (create_tree ?hlist2))"
        by simp
      then have "X (HTreeHandle (create_tree ?hlist1)) (HTreeHandle (create_tree ?hlist2))"
        using create_tree_cong by auto
      then show ?thesis using OCreateTree True L assms eq_state_hpush eq_step_result_rel_def by auto
    next
      case False
      then show ?thesis using OCreateTree L eq_step_result_rel_def by auto
    qed
  next
    case (ORunInternal)
    have "eq_state_rel X (run_internal s1) (run_internal s2)"
      using assms run_internal_def eq_state_rel_def by auto
    then show ?thesis using ORunInternal eq_step_result_rel_def by auto
  next
    case (OReturn i)
    then show ?thesis
    proof (cases "i < length (hs s1)")
      case True
      then have EQ: "X (hs s1 ! i) (hs s2 ! i)" using S eq_state_hs_nth by auto
      then show ?thesis using OReturn True L eq_step_result_rel_def by auto
    next
      case False
      then show ?thesis using OReturn L eq_step_result_rel_def by auto
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes S: "eq_state_rel X s1 s2"
     and S1: "step op s1 = None"
   shows "step op s2 = None"
proof -
  have "eq_step_result_rel X (step op s1) (step op s2)"
    using step_fun_eq assms by blast
  then show ?thesis using S1 using eq_step_result_rel_def by (cases "step op s2") auto
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes S: "eq_state_rel X s1 s2"
    and S1: "step op s1 = Some (Return h1)"
  shows "\<exists>h2. step op s2 = Some (Return h2) \<and> X h1 h2"
proof -
  have H: "eq_step_result_rel X (step op s1) (step op s2)"
    using step_fun_eq assms by blast
  then show ?thesis using assms(2) eq_step_result_rel_def 
  proof (cases "step op s2")
    case None
    then show ?thesis using H eq_step_result_rel_def S1 by auto
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Continue)
      then show ?thesis using H eq_step_result_rel_def S1 Some by auto
    next
      case (Return x)
      then have "X h1 x" using H eq_step_result_rel_def S1 Some by auto
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes S: "eq_state_rel X s1 s2"
    and S1: "step op s1 = Some (Continue s1')"
  shows "\<exists>s2'. step op s2 = Some (Continue s2') \<and> eq_state_rel X s1' s2'"
proof -
  have H: "eq_step_result_rel X (step op s1) (step op s2)"
    using step_fun_eq assms by blast
  then show ?thesis using S eq_step_result_rel_def 
  proof (cases "step op s2")
    case None
    then show ?thesis using H eq_step_result_rel_def S1 by auto
  next
    case (Some a)
    then show ?thesis
    proof (cases a)
      case (Return)
      then show ?thesis using H eq_step_result_rel_def S1 Some by auto
    next
      case (Continue x)
      then have "eq_state_rel X s1' x" using H eq_step_result_rel_def S1 Some by auto
      then have "step op s2 = Some (Continue x) \<and> eq_state_rel X s1' x"
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  shows "eq_state_rel X s1 s2 \<Longrightarrow> rel_opt X (exec p s1) (exec p s2)"
proof (induction p arbitrary: s1 s2)
  case Nil
  then show ?case by auto
next
  case (Cons i xs)
  assume S: "eq_state_rel X s1 s2"

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
      have Ex: "\<exists>s2'. step i s2 = Some (Continue s2') \<and> eq_state_rel X s1' s2'"
        using step_eq_continue[OF assms S S1] by assumption
      then obtain s2' where S2: "step i s2 = Some (Continue s2')"
                        and EQ': "eq_state_rel X s1' s2'"
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
      and S: "eq_state_rel X s1 s2"
      and S1: "exec p s1 = Some h1"
    shows "\<exists>h2. exec p s2 = Some h2 \<and> X h1 h2"
proof -
  have H: "rel_opt X (exec p s1) (exec p s2)"
    using exec_eq[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                  create_blob_cong create_tree_cong X_preserve_blob
                  X_preserve_tree X_preserve_thunk X_tree_to_thunk
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
      and S: "eq_state_rel X s1 s2"
      and S1: "exec p s1 = None"
    shows "exec p s2 = None"
proof -
 have H: "rel_opt X (exec p s1) (exec p s2)"
    using exec_eq[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                  create_blob_cong create_tree_cong X_preserve_blob
                  X_preserve_tree X_preserve_thunk X_tree_to_thunk
                  X_self S] .
  then show ?thesis
    using S1 by (cases "exec p s2") auto
qed

(* 6. Given two equivalent trees, thinking them for one step either both returns None, or
returns equivalent handles*)

lemma state_init_eq:
  assumes "X (HTreeHandle t1) (HTreeHandle t2)"
  shows "eq_state_rel X (state_init (create_thunk t1)) (state_init (create_thunk t2))"
  using assms
  unfolding state_init_def eq_state_rel_def
  by simp

lemma think_eq:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
    and S: "X (HTreeHandle t1) (HTreeHandle t2)"
    shows "rel_opt X (think (create_thunk t1)) (think (create_thunk t2))"
proof -
  let ?s1 = "state_init (create_thunk t1)"
  let ?s2 = "state_init (create_thunk t2)"
  have EQSTATE: "eq_state_rel X ?s1 ?s2"
    using state_init_eq S
    by auto
  have SAMEPROG: "get_prog (get_thunk_tree (create_thunk t1)) = get_prog (get_thunk_tree (create_thunk t2))"
    using get_prog_cong S
    by auto

  show ?thesis
  proof (cases "think (create_thunk t1)")
    case None
    then have "think (create_thunk t2) = None"
      using SAMEPROG exec_eq_none[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                  create_blob_cong create_tree_cong X_preserve_blob
                  X_preserve_tree X_preserve_thunk X_tree_to_thunk
                  X_self EQSTATE] think_def by auto
    then show ?thesis using None by auto
  next
    case (Some h1)
    then have SOME1: "exec (get_prog (get_thunk_tree (create_thunk t1))) ?s1 = Some h1"
      using think_def by auto
    have "\<exists>h2. exec (get_prog (get_thunk_tree (create_thunk t1))) ?s2 = Some h2 \<and> X h1 h2"
      using exec_eq_some[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
                  create_blob_cong create_tree_cong X_preserve_blob
                  X_preserve_tree X_preserve_thunk X_tree_to_thunk
                  X_self EQSTATE SOME1] .
    then obtain h2 where "exec (get_prog (get_thunk_tree (create_thunk t2))) ?s2 = Some h2 \<and> X h1 h2"
      using SAMEPROG by auto
    then show ?thesis using Some think_def by auto
  qed
qed

corollary think_eq_some:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes S: "X (HTreeHandle t1) (HTreeHandle t2)"
  assumes S1: "think (create_thunk t1) = Some r1"
    shows "\<exists>r2. think (create_thunk t2) = Some r2 \<and> X r1 r2"
proof -
  have R: "rel_opt X (think (create_thunk t1)) (think (create_thunk t2))"
    using get_blob_data_cong get_tree_size_cong get_tree_data_cong create_blob_cong
          create_tree_cong X_preserve_blob X_preserve_tree X_preserve_thunk X_tree_to_thunk
          X_self get_prog_cong S
    by (rule think_eq[of X t1 t2])
  then show ?thesis using S1 by (cases "think (create_thunk t2)") auto
qed

corollary think_eq_none:
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
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes X_tree_to_thunk: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_self: "\<And>h. X h h"
  assumes get_prog_cong: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"
  assumes S: "X (HTreeHandle t1) (HTreeHandle t2)"
     and S1: "think (create_thunk t1) = None"
   shows "think (create_thunk t2) = None"
proof -
  have R: "rel_opt X (think (create_thunk t1)) (think (create_thunk t2))"
    using get_blob_data_cong get_tree_size_cong get_tree_data_cong create_blob_cong
          create_tree_cong X_preserve_blob X_preserve_tree X_preserve_thunk X_tree_to_thunk
          X_self get_prog_cong S
    by (rule think_eq[of X t1 t2])
  then show ?thesis using S1 by (cases "think (create_thunk t2)") auto
qed

lemma not_is_thunk_eq:
 fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes X_preserve_blob: "\<And>b h. X (HBlobHandle b) h \<Longrightarrow> \<exists>b'. h = (HBlobHandle b')"
  assumes X_preserve_tree: "\<And>t h. X (HTreeHandle t) h \<Longrightarrow> \<exists>t'. h = (HTreeHandle t')"
  assumes X_preserve_thunk: "\<And>th h. X (HThunkHandle th) h \<Longrightarrow> \<exists>th'. h = (HThunkHandle th')"
  assumes S: "X h1 h2"
  assumes NT1: "\<not> is_thunk h1"
  shows "\<not> is_thunk h2"
proof (cases h1)
  case (HBlobHandle b1)
  then obtain b2 where "h2 = HBlobHandle b2"
    using X_preserve_blob S by auto
  then show ?thesis by auto
next
  case (HTreeHandle t1)
  then obtain t2 where "h2 = HTreeHandle t2"
    using X_preserve_tree S by auto
  then show ?thesis by auto
next
  case (HThunkHandle th1)
  then show ?thesis using NT1 by auto
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
| R_trans_thunk:
    "R (HThunkHandle th1) (HThunkHandle th2)
     \<Longrightarrow> R (HThunkHandle th2) (HThunkHandle th3)
     \<Longrightarrow> R (HThunkHandle th1) (HThunkHandle th3)"

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
  case R_trans_thunk
  then show ?thesis by simp
qed

thm eq.coinduct

(* TODO: remove this axiom with real get_prog definition *) 
axiomatization where
  get_prog_R:
    "R (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"

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
    case (R_trans_thunk th1 th2 th3)
    then show ?thesis by auto
  next
    case (R_tree_to_thunk t1 t2)

    have TH: "rel_opt R (think (create_thunk t1)) (think (create_thunk t2))"
    proof (rule_tac X=R in think_eq)
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
      show "R (HTreeHandle t1) (HTreeHandle t2)"
        using R_tree_to_thunk(3) .
    qed

    show ?thesis
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

      then show ?thesis
      proof (cases r1)
        case (HBlobHandle b1)
        then have NT: "\<not> is_thunk r1" by auto
        
        obtain "t2'" where "r2 = HBlobHandle t2'"
          using HBlobHandle RRES R_preserve_blob by auto
        then have "\<not> is_thunk r2" by auto
        then show ?thesis using Some SOME2 R_tree_to_thunk ROREQ NT by auto
      next
        case (HTreeHandle t1')
        then have NT: "\<not> is_thunk r1" by auto

        obtain "t2'" where "r2 = HTreeHandle t2'" 
          using HTreeHandle RRES R_preserve_tree by auto
        then have "\<not> is_thunk r2" by auto
        then show ?thesis using Some SOME2 R_tree_to_thunk ROREQ NT by auto
      next
        case (HThunkHandle th1)
        then obtain th2 where TH2: "r2 = HThunkHandle th2" 
          using R_preserve_thunk RRES by auto

        have "think (create_thunk t2) = Some (HThunkHandle th2)"
          using SOME2 TH2 by auto
        then have "eq (HThunkHandle (create_thunk t2)) (HThunkHandle th2)"
          by (rule eq.EqThunkSingleStep)
        then have STEP2: "eq (HThunkHandle th2) (HThunkHandle (create_thunk t2))"
          by (rule eq.EqThunkSymm)

        have "think (create_thunk t1) = Some (HThunkHandle th1)"
          using Some HThunkHandle by auto
        then have "eq (HThunkHandle (create_thunk t1)) (HThunkHandle th1)"
          by (rule eq.EqThunkSingleStep)
        then have STEP1: "R (HThunkHandle (create_thunk t1)) (HThunkHandle th1)"
          by (rule R.R_from_eq)

        have SS: "R (HThunkHandle th1) (HThunkHandle th2)" using RRES HThunkHandle TH2 by auto
       
        have STEP1: "R (HThunkHandle (create_thunk t1)) (HThunkHandle th2)"
          using STEP1 SS by (rule R.R_trans_thunk)

        show ?thesis using R_tree_to_thunk HThunkHandle TH2 STEP1 STEP2 by auto
      qed
    qed
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
