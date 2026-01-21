theory eqqq
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
  "(get_blob_data b1 = get_blob_data b2) \<Longrightarrow> eq (HBlobHandle b1) (HBlobHandle b2)"
| EqTree:
  "list_all2 eq (get_tree_raw t1) (get_tree_raw t2) \<Longrightarrow>
   eq (HTreeHandle t1) (HTreeHandle t2)"
| EqThunk:
  "force (HThunkHandle th1) = Some r1 \<Longrightarrow>
   force (HThunkHandle th2) = Some r2 \<Longrightarrow>
    eq r1 r2 \<Longrightarrow>
   eq (HThunkHandle th1) (HThunkHandle th2)"
| EqThunkTree:
   "eq (HTreeHandle (get_thunk_tree th1)) (HTreeHandle (get_thunk_tree th2)) \<Longrightarrow>
    eq (HThunkHandle th1) (HThunkHandle th2)"
| EqSelf:
   "eq h h"

axiomatization where
  get_prog_eq:
    "eq (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> get_prog t1 = get_prog t2"

lemma eq_same_type:
  assumes "eq h1 h2"
  shows "get_type h1 = get_type h2"
  using assms
  by (cases rule: eq.cases) auto 

(* eq preserved by thunk application *)

(* 1. Useful lemmas and definitions *)
definition relate_opt :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> bool" where
  "relate_opt P x y \<equiv>
     (case x of None \<Rightarrow> y = None 
     | Some a \<Rightarrow> (\<exists>b. y = Some b \<and> P a b))"

definition eq_state :: "state \<Rightarrow> state \<Rightarrow> bool" where
  "eq_state s1 s2 \<equiv>
     list_all2 (\<lambda>h1 h2. eq h1 h2) (hs s1) (hs s2) \<and> ds s1 = ds s2"

lemma list_all2_append:
  assumes "list_all2 P xs ys"
    and "P x y"
  shows   "list_all2 P (xs @ [x]) (ys @ [y])"
  using assms
  by (induction arbitrary: x y rule: list_all2_induct) simp_all

lemma eq_state_hpush:
  assumes "eq_state s1 s2" and "eq h1 h2"
  shows "eq_state (hpush s1 h1) (hpush s2 h2)"
  using assms unfolding eq_state_def hpush_def
  by (auto simp: list_all2_append)

lemma eq_dpush:
  assumes "eq_state s1 s2" and "d1 = d2"
  shows "eq_state (dpush s1 d1) (dpush s2 d2)"
  using assms unfolding eq_state_def dpush_def by auto

lemma eq_same_kind_blob:
  assumes "eq (HBlobHandle b1) h2"
  obtains "b2" where "h2 = HBlobHandle b2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_not_blob:
  assumes "eq h1 h2"
  shows "(\<forall>b. h1 \<noteq> HBlobHandle b) \<Longrightarrow> (\<forall>b. h2 \<noteq> HBlobHandle b)"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_tree:
  assumes "eq (HTreeHandle t1) h2"
  obtains "t2" where "h2 = HTreeHandle t2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_not_tree:
  assumes "eq h1 h2"
  shows "(\<forall>t. h1 \<noteq> HTreeHandle t) \<Longrightarrow> (\<forall>t. h2 \<noteq> HTreeHandle t)"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_same_kind_thunk:
  assumes "eq (HThunkHandle th1) h2"
  obtains "th2" where "h2 = HThunkHandle th2"
  using assms
  by (cases rule: eq.cases) auto

lemma eq_not_thunk:
  assumes "eq h1 h2" and "\<not> is_thunk h1"
  shows   "\<not> is_thunk h2"
  using assms
  by (cases h1) auto

lemma eq_state_hs:
  "eq_state s1 s2 \<Longrightarrow> list_all2 (\<lambda>h1 h2. eq h1 h2) (hs s1) (hs s2)"
  by (simp add: eq_state_def)

lemma eq_state_ds:
  "eq_state s1 s2 \<Longrightarrow> (ds s1) = (ds s2)"
  by (simp add: eq_state_def)

lemma eq_state_hs_same_length:
  assumes "eq_state s1 s2"
  shows "length (hs s1) = length (hs s2)"
  using eq_state_hs[OF assms]
  by (simp add: list_all2_lengthD)

lemma eq_state_hs_nth:
  assumes "eq_state s1 s2" "i < length (hs s1)"
  shows "eq ((hs s1) ! i) ((hs s2)! i) \<and> i < length (hs s2)"
  using eq_state_hs[OF assms(1)] assms(2)
  by (simp add: list_all2_conv_all_nth)
  
definition eq_step_result :: "step_result option \<Rightarrow> step_result option \<Rightarrow> bool" where
  "eq_step_result r1 r2 \<equiv> 
   (case (r1, r2) of
     (Some (Continue s1), Some (Continue s2)) \<Rightarrow> eq_state s1 s2
   | (Some (Return r1), Some (Return r2)) \<Rightarrow> eq r1 r2
   | (None, None) \<Rightarrow> True
   | (_, _) \<Rightarrow> False)"

(* 2. API functions respect sem_eq *)
lemma get_blob_data_eq:
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

lemma get_tree_size_eq:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
  shows   "get_tree_size t1 = get_tree_size t2"
  using eq_tree_children[OF assms]
  by (simp add: get_tree_size_def list_all2_lengthD)

lemma get_tree_data_eq:
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

lemma create_blob_eq:
  assumes "d1 = d2"
  shows "eq (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
proof -
  have "get_blob_data (create_blob d1) = get_blob_data (create_blob d2)" 
    using assms by simp_all
  then show ?thesis by (rule eq.EqBlob) 
qed

lemma create_tree_eq:
  assumes "list_all2 eq xs ys"
  shows "eq (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
proof -
  have "list_all2 eq (get_tree_raw (create_tree xs)) (get_tree_raw (create_tree ys))"
    using assms by simp_all
  then show ?thesis by (rule eq.EqTree)
qed

lemma create_thunk_eq:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
  shows   "eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
proof -
  have EQ: "eq (HTreeHandle (get_thunk_tree (create_thunk t1))) (HTreeHandle (get_thunk_tree (create_thunk t2)))"
    using assms
    by simp_all
  then show ?thesis by (rule eq.EqThunkTree)
qed

lemma run_internal_eq:
  assumes "eq_state s1 s2"
  shows "eq_state (run_internal s1) (run_internal s2)"
proof -
  have "list_all2 eq (hs s1) (hs s2)" using assms unfolding eq_state_def by simp_all
  then have HS: "list_all2 eq (hs (run_internal s1)) (hs (run_internal s2))" 
    using run_internal_hs 
    by simp

  have DS: "ds s1 = ds s2" using assms unfolding eq_state_def by simp_all
  have DS': "ds (run_internal s1) = ds (run_internal s2)"
    using run_internal_ds_equiv[OF DS]
    by assumption

  show ?thesis using HS DS' eq_state_def by auto
qed

lemma step_eq_none:
  assumes "eq_state s1 s2"
  and "step op s1 = None"
  shows "step op s2 = None"
proof -
  have L: "length (hs s1) = length (hs s2)" using eq_state_hs_same_length[OF assms(1)] .
  have D: "(ds s1) = (ds s2)" using eq_state_ds[OF assms(1)] .

  show ?thesis
  proof (cases op)
    case (OGetBlobData x)
    show ?thesis 
    proof (cases "x < length (hs s1)")
      case False
      then show ?thesis using L OGetBlobData False by (simp add: step.simps)
    next 
      case True
      then have EQ: "eq ((hs s1) ! x) ((hs s2) !x)" using eq_state_hs_nth[OF assms(1) True] by simp
      have "\<not> (\<exists>b. (hs s1) ! x = HBlobHandle b)"
        using True OGetBlobData assms(2)
        by (auto simp: step.simps split: handle.splits)
      then have "\<not> (\<exists>b. (hs s2) ! x = HBlobHandle b)"
        using eq_not_blob EQ
        by blast
      then show ?thesis using OGetBlobData True by (auto simp: step.simps split: handle.splits)
    qed
  next
    case (OGetTreeData x y)
    show ?thesis
    proof (cases "x < length (hs s1)")
      case False
      then show ?thesis using L OGetTreeData False by (simp add: step.simps)
    next
      case True
      then have EQ: "eq ((hs s1) ! x) ((hs s2) !x)" 
        using eq_state_hs_nth[OF assms(1) True] by simp
      have EQL: "x < length (hs s2)" using eq_state_hs_nth[OF assms(1) True] by simp
      show ?thesis
      proof (cases "\<not>(\<exists>t. (hs s1) ! x = HTreeHandle t)")
        case True
        then have "\<not>(\<exists>t. (hs s2) ! x = HTreeHandle t)" using eq_not_tree EQ by blast
        then show ?thesis using OGetTreeData True 
          by (auto simp: step.simps split: handle.splits)
      next
        case False
        then obtain "t1" where EQ1: "(hs s1) ! x = HTreeHandle t1"
          by auto
        then have Y: "\<not> y < get_tree_size t1" using OGetTreeData True False assms(2) 
          by (auto simp add: step.simps split: handle.splits)
        have "\<exists>t. (hs s2) ! x = HTreeHandle t" using EQ eq_same_kind_tree EQ1 by simp blast
        then obtain "t2" where EQ2: "(hs s2) ! x = HTreeHandle t2" by auto
        then have "\<not> y < get_tree_size t2" using Y EQ EQ1 EQ2 get_tree_size_eq by simp
        then show ?thesis using OGetTreeData EQ2 EQL 
          by (auto simp: step.simps split: handle.splits)
      qed
    qed
  next
    case (OCreateBlob x)
    then show ?thesis using assms(2) OCreateBlob D by (auto simp: step.simps)
  next
    case (OCreateThunk x)
    show ?thesis 
    proof (cases "x < length (hs s1)")
      case True
      have "\<not>(\<exists>t. (hs s1) ! x = HTreeHandle t)" 
        using eq_state_hs_nth[OF assms(1) True] OCreateThunk True assms(2) 
        by (auto simp: step.simps split: handle.splits)
      then have "\<not>(\<exists>t. (hs s2) !x = HTreeHandle t)" 
        using eq_state_hs_nth[OF assms(1) True] eq_not_tree by auto
      then show ?thesis using OCreateThunk True 
        by (auto simp: step.simps split: handle.splits)
    next 
      case False
      then show ?thesis 
        using L OCreateThunk 
        by (auto simp: step.simps split: handle.splits)
    qed
  next
    case (OCreateTree xs)
    then show ?thesis
      using assms(2) L
      by (auto simp: step.simps Let_def split: if_splits)
  next
    case (ORunInternal)
    then show ?thesis using assms by (auto simp: step.simps)
  next
    case (OReturn x)
    then show ?thesis using assms L 
      by (auto simp: step.simps)
  qed
qed


lemma step_eq_return:
  assumes "eq_state s1 s2"
  and "step op s1 = Some (Return h1)"
shows "\<exists>h2. step op s2 = Some (Return h2) \<and> eq h1 h2"
proof -
  have L: "length (hs s1) = length (hs s2)" using eq_state_hs_same_length[OF assms(1)] .

  show ?thesis
  proof (cases op)
    case (OGetBlobData x)
    then have False 
      using assms(2)
      by (auto simp: step.simps split: handle.splits if_splits)
    then show ?thesis by auto
  next
    case (OGetTreeData x y)
    then have False 
      using assms(2)
      by (auto simp: step.simps split: handle.splits if_splits)
    then show ?thesis by auto
  next
    case (OCreateBlob x)
    then have False 
      using assms(2)
      by (auto simp: step.simps split: handle.splits if_splits)
    then show ?thesis by auto
  next
    case (OCreateTree xs)
    then have False 
      using assms(2)
      by (auto simp: step.simps split: handle.splits if_splits)
    then show ?thesis by auto
  next
    case (OCreateThunk x)
    then have False 
      using assms(2)
      by (auto simp: step.simps split: handle.splits if_splits)
    then show ?thesis by auto
  next
    case (ORunInternal)
    then have False 
      using assms(2)
      by (auto simp: step.simps split: handle.splits if_splits)
    then show ?thesis by auto
  next
    case (OReturn x)
    then have L1:"x < length (hs s1)" and H1:"(hs s1) ! x = h1"
      using assms(2) OReturn
      by (auto simp: step.simps split: if_splits)

    let ?h2 = "(hs s2) ! x"

    have "x < length (hs s2)" using L L1 by simp
    then have STEP: "step op s2 = Some (Return ?h2)" 
      using OReturn 
      by (auto simp: step.simps)

    have "eq h1 ?h2" using assms(1) H1 eq_state_hs_nth L L1 by auto

    then show ?thesis using STEP by auto
  qed
qed

lemma step_eq_continue:
  assumes "eq_state s1 s2"
  and "step op s1 = Some (Continue r1)"
shows "\<exists>r2. step op s2 = Some (Continue r2) \<and> eq_state r1 r2"
proof -
  have L: "length (hs s1) = length (hs s2)" using eq_state_hs_same_length[OF assms(1)] .
  have D : "(ds s1) = (ds s2)" using eq_state_ds[OF assms(1)] .

  show ?thesis
  proof (cases op)
    case (OReturn x)
    then have False 
      using assms(2)
      by (cases "x < length (hs s1)") (auto simp: step.simps)
    then show ?thesis by auto
  next
    case (OGetBlobData x)
    obtain b1 where L1: "x < length (hs s1)" 
           and B1: "hs s1 ! x = HBlobHandle b1"
           and R1: "r1 = dpush s1 (get_blob_data b1)"
      using OGetBlobData assms(2)
      by (auto simp: step.simps split: if_splits handle.splits step_result.splits)

    have EQ: "eq (hs s1 ! x) (hs s2 ! x)" using L1 assms(1) eq_state_hs_nth by auto
    then obtain b2 where B2: "hs s2 ! x = HBlobHandle b2" 
      using eq_same_kind_blob B1 by auto

    have "get_blob_data b1 = get_blob_data b2"
      using EQ B1 B2 get_blob_data_eq
      by auto

    then have STATE:"eq_state (dpush s1 (get_blob_data b1)) (dpush s2 (get_blob_data b2))"
      using assms(1) eq_dpush by auto

    have STEP: "step op s2 = Some(Continue(dpush s2 (get_blob_data b2)))"
      using L L1 B2 OGetBlobData 
      by (auto simp: step.simps split:if_splits handle.splits)

    let ?r2 = "Some(Continue(dpush s2 (get_blob_data b2)))"
    show ?thesis using STEP STATE R1 by auto
  next
    case (OGetTreeData x y)
    obtain h1 where L1: "x < length (hs s1)" 
              and H1: "hs s1 ! x = HTreeHandle h1" 
              and S1: "y < get_tree_size h1" 
              and R1: "r1 = hpush s1 (get_tree_data h1 y)"
      using assms(2) OGetTreeData by (auto simp: step.simps split: if_splits handle.splits)

    have EQ: "eq (hs s1 ! x) (hs s2 ! x)" using L1 assms(1) eq_state_hs_nth by auto
    then obtain h2 where H2: "hs s2 ! x = HTreeHandle h2" 
      using eq_same_kind_tree H1 by auto

    have S2: "y < get_tree_size h2" using EQ H1 H2 get_tree_size_eq S1 by auto

    have EQOUT: "eq (get_tree_data h1 y) (get_tree_data h2 y)" 
      using get_tree_data_eq S1 EQ H1 H2 by auto

    let ?r2 = "hpush s2 (get_tree_data h2 y)"
    have STATE: "eq_state r1 ?r2" using eq_state_hpush assms(1) EQOUT S1 R1 by auto
    have STEP: "step op s2 = Some(Continue ?r2)" using OGetTreeData L L1 H2 S2 
      by (auto simp: step.simps split: if_splits handle.splits)
    show ?thesis using STATE STEP by auto
  next
    case (OCreateBlob x)
    then have L1: "x < length (ds s1)" 
         and R1: "r1 = hpush s1 (HBlobHandle (create_blob (ds s1 ! x)))"
      using assms(2) by (auto simp: step.simps split: if_splits)

    have "(ds s1) ! x = (ds s2) ! x"
      using D L1 by simp
    then have EQOUT: "eq (HBlobHandle (create_blob (ds s1 ! x))) (HBlobHandle (create_blob (ds s2 ! x)))"
      using create_blob_eq
      by auto

    let ?r2 = "hpush s2 (HBlobHandle (create_blob (ds s2 ! x)))"
    have STATE: "eq_state r1 ?r2"
      using assms(1) EQOUT eq_state_hpush R1 by auto
    have STEP: "step op s2 = Some (Continue ?r2)"
      using D L1 OCreateBlob by (auto simp: step.simps split: if_split handle.splits)
    show ?thesis using STATE STEP by auto
  next
    case (OCreateTree xs)
    let ?hlist1 = "map (\<lambda>i. hs s1 ! i) xs"
    let ?hlist2 = "map (\<lambda>i. hs s2 ! i) xs"

    have L1: "\<forall>x \<in> set xs. x < length (hs s1)"
     and R1: "r1 = hpush s1 (HTreeHandle (create_tree ?hlist1))"
      using assms(2) OCreateTree 
      by (auto simp: step.simps split: if_splits handle.splits)

    have "list_all2 eq ?hlist1 ?hlist2"
    proof -
      have "\<forall> x \<in> set xs. eq (hs s1 ! x) (hs s2 ! x)"
        using L L1 assms(1) eq_state_hs_nth by auto
      then show ?thesis by (induction xs) auto
    qed

    then have EQ: "eq (HTreeHandle (create_tree ?hlist1)) (HTreeHandle (create_tree ?hlist2))"
      using create_tree_eq
      by auto

    let ?r2 = "hpush s2 (HTreeHandle (create_tree ?hlist2))"
    have STATE: "eq_state r1 ?r2"
      using assms(1) EQ eq_state_hpush R1 by auto
    have STEP: "step op s2 = Some (Continue ?r2)"
      using L L1 OCreateTree by (auto simp: step.simps split: if_split handle.splits)
    show ?thesis using STATE STEP by auto
  next
    case (OCreateThunk i)
    then obtain t1 where L1: "i < length (hs s1)"
                    and T1: "(hs s1 ! i) = HTreeHandle t1"
                    and R1: "r1 = hpush s1 (HThunkHandle (create_thunk t1))"
      using assms(2)
      by (auto simp: step.simps split: if_splits handle.splits)

    have EQ: "eq (hs s1 ! i) (hs s2 ! i)" 
      using assms(1) eq_state_hs_nth L L1
      by auto
    then obtain t2 where T2: "(hs s2 ! i) = HTreeHandle t2"
      using eq_same_kind_tree T1
      by auto

    let ?r2 = "hpush s2 (HThunkHandle (create_thunk t2))"

    have "eq (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
      using T1 T2 EQ create_thunk_eq
      by auto
    then have STATE: "eq_state r1 ?r2"
      using assms(1) eq_state_hpush R1 by auto
    have STEP: "step op s2 = Some (Continue ?r2)"
      using L L1 OCreateThunk T2 by (auto simp: step.simps split: if_split handle.splits)
    then show ?thesis using STATE by auto
  next
    case (ORunInternal)
    then have R1: "r1 = run_internal s1"
      using assms(2)
      by (auto simp: step.simps)

    let ?r2 = "run_internal s2"
    have STATE: "eq_state r1 ?r2"
      using assms(1) R1 run_internal_eq
      by auto
    have STEP: "step op s2 = Some (Continue ?r2)" 
      using ORunInternal by (auto simp: step.simps)
    then show ?thesis using STATE by auto
  qed
qed

lemma step_fun_eq:
  assumes "eq_state s1 s2"
  shows   "eq_step_result (step op s1) (step op s2)"
proof (cases "step op s1")
  case None
  then show ?thesis using assms eq_step_result_def step_eq_none by auto
next
  case (Some r1)
  show ?thesis
  proof (cases r1)
    case (Continue x1)
    obtain x2 where "step op s2 = Some (Continue x2) \<and> eq_state x1 x2"
      using assms Some Continue step_eq_continue by blast
    then show ?thesis using eq_step_result_def Some Continue by auto
  next
    case (Return x1)
    obtain x2 where "step op s2 = Some (Return x2) \<and> eq x1 x2"
      using assms Some Return step_eq_return by blast
    then show ?thesis using eq_step_result_def Some Return by auto
  qed
qed

lemma exec_eq_some:
  assumes "eq_state s1 s2"
      and "exec p s1 = Some h1"
    shows "\<exists>h2. exec p s2 = Some h2 \<and> eq h1 h2"
  using assms
proof (induction p arbitrary: s1 s2 h1)
  case Nil
  then show ?case using assms(1) by auto
next
  case (Cons op xs)
  have EQ: "eq_step_result (step op s1) (step op s2)"
    using assms(1) step_fun_eq Cons by auto

  show ?case
  proof (cases "step op s1")
    case None
    then show ?thesis using assms(2) Cons by auto
  next
    case (Some r1)
    show ?thesis
    proof (cases r1)
      case (Continue s1')
      then have E1: "exec xs s1' = Some h1"
        using Some Cons by (auto simp: exec.simps)

      have S1: "step op s1 = Some (Continue s1')" 
        using Some Continue 
        by simp
      then obtain s2' where S2: "step op s2 = Some (Continue s2')"
        using step_eq_continue assms(1) Cons
        by blast

      have "eq_step_result (step op s1) (step op s2)"
        using assms(1) step_fun_eq Cons
        by blast
      then have "eq_state s1' s2'"
        unfolding eq_step_result_def
        using S1 S2
        by auto

      then obtain h2 where H2: "exec xs s2' = Some h2 \<and> eq h1 h2"
        using Cons.IH E1 by blast
      have "exec (op # xs) s2 = Some h2"
        using Cons S2 H2 by auto
      then show ?thesis 
        using H2 by auto
    next
      case (Return h1')
      then have "h1 = h1'" using assms(2) Some Cons by auto
      then have H1: "step op s1 = Some (Return h1)" 
        using Some Return by simp
      then obtain h2 where H2: "step op s2 = Some (Return h2)"
        using step_eq_return assms(1) Cons
        by blast

      have "eq_step_result (step op s1) (step op s2)"
        using assms(1) step_fun_eq Cons
        by blast
      then have "eq h1 h2"
        unfolding eq_step_result_def
        using H1 H2
        by auto
      then show ?thesis using Cons H2 by auto
    qed
  qed
qed

lemma exec_eq_none:
"eq_state s1 s2 \<Longrightarrow> exec p s1 = None \<Longrightarrow> exec p s2 = None"
proof (induction p arbitrary: s1 s2)
  case Nil
  then show ?case by auto
next
  case (Cons op xs)
  have EQ: "eq_step_result (step op s1) (step op s2)"
    using step_fun_eq[OF Cons.prems(1)] Cons by auto

  show ?case
  proof (cases "step op s1")
    case None
    then have "step op s1 = None" by simp
    then have "step op s2 = None" 
      using step_eq_none Cons.prems(1)
      by auto
    then show ?thesis using Cons by auto
  next
    case (Some r1)
    then show ?thesis
    proof (cases r1)
      case (Return h1)
      then show ?thesis using Cons.prems(2) Cons Some by auto
    next
      case (Continue s1')
      then have S1: "step op s1 = Some (Continue s1')" using Some by simp
      then obtain s2' where S2: "step op s2 = Some(Continue s2')" 
                        and EQ': "eq_state s1' s2'"
        using step_eq_continue Cons.prems(1) by blast

      have "exec xs s1' = None"
        using Cons Some Continue by simp
      then have "exec xs s2' = None"
        using EQ' Cons.IH
        by auto
      then show ?thesis using Cons S2 by auto
    qed
  qed
qed

lemma state_init_eq:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
  shows "eq_state (state_init (create_thunk t1)) (state_init (create_thunk t2))"
  using assms
  unfolding state_init_def eq_state_def
  by simp

lemma think_eq_some:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
      and "think (create_thunk t1) = Some r1"
    shows "\<exists>r2. think (create_thunk t2) = Some r2 \<and> eq r1 r2"
proof -
  let ?s1 = "state_init (create_thunk t1)"
  let ?s2 = "state_init (create_thunk t2)"

  have EQ: "eq_state ?s1 ?s2"
    using state_init_eq assms(1)
    by auto

  have "get_prog (get_thunk_tree (create_thunk t1)) = get_prog (get_thunk_tree (create_thunk t2))"
    using get_prog_eq assms(1)
    by auto
  then have "exec (get_prog (get_thunk_tree (create_thunk t2))) ?s1 = Some r1"
    using assms(2)
    unfolding think_def
    by simp
  then obtain r2 where "exec (get_prog (get_thunk_tree (create_thunk t2))) ?s2 = Some r2 \<and> eq r1 r2"
    using EQ exec_eq_some
    by blast
  then show ?thesis using think_def by auto
qed

lemma think_eq_none:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
     and "think (create_thunk t1) = None"
   shows "think (create_thunk t2) = None"
proof -
  let ?s1 = "state_init (create_thunk t1)"
  let ?s2 = "state_init (create_thunk t2)"

  have EQ: "eq_state ?s1 ?s2"
    using state_init_eq assms(1)
    by auto

  have "get_prog (get_thunk_tree (create_thunk t1)) = get_prog (get_thunk_tree (create_thunk t2))"
    using get_prog_eq assms(1)
    by auto
  then have "exec (get_prog (get_thunk_tree (create_thunk t2))) ?s1 = None"
    using assms(2)
    unfolding think_def
    by simp
  then show ?thesis
    using EQ exec_eq_none think_def
    by auto
qed

fun eq_opt :: "handle option \<Rightarrow> handle option \<Rightarrow> bool" where
  "eq_opt None None = True"
| "eq_opt (Some h1) (Some h2) = eq h1 h2"
| "eq_opt _ _ = False"

lemma force_with_fuel_eq:
  shows "\<And>t1 t2 h1.
    eq (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
    force_with_fuel (Suc n1) (HThunkHandle (create_thunk t1)) = Some h1 \<Longrightarrow>
    \<not> is_thunk h1 \<Longrightarrow>
    \<exists>n2 h2.
      force_with_fuel (Suc n2) (HThunkHandle (create_thunk t2)) = Some h2
      \<and> \<not> is_thunk h2 \<and> eq h1 h2"
proof (induction n1)
  case 0
  then show ?case
  proof (cases "think (create_thunk t1)")
    case None
    then show ?thesis using 0 by auto
  next
    case (Some h1')
    then have "force_with_fuel (Suc 0) (HThunkHandle (create_thunk t1)) = force_with_fuel 0 h1'"
      using 0 by auto
    then have "force_with_fuel 0 h1' = Some h1" 
      using 0 by auto
    then have NT1: "\<not> is_thunk h1'" and EQ': "Some h1' = Some h1"
      by (auto simp: force_with_fuel.simps split: if_split handle.splits)

    obtain h2' where Some2: "think (create_thunk t2) = Some h2'"
                 and    EQ: "eq h1' h2'"
      using 0(1) think_eq_some Some
      by blast

    have NT2: "\<not> is_thunk h2'" using NT1 eq_not_thunk EQ by auto
    then have "force_with_fuel 0 h2' = Some h2'" 
      by (auto simp: force_with_fuel.simps split: if_split handle.splits)
    then have FORCE2: "force_with_fuel (Suc 0) (HThunkHandle (create_thunk t2)) = Some h2'"
      using Some2 by auto
    have EQN: "eq h1 h2'" using EQ' EQ by simp
    show ?thesis using FORCE2 NT2 EQN by auto
  qed
next
  case (Suc n)
  then show ?case
  proof (cases "think (create_thunk t1)")
    case None
    then show ?thesis using Suc by auto
  next
    case (Some h1')
    then have F1: "force_with_fuel (Suc n) h1' = Some h1"
      using Suc
      by auto

    show ?thesis
    proof (cases h1')
      case (HBlobHandle b1)
      then have FN1: "force_with_fuel (Suc n) (HThunkHandle (create_thunk t1)) = Some h1'"
        using Some by auto
      have NT1: "\<not> is_thunk h1'" using HBlobHandle by auto

      have "force_with_fuel (Suc n) h1' = Some h1'" using HBlobHandle by auto
      then have EQ1: "h1' = h1" using F1 Suc by auto
      
      obtain n2 h2 where FN2: "force_with_fuel (Suc n2) (HThunkHandle (create_thunk t2)) = Some h2"
                     and NT2: "\<not>is_thunk h2"
                     and EQ2: "eq h1' h2"
        using Suc.IH[OF Suc(2) FN1 NT1] by auto
      have EQ: "eq h1 h2" using EQ1 EQ2 by simp
      then show ?thesis using FN2 NT2 EQ by auto
    next
      case (HTreeHandle tr1)
      then have FN1: "force_with_fuel (Suc n) (HThunkHandle (create_thunk t1)) = Some h1'"
        using Some by auto
      have NT1: "\<not> is_thunk h1'" using HTreeHandle by auto

      have "force_with_fuel (Suc n) h1' = Some h1'" using HTreeHandle by auto
      then have EQ1: "h1' = h1" using F1 Suc by auto
      
      obtain n2 h2 where FN2: "force_with_fuel (Suc n2) (HThunkHandle (create_thunk t2)) = Some h2"
                     and NT2: "\<not>is_thunk h2"
                     and EQ2: "eq h1' h2"
        using Suc.IH[OF Suc(2) FN1 NT1] by auto
      have EQ: "eq h1 h2" using EQ1 EQ2 by simp
      then show ?thesis using FN2 NT2 EQ by auto
    next
      case (HThunkHandle th1)
      then have FN1: "force_with_fuel (Suc n) (HThunkHandle th1) = Some h1"
        using Some Suc by auto

      obtain h2 where T: "think (create_thunk t2) = Some h2"
                  and E: "eq (HThunkHandle th1) h2"
        using think_eq_some Suc(2) Some HThunkHandle by blast
      then obtain th2 where S: "h2 = HThunkHandle th2"
        using eq_same_kind_thunk by auto
      then have "think (create_thunk t2) = Some (HThunkHandle th2)" 
        using T by simp
      have EQ: "eq (HThunkHandle th1) (HThunkHandle th2)" using S E by simp

      then show ?thesis
      proof (cases rule: eq.cases)
        case (EqThunk h1' h2')
        then have FT: "forces_to (HThunkHandle th2) h2'"
          using force_some
          by auto
        then obtain n2' where "force_with_fuel n2' (HThunkHandle th2) = Some h2'"
          unfolding forces_to_def
          by auto
        then have EV1: "force_with_fuel (Suc n2') (HThunkHandle (create_thunk t2)) = Some h2'"
          using S T
          by auto

        from FT have EV2: "\<not> is_thunk h2'" using forces_to_def by auto

        have "\<exists>fuel. force_with_fuel fuel (HThunkHandle th1) = Some h1" 
          using FN1 by blast
        then have "forces_to (HThunkHandle th1) h1" using Suc(4) forces_to_def by auto
        then have "force (HThunkHandle th1) = Some h1" using force_unique by blast
        then have "h1 = h1'" using EqThunk by simp
        then have EV3: "eq h1 h2'" using EqThunk by simp

        then show ?thesis using EV1 EV2 EV3 by auto
      next
        case (EqThunkTree)

        have "force_with_fuel (Suc n) (HThunkHandle th1) = Some h1"
          using F1 HThunkHandle by auto
        then have "force_with_fuel (Suc n) (HThunkHandle (create_thunk (get_thunk_tree th1))) = Some h1"
          by auto
        then obtain n2' h2' where F2: "force_with_fuel (Suc n2') (HThunkHandle (create_thunk (get_thunk_tree th2))) = Some h2'"
                              and NT2: "\<not> is_thunk h2'" 
                              and EQ2: "eq h1 h2'"
          using Suc.IH[OF EqThunkTree _ Suc(4)]
          by auto

        have F2: "force_with_fuel (Suc n2') (HThunkHandle th2) = Some h2'"
          using F2
          by simp

        have F2: "force_with_fuel (Suc (Suc n2')) (HThunkHandle (create_thunk t2)) = Some h2'"
          using F2 T S Suc by auto

        then show ?thesis using F2 NT2 EQ2 by auto
      next
        case (EqSelf)
        then have F2: "force_with_fuel (Suc n) (HThunkHandle th2) = Some h1"
          using FN1 by simp
        then have F2: "force_with_fuel (Suc (Suc n)) (HThunkHandle (create_thunk t2)) = Some h1"
          using T S Suc by auto

        have "eq h1 h1" by (rule eq.EqSelf)
        then show ?thesis using F2 Suc(4) by auto
      qed
    qed
  qed
qed

lemma force_eq_tree:
  assumes "eq (HTreeHandle t1) (HTreeHandle t2)"
      and "force (HThunkHandle (create_thunk t1)) = Some r1"
    shows "\<exists>r2. force (HThunkHandle (create_thunk t2)) = Some r2 \<and> eq r1 r2"
proof -
  have "forces_to (HThunkHandle (create_thunk t1)) r1"
    using assms(2) force_some
    by blast
  then obtain n1 where F1: "force_with_fuel n1 (HThunkHandle (create_thunk t1)) = Some r1"
                   and NT1: "\<not> is_thunk r1"
    using forces_to_def
    by auto

  show ?thesis
  proof (cases n1)
    case 0
    then show ?thesis using F1 by auto
  next
    case (Suc n1')
    then have "force_with_fuel (Suc n1') (HThunkHandle (create_thunk t1)) = Some r1"
      using F1 by auto
    then obtain n2 h2 where F2: "force_with_fuel (Suc n2) (HThunkHandle (create_thunk t2)) = Some h2"
                        and NT2: "\<not> is_thunk h2"
                        and EQ2: "eq r1 h2"
      using force_with_fuel_eq[OF assms(1) _ NT1]
      by blast

    have "\<exists>n2. force_with_fuel n2 (HThunkHandle (create_thunk t2)) = Some h2" using F2 by blast
    then have "forces_to (HThunkHandle (create_thunk t2)) h2" using NT2 forces_to_def by blast
    then have "force (HThunkHandle (create_thunk t2)) = Some h2" using force_unique by auto
    then show ?thesis using EQ2 by blast
  qed
qed

lemma force_to_eq:
  assumes "eq h1 h2"
      and "force h1 = Some r1"
    shows "\<exists>r2. force h2 = Some r2 \<and> eq r1 r2"
  using assms(1)
proof (cases rule:eq.cases)
  case (EqBlob b1 b2)
  then have "force_with_fuel 0 h1 = Some(HBlobHandle b1)"
        and "force_with_fuel 0 h2 = Some(HBlobHandle b2)"
    by auto
  then have "forces_to h1 (HBlobHandle b1)"
        and "forces_to h2 (HBlobHandle b2)"
    using forces_to_def
    by auto
  then have F1: "force h1 = Some (HBlobHandle b1)"
        and F2: "force h2 = Some (HBlobHandle b2)"
    using force_unique
    by auto

  have "r1 = HBlobHandle b1" using F1 assms(2) by auto
  then show ?thesis using assms(1) F2 EqBlob by auto
next
  case (EqTree t1 t2)
  then have "force_with_fuel 0 h1 = Some (HTreeHandle t1)"
        and "force_with_fuel 0 h2 = Some (HTreeHandle t2)"
    by auto
  then have "forces_to h1 (HTreeHandle t1)"
        and "forces_to h2 (HTreeHandle t2) "
    using forces_to_def
    by auto
  then have F1: "force h1 = Some (HTreeHandle t1)"
        and F2: "force h2 = Some (HTreeHandle t2)"
    using force_unique
    by auto

  have "r1 = HTreeHandle t1" using F1 assms(2) by auto
  then show ?thesis using assms(1) F2 EqTree by auto
next
  case (EqThunk th1 r1' th2 r2')
  then have F: "force h2 = Some r2'"
        and E: "eq r1' r2'"
    by auto

  have "r1 = r1'" using EqThunk assms(2) by auto
  then have "force h2 = Some r2' \<and> eq r1 r2'" using F E by auto
  then show ?thesis by auto
next
  case (EqSelf)
  then have X: "force h2 = Some r1" using assms(2) by auto
  have "eq r1 r1" by (rule eq.EqSelf)
  then show ?thesis using X by auto
next
  case (EqThunkTree th1 th2)

  have F: "force (HThunkHandle (create_thunk (get_thunk_tree th1))) = Some r1"
    using assms(2) EqThunkTree by simp

  obtain r2 where "force (HThunkHandle (create_thunk (get_thunk_tree th2))) = Some r2 \<and> eq r1 r2"
    using force_eq_tree[OF EqThunkTree(3) F]  by auto 
  then have "force (HThunkHandle th2) = Some r2 \<and> eq r1 r2" by simp
  then show ?thesis using EqThunkTree(2) by simp
qed

inductive coupon_eq :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  CouponBlob:
  "(get_blob_data b1 = get_blob_data b2) \<Longrightarrow> coupon_eq (HBlobHandle b1) (HBlobHandle b2)"
| CouponTree:
  "list_all2 coupon_eq (get_tree_raw t1) (get_tree_raw t2) \<Longrightarrow>
   coupon_eq (HTreeHandle t1) (HTreeHandle t2)"
| CouponThunk:
  "force (HThunkHandle th1) = Some r1 \<Longrightarrow>
   force (HThunkHandle th2) = Some r2 \<Longrightarrow>
    coupon_eq r1 r2 \<Longrightarrow>
   coupon_eq (HThunkHandle th1) (HThunkHandle th2)"
| CouponThunkTree:
   "coupon_eq (HTreeHandle (get_thunk_tree th1)) (HTreeHandle (get_thunk_tree th2)) \<Longrightarrow>
    coupon_eq (HThunkHandle th1) (HThunkHandle th2)"
| CouponSelf:
   "coupon_eq h h"
| CouponThunkForce:
   "coupon_eq (HThunkHandle th1) (HThunkHandle th2) \<Longrightarrow>
    force (HThunkHandle th1) = Some r1 \<Longrightarrow>
    force (HThunkHandle th2) = Some r2 \<Longrightarrow>
    coupon_eq r1 r2"

theorem coupon_legit:
  assumes "coupon_eq h1 h2"
  shows "eq h1 h2"
  using assms
proof (induction rule : coupon_eq.induct)
  case (CouponBlob b1 b2)
  then show ?case by (rule eq.EqBlob)
next
  case (CouponTree t1 t2)
  then have "list_all2 (\<lambda>x1 x2. eq x1 x2) (get_tree_raw t1) (get_tree_raw t2)"
    by (induction rule: list_all2_induct) simp_all
  then show ?case by (rule eq.EqTree)
next
  case (CouponThunk th1 r1 th2 r2)
  show ?case using CouponThunk(1) CouponThunk(2) CouponThunk(4) by (rule eq.EqThunk)
next
  case (CouponThunkTree th1 th2)
  show ?case using CouponThunkTree(2) by (rule eq.EqThunkTree)
next
  case (CouponSelf h)
  show ?case by (rule eq.EqSelf)
next
  case (CouponThunkForce th1 th2 r1 r2)
  then obtain r2' where "force (HThunkHandle th2) = Some r2'"
                    and "eq r1 r2'"
    using force_to_eq[OF CouponThunkForce(4)] CouponThunkForce.hyps(2)
    by auto
  then have "eq r1 r2" using force_unique CouponThunkForce(3) by auto
  then show ?case by auto
qed

end

