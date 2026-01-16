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

inductive step :: "op \<Rightarrow> state \<Rightarrow> step_result \<Rightarrow> bool"
  where
    StepGetBlobData:
    "i < length (hs s) \<Longrightarrow> hs s ! i = HBlobHandle b \<Longrightarrow>
    step (OGetBlobData i) s (Continue (dpush s (get_blob_data b)))"

| StepGetTreeData:
  "i < length (hs s) \<Longrightarrow> 
     hs s ! i = HTreeHandle t \<Longrightarrow>
     j < get_tree_size t \<Longrightarrow>
    step (OGetTreeData i j) s (Continue (hpush s (get_tree_data t j)))"

| StepCreateBlob:
  "i < length (ds s) \<Longrightarrow> 
    step (OCreateBlob i) s (Continue (hpush s (HBlobHandle (create_blob (ds s ! i)))))"

| StepCreateThunk:
  "i < length (hs s) \<Longrightarrow> hs s ! i = HTreeHandle t \<Longrightarrow>
    step (OCreateThunk i) s (Continue (hpush s (HThunkHandle (create_thunk t))))"

| StepCreateTree:
  "\<forall>i\<in>set xs. i < length (hs s) \<Longrightarrow>
     hlist = map (\<lambda>i. hs s ! i) xs \<Longrightarrow>
     step (OCreateTree xs) s (Continue (hpush s (HTreeHandle (create_tree hlist) )))" 

| StepReturn:
  "i < length (hs s) \<Longrightarrow> r = hs s ! i \<Longrightarrow>
    step (OReturn i) s (Return (hs s ! i))"

| StepRunInternal:
  "step ORunInternal s (Continue (run_internal s))"

fun step_fun :: "op \<Rightarrow> state \<Rightarrow> step_result option" where
  "step_fun (OGetBlobData i) s = 
      (if i < length (hs s) then
         (case (hs s ! i) of
          HBlobHandle b \<Rightarrow> Some (Continue (dpush s (get_blob_data b)))
        | _ \<Rightarrow> None)
       else None)"
| "step_fun (OGetTreeData i j) s =
      (if i < length (hs s) then
         (case (hs s ! i) of
          HTreeHandle t \<Rightarrow> (if (j < get_tree_size t) 
                            then Some (Continue (hpush s (get_tree_data t j))) 
                            else None)
          | _ \<Rightarrow> None)
       else None)"
| "step_fun (OCreateBlob i) s =
      (if i < length (ds s) then
         Some (Continue (hpush s (HBlobHandle (create_blob (ds s ! i)))))
       else None)"
| "step_fun (OCreateThunk i) s =
      (if i < length (hs s) then
         case (hs s ! i) of
         HTreeHandle t \<Rightarrow> Some (Continue (hpush s (HThunkHandle (create_thunk t))))
         | _ \<Rightarrow> None
       else None)"
| "step_fun (OCreateTree xs) s =
      (if (\<forall>i\<in>set xs. i < length (hs s)) then
        (let hlist = map (\<lambda>i. hs s ! i) xs in
         Some (Continue (hpush s (HTreeHandle (create_tree hlist)))))
      else None)"
| "step_fun (OReturn i) s =
      (if i < length (hs s) then Some (Return (hs s ! i)) else None)"
| "step_fun (ORunInternal) s = Some (Continue (run_internal s))"

inductive exec :: "userprog \<Rightarrow> state \<Rightarrow> handle \<Rightarrow> bool"
  where
    ExecReturn:
    "step i s (Return r) \<Longrightarrow> exec (i # xs) s r"
  | ExecStep:
    "step i s (Continue s') \<Longrightarrow> exec xs s' r \<Longrightarrow> exec (i # xs) s r"

fun exec_fun :: "userprog \<Rightarrow> state \<Rightarrow> handle option"
  where
    "exec_fun [] s = None"
  | "exec_fun (i # xs) s =
   (case (step_fun i s) of
   None \<Rightarrow> None
   | Some (Return r) \<Rightarrow> Some r
   | Some (Continue s') \<Rightarrow> exec_fun xs s')"

(* Thunk evaluation *)

definition state_init :: "ThunkHandle \<Rightarrow> state" where
  "state_init thunk \<equiv> \<lparr> hs = [HTreeHandle (get_thunk_tree thunk)], ds = [] \<rparr>"

definition apply_thunk :: "ThunkHandle \<Rightarrow> handle option" where
  "apply_thunk th \<equiv> exec_fun (get_prog (get_thunk_tree th)) (state_init th)" 

fun is_thunk :: "handle \<Rightarrow> bool" where
  "is_thunk (HThunkHandle _) = True"
| "is_thunk _ = False"

inductive force_with_fuel :: "nat \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> bool" where
  Done:
  "\<not> is_thunk h \<Longrightarrow> force_with_fuel n h h"
| Step:
  "h = HThunkHandle thunk \<Longrightarrow>
     Some h1 = apply_thunk thunk \<Longrightarrow>
     force_with_fuel n h1 h2 \<Longrightarrow>
     force_with_fuel (Suc n) h h2"

fun force_with_fuel_fun :: "nat \<Rightarrow> handle \<Rightarrow> handle option" where
  "force_with_fuel_fun n h =
     (case h of
        HThunkHandle th \<Rightarrow>
          (case n of
             0 \<Rightarrow> None
           | Suc n' \<Rightarrow>
               (case apply_thunk th of
                  None \<Rightarrow> None
                | Some h1 \<Rightarrow> force_with_fuel_fun n' h1))
       | _ \<Rightarrow> Some h)"

definition forces_to :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  "forces_to h h1 \<equiv> (\<exists>fuel. force_with_fuel_fun fuel h = Some h1 \<and> \<not> is_thunk h1)"

(* Determinism *)

lemma step_deterministic:
  assumes "step op s o1" "step op s o2"
  shows   "o1 = o2"
  using assms
proof (induction arbitrary: o2 rule: step.induct)
  case (StepGetBlobData i s b)
  from StepGetBlobData.prems(1) show ?case
    by (cases rule: step.cases; auto simp: StepGetBlobData(2))
next
  case (StepGetTreeData i s b j)
  from StepGetTreeData.prems(1) show ?case
    by (cases rule: step.cases; auto simp: StepGetTreeData(2))
next
  case (StepCreateBlob i s)
  from StepCreateBlob.prems(1) show ?case
    by (cases rule: step.cases; auto)
next
  case (StepCreateThunk i s t)
  from StepCreateThunk.prems(1) show ?case
    by (cases rule: step.cases; auto simp: StepCreateThunk(2))
next
  case (StepCreateTree xs s hs)
  from StepCreateTree.prems(1) show ?case
    by (cases rule: step.cases; auto simp: StepCreateTree(2))
next
  case (StepReturn i s r)
  from StepReturn.prems(1) show ?case
    by (cases rule: step.cases; auto)
next
  case (StepRunInternal s)
  from StepRunInternal.prems(1) show ?case
    by (cases rule: step.cases; auto)
qed

lemma exec_deterministic:
  assumes "exec p s o1" "exec p s o2"
  shows   "o1 = o2"
  using assms
proof (induction arbitrary: o2 rule: exec.induct)
  case (ExecReturn i s r1 xs)
  then show ?case
    by (cases rule: exec.cases[OF ExecReturn.prems(1)])
      (auto dest: step_deterministic)
next
  case (ExecStep i s s' xs r)
  have H1: "step i s (Continue s')" using ExecStep.hyps(1) by assumption
  have H2: "exec xs s' r" using ExecStep.hyps(2) by assumption
  have E2: "exec (i # xs) s o2" using ExecStep.prems by assumption

  then show ?case
  proof (cases rule: exec.cases[OF E2])
    case (1 i s r xs)
    have Hret2: "step i s (Return r)" using 1(4) .
    have Hret1: "step i s (Continue s')" using 1(1) 1(2) H1 by simp
    have "Continue s' = Return r" using step_deterministic[OF Hret1 Hret2] by simp
    thus ?thesis by simp
  next
    case (2 ia sa s'a xsa ra)
    have Hstep1: "step i s (Continue s'a)" using 2(1) 2(2) 2(4) by simp
    have S: "s' = s'a" using step_deterministic[OF H1 Hstep1] by simp
    have "exec xs s' o2" using 2(5) 2(1) 2(3) S by auto
    thus ?thesis using ExecStep.IH by auto
  qed
qed

lemma force_with_fuel_deterministic:
  assumes A: "force_with_fuel n h r1"
    and B: "force_with_fuel n h r2"
  shows "r1 = r2"
  using A B
proof (induction arbitrary: r2 rule: force_with_fuel.induct)
  case (Done h n)
  then show ?case
    by (cases rule: force_with_fuel.cases[OF Done.prems]) auto
next
  case (Step h thunk h1 n h2)
  then show ?case
  proof (cases rule: force_with_fuel.cases[OF Step.prems])
    case (1 ha na)
    have A: "\<not> is_thunk h" using 1(4) 1(2) by auto
    have B: "is_thunk h" using local.Step(1) by auto
    thus ?thesis using A B by auto
  next
    case (2 ha thunka h1a na h2a)
    have "thunka = thunk" using 2(2) 2(4) Step.hyps(1) by auto
    then have "apply_thunk thunka = apply_thunk thunk" by auto
    then have "Some h1a = Some h1" using 2(5) Step.hyps(2) by simp
    then have "h1a = h1" by simp
    then have "force_with_fuel n h1 h2a" using 2(1) 2(6) by auto
    thus ?thesis using Step.IH 2(3) by auto
  qed
qed

lemma evaluate_with_fuel_pad:
  assumes "force_with_fuel f h nf" and "\<not> is_thunk nf"
  shows "force_with_fuel (f + k) h nf"
  using assms
  by (induction rule: force_with_fuel.induct) (simp_all add: force_with_fuel.intros)

lemma force_with_fuel_fun_pad:
  assumes "force_with_fuel_fun f h = Some h1" and "\<not> is_thunk h1"
  shows "force_with_fuel_fun (f + k) h = Some h1"
  using assms
proof (induction f arbitrary: h)
  case 0 then show ?case by (cases h) auto
next
  case (Suc f')
  then show ?case 
  proof (cases h) 
    case (HBlobHandle b)
    then have "force_with_fuel_fun (Suc f') h = Some h" by simp_all
    then have "h1 = h" using Suc.prems(1) by auto
    then show ?thesis using HBlobHandle by auto
  next
    case (HTreeHandle t)
    then have "force_with_fuel_fun (Suc f') h = Some h" by simp_all
    then have "h1 = h" using Suc.prems(1) by auto
    then show ?thesis using HTreeHandle by auto
  next
    case (HThunkHandle th)
    from Suc.prems(1) HThunkHandle obtain h2 where
      A: "apply_thunk th = Some h2"
      and B: "force_with_fuel_fun f' h2 = Some h1" by (simp split: option.splits)

    have "force_with_fuel_fun (f' + k) h2 = Some h1" using B Suc.IH Suc.prems(2) by auto
    then show ?thesis using HThunkHandle A by simp_all
  qed
qed

lemma forces_to_deterministic:
  assumes "forces_to h h1" and "forces_to h h2"
  shows "h1 = h2"
  using assms
proof -
  obtain f1 where A: "force_with_fuel_fun f1 h = Some h1" and NT1: "\<not> is_thunk h1"
    using assms(1) unfolding forces_to_def by auto
  obtain f2 where B: "force_with_fuel_fun f2 h = Some h2" and NT2: "\<not> is_thunk h2"
    using assms(2) unfolding forces_to_def by auto
  let ?F = "max f1 f2"
  let ?k1 = "?F - f1"
  let ?k2 = "?F - f2"
  have "force_with_fuel_fun (f1 + ?k1) h = Some h1"
    using force_with_fuel_fun_pad[OF A NT1] .
  then have AA: "force_with_fuel_fun ?F h = Some h1" by simp
  have "force_with_fuel_fun (f2 + ?k2) h = Some h2" 
    using force_with_fuel_fun_pad[OF B NT2] .
  then have BB: "force_with_fuel_fun ?F h = Some h2" by simp
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
  "get_thunk_tree (create_thunk t) = t"

(* Coupon rules *)

inductive coupon_eq :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  Storage:
  "get_blob_data h1 = get_blob_data h2 \<Longrightarrow> coupon_eq (HBlobHandle h1) (HBlobHandle h2)"
| Tree:
  "get_tree_size t1 = get_tree_size t2 \<Longrightarrow>
     (\<forall> i < get_tree_size t1. coupon_eq (get_tree_data t1 i) (get_tree_data t2 i)) \<Longrightarrow>
     coupon_eq (HTreeHandle t1) (HTreeHandle t2)"
| ThunkByTree:
  "coupon_eq (HTreeHandle (get_thunk_tree th1)) (HTreeHandle (get_thunk_tree th2)) \<Longrightarrow>
     coupon_eq (HThunkHandle th1) (HThunkHandle th2)"
| ThunkByEvaluate:
  "forces_to (HThunkHandle th1) h \<Longrightarrow>
     forces_to (HThunkHandle th2) h \<Longrightarrow>
     coupon_eq (HThunkHandle th1) (HThunkHandle th2)"

(* Semantic rules *)

coinductive sem_eq :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  SemBlob:
  "(get_blob_data b1 = get_blob_data b2) \<Longrightarrow> sem_eq (HBlobHandle b1) (HBlobHandle b2)"
| SemTree:
  "list_all2 sem_eq (get_tree_raw t1) (get_tree_raw t2) \<Longrightarrow>
   sem_eq (HTreeHandle t1) (HTreeHandle t2)"
| SemThunk:
  "(force (HThunkHandle th1) = Some r1 \<Longrightarrow>
    force (HThunkHandle th2) = Some r2 \<Longrightarrow>
     sem_eq r1 r2) \<Longrightarrow>
   sem_eq (HThunkHandle th1) (HThunkHandle th2)"

coinductive sem_eq_k :: "nat \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> bool" where
  SemBlob:
  "(get_blob_data b1 = get_blob_data b2) \<Longrightarrow> sem_eq_k k (HBlobHandle b1) (HBlobHandle b2)"
| SemTree:
  "list_all2 sem_eq (get_tree_raw t1) (get_tree_raw t2) \<Longrightarrow>
   sem_eq_k k (HTreeHandle t1) (HTreeHandle t2)"
| SemThunk0:
  "sem_eq_k 0 (HThunkHandle th1) (HThunkHandle th2)"
| SemThunkk:
  "(force (HThunkHandle th1) = Some r1 \<Longrightarrow>
    force (HThunkHandle th2) = Some r2 \<Longrightarrow>
     sem_eq_k k r1 r2) \<Longrightarrow>
   sem_eq_k (Suc k) (HThunkHandle th1) (HThunkHandle th2)"

lemma sem_eq_same_type:
  assumes "sem_eq h1 h2"
  shows "get_type h1 = get_type h2"
  using assms
  by (cases rule: sem_eq.cases) auto

(* sem_eq preserved by thunk application *)

(* 1. Useful lemmas and definitions *)
definition relate_opt :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> bool" where
  "relate_opt P x y \<equiv>
     (case x of None \<Rightarrow> y = None 
     | Some a \<Rightarrow> (\<exists>b. y = Some b \<and> P a b))"

definition sem_eq_state :: "state \<Rightarrow> state \<Rightarrow> bool" where
  "sem_eq_state s1 s2 \<equiv>
     list_all2 (\<lambda>h1 h2. sem_eq h1 h2) (hs s1) (hs s2) \<and> ds s1 = ds s2"

lemma list_all2_append:
  assumes "list_all2 P xs ys"
    and "P x y"
  shows   "list_all2 P (xs @ [x]) (ys @ [y])"
  using assms
  by (induction arbitrary: x y rule: list_all2_induct) simp_all

lemma list_all2_nthD:
  assumes "list_all2 R xs ys" "i < length xs"
  shows "i < length ys \<and> R (xs ! i) (ys ! i)"
  using assms
  by (auto simp: list_all2_conv_all_nth)

lemma sem_eq_state_hpush:
  assumes "sem_eq_state s1 s2" and "sem_eq h1 h2"
  shows "sem_eq_state (hpush s1 h1) (hpush s2 h2)"
  using assms unfolding sem_eq_state_def hpush_def
  by (auto simp: list_all2_append)

lemma sem_eq_dpush:
  assumes "sem_eq_state s1 s2" and "d1 = d2"
  shows "sem_eq_state (dpush s1 d1) (dpush s2 d2)"
  using assms unfolding sem_eq_state_def dpush_def by auto

lemma sem_eq_same_kind:
  assumes "sem_eq h1 h2"
  shows
    "(\<exists>b1 b2. h1 = HBlobHandle b1 \<and> h2 = HBlobHandle b2) \<or>
     (\<exists>t1 t2. h1 = HTreeHandle t1 \<and> h2 = HTreeHandle t2) \<or>
     (\<exists>k1 k2. h1 = HThunkHandle k1 \<and> h2 = HThunkHandle k2)"
  using assms
  by (cases rule: sem_eq.cases) auto

definition rel_step_result :: "step_result \<Rightarrow> step_result \<Rightarrow> bool" where
  "rel_step_result r1 r2 \<equiv> 
   (case (r1, r2) of
     (Continue s1, Continue s2) \<Rightarrow> sem_eq_state s1 s2
   | (Return r1, Return r2) \<Rightarrow> sem_eq r1 r2
   | (_, _) \<Rightarrow> False)"

(* 2. API functions respect sem_eq *)
lemma get_blob_data_sem_eq:
  assumes "sem_eq (HBlobHandle b1) (HBlobHandle b2)"
  shows "get_blob_data b1 = get_blob_data b2"
  using assms
  by (cases rule: sem_eq.cases) auto

lemma sem_eq_tree_children:
  assumes "sem_eq (HTreeHandle t1) (HTreeHandle t2)"
  shows "list_all2 sem_eq (get_tree_raw t1) (get_tree_raw t2)"
  using assms
  by (cases rule: sem_eq.cases) auto

lemma get_tree_size_sem_eq:
  assumes "sem_eq (HTreeHandle t1) (HTreeHandle t2)"
  shows   "get_tree_size t1 = get_tree_size t2"
  using sem_eq_tree_children[OF assms]
  by (simp add: get_tree_size_def list_all2_lengthD)

lemma get_tree_data_sem_eq:
  assumes "sem_eq (HTreeHandle t1) (HTreeHandle t2)" and "i < get_tree_size t1"
  shows "sem_eq (get_tree_data t1 i) (get_tree_data t2 i)"
proof -
  have A: "i < length (get_tree_raw t1)" using assms(2) get_tree_size_def by auto
  have "list_all2 sem_eq (get_tree_raw t1) (get_tree_raw t2)" 
    using sem_eq_tree_children[OF assms(1)] .
  then have "sem_eq ((get_tree_raw t1) ! i) ((get_tree_raw t2) ! i)" 
    using list_all2_nthD[OF _ A] by auto
  then show ?thesis by (simp add: get_tree_data_def[symmetric]) 
qed

lemma create_blob_sem_eq:
  assumes "d1 = d2"
  shows "sem_eq (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
proof -
  have "get_blob_data (create_blob d1) = get_blob_data (create_blob d2)" 
    using assms by simp_all
  then show ?thesis by (rule sem_eq.SemBlob) 
qed

lemma create_tree_sem_eq:
  assumes "list_all2 sem_eq xs ys"
  shows "sem_eq (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
proof -
  have "list_all2 sem_eq (get_tree_raw (create_tree xs)) (get_tree_raw (create_tree ys))"
    using assms by simp_all
  then show ?thesis by (rule sem_eq.SemTree)
qed





