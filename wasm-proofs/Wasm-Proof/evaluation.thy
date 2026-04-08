theory evaluation
  imports apply_tree
begin

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

lemma eval_with_fuel_not_encode:
  assumes "eval_with_fuel n h = Some r"
  shows "(\<exists>b. r = HBlobHandle b) \<or> (\<exists>t. r = HTreeHandle t) \<or> (\<exists>th. r = HThunkHandle th)"
  using assms
proof (induction n arbitrary: h)
  case 0 
  then show ?thesis by (cases h) auto
next
  case (Suc n')
  then show ?case
  proof (cases h)
    case (HBlobHandle b) then show ?thesis using Suc by auto
  next
    case (HThunkHandle t) then show ?thesis using Suc by auto
  next
    case (HTreeHandle t) 
    then show ?thesis 
      using Suc
      by (metis (lifting) eval_with_fuel.simps(2) handle.simps(18) not_None_eq option.simps(4,5))
  next
    case (HEncodeHandle e)
    then show ?thesis
      by (metis (no_types, lifting) Suc.IH Suc.prems eval_with_fuel.simps(2) handle.simps(20) option.case_eq_if option.distinct(1))
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

lemma evals_to_tree_to_exists:
  assumes "list_all (\<lambda>x. \<exists>y. evals_to x y) xs"
  shows "\<exists>fuel ys. eval_list_with_fuel fuel xs = Some ys"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then obtain fuel ys where T: "eval_list_with_fuel fuel xs = Some ys" by auto

  obtain fuel' y where "eval_with_fuel fuel' x = Some y"
    using Cons.prems evals_to_def by auto

  let ?f = "max fuel fuel'"
  let ?f1 = "?f - fuel"
  let ?f2 = "?f - fuel'"

  have "eval_list_with_fuel (fuel + ?f1) xs = Some ys" using eval_list_with_fuel_padding[OF T] .
  then have T: "list_all2 (\<lambda>x y. eval_with_fuel ?f x = Some y) xs ys" 
    using eval_list_to_list_all by auto
  have "eval_with_fuel (fuel' + ?f2) x = Some y"  
    using \<open>eval_with_fuel fuel' x = Some y\<close> fuel_padding by blast
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

lemma evals_to_not_encode:
  assumes "evals_to h r"
  shows "(\<exists>b. r = HBlobHandle b) \<or> (\<exists>t. r = HTreeHandle t) \<or> (\<exists>th. r = HThunkHandle th)"
  using assms eval_with_fuel_not_encode
  unfolding evals_to_def
  by auto

lemma forces_to_implies_evals_to:
  assumes "forces_to (get_encode_thunk e) (HBlobHandle b)"
  shows "evals_to (HEncodeHandle e) (HBlobHandle b)"
  by (metis (lifting) add_cancel_right_left assms eval_with_fuel.simps(1,2) eval_with_fuel_padding evals_to_def execute_with_fuel.simps forces_to_def
      handle.simps(17,20) option.simps(5))

lemma evals_to_implies_forces_to:
  assumes "evals_to (HEncodeHandle e) (HBlobHandle b)"
  shows "\<exists>e'. forces_to (get_encode_thunk e) e' \<and> evals_to e' (HBlobHandle b)"
proof -
  obtain f where "eval_with_fuel f (HEncodeHandle e) =Some (HBlobHandle b)"
  using assms evals_to_def by blast
  then obtain f' e' where "execute_with_fuel f' e = Some e'"
   and "eval_with_fuel f' e' = Some (HBlobHandle b)"
   and "Suc f' = f"
    by (smt (verit, del_insts) eval_with_fuel.elims handle.simps(20) is_none_code(2) option.case_eq_if option.distinct(1) option.split_sel_asm)
  then show ?thesis
    using evals_to_def executes_to_def
    using forces_to_def by auto
qed

lemma evals_to_implies_forces_to_tree:
  assumes "evals_to (HEncodeHandle e) (HTreeHandle t)"
  shows "\<exists>e'. forces_to (get_encode_thunk e) e' \<and> evals_to e' (HTreeHandle t)"
proof -
  obtain f where "eval_with_fuel f (HEncodeHandle e) =Some (HTreeHandle t)"
  using assms evals_to_def by blast
  then obtain f' e' where "execute_with_fuel f' e = Some e'"
   and "eval_with_fuel f' e' = Some (HTreeHandle t)"
   and "Suc f' = f"
    by (smt (verit, del_insts) eval_with_fuel.elims handle.simps(20) is_none_code(2) option.case_eq_if option.distinct(1) option.split_sel_asm)
  then show ?thesis
    using evals_to_def executes_to_def
    using forces_to_def by auto
qed

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

lemma eval_not_encode:
  assumes "eval h = Some r"
  shows "(\<exists>b. r = HBlobHandle b) \<or> (\<exists>t. r = HTreeHandle t) \<or> (\<exists>th. r = HThunkHandle th)"
  using evals_to_not_encode eval_some[OF assms]
  by auto

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

lemma eval_entry_to_eval_tree:
  assumes "list_all2 (\<lambda>x y. evals_to x y) xs ys"
  shows "eval (HTreeHandle (create_tree xs)) = Some (HTreeHandle (create_tree ys))"
proof -
  obtain f where "eval_list_with_fuel f xs = Some ys"
    using assms evals_to_tree_to by auto
  then have "eval_with_fuel (Suc f) (HTreeHandle (create_tree xs)) = Some (HTreeHandle (create_tree ys))"
    by auto
  then show ?thesis 
    using evals_to_def eval_unique by blast
qed

lemma eval_tree_to_eval_entry:
  assumes "eval (HTreeHandle t) = Some r"
  shows "r = HTreeHandle (create_tree (map (\<lambda>x. the (eval x)) (get_tree_raw t))) \<and> (list_all (\<lambda>x. \<exists>t'. eval x = Some t') (get_tree_raw t))"
proof -
  have "\<exists>f. eval_with_fuel f (HTreeHandle t) = Some r"
    using assms
    using eval_some evals_to_def by blast
  then have "\<exists>t' f. eval_tree_with_fuel f t = Some t' \<and> r = (HTreeHandle t')"
    by (metis (lifting) eval_with_fuel.elims handle.simps(18) option.case_eq_if option.distinct(1) option.exhaust_sel option.inject)
  then obtain t' f where 1: "eval_tree_with_fuel f t = Some t'"
                     and 2: "r = HTreeHandle t'"
    by blast
  then obtain ys where 3: "eval_list_with_fuel f (get_tree_raw t) = Some ys"
    by fastforce  
  then have 4: "list_all2 (\<lambda>x y. eval x = Some y) (get_tree_raw t) ys"
    using eval_list_to_list_all
    by (smt (verit, ccfv_SIG) eval_unique evals_to_def list_all2_mono)
  then have "(map (\<lambda>x. the (eval x))) (get_tree_raw t) = ys"
  proof (induction rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons x y xs ys)
    then show ?case by simp
  qed
  then have 5: "r = HTreeHandle (create_tree ((map (\<lambda>x. the (eval x))) (get_tree_raw t)))"
    using 1 2 3
    by auto

  have "(list_all (\<lambda>x. \<exists>t'. eval x = Some t') (get_tree_raw t))"
    using 4
    by (simp add: list_all2_conv_all_nth list_all_length)
  then show ?thesis using 5 by auto
qed

inductive value_tree :: "TreeHandle \<Rightarrow> bool"
and value_handle :: "handle \<Rightarrow> bool"
where
  tree[intro]:
    "list_all value_handle (get_tree_raw t) \<Longrightarrow> value_tree t"
| blob_handle[intro]:
    "value_handle (HBlobHandle b)"
| tree_handle[intro]:
    "value_tree t \<Longrightarrow> value_handle (HTreeHandle t)"
| thunk_handle[intro]:
    "value_handle (HThunkHandle t)"

lemma eval_with_fuel_to_value_handle:
  "eval_with_fuel f h = Some r \<Longrightarrow> value_handle r"
proof (induction f arbitrary: h r)
  case 0
  then show ?case by (cases "h") auto
next
  case (Suc n)

  show ?case
  proof (cases "h") 
    case (HBlobHandle) then show ?thesis using Suc by auto
  next
    case (HThunkHandle) then show ?thesis using Suc by auto
  next
    case (HEncodeHandle e)
    then obtain res where "execute_with_fuel n e = Some res"
                      and rdef: "eval_with_fuel n res = Some r"
      using Suc
      by (metis (no_types, lifting) eval_with_fuel.simps(2) handle.simps(20) not_None_eq option.simps(4,5))
    then show ?thesis using Suc.IH by auto
  next
    case (HTreeHandle t)
    then obtain ys where "eval_list_with_fuel n (get_tree_raw t) = Some ys"
                     and rdef: "r = HTreeHandle (create_tree ys)"
      using Suc
      by (metis (lifting) eval_tree_with_fuel.simps eval_with_fuel.simps(2) handle.simps(18) not_None_eq option.simps(4,5))
    then have "list_all2 (\<lambda>x y. eval_with_fuel n x = Some y) (get_tree_raw t) ys"
      using eval_list_to_list_all
      by auto
    then have "list_all value_handle ys"
      using Suc.IH 
      by (metis (mono_tags, lifting) list_all2_conv_all_nth list_all_length)
    then have "value_handle r"
      using rdef
      by (simp add: value_tree_value_handle.tree value_tree_value_handle.tree_handle)
    then show ?thesis by auto
  qed
qed

lemma eval_to_value_handle:
  "eval h = Some r \<Longrightarrow> value_handle r"
  using eval_with_fuel_to_value_handle
  using eval_some evals_to_def by blast

lemma value_handle_not_encode:
  assumes "value_handle h"
  shows "\<not> (\<exists>e. h = HEncodeHandle e)"
  using assms value_handle.simps by blast

lemma value_tree_to_sametypedness:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes X_tree_implies_all_child: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
    list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_preserve_value_handle: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> 
         \<not> (\<exists>e. h1 = HEncodeHandle e) \<Longrightarrow>
         \<not> (\<exists>e. h2 = HEncodeHandle e) \<Longrightarrow>
         ((\<exists>b. h1 = HBlobHandle b) \<longleftrightarrow> (\<exists>b. h2 = HBlobHandle b))
       \<and> ((\<exists>t. h1 = HTreeHandle t) \<longleftrightarrow> (\<exists>t. h2 = HTreeHandle t))
       \<and> ((\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th))"
  assumes VT1: "value_tree t1"
  shows "\<forall>t2. (X (HTreeHandle t1) (HTreeHandle t2) \<longrightarrow>
         value_tree t2 \<longrightarrow>
         same_typed_tree t1 t2)"
  using VT1
proof (induction t1 rule: wfp_induct[OF wfp_tree_child])
  case (1 x)
  show ?case
  proof
    fix t2
    show "X (HTreeHandle x) (HTreeHandle t2) \<longrightarrow>
          value_tree t2 \<longrightarrow> same_typed_tree x t2"
    proof (intro impI)
      assume Xtree: "X (HTreeHandle x) (HTreeHandle t2)"
      assume VT2: "value_tree t2"
      show "same_typed_tree x t2"
      proof -
        have L: "length (get_tree_raw x) = length (get_tree_raw t2)"
          using X_tree_implies_all_child Xtree list_all2_lengthD by blast

        moreover have "\<forall>i < length (get_tree_raw x). same_typed_handle (get_tree_raw x ! i) (get_tree_raw t2 ! i)"
        proof
          fix i
          show "i < length (get_tree_raw x) \<longrightarrow> same_typed_handle (get_tree_raw x ! i) (get_tree_raw t2 ! i)"
          proof (intro impI)
            assume assm: "i < length (get_tree_raw x)"

            let ?lhs = "get_tree_raw x ! i"
            let ?rhs = "get_tree_raw t2 ! i"

            have EQLR: "X ?lhs ?rhs"
              using Xtree L assm
              using X_tree_implies_all_child list_all2_nthD by blast

            have VHL: "value_handle ?lhs"
              using "1.prems"
              by (simp add: assm list_all_length value_tree.simps)

            have VHR: "value_handle ?rhs"
              using VT2 L assm
              by (simp add: assm list_all_length value_tree.simps)

            from VHL
            show "same_typed_handle ?lhs ?rhs"
            proof (cases ?lhs)
              case (blob_handle b)
              then show ?thesis
                using X_preserve_value_handle EQLR VHL VHR value_handle_not_encode
                by (metis same_typed_handle.simps)
            next
              case (thunk_handle t)
              then show ?thesis
                using X_preserve_value_handle EQLR VHL VHR value_handle_not_encode
                by (metis same_typed_handle.simps)
            next
              case (tree_handle t)
              then obtain t' where tree_handle': "?rhs = HTreeHandle t'"
                using X_preserve_value_handle EQLR VHL VHR value_handle_not_encode
                by (metis)

              have "tree_child t x" 
                by (metis assm local.tree_handle(1) nth_mem tree_child_def)
              moreover have "value_tree t" using VHL
                using local.tree_handle(2) by auto
              moreover have "X (HTreeHandle t) (HTreeHandle t')"
                using tree_handle tree_handle' EQLR by auto
              moreover have "value_tree t'"
                using VHR tree_handle' value_handle.simps by auto
              ultimately have "same_typed_tree t t'"
                using "1.IH" by blast

              then show ?thesis
                using local.tree_handle(1) tree_handle' by auto
            qed
          qed
        qed

        ultimately show ?thesis
          using list_all2_all_nthI
          by blast
      qed
    qed
  qed
qed

lemma value_handle_to_sametypedness:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes X_tree_implies_all_child: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
    list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_preserve_value_handle: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> 
         \<not> (\<exists>e. h1 = HEncodeHandle e) \<Longrightarrow>
         \<not> (\<exists>e. h2 = HEncodeHandle e) \<Longrightarrow>
         ((\<exists>b. h1 = HBlobHandle b) \<longleftrightarrow> (\<exists>b. h2 = HBlobHandle b))
       \<and> ((\<exists>t. h1 = HTreeHandle t) \<longleftrightarrow> (\<exists>t. h2 = HTreeHandle t))
       \<and> ((\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th))"
  assumes relX: "X h1 h2" 
      and VH1: "value_handle h1"
      and VH2: "value_handle h2"
    shows "same_typed_handle h1 h2"
  using VH1
proof (cases h1)
  case (blob_handle b)
  then show ?thesis
    using VH2 X_preserve_value_handle assms(3) value_handle_not_encode by blast
next
  case (thunk_handle th)
  then show ?thesis
    using VH2 X_preserve_value_handle assms(3) value_handle_not_encode by blast
next
  case (tree_handle t1)
  then obtain t2 where tree_handle': "h2 = HTreeHandle t2"
    using VH2 X_preserve_value_handle assms(3) value_handle_not_encode by blast

  have "same_typed_tree t1 t2"
    using relX tree_handle tree_handle' assms value_tree_to_sametypedness
    using value_handle.simps by fastforce

  then show ?thesis
    using tree_handle tree_handle'
    by blast
qed

lemma eq_tree_eval_fuel_n:
 fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes create_tree_cong: "\<And>xs ys. list_all2 X xs ys
                             \<Longrightarrow> X (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
  assumes X_tree_implies_all_children: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow>
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
      using X_tree_implies_all_children E by auto

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
    then have RHS: "X (HTreeHandle v1) (HTreeHandle ?v2)"
      using \<open>eval_tree_with_fuel n t1 = Some v1\<close> eval_raw1 by fastforce

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
      using X_tree_implies_all_children E by auto

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
      using create_tree_cong[of "get_tree_raw(create_tree xs')" "get_tree_raw v2"]
      using \<open>eval_tree_with_fuel n t2 = Some v2\<close> eval_raw2 by auto
    then show "(\<exists>v1. evals_tree_to t1 v1 \<and> X (HTreeHandle v1) (HTreeHandle v2))" using LHS by auto
  qed

  then show ?thesis using LHS RHS by blast
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
  assumes create_thunk_cong: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_tree_implies_all_children: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_preserve_thunk: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th))"
  assumes X_preserve_blob_or_encode: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<longrightarrow> (\<exists>b. h2 = HBlobHandle b))"
  assumes X_preserve_blob_or_encode_rev: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h2 = HBlobHandle b) \<longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)))"
  assumes X_preserve_tree_or_encode: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h2 = HTreeHandle b)))"
  assumes X_preserve_tree_or_encode_rev: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h2 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)))"
  assumes X_encode_eval: "\<And>e h2. 
         X (HEncodeHandle e) h2 \<Longrightarrow> 
         \<not> (\<exists>e2. h2 = HEncodeHandle e2) \<Longrightarrow>
         executes_to e h2"
  assumes X_encode_reasons: "\<And>e1 e2. 
         X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> 
         X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or>
         rel_opt X (execute e1) (execute e2)"
  assumes X_encode_eval_rev_does_not_exist: "\<And>e h1. 
         X h1 (HEncodeHandle e) \<Longrightarrow> 
         \<not> (\<exists>e1. h1 = HEncodeHandle e1) \<Longrightarrow>
         False"
  assumes X_blob_complete: "\<And>b1 b2.
         get_blob_data b1 = get_blob_data b2 \<Longrightarrow> X (HBlobHandle b1) (HBlobHandle b2)"
  assumes X_thunk_reasons: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow> (
     X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  assumes X_self: "\<And>h. X h h"
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
        using 0 T1 X_preserve_thunk by blast
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
      then obtain t1 where T1: "h1 = HThunkHandle t1"
        using 0 T2 X_preserve_thunk by blast
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
        using 0 T2 X_preserve_thunk by blast
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

      from X_preserve_blob_or_encode 0 HBlobHandle
      have "(\<exists>b. h2 = HBlobHandle b)" by blast
      then obtain b2 where B2: "h2 = HBlobHandle b2" by auto
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

      from X_preserve_blob_or_encode_rev 0 HBlobHandle
      have "(\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)" by blast
      then show ?thesis
      proof
        assume "\<exists>b1. h1 = HBlobHandle b1"
        then obtain b1 where B1: "h1 = HBlobHandle b1" by auto
        then have "eval_with_fuel 0 h1 = Some h1" by auto
        then have E1: "evals_to h1 h1" using evals_to_def by blast

        have "v2 = h2" using ASSM HBlobHandle by auto
        then have "X h1 v2" using 0 by auto
        then show ?thesis using E1 by auto
      next
        assume "\<exists>e. h1 = HEncodeHandle e"
        then obtain e where E: "h1 = HEncodeHandle e" by auto
        then have "executes_to e h2"
          using "0" HBlobHandle X_encode_eval by blast
        then have "evals_to h1 h2"
          by (simp add: E HBlobHandle executes_to_def forces_to_def forces_to_implies_evals_to)
        moreover have "X h2 h2"
          by (simp add: HBlobHandle X_blob_complete)
        ultimately show ?thesis
          using ASSM HBlobHandle by auto
      qed
    next
      case (HThunkHandle t2)
      then have "\<exists>t1. h1 = HThunkHandle t1"
        using P2 by blast
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

  have X_preserve_value_handle: "\<And>h1 h2. 
       X h1 h2 \<Longrightarrow> 
       \<not> (\<exists>e. h1 = HEncodeHandle e) \<Longrightarrow>
       \<not> (\<exists>e. h2 = HEncodeHandle e) \<Longrightarrow>
       ((\<exists>b. h1 = HBlobHandle b) \<longleftrightarrow> (\<exists>b. h2 = HBlobHandle b))
     \<and> ((\<exists>t. h1 = HTreeHandle t) \<longleftrightarrow> (\<exists>t. h2 = HTreeHandle t))
     \<and> ((\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th))"
  by (meson X_preserve_blob_or_encode X_preserve_blob_or_encode_rev X_preserve_thunk X_preserve_tree_or_encode X_preserve_tree_or_encode_rev)

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
          then obtain tree' where EVTree1: "eval_tree_with_fuel f' (get_thunk_tree t1) = Some tree'"
                            and   Apply1: "apply_tree tree' = Some v1"
            by (cases "eval_tree_with_fuel f' (get_thunk_tree t1)") auto
          then obtain tree2' where EVTree2: "evals_tree_to (get_thunk_tree t2) tree2'"
                             and  EQApplyTree: "X (HTreeHandle tree') (HTreeHandle tree2')"
            using eq_tree_eval_fuel_n[OF create_tree_cong X_tree_implies_all_children eval_cong_f' EQTREE] 
            by auto

          have VH1: "value_handle (HTreeHandle tree')"
            using EVTree1 eval_with_fuel_to_value_handle
            by (metis eval_with_fuel.simps(2) handle.simps(18) option.simps(5))

          have VH2: "value_handle (HTreeHandle tree2')"
            using EVTree2 eval_with_fuel_to_value_handle
            by (metis eval_with_fuel.simps(2) evals_tree_to_def handle.simps(18) option.simps(5))


          have sametyped: "same_typed_tree tree' tree2'"
            using VH1 VH2 EQApplyTree X_tree_implies_all_children X_preserve_value_handle value_tree_to_sametypedness
            using value_handle.simps by force


          have "rel_opt X (apply_tree tree') (apply_tree tree2') \<and> rel_opt same_typed_handle (apply_tree tree') (apply_tree tree2')"
            using apply_tree_X sametyped EQApplyTree get_blob_data_cong get_tree_size_cong get_tree_data_cong create_blob_cong create_tree_cong create_encode_cong create_thunk_cong
            by blast

          then obtain v2 where Apply2: "apply_tree tree2' = Some v2" 
                           and EQOUT: "X v1 v2"
                           and SAMETYPEOUT: "same_typed_handle v1 v2"
            using Apply1
            using rel_opt.elims(1) by force

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
        using ASSM X_preserve_thunk by blast
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
          then obtain tree2' where EVTree2: "eval_tree_with_fuel f' (get_thunk_tree t2) = Some tree2'"
                             and Apply2: "apply_tree tree2' = Some v2"
            by (cases "eval_tree_with_fuel f' (get_thunk_tree t2)") auto
          then obtain tree' where EVTree1: "evals_tree_to (get_thunk_tree t1) tree'" 
                            and   EQApplyTree: "X (HTreeHandle tree') (HTreeHandle tree2')"
            using eq_tree_eval_fuel_n[OF create_tree_cong X_tree_implies_all_children eval_cong_f' EQTREE]
            by auto

          have VH2: "value_handle (HTreeHandle tree2')"
            using EVTree2 eval_with_fuel_to_value_handle
            by (metis eval_with_fuel.simps(2) handle.simps(18) option.simps(5))

          have VH1: "value_handle (HTreeHandle tree')"
            using EVTree1 eval_with_fuel_to_value_handle
            by (metis eval_with_fuel.simps(2) evals_tree_to_def handle.simps(18) option.simps(5))

          have sametyped: "same_typed_tree tree' tree2'"
            using VH1 VH2 EQApplyTree X_tree_implies_all_children X_preserve_value_handle value_tree_to_sametypedness
            using value_handle.simps by force

          have "rel_opt X (apply_tree tree') (apply_tree tree2') \<and> rel_opt same_typed_handle (apply_tree tree') (apply_tree tree2')"
            using apply_tree_X sametyped EQApplyTree get_blob_data_cong get_tree_size_cong get_tree_data_cong create_blob_cong create_tree_cong create_encode_cong create_thunk_cong
            by blast

          then obtain v1 where Apply1: "apply_tree tree' = Some v1" 
                           and EQOUT: "X v1 v2"
                           and SAMETYPEOUT: "same_typed_handle v1 v2"
            using Apply2
            using rel_opt.elims(1) by force

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

            have "(\<exists>b. t2' = HBlobHandle b)"
            using EQOUT HBlobHandle X_preserve_blob_or_encode by blast
            then obtain b2 where Blob2: "t2' = HBlobHandle b2" by auto
            then obtain fuel where "think_with_fuel fuel t2 = Some t2'" using T2 thinks_to_def by auto
            then show ?thesis
                by (metis (no_types, lifting) Blob2 EQOUT EQV1 force_with_fuel.simps(2) forces_to_def handle.simps(17) option.simps(5))
          next
            case (HTreeHandle t1)
            then have EQV1: "v1 = t1'" using F1 T1 by auto

            have assms: "(\<exists>b. t2' = HTreeHandle b)"
            using EQOUT HTreeHandle X_preserve_tree_or_encode by blast
            then obtain b2 where Tree2: "t2' = HTreeHandle b2" by auto
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
            then show ?thesis
            proof (cases "\<exists>e2. t2' = HEncodeHandle e2")
              case False
              then have "executes_to e1 t2'"
                using EQOUT HEncodeHandle X_encode_eval by blast
              then have T2'TYPE: "(\<exists>b2. t2' = HBlobHandle b2) \<or> (\<exists>tree. t2' = HTreeHandle tree)"
                by (metis execute_with_fuel.simps executes_to_def force_with_fuel_not_thunk)

              have "executes_to e1 v1"
                using F1 HEncodeHandle T1 executes_to_def by auto
              then have "v1 = t2'"
                by (simp add: \<open>executes_to e1 t2'\<close> executes_to_deterministic)
              then have "X v1 t2'"
                using X_self by auto

              moreover have "forces_to t2 t2'"
                using T2'TYPE
                by (metis (no_types, lifting) T2 force_with_fuel.simps(2) forces_to_def handle.simps(17,18) option.simps(5) thinks_to_def)
              ultimately show ?thesis by blast
            next
              case True
              then obtain e2 where "t2' = HEncodeHandle e2" by auto
              then have "X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or> rel_opt X (execute e1) (execute e2)" 
                using EQOUT HEncodeHandle X_encode_reasons by blast

              then show ?thesis
              proof
                assume "rel_opt X (execute e1) (execute e2)"

                moreover have "execute e1 = Some v1"
                  using F1 HEncodeHandle T1 execute_unique executes_to_def by auto
                ultimately obtain v2 where "execute e2 = Some v2" and "X v1 v2" 
                  by (metis execute_deterministic option.distinct(1) rel_opt.elims(2))
           
                obtain fuel where Fuel1: "think_with_fuel fuel t2 = Some t2'"
                  using T2 thinks_to_def by blast
                obtain fuel' where Fuel2: "force_with_fuel fuel' (get_encode_thunk e2) = Some v2"
                  using \<open>execute e2 = Some v2\<close> execute_some executes_to_def by force
           
                let ?f = "max fuel fuel'"
                let ?f1 = "?f - fuel"
                let ?f2 = "?f - fuel'"
           
                have "think_with_fuel (fuel + ?f1) t2 = Some t2'"
                  using Fuel1 think_with_fuel_padding by blast
                moreover have "force_with_fuel (fuel' + ?f2) (get_encode_thunk e2) = Some v2"
                  using Fuel2 force_with_fuel_padding by blast
                ultimately have "force_with_fuel (Suc ?f) t2 = Some v2"
                  by (simp add: \<open>t2' = handle.HEncodeHandle e2\<close>)
                then have "forces_to t2 v2"
                  using forces_to_def by blast
           
                then show ?thesis
                  using \<open>X v1 v2\<close> by blast
              next
                assume rel_thunk: "X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"

                have "force_with_fuel f' (get_encode_thunk e1) = Some v1"
                  using F1 HEncodeHandle T1 by auto
                then obtain v2 where "forces_to (get_encode_thunk e2) v2 \<and> X v1 v2"
                  using rel_thunk relevant_IH_force by blast
                then obtain fuel where FUEL1: "force_with_fuel fuel (get_encode_thunk e2) = Some v2"
                  using forces_to_def by blast

                obtain fuel' where FUEL2: "think_with_fuel fuel' t2 = Some t2'"
                  using T2 thinks_to_def by blast

                have "think_with_fuel (max fuel fuel') t2 = Some t2'"
                  by (metis FUEL2 add.commute nat_minus_add_max think_with_fuel_padding)
                moreover have "force_with_fuel (max fuel fuel') (get_encode_thunk e2) = Some v2"
                  by (metis FUEL1 fuel_padding less_eqE max.cobounded1)
                ultimately have "force_with_fuel (Suc (max fuel fuel')) t2 = Some v2"
                  by (simp add: \<open>t2' = handle.HEncodeHandle e2\<close>)
                then show ?thesis
                  using \<open>forces_to (get_encode_thunk e2) v2 \<and> X v1 v2\<close> forces_to_def by blast
              qed
            qed
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
            then have "(\<exists>b1. t1' = HBlobHandle b1) \<or> (\<exists>e1. t1' = HEncodeHandle e1)"
              using EQOUT HBlobHandle X_preserve_blob_or_encode_rev by blast
            then show ?thesis
            proof
              assume "\<exists>b1. t1' = HBlobHandle b1"
              then obtain b1 where Blob1: "t1' = HBlobHandle b1" by auto
              then obtain fuel where "think_with_fuel fuel t1 = Some t1'" 
                using T1 thinks_to_def by auto
              then have "force_with_fuel (Suc fuel) t1 = Some t1'" using Blob1 by auto
              then show ?thesis using forces_to_def EQOUT EQV by blast
            next
              assume "\<exists>e1. t1' = HEncodeHandle e1"
              then obtain e1 where "t1' = HEncodeHandle e1" by auto
              then have "executes_to e1 t2'"
                using EQOUT HBlobHandle X_encode_eval by blast
              then have "forces_to t1 t2'"
                by (smt (verit, best) T1 \<open>t1' = handle.HEncodeHandle e1\<close>
                    add.commute execute_with_fuel.simps executes_to_def
                    force_with_fuel.simps(2) forces_to_def fuel_padding
                    handle.simps(20) option.simps(5) thinks_to_def)
              moreover have "X t2' v2" using EQV X_self by auto
              ultimately show ?thesis by blast
            qed
          next
            case (HTreeHandle t2)
            then have EQV: "v2 = t2'" using F2 T2 by auto
            then have "(\<exists>b1. t1' = HTreeHandle b1) \<or> (\<exists>e1. t1' = HEncodeHandle e1)" 
              using EQOUT HTreeHandle X_preserve_tree_or_encode_rev by blast
            then show ?thesis
            proof
              assume "\<exists>b1. t1' = HTreeHandle b1"
              then obtain b1 where Tree1: "t1' = HTreeHandle b1" by auto
              then obtain fuel where "think_with_fuel fuel t1 = Some t1'" 
              using T1 thinks_to_def by auto
              then have "force_with_fuel (Suc fuel) t1 = Some t1'" using Tree1 by auto
              then show ?thesis using forces_to_def EQOUT EQV by blast
            next
              assume "\<exists>e1. t1' = HEncodeHandle e1"
              then obtain e1 where "t1' = HEncodeHandle e1" by auto
              then have "executes_to e1 t2'"
                using EQOUT HTreeHandle X_encode_eval by blast
              then have "forces_to t1 t2'"
                by (smt (verit, best) T1 \<open>t1' = handle.HEncodeHandle e1\<close>
                    add.commute execute_with_fuel.simps executes_to_def
                    force_with_fuel.simps(2) forces_to_def fuel_padding
                    handle.simps(20) option.simps(5) thinks_to_def)
              moreover have "X t2' v2" using EQV X_self by auto
              ultimately show ?thesis by blast
            qed
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
            then have "\<exists>e1. t1' = HEncodeHandle e1" 
              using EQOUT X_encode_eval_rev_does_not_exist by blast
            then obtain e1 where Encode1: "t1' = HEncodeHandle e1" by auto
            then have "X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or> rel_opt X (execute e1) (execute e2)"
              using EQOUT HEncodeHandle X_encode_reasons by blast
            then show ?thesis
            proof
              assume "rel_opt X (execute e1) (execute e2) "
              moreover have "execute e2 = Some v2"
                using F2 HEncodeHandle T2 execute_unique executes_to_def by auto

              ultimately obtain v1 where "execute e1 = Some v1" and "X v1 v2"
                by (metis execute_deterministic option.distinct(1) rel_opt.elims(2))
            
              obtain fuel where Fuel1: "think_with_fuel fuel t1 = Some t1'"
                using T1 thinks_to_def by blast
              obtain fuel' where Fuel2: "force_with_fuel fuel' (get_encode_thunk e1) = Some v1"
                using \<open>execute e1 = Some v1\<close> execute_some executes_to_def by force
            
              let ?f = "max fuel fuel'"
              let ?f1 = "?f - fuel"
              let ?f2 = "?f - fuel'"
            
              have "think_with_fuel (fuel + ?f1) t1 = Some t1'"
                using Fuel1 think_with_fuel_padding by blast
              moreover have "force_with_fuel (fuel' + ?f2) (get_encode_thunk e1) = Some v1"
                using Fuel2 force_with_fuel_padding by blast
              ultimately have "force_with_fuel (Suc ?f) t1 = Some v1"
                by (simp add: \<open>t1' = handle.HEncodeHandle e1\<close>)
              then have "forces_to t1 v1"
                using forces_to_def by blast
            
              then show ?thesis
                using \<open>X v1 v2\<close> by blast
            next
              assume "X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
              moreover have "force_with_fuel f' (get_encode_thunk e2) = Some v2"
                using F2 HEncodeHandle T2 by auto
              ultimately obtain v1 where "forces_to (get_encode_thunk e1) v1 \<and> X v1 v2"
                using relevant_IH_force by blast
              then obtain fuel where FUEL1: "force_with_fuel fuel (get_encode_thunk e1) = Some v1"
                using forces_to_def by blast

              obtain fuel' where "think_with_fuel fuel' t1 = Some t1'"
                using T1 thinks_to_def by blast
              then have "think_with_fuel (max fuel fuel') t1 = Some t1'"
                by (metis add.commute nat_minus_add_max think_with_fuel_padding)
              moreover have "force_with_fuel (max fuel fuel') (get_encode_thunk e1) = Some v1"
                by (metis FUEL1 fuel_padding max.cobounded1
                    ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
              ultimately have "force_with_fuel (Suc (max fuel fuel')) t1 = Some v1"
                by (simp add: Encode1)

              then show ?thesis
                using \<open>forces_to (get_encode_thunk e1) v1 \<and> X v1 v2\<close> forces_to_def by blast
            qed
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
        then obtain b2 where "h2 = HBlobHandle b2"
          using EQH X_preserve_blob_or_encode by blast
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
        then obtain t2 where T2: "h2 = HTreeHandle t2" 
          using EQH X_preserve_tree_or_encode by blast
        then have EQTREE: "X (HTreeHandle t1) (HTreeHandle t2)" using EQH HTreeHandle by auto

        obtain tree' where "eval_tree_with_fuel f' t1 = Some tree'"
                     and   V1: "v1 = HTreeHandle tree'"
          using ASSM HTreeHandle by (cases "eval_tree_with_fuel f' t1") auto
        then obtain tree2' where "evals_tree_to t2 tree2'"
                           and   EQTREE: "X (HTreeHandle tree') (HTreeHandle tree2')"
          using eq_tree_eval_fuel_n[OF create_tree_cong X_tree_implies_all_children eval_cong_f' EQTREE]
          by auto
        then obtain fuel where "eval_tree_with_fuel fuel t2 = Some tree2'" 
          using evals_tree_to_def by auto
        then have "eval_with_fuel (Suc fuel) h2 = Some (HTreeHandle tree2')" using T2 by auto
        then have "evals_to h2 (HTreeHandle tree2')" using evals_to_def by blast
        then show ?thesis using V1 EQTREE by auto
      next
        case (HEncodeHandle e1)
        then show ?thesis
        proof (cases "\<exists>e2. h2 = HEncodeHandle e2")
          case True
          then obtain e2 where E2: "h2 = HEncodeHandle e2" by auto
          then have "X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or> rel_opt X (execute e1) (execute e2)"
            using EQH HEncodeHandle X_encode_reasons by blast
          then show ?thesis
          proof
            assume rel_execute: "rel_opt X (execute e1) (execute e2)"

            obtain h1' where "execute_with_fuel f' e1 = Some h1'"
                       and   Eval1: "eval_with_fuel f' h1' = Some v1"
              using ASSM HEncodeHandle
              by (cases "execute_with_fuel f' e1") auto
            then obtain h2' where "executes_to e2 h2'"
                            and   EQ': "X h1' h2'"
              using rel_execute
              by (metis execute_some execute_unique executes_to_def option.distinct(1) option.inject rel_opt.elims(2))
        
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
          next
            assume rel_thunk: "X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
            obtain h1' where "execute_with_fuel f' e1 = Some h1'"
                       and   Eval1: "eval_with_fuel f' h1' = Some v1"
              using ASSM HEncodeHandle
              by (cases "execute_with_fuel f' e1") auto
            then have "force_with_fuel f' (get_encode_thunk e1) = Some h1'" by simp
            then obtain h2' where FUEL1: "forces_to (get_encode_thunk e2) h2' \<and> X h1' h2'"
              using rel_thunk relevant_IH_force by force
            then obtain v2 where FUEL2: "evals_to h2' v2"
              using Eval1 eval_cong_f' by force

            obtain fuel1 where "force_with_fuel fuel1 (get_encode_thunk e2) = Some h2'" 
              using forces_to_def FUEL1 by blast
            moreover obtain fuel2 where "eval_with_fuel fuel2 h2' = Some v2"
              using evals_to_def FUEL2 by blast
            ultimately have "force_with_fuel (max fuel1 fuel2) (get_encode_thunk e2) = Some h2'"
                        and "eval_with_fuel (max fuel1 fuel2) h2' = Some v2"
              by (metis fuel_padding max.cobounded1 ordered_cancel_comm_monoid_diff_class.add_diff_inverse, 
                  metis \<open>eval_with_fuel fuel2 h2' = Some v2\<close> add.commute fuel_padding nat_minus_add_max)
            then have "eval_with_fuel (Suc (max fuel1 fuel2)) h2 = Some v2"
              by (simp add: E2)

            then show ?thesis
              using Eval1 FUEL1 FUEL2 eval_cong_f' evals_to_def evals_to_deterministic by blast
          qed
        next
          case False
          then have "executes_to e1 h2"
            using EQH HEncodeHandle X_encode_eval by blast
          then have "execute_with_fuel f' e1 = Some h2 \<and> eval_with_fuel f' h2 = Some v1"
            by (smt (verit, best) ASSM HEncodeHandle eval_with_fuel.simps(2) execute_unique executes_to_def handle.simps(20) is_none_code(2) option.simps(4,5) option.split_sel_asm)
          then have "evals_to h2 v1"
            using evals_to_def by blast
          then show ?thesis
            using X_self by blast
        qed
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
        then have "(\<exists>b1. h1 = HBlobHandle b1) \<or> (\<exists>e1. h1 = HEncodeHandle e1)"
          using EQH X_preserve_blob_or_encode_rev by blast
        then show ?thesis
        proof
          assume "\<exists>b1. h1 = HBlobHandle b1"
          then obtain b1 where "h1 = HBlobHandle b1" by auto
          then have "eval_with_fuel 0 h1 = Some h1" by auto
          then have "evals_to h1 h1" using evals_to_def by blast
          then show ?thesis using ASSM EQH HBlobHandle by auto
        next
          assume "\<exists>e1. h1 = HEncodeHandle e1"
          then obtain e1 where "h1 = HEncodeHandle e1" by auto
          then have "evals_to h1 h2"
            using EQH HBlobHandle X_encode_eval executes_to_def forces_to_def forces_to_implies_evals_to by auto
          then show ?thesis
            using ASSM HBlobHandle X_self by auto
        qed
      next
        case (HTreeHandle t2)
        then have "(\<exists>t1. h1 = HTreeHandle t1) \<or> (\<exists>e1. h1 = HEncodeHandle e1)"
          using EQH X_preserve_tree_or_encode_rev by blast
        then show ?thesis
        proof 
          assume "\<exists>t1. h1 = HTreeHandle t1"
          then obtain t1 where T1: "h1 = HTreeHandle t1" by auto
          then have EQTREE: "X (HTreeHandle t1) (HTreeHandle t2)" using EQH HTreeHandle by auto

          obtain list2' where "eval_list_with_fuel f' (get_tree_raw t2) = Some list2'"
                        and   V2: "v2 = HTreeHandle (create_tree list2')"
            using ASSM HTreeHandle 
            apply (cases "eval_tree_with_fuel f' t2") 
            apply simp
            by (metis (lifting) eval_tree_with_fuel.simps eval_with_fuel.simps(2) handle.simps(18) not_None_eq option.simps(4,5))

          then have "list_all2 (\<lambda>x y. eval_with_fuel f' x = Some y) (get_tree_raw t2) list2'"
            using eval_list_to_list_all
            by simp

          moreover have "list_all2 (\<lambda>x y. X x y) (get_tree_raw t1) (get_tree_raw t2)"
            using EQTREE X_tree_implies_all_children by auto

          then have A: "list_all2 (\<lambda>x y. (\<exists>v1. evals_to x v1 \<and> X v1 y)) (get_tree_raw t1) list2'"
            by (smt (verit, best) calculation eval_cong_f' list_all2_trans)

          then have "list_all (\<lambda>x. (\<exists>v1. evals_to x v1)) (get_tree_raw t1)"
            using list_all2_lengthD list_all2_nthD2 list_all_length by fastforce

          then obtain list1' fuel' where "eval_list_with_fuel fuel' (get_tree_raw t1) = Some list1'"
            using evals_to_tree_to_exists
            by presburger

          then have "list_all2 (\<lambda>x y.  evals_to x y) (get_tree_raw t1) list1'"
            by (metis (mono_tags, lifting) eval_list_to_list_all evals_to_def
                list_all2_mono)

          then have "list_all2 (\<lambda>x y. X x y) list1' list2'"
            using A
            by (smt (verit, best) evals_to_deterministic list_all2_conv_all_nth)

          then have "X (HTreeHandle (create_tree list1')) (HTreeHandle (create_tree list2'))"
            using create_tree_cong by blast

          have "evals_to h1 (HTreeHandle (create_tree list1'))"
            by (metis T1 \<open>eval_list_with_fuel fuel' (get_tree_raw t1) = Some list1'\<close>
                eval_tree_with_fuel.simps eval_with_fuel.simps(2) evals_to_def
                handle.simps(18) option.simps(5))

          then show ?thesis
            using V2
              \<open>X (HTreeHandle (create_tree list1')) (HTreeHandle (create_tree list2'))\<close>
            by blast
        next
          assume "\<exists>e1. h1 = HEncodeHandle e1"
          then obtain e1 where "h1 = HEncodeHandle e1" by auto
          then have "executes_to e1 h2"
            using EQH HTreeHandle X_encode_eval by blast
          then obtain fuel where "execute_with_fuel fuel e1 = Some h2"
            using executes_to_def by blast

          let ?f = "max fuel (Suc f')"
          let ?f1 = "?f - fuel"
          let ?f2 = "?f - (Suc f')"

          have "execute_with_fuel (fuel + ?f1) e1 = Some h2"
            using \<open>execute_with_fuel fuel e1 = Some h2\<close> execute_with_fuel_padding
            by presburger
          moreover have "eval_with_fuel ((Suc f') + ?f2) h2 = Some v2"
            using ASSM fuel_padding by blast
          ultimately have "eval_with_fuel ?f h2 = Some v2"
            by auto

          then show ?thesis
            by (metis (no_types, lifting) X_self
                \<open>execute_with_fuel (fuel + (max fuel (Suc f') - fuel)) e1 = Some h2\<close>
                \<open>h1 = handle.HEncodeHandle e1\<close> add.commute diff_add_inverse
                eval_with_fuel.simps(2) evals_to_def handle.simps(20) max.commute
                nat_minus_add_max option.simps(5))
        qed
      next
        case (HThunkHandle t2)
        then have "\<exists>t1. h1 = HThunkHandle t1"
          using EQH relevant_IH_force by blast
        then obtain t1 where "h1 = HThunkHandle t1" by auto
        then have "eval_with_fuel 0 h1 = Some h1" by auto
        then have "evals_to h1 h1" using evals_to_def by blast
        then show ?thesis using ASSM EQH HThunkHandle by auto
      next
        case (HEncodeHandle e2)
        then have "\<exists>e1. h1 = HEncodeHandle e1"
          using EQH X_encode_eval_rev_does_not_exist by blast
        then obtain e1 where E1: "h1 = HEncodeHandle e1" by auto
        then have EQENCODE: "X (HEncodeHandle e1) (HEncodeHandle e2)" 
          using EQH HEncodeHandle by auto
        then have rel: "X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or> rel_opt X (execute e1) (execute e2)"
          using X_encode_reasons by blast

        obtain h2' where Execute2: "execute_with_fuel f' e2 = Some h2'"
                   and   Eval2: "eval_with_fuel f' h2' = Some v2"
          using ASSM HEncodeHandle
          by (cases "execute_with_fuel f' e2") auto

        from rel
        have "\<exists>h1'. executes_to e1 h1' \<and> X h1' h2'"
        proof
          assume rel: "rel_opt X (execute e1) (execute e2)"
          then show ?thesis
            by (metis Execute2 execute_some execute_unique executes_to_def option.distinct(1) option.sel rel_opt.elims(2))
        next
          assume rel_thunk: "X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2))"
          have "force_with_fuel f' (get_encode_thunk e2) = Some h2'" using Execute2 by simp
          then obtain h1' where "forces_to (get_encode_thunk e1) h1' \<and> X h1' h2'"
            using rel_thunk relevant_IH_force by force
          moreover then have "executes_to e1 h1'"
            by (simp add: executes_to_def forces_to_def)
          ultimately show ?thesis
            by blast
        qed
        then obtain h1' where "executes_to e1 h1'"
                          and   EQ': "X h1' h2'"
          by auto
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
  assumes create_thunk_cong: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_tree_implies_all_children: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_preserve_thunk: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th))"
  assumes X_preserve_blob_or_encode: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<longrightarrow> (\<exists>b. h2 = HBlobHandle b))"
  assumes X_preserve_blob_or_encode_rev: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h2 = HBlobHandle b) \<longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)))"
  assumes X_preserve_tree_or_encode: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h2 = HTreeHandle b)))"
  assumes X_preserve_tree_or_encode_rev: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h2 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)))"
  assumes X_encode_eval: "\<And>e h2. 
         X (HEncodeHandle e) h2 \<Longrightarrow> 
         \<not> (\<exists>e2. h2 = HEncodeHandle e2) \<Longrightarrow>
         executes_to e h2"
  assumes X_encode_reasons: "\<And>e1 e2. 
         X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> 
         X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or>
         rel_opt X (execute e1) (execute e2)"
  assumes X_encode_eval_rev_does_not_exist: "\<And>e h1. 
         X h1 (HEncodeHandle e) \<Longrightarrow> 
         \<not> (\<exists>e1. h1 = HEncodeHandle e1) \<Longrightarrow>
         False"
  assumes X_blob_complete: "\<And>b1 b2.
         get_blob_data b1 = get_blob_data b2 \<Longrightarrow> X (HBlobHandle b1) (HBlobHandle b2)"
  assumes X_thunk_reasons: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow> (
     X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  assumes X_self: "\<And>h. X h h"
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
           create_blob_cong create_tree_cong create_encode_cong create_thunk_cong X_tree_implies_all_children
           X_preserve_thunk X_preserve_blob_or_encode X_preserve_blob_or_encode_rev X_preserve_tree_or_encode X_preserve_tree_or_encode_rev
           X_encode_eval X_encode_reasons X_encode_eval_rev_does_not_exist X_blob_complete X_thunk_reasons X_self
           ] by auto

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
  assumes create_thunk_cong: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_tree_implies_all_children: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_preserve_thunk: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th))"
  assumes X_preserve_blob_or_encode: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<longrightarrow> (\<exists>b. h2 = HBlobHandle b))"
  assumes X_preserve_blob_or_encode_rev: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h2 = HBlobHandle b) \<longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)))"
  assumes X_preserve_tree_or_encode: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h2 = HTreeHandle b)))"
  assumes X_preserve_tree_or_encode_rev: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h2 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)))"
  assumes X_encode_eval: "\<And>e h2. 
         X (HEncodeHandle e) h2 \<Longrightarrow> 
         \<not> (\<exists>e2. h2 = HEncodeHandle e2) \<Longrightarrow>
         executes_to e h2"
  assumes X_encode_reasons: "\<And>e1 e2. 
         X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> 
         X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or>
         rel_opt X (execute e1) (execute e2)"
  assumes X_encode_eval_rev_does_not_exist: "\<And>e h1. 
         X h1 (HEncodeHandle e) \<Longrightarrow> 
         \<not> (\<exists>e1. h1 = HEncodeHandle e1) \<Longrightarrow>
         False"
  assumes X_blob_complete: "\<And>b1 b2.
         get_blob_data b1 = get_blob_data b2 \<Longrightarrow> X (HBlobHandle b1) (HBlobHandle b2)"
  assumes X_thunk_reasons: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow> (
     X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  assumes X_self: "\<And>h. X h h"
  assumes E: "X h1 h2"
  shows "rel_opt X (eval h1) (eval h2)"
proof -
 have eval_all_n: "\<And>h1 h2 n. X h1 h2 \<Longrightarrow>
        (\<forall>v1. eval_with_fuel n h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
      \<and>
        (\<forall>v2. eval_with_fuel n h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))"
      using eq_forces_to_induct[OF get_blob_data_cong get_tree_size_cong get_tree_data_cong
           create_blob_cong create_tree_cong create_encode_cong create_thunk_cong X_tree_implies_all_children
           X_preserve_thunk X_preserve_blob_or_encode X_preserve_blob_or_encode_rev X_preserve_tree_or_encode X_preserve_tree_or_encode_rev
           X_encode_eval X_encode_reasons X_encode_eval_rev_does_not_exist X_blob_complete X_thunk_reasons X_self
           ] by auto

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
  assumes create_thunk_cong: "\<And> t1 t2. X (HTreeHandle t1) (HTreeHandle t2) 
           \<Longrightarrow> X (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
  assumes X_tree_implies_all_children: "\<And>t1 t2. X (HTreeHandle t1) (HTreeHandle t2) \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_preserve_thunk: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th))"
  assumes X_preserve_blob_or_encode: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<longrightarrow> (\<exists>b. h2 = HBlobHandle b))"
  assumes X_preserve_blob_or_encode_rev: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h2 = HBlobHandle b) \<longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)))"
  assumes X_preserve_tree_or_encode: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h2 = HTreeHandle b)))"
  assumes X_preserve_tree_or_encode_rev: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> ((\<exists>b. h2 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)))"
  assumes X_encode_eval: "\<And>e h2. 
         X (HEncodeHandle e) h2 \<Longrightarrow> 
         \<not> (\<exists>e2. h2 = HEncodeHandle e2) \<Longrightarrow>
         executes_to e h2"
  assumes X_encode_reasons: "\<And>e1 e2. 
         X (HEncodeHandle e1) (HEncodeHandle e2) \<Longrightarrow> 
         X (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or>
         rel_opt X (execute e1) (execute e2)"
  assumes X_encode_eval_rev_does_not_exist: "\<And>e h1. 
         X h1 (HEncodeHandle e) \<Longrightarrow> 
         \<not> (\<exists>e1. h1 = HEncodeHandle e1) \<Longrightarrow>
         False"
  assumes X_blob_complete: "\<And>b1 b2.
         get_blob_data b1 = get_blob_data b2 \<Longrightarrow> X (HBlobHandle b1) (HBlobHandle b2)"
  assumes X_thunk_reasons: "\<And>t1 t2. X (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow> (
     X (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> X r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2))) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  assumes X_self: "\<And>h. X h h"
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
           create_blob_cong create_tree_cong create_encode_cong create_thunk_cong X_tree_implies_all_children
           X_preserve_thunk X_preserve_blob_or_encode X_preserve_blob_or_encode_rev X_preserve_tree_or_encode X_preserve_tree_or_encode_rev
           X_encode_eval X_encode_reasons X_encode_eval_rev_does_not_exist X_blob_complete X_thunk_reasons X_self
           ] by auto

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

end