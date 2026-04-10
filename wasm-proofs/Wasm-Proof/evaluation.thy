theory evaluation
  imports apply_tree digest slice identify
begin

fun is_thunk :: "handle \<Rightarrow> bool" where
  "is_thunk (Thunk _) = True"
| "is_thunk _ = False"

(* infixl takes a number for the precedence level of the symbol. It decides how strong the binding power is. (e.g. whether a |>> b + c is understood as (a |>> b) + c or a |>> (b + c) 

precedence level of =\<and>equiv is 2 *)

abbreviation obind (infixl "|>>" 55) where
  "x |>> f \<equiv> (case x of
               Some x' \<Rightarrow> f x'
             | None \<Rightarrow> None)"

abbreviation omap (infixl "<$>" 55) where
  "x <$> f \<equiv> map_option f x"

fun lift_data :: "Data \<Rightarrow> Data"
  where
  "lift_data (Ref (TreeRef t)) = (Object (TreeObj t))" 
| "lift_data (Ref (BlobRef b)) = (Object (BlobObj b))"
| "lift_data (Object v) = (Object v)"

fun lift :: "handle \<Rightarrow> handle"
  where
  "lift (Data d) = (Data (lift_data d))"
| "lift (Thunk t) = (Thunk t)"
| "lift (Encode e) = (Encode e)"

fun lower_data :: "Data \<Rightarrow> Data"
  where
  "lower_data (Ref x) = Ref x"
| "lower_data (Object (TreeObj t)) = (Ref (TreeRef t))"
| "lower_data (Object (BlobObj b)) = (Ref (BlobRef  b))"

fun lower :: "handle \<Rightarrow> handle"
  where
  "lower (Data d) = (Data (lower_data d))"
| "lower (Thunk t) = (Thunk t)"
| "lower (Encode e) = (Encode e)"

fun get_thunk_inner :: "Thunk \<Rightarrow> handle"
  where
  "get_thunk_inner (Application t) = HTreeObj t"
| "get_thunk_inner (Identification d) = Data d"
| "get_thunk_inner (Selection t) = HTreeObj t"
| "get_thunk_inner (Digestion t) = HTreeObj t"

fun think_with_fuel :: "nat \<Rightarrow> Thunk \<Rightarrow> handle option"
and force_with_fuel :: "nat \<Rightarrow> Thunk \<Rightarrow> handle option"
and execute_with_fuel :: "nat \<Rightarrow> Encode \<Rightarrow> handle option"
and eval_with_fuel :: "nat \<Rightarrow> handle \<Rightarrow> handle option"
and eval_tree_with_fuel :: "nat \<Rightarrow> TreeName \<Rightarrow> TreeName option"
and eval_list_with_fuel :: "nat \<Rightarrow> handle list \<Rightarrow> handle list option"
where
  "think_with_fuel 0 thunk = None"
| "think_with_fuel (Suc n) thunk = 
   (case thunk of
   Application tree \<Rightarrow> (eval_tree_with_fuel n tree) 
                       |>> apply_tree
 | Identification data \<Rightarrow> identify data
 | Selection tree \<Rightarrow> (eval_tree_with_fuel n tree) 
                     |>> slice 
                     <$> (\<lambda>r. (Data (Ref r)))
 | Digestion tree \<Rightarrow> (case (eval_tree_with_fuel n tree) of
                       None \<Rightarrow> None
                     | Some tree' \<Rightarrow>
                       (case (slice tree') of
                         None \<Rightarrow> None
                       | Some ref \<Rightarrow>
                          (case ref of
                           BlobRef b \<Rightarrow> None
                         | TreeRef t \<Rightarrow> (eval_tree_with_fuel n t) <$> digest <$> HTreeObj ))))"
| "force_with_fuel 0 thunk = None"
| "force_with_fuel (Suc n) thunk =
   (case (think_with_fuel n thunk) of
      None \<Rightarrow> None
    | Some h \<Rightarrow> 
        (case h of
           Data _ \<Rightarrow> Some h
         | Thunk thunk' \<Rightarrow> force_with_fuel n thunk'
         | Encode (Strict thunk') \<Rightarrow> force_with_fuel n thunk'
         | Encode (Shallow thunk') \<Rightarrow> force_with_fuel n thunk'))"
| "execute_with_fuel n encode =
    (case encode of 
     Strict thunk \<Rightarrow> force_with_fuel n thunk <$> lift
   | Shallow thunk \<Rightarrow> force_with_fuel n thunk <$> lower)"
| "eval_list_with_fuel f [] = Some []"
| "eval_list_with_fuel f (x # xs) =
   (case (eval_with_fuel f x) of
    None \<Rightarrow> None
  | Some y \<Rightarrow> (case (eval_list_with_fuel f xs) of
               None \<Rightarrow> None
             | Some ys \<Rightarrow> Some (y # ys)))"
| "eval_tree_with_fuel n t =  
   eval_list_with_fuel n (get_tree_raw t) <$> create_tree"
| "eval_with_fuel 0 h =
   (case h of
    Thunk _ \<Rightarrow> Some h
  | (Data (Ref _)) \<Rightarrow> Some h
  | (Data (Object (BlobObj _))) \<Rightarrow> Some h
  | _ \<Rightarrow> None)"
| "eval_with_fuel (Suc n) h =
    (case h of
    Thunk _ \<Rightarrow> Some h
  | (Data (Ref _)) \<Rightarrow> Some h
  | (Data (Object (BlobObj _))) \<Rightarrow> Some h
  | (Data (Object (TreeObj tree))) \<Rightarrow> 
       (eval_tree_with_fuel n tree)
       <$> HTreeObj 
  | Encode encode \<Rightarrow> (case (execute_with_fuel n encode) of
                             None \<Rightarrow> None
                           | Some h \<Rightarrow> eval_with_fuel n h))"

definition thinks_to :: "Thunk \<Rightarrow> handle \<Rightarrow> bool" where
  "thinks_to h h1 \<equiv> (\<exists>fuel. think_with_fuel fuel h = Some h1)"

definition forces_to :: "Thunk \<Rightarrow> handle \<Rightarrow> bool" where
  "forces_to h h1 \<equiv> (\<exists>fuel. force_with_fuel fuel h = Some h1)"

definition executes_to :: "Encode \<Rightarrow> handle \<Rightarrow> bool" where
  "executes_to h h1 \<equiv> (\<exists>fuel. execute_with_fuel fuel h = Some h1)"

definition evals_tree_to :: "TreeName \<Rightarrow> TreeName \<Rightarrow> bool" where
  "evals_tree_to h h1 \<equiv> (\<exists>fuel. eval_tree_with_fuel fuel h = Some h1)"

definition evals_to :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  "evals_to h h1 \<equiv> (\<exists>fuel. eval_with_fuel fuel h = Some h1)"

(* Determinism *)
lemma force_with_fuel_to_data:
  assumes "force_with_fuel n h = Some r"
  shows "(\<exists>d. r = Data d)"
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
    then show ?thesis 
      using Suc Some 
      by (cases r', auto, auto, auto, case_tac x3, force+)
  qed
qed

lemma eval_with_fuel_not_encode:
  assumes "eval_with_fuel n h = Some r"
  shows "(\<exists>d. r = Data d) \<or> (\<exists>th. r = Thunk th)"
  using assms
proof (induction n arbitrary: h)
  case 0 
  then show ?thesis 
    by (cases h, simp, case_tac x1, case_tac x1a; simp; blast)
next
  case (Suc n')
  then show ?case
  proof (cases h)
    case (Thunk t) then show ?thesis using Suc by auto
  next
    case (Data d)
    then show ?thesis
    proof (cases d)
      case (Object obj)
      then show ?thesis using Suc Data Object by (cases obj) auto
    next
      case (Ref)
      then show ?thesis using Suc Data by auto
    qed
  next
    case (Encode e)
    then show ?thesis
      by (metis (no_types, lifting) Suc.IH Suc.prems
          eval_with_fuel.simps(2) handle.simps(12) option.case_eq_if
          rel_opt.simps(1,4))
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
      using P2
      by (simp, metis Encode.case(2) Encode.exhaust Encode.simps(5)
          force_with_fuel.simps(1) option.distinct(1) option.map(1))

    have P6: "\<forall>h v. eval_with_fuel 0 h = Some v \<longrightarrow> eval_with_fuel (0 + k) h = Some v"
    proof (intro allI impI)
      fix h v
      assume ASSM: "eval_with_fuel 0 h = Some v"
      show "eval_with_fuel (0 + k) h = Some v"
      proof (cases h)
        case (Thunk th)
        then show ?thesis using ASSM by (cases k) auto
      next
        case (Encode e)
        then show ?thesis using ASSM by (cases k) auto
      next
        case (Data d)
        then show ?thesis using ASSM 
          apply (cases d; cases k, force)
          apply (case_tac x1; fastforce)
          apply force
          done
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
    assume ASSM: "think_with_fuel (Suc f) th = Some r"
    then show "think_with_fuel (Suc f + k) th = Some r"
    proof (cases th)
      case (Application tree)
      then obtain t' where "eval_tree_with_fuel f tree = Some t'"
                     and  APPLY: "apply_tree t' = Some r"
        using ASSM
        by (cases "eval_tree_with_fuel f tree") force+
      then show ?thesis
        using Suc.IH Application by auto
    next
      case (Identification d)
      then show ?thesis using ASSM by auto
    next
      case (Selection tree)
      then obtain t' where "eval_tree_with_fuel f tree = Some t'"
                       and "(slice t') <$> (\<lambda>r. (Data (Ref r))) = Some r"
        by (metis (no_types, lifting) ASSM None_eq_map_option_iff
            Thunk.simps(19) not_Some_eq option.case_eq_if option.sel
            think_with_fuel.simps(2))
      then show ?thesis
        using Suc.IH Selection ASSM by force
    next
      case (Digestion tree)
      then obtain t' where 1: "eval_tree_with_fuel f tree = Some t'"
        using ASSM by fastforce
      then obtain t'' where 2: "slice t' = Some (TreeRef t'')"
        using ASSM Digestion
        by (metis (no_types, lifting) Ref.exhaust Ref.simps(5) Thunk.simps(20)
            not_Some_eq option.case_eq_if option.sel think_with_fuel.simps(2))
      then obtain t''' where 3: "eval_tree_with_fuel f t'' = Some t'''"
        using ASSM Digestion 1 2
        by fastforce
      have "r = HTreeObj (digest t''')"
        using Digestion ASSM 1 2 3
        by force

      then show ?thesis
        using Suc.IH Digestion ASSM 1 2 3
        using think_with_fuel.elims by fastforce
    qed
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
        case (Data d)
        then show ?thesis using Think ThinkIH assm1 by auto
      next
      next
        case (Thunk thunk')
        then show ?thesis 
          using Suc.IH assm1 ThinkIH Thunk Think by force 
      next
        case (Encode encode')
        then show ?thesis
          using Think assm1 Suc.IH
          by (cases encode'; simp)
      qed
    qed
  qed
      
  have P3: "\<forall>h v. execute_with_fuel (Suc f) h = Some v \<longrightarrow> execute_with_fuel (Suc f + k) h = Some v"
  proof (intro allI impI)
    fix h v
    assume "execute_with_fuel (Suc f) h = Some v"
    then show "execute_with_fuel (Suc f + k) h = Some v" 
      using P2 by (cases h; auto)
  qed

  have P6: "\<forall>h v. eval_with_fuel (Suc f) h = Some v \<longrightarrow> eval_with_fuel (Suc f + k) h = Some v"
  proof (intro allI impI)
    fix h v
    assume ASSM: "eval_with_fuel (Suc f) h = Some v"
    show "eval_with_fuel (Suc f + k) h = Some v"
    proof (cases h)
      case (Data d)
      then show ?thesis
      proof (cases d)
        case Ref 
        then show ?thesis using ASSM Data by auto
      next
        case (Object obj)
        then show ?thesis
        proof (cases obj)
          case (BlobObj)
          then show ?thesis using ASSM Data Object by auto
        next
          case (TreeObj t)
          then obtain tree' where "eval_tree_with_fuel f t = Some tree'"
                        and V: "v = HTreeObj tree'"
            using ASSM Data Object
            by (cases "eval_tree_with_fuel f t") auto
          
          then have "eval_tree_with_fuel (f + k) t = Some tree'"
            using Suc.IH by auto
          then show ?thesis 
            using V ASSM Data TreeObj Object by simp
        qed
      qed
    next
      case (Thunk th)
      then show ?thesis using ASSM by (cases k) auto
    next
      case (Encode e)
      then obtain h' where "execute_with_fuel f e = Some h'"
                       and "eval_with_fuel f h' = Some v"
        using ASSM
        by (cases "execute_with_fuel f e") auto
      then have "execute_with_fuel (f + k) e = Some h'"
           and  "eval_with_fuel (f + k) h' = Some v"
        using Suc.IH by auto
      then show ?thesis using Encode by auto
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
  show ?thesis using AA BB
    by force
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

lemma forces_to_data:
  assumes "forces_to h r"
  shows "(\<exists>d. r = Data d)"
  using assms force_with_fuel_to_data
  unfolding forces_to_def
  by auto

lemma evals_to_not_encode:
  assumes "evals_to h r"
  shows "(\<exists>d. r = Data d) \<or> (\<exists>th. r = Thunk th)"
  using assms eval_with_fuel_not_encode
  unfolding evals_to_def
  by auto

lemma forces_to_implies_evals_to:
  assumes "forces_to t (HBlobObj b)"
  shows "evals_to (Encode (Strict t)) (HBlobObj b)"
  using assms
  unfolding evals_to_def forces_to_def
proof
  fix x
  assume "force_with_fuel x t = Some (HBlobObj b)"
  then have 1: "execute_with_fuel x (Strict t) = Some (HBlobObj b)" by simp
  moreover have 2: "eval_with_fuel x (HBlobObj b) = Some (HBlobObj b)"
    by (metis Data.simps(5) HBlobObj_def Object.simps(5) add_cancel_right_left eval_with_fuel.simps(1)
        eval_with_fuel_padding handle.simps(10))

  ultimately have "eval_with_fuel (Suc x) (Encode (Strict t)) = Some (HBlobObj b)"
    by (simp del: execute_with_fuel.simps)

  then show " \<exists>fuel.
            eval_with_fuel fuel
             (Encode
               (Strict t)) =
            Some (HBlobObj b)"
    by blast
qed

definition endpoint :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "endpoint f h \<equiv>
     (if (\<exists>v. f h v)
      then Some (THE v. f h v)
      else None)"

definition think :: "Thunk \<Rightarrow> handle option" where
  "think h = endpoint thinks_to h"

definition force :: "Thunk \<Rightarrow> handle option" where
  "force h = endpoint forces_to h"

definition execute :: "Encode \<Rightarrow> handle option" where
  "execute h = endpoint executes_to h"

definition eval :: "handle \<Rightarrow> handle option" where
  "eval h = endpoint evals_to h"

definition eval_tree :: "TreeName \<Rightarrow> TreeName option" where
  "eval_tree h = endpoint evals_tree_to h"

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

lemma force_data:
  assumes "force h = Some r"
  shows "(\<exists>d. r = Data d)"
  using  forces_to_data force_some[OF assms]
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

lemma eval_tree_some:
  assumes "eval_tree h = Some h1"
  shows "evals_tree_to h h1"
  by (metis assms endpoint_some eval_tree_def evals_tree_to_deterministic)

lemma eval_not_encode:
  assumes "eval h = Some r"
  shows "(\<exists>d. r = Data d) \<or> (\<exists>th. r = Thunk th)"
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

lemma eval_tree_unique:
  assumes "evals_tree_to h h1"
  shows "eval_tree h = Some h1"
  by (simp add: assms endpoint_unique eval_tree_def evals_tree_to_deterministic)

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
  shows "eval (HTreeObj (create_tree xs)) = Some (HTreeObj (create_tree ys))"
proof -
  obtain f where "eval_list_with_fuel f xs = Some ys"
    using assms evals_to_tree_to by auto
  then have "eval_with_fuel (Suc f) (HTreeObj (create_tree xs)) = Some (HTreeObj (create_tree ys))"
    by auto
  then show ?thesis 
    using evals_to_def eval_unique by blast
qed

lemma eval_tree_to_eval_entry:
  assumes "eval (HTreeObj t) = Some r"
  shows "r = (HTreeObj (create_tree (map (\<lambda>x. the (eval x)) (get_tree_raw t)))) \<and> (list_all (\<lambda>x. \<exists>t'. eval x = Some t') (get_tree_raw t))"
proof -
  have "\<exists>f. eval_with_fuel f (HTreeObj t) = Some r"
    using assms
    using eval_some evals_to_def by blast
  then have "\<exists>t' f. eval_tree_with_fuel f t = Some t'"
    unfolding HTreeObj_def
    by (metis (no_types, lifting) Data.simps(5)
        None_eq_map_option_iff Object.simps(6)
        eval_with_fuel.elims handle.simps(10) option.distinct(1)
        option.exhaust_sel)
  then obtain t' f where 1: "eval_tree_with_fuel f t = Some t'"
    by blast
  then have "eval_with_fuel (Suc f) (HTreeObj t) = Some (HTreeObj t')" by simp
  then have 2: "r = (HTreeObj t')"
    using assms eval_deterministic eval_unique evals_to_def
    by blast
  then obtain ys where 3: "eval_list_with_fuel f (get_tree_raw t) = Some ys"
    using 1 by auto
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
  then have 5: "r = HTreeObj (create_tree ((map (\<lambda>x. the (eval x))) (get_tree_raw t)))"
    using 1 2 3
    by auto

  have "(list_all (\<lambda>x. \<exists>t'. eval x = Some t') (get_tree_raw t))"
    using 4
    by (simp add: list_all2_conv_all_nth list_all_length)
  then show ?thesis using 5 by auto
qed

lemma eval_hs:
  "eval h = 
    (case h of
      Thunk _ \<Rightarrow> Some h
    | (Data (Ref _ )) \<Rightarrow> Some h
    | (Data (Object (BlobObj _))) \<Rightarrow> Some h
    | (Data (Object (TreeObj tree))) \<Rightarrow> 
                    (eval_tree tree) <$> HTreeObj
    | Encode encode \<Rightarrow> execute encode |>> eval)"
proof (cases h)
  case Thunk
  then show ?thesis
    by (metis eval_unique eval_with_fuel.simps(1) evals_to_def handle.simps(11))
next
  case (Data d)
  then show ?thesis
  proof (cases d)
    case Ref
    then show ?thesis
      by (metis (no_types, lifting) Data Data.simps(6) eval_unique eval_with_fuel.simps(2) evals_to_def
          handle.simps(10))
  next
    case (Object obj)
    then show ?thesis
    proof (cases obj)
      case BlobObj
      then show ?thesis 
      by (metis Data Data.simps(5) Object Object.simps(5) eval_unique eval_with_fuel.simps(1) evals_to_def
          handle.simps(10))
  next
    case (TreeObj t)
    then show ?thesis
    proof (cases "eval_tree t")
      case (Some t')
      then obtain f where "eval_tree_with_fuel f t  = Some t'"
        using eval_tree_some evals_tree_to_def by blast
      then have "eval_with_fuel (Suc f) (HTreeObj t) = Some (HTreeObj t')" by simp
      then show ?thesis 
        by (metis Data Data.simps(5) HTreeObj_def Object Object.simps(6) Some TreeObj eval_unique
            evals_to_def handle.simps(10) option.simps(9))
    next
      case None
      have "eval h = None"
      proof (rule ccontr)
        assume "eval h \<noteq> None"
        then obtain f t' where "eval_with_fuel f h = Some (HTreeObj t')"
          using TreeObj
          by (metis Data HTreeObj_def Object eval_some
              eval_tree_to_eval_entry evals_to_def option.exhaust)
        then obtain f' where "f = Suc f'"
          using Data Object TreeObj
          by (cases f, simp, blast)
        then have "eval_tree_with_fuel f' t = Some t'"
          using Data Object TreeObj
            \<open>eval_with_fuel f h = Some (HTreeObj t')\<close> by auto
        then show False
          using None
          by (metis eval_tree_unique evals_tree_to_def
              option.discI)
        qed
        then show ?thesis
          by (simp add: Data None Object TreeObj)
      qed
    qed
  qed
next
  case (Encode e)
  then show ?thesis
  proof (cases "execute e")
    case (Some e')
    then obtain f1 where Fuel1: "execute_with_fuel f1 e = Some e'"
      using execute_some executes_to_def by blast

    show ?thesis
    proof (cases "eval e'")
      case (Some e'')
      then obtain f2 where Fuel2:"eval_with_fuel f2 e' = Some e''"
        using eval_some evals_to_def by blast
      have "eval_with_fuel (Suc (max f1 f2)) h = Some e''"
        by (smt (verit, ccfv_SIG) Encode Fuel1 Fuel2 add.commute eval_with_fuel.simps(2) fuel_padding
            handle.simps(12) max.commute nat_minus_add_max option.simps(5))
      then show ?thesis
        by (metis (no_types, lifting) Encode Some
            \<open>\<And>thesis. (\<And>f1. execute_with_fuel f1 e = Some e' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> eval_unique evals_to_def
            execute_unique executes_to_def handle.simps(12) option.simps(5))
    next
      case None
      have "eval h = None"
      proof (rule ccontr)
        assume "eval h \<noteq> None"
        then obtain f h' where "eval_with_fuel f h = Some h'"
          by (meson eval_some evals_to_def option.exhaust)
        then obtain f' where "f = Suc f'"
          by (metis Encode eval_with_fuel.simps(1) handle.simps(12) nat.exhaust_sel option.distinct(1))
        then obtain e' where "execute_with_fuel f' e = Some e'"
                       and "eval_with_fuel f' e' = Some h'"
          by (metis (no_types, lifting) Encode \<open>eval_with_fuel f h = Some h'\<close> eval_with_fuel.simps(2)
              handle.simps(12) option.case_eq_if option.distinct(1) option.exhaust_sel)
        then show False
          using None
          by (metis Some eval_unique evals_to_def execute_unique executes_to_def option.discI option.sel)
      qed
      then show ?thesis
        using Encode Some None by auto
    qed
  next
    case None
    have "eval h = None"
    proof (rule ccontr)
      assume "eval h \<noteq> None"
      then obtain f h' where "eval_with_fuel f h = Some h'"
        by (meson eval_some evals_to_def option.exhaust)
      then obtain f' where "f = Suc f'"
        by (metis Encode eval_with_fuel.simps(1) handle.simps(12) nat.exhaust_sel option.distinct(1))
      then obtain e' where "execute_with_fuel f' e = Some e'"
                     and "eval_with_fuel f' e' = Some h'"
        by (metis (no_types, lifting) Encode \<open>eval_with_fuel f h = Some h'\<close> eval_with_fuel.simps(2)
              handle.simps(12) option.case_eq_if option.distinct(1) option.exhaust_sel)
      then show False
        using None execute_unique executes_to_def by fastforce
      qed
      then show ?thesis
        by (simp add: Encode None)
    qed
  qed

lemma execute_hs:
  "execute e = 
    (case e of
     Strict t \<Rightarrow> force t <$> lift
   | Shallow t \<Rightarrow> force t <$> lower)"
proof (cases e)
  case (Strict t)
  have "\<And>h. execute (Strict t) = Some h \<Longrightarrow> (force t <$> lift = Some h)"
    using execute_some executes_to_def force_unique forces_to_def by fastforce

  moreover have "\<And>h. (force t <$> lift = Some h) \<Longrightarrow> execute (Strict t) = Some h"
    by (metis (mono_tags, lifting) Encode.simps(5)
        \<open>\<And>h. execute (Strict t) = Some h \<Longrightarrow> force t <$> lift = Some h\<close> endpoint_def execute_def
        execute_with_fuel.simps executes_to_def force_def forces_to_def map_option_case
        option.case_eq_if)

  ultimately show ?thesis
    using Strict
    by (metis Encode.simps(5) not_Some_eq)
next
  case (Shallow t)
  have "\<And>h. execute (Shallow t) = Some h \<Longrightarrow> (force t <$> lower = Some h)"
    using execute_some executes_to_def force_unique forces_to_def by fastforce

  moreover have "\<And>h. (force t <$> lower = Some h) \<Longrightarrow> execute (Shallow t) = Some h"
    by (metis (no_types, lifting) Encode.simps(6) calculation endpoint_def endpoint_def execute_def
        execute_with_fuel.simps executes_to_def force_def forces_to_def map_option_eq_Some)

  ultimately show ?thesis
    using Shallow
    by (metis Encode.simps(6) option.exhaust)
qed

lemma force_hs:
  "force t = 
     think t |>> 
        (\<lambda>h. 
          (case h of
             Data _ \<Rightarrow> Some h
           | Thunk thunk' \<Rightarrow> force thunk'
           | Encode (Strict thunk') \<Rightarrow> force thunk'
           | Encode (Shallow thunk') \<Rightarrow> force thunk'))"
proof -
  have "\<And>h. force t = Some h \<Longrightarrow> \<exists>h'. (think t = Some h' \<and> (case h' of
             Data _ \<Rightarrow> Some h'
           | Thunk thunk' \<Rightarrow> force thunk'
           | Encode (Strict thunk') \<Rightarrow> force thunk'
           | Encode (Shallow thunk') \<Rightarrow> force thunk') = Some h)"
  proof -
    fix h
    assume "force t = Some h"
    then obtain f where "force_with_fuel f t = Some h"
      using force_some forces_to_def by blast
    then obtain f' where "force_with_fuel (Suc f') t = Some h"
      by (metis force_with_fuel.simps(1) nat.exhaust_sel option.simps(3))
    then obtain h' where 1: "think_with_fuel f' t = Some h'" and 2: "(case h' of
             Data _ \<Rightarrow> Some h'
           | Thunk thunk' \<Rightarrow> force_with_fuel f' thunk'
           | Encode (Strict thunk') \<Rightarrow> force_with_fuel f' thunk'
           | Encode (Shallow thunk') \<Rightarrow> force_with_fuel f' thunk') = Some h"
      by (metis (lifting) force_with_fuel.simps(2) option.exhaust option.simps(4,5))
    then have 2: "(case h' of
             Data _ \<Rightarrow> Some h'
           | Thunk thunk' \<Rightarrow> force thunk'
           | Encode (Strict thunk') \<Rightarrow> force thunk'
           | Encode (Shallow thunk') \<Rightarrow> force thunk') = Some h"
    proof (cases h')
      case Data 
      then show ?thesis
        using "2" by auto
    next
      case (Thunk)
      then show ?thesis 
        using 2 force_unique forces_to_def by auto
    next
      case (Encode e)
      then show ?thesis
        using 2 force_unique forces_to_def Encode 
        by (cases e) auto
    qed

    have "think t = Some h'"
      using 1 think_unique thinks_to_def by blast
    then show "\<exists>h'. (think t = Some h' \<and> (case h' of
             Data _ \<Rightarrow> Some h'
           | Thunk thunk' \<Rightarrow> force thunk'
           | Encode (Strict thunk') \<Rightarrow> force thunk'
           | Encode (Shallow thunk') \<Rightarrow> force thunk') = Some h)"
      using 1 2 by auto
  qed

  moreover have "\<And>h h'. (think t = Some h \<and> (case h of
             Data _ \<Rightarrow> Some h
           | Thunk thunk' \<Rightarrow> force thunk'
           | Encode (Strict thunk') \<Rightarrow> force thunk'
           | Encode (Shallow thunk') \<Rightarrow> force thunk') = Some h') \<Longrightarrow> force t = Some h'"
  proof -
    fix h h'
    assume ASSM: "(think t = Some h \<and> (case h of
             Data _ \<Rightarrow> Some h
           | Thunk thunk' \<Rightarrow> force thunk'
           | Encode (Strict thunk') \<Rightarrow> force thunk'
           | Encode (Shallow thunk') \<Rightarrow> force thunk') = Some h')"
    show "force t = Some h'"
    proof (cases h)
      case Data
      then obtain f where "think_with_fuel f t = Some h"
        using ASSM think_some thinks_to_def by blast
      then have "h' = h" and "force_with_fuel (Suc f) t = Some h'"
        using ASSM Data apply auto[1]
        using ASSM Data \<open>think_with_fuel f t = Some h\<close> by auto
      then show ?thesis
        using force_unique forces_to_def by blast
    next
      case (Thunk thunk')
      then obtain f1 where Fuel1: "think_with_fuel f1 t = Some (Thunk thunk')"
        using ASSM think_some thinks_to_def by blast
      obtain f2 where Fuel2: "force_with_fuel f2 thunk' = Some h'"
        using ASSM force_some forces_to_def Thunk by fastforce 

      have "force_with_fuel (Suc (max f1 f2)) t = Some h'"
        using fuel_padding Fuel1 Fuel2
        by (metis (no_types, lifting) add.commute
            force_with_fuel.simps(2) handle.simps(11) max.commute
            nat_minus_add_max option.simps(5))
      then show ?thesis
        using force_unique forces_to_def by blast
    next
      case (Encode e)
      then show ?thesis
      proof (cases e)
        case (Strict thunk')
          then obtain f1 where Fuel1: "think_with_fuel f1 t = Some (Encode (Strict thunk'))"
            using ASSM think_some thinks_to_def Encode by blast
          obtain f2 where Fuel2: "force_with_fuel f2 thunk' = Some h'"
            using ASSM force_some forces_to_def Encode Strict by fastforce 
    
          have Fuel1: "think_with_fuel (max f1 f2) t = Some (Encode (Strict thunk'))"
            using fuel_padding Fuel1
            by (metis max.cobounded1
                ordered_cancel_comm_monoid_diff_class.add_diff_inverse)

          have Fuel2: "force_with_fuel (max f1 f2) thunk' = Some h'"
            using fuel_padding Fuel2
            by (metis add.commute nat_minus_add_max)

          have "force_with_fuel (Suc (max f1 f2)) t = Some h'"
            using Fuel1 Fuel2
            by simp
          then show ?thesis
            using force_unique forces_to_def by blast
        next
          case (Shallow thunk')
          then obtain f1 where Fuel1: "think_with_fuel f1 t = Some (Encode (Shallow thunk'))"
            using ASSM think_some thinks_to_def Encode by blast
          obtain f2 where Fuel2: "force_with_fuel f2 thunk' = Some h'"
            using ASSM force_some forces_to_def Encode Shallow by fastforce
    
          have Fuel1: "think_with_fuel (max f1 f2) t = Some (Encode (Shallow thunk'))"
            using fuel_padding Fuel1
            by (metis max.cobounded1
                ordered_cancel_comm_monoid_diff_class.add_diff_inverse)

          have Fuel2: "force_with_fuel (max f1 f2) thunk' = Some h'"
            using fuel_padding Fuel2
            by (metis add.commute nat_minus_add_max)

          have "force_with_fuel (Suc (max f1 f2)) t = Some h'"
            using Fuel1 Fuel2
            by simp
          then show ?thesis
            using force_unique forces_to_def by blast
        qed
      qed
    qed

    ultimately show ?thesis
      by (metis (no_types, lifting) ext option.case_eq_if
          option.distinct(1) option.exhaust_sel option.sel)
  qed

lemma think_hs:
"think t = 
  (case t of
     Application tree \<Rightarrow> eval_tree tree |>> apply_tree
   | Identification data \<Rightarrow> identify data
   | Selection tree \<Rightarrow> eval_tree tree |>> slice <$> (\<lambda>r. (Data (Ref r)))
   | Digestion tree \<Rightarrow> eval_tree tree 
               |>> (\<lambda>tree'. slice tree' |>> 
                   (\<lambda>ref. case ref of 
                          BlobRef b \<Rightarrow> None 
                        | TreeRef t \<Rightarrow> eval_tree t <$> digest <$> HTreeObj)))"
proof (cases t)
  case (Application tree)
  have "\<And>h. think t = Some h \<Longrightarrow> \<exists>tree'. eval_tree tree = Some tree' \<and> apply_tree tree' = Some h" 
    by (metis (no_types, lifting) Application Thunk.simps(17) eval_tree_unique evals_tree_to_def
        option.case_eq_if option.distinct(1) option.exhaust_sel think_some think_with_fuel.elims
        thinks_to_def)

  moreover have "\<And>tree' h. eval_tree tree = Some tree' \<and> apply_tree tree' = Some h \<Longrightarrow> think t = Some h"
    by (metis (lifting) Application Thunk.simps(17) eval_tree_some evals_tree_to_def option.simps(5)
        think_unique think_with_fuel.simps(2) thinks_to_def)
 
  ultimately show ?thesis
    by (metis (lifting) Application Thunk.simps(17) option.case_eq_if option.distinct(1) option.exhaust_sel
        option.sel)
next
  case Identification
  then show ?thesis
    by (metis (lifting) Thunk.simps(18) identify.simps think_unique think_with_fuel.simps(2)
        thinks_to_def)
next
  case (Selection tree)
  have "\<And>h. think t = Some h \<Longrightarrow> \<exists>tree' h''. eval_tree tree = Some tree' \<and> slice tree' = Some h'' \<and> h = (Data (Ref h''))" 
    by (smt (verit, ccfv_threshold) Selection Thunk.simps(19) endpoint_def eval_tree_unique evals_tree_to_def
        is_none_code(2) map_option_eq_Some option.case_eq_if option.distinct(1) option.split_sel_asm think_def
        think_unique think_with_fuel.elims thinks_to_def)

  moreover have "\<And>tree' h'. eval_tree tree = Some tree' \<and> slice tree' = Some h' \<Longrightarrow> think t = Some (Data (Ref h'))"
    by (metis (no_types, lifting) Selection Thunk.simps(19) eval_tree_some evals_tree_to_def map_option_case
        option.simps(5) think_unique think_with_fuel.simps(2) thinks_to_def)
 
  ultimately show ?thesis
    by (smt (verit, best) Selection Thunk.simps(19) map_option_eq_Some not_None_eq option.simps(4,5))
next
  case (Digestion tree)
  have A: "\<And>h. think t = Some h \<Longrightarrow> \<exists>tree' tree'' tree'''. eval_tree tree = Some tree' \<and> slice tree' = Some (TreeRef tree'') \<and> eval_tree tree'' = Some tree''' \<and> h = (Data (Object (TreeObj (digest tree'''))))" 
  proof -
    fix h
    assume ASSM: "think t = Some h"
    then obtain f where 1: "think_with_fuel (Suc f) t = Some h" 
      using think_some thinks_to_def 
      by (metis option.distinct(1) think_with_fuel.elims)

    then obtain tree' where 2: "eval_tree_with_fuel f tree = Some tree'"
      using ASSM Digestion
      by fastforce
    obtain tree'' where 3: "slice tree' = Some (TreeRef tree'')"
      using 1 2
      by (metis (no_types, lifting) Digestion Ref.exhaust Ref.simps(5) Thunk.simps(20) not_Some_eq
          option.case_eq_if option.sel think_with_fuel.simps(2))
    obtain tree''' where 4: "eval_tree_with_fuel f tree'' = Some tree'''"
      using 1 2 3
      using Digestion by fastforce
    have "h = (Data (Object (TreeObj (digest tree'''))))"
      using 1 2 3 4 Digestion by force
    then show "\<exists>tree' tree'' tree'''. eval_tree tree = Some tree' \<and> slice tree' = Some (TreeRef tree'') \<and> eval_tree tree'' = Some tree''' \<and> h = (Data (Object (TreeObj (digest tree'''))))"
      using 1 2 3 4
      using eval_tree_unique evals_tree_to_def by blast
  qed

  have B: "\<And>tree' tree'' tree'''. eval_tree tree = Some tree' \<and> slice tree' = Some (TreeRef tree'') \<and> eval_tree tree'' = Some tree''' \<Longrightarrow> \<exists>h. think t = Some h" 
  proof -
    fix tree' tree'' tree'''
    assume ASSM: "eval_tree tree = Some tree' \<and> slice tree' = Some (TreeRef tree'') \<and> eval_tree tree'' = Some tree'''"

    obtain f1 where Fuel1: "eval_tree_with_fuel f1 tree = Some tree'"
      using ASSM
      using eval_tree_some evals_tree_to_def by blast

    obtain f2 where Fuel2: "eval_tree_with_fuel f2 tree'' = Some tree'''"
      using ASSM eval_tree_some evals_tree_to_def by blast

    have Fuel1: "eval_tree_with_fuel (max f1 f2) tree = Some tree'"
      using Fuel1 fuel_padding
      by (metis add.commute max.commute nat_minus_add_max)

    have Fuel2: "eval_tree_with_fuel (max f1 f2) tree'' = Some tree'''"
      using Fuel2 fuel_padding
      by (metis add.commute nat_minus_add_max)

    have "think_with_fuel (Suc (max f1 f2)) t = Some (HTreeObj (digest tree'''))"
      using Fuel1 Fuel2 ASSM
      by (simp add: Digestion map_option_case)
    then show "\<exists>h. think t = Some h"
      by (metis think_unique thinks_to_def)
  qed

  show ?thesis
  proof (cases "think t")
    case (Some h)
    then show ?thesis
      using A
      using Digestion by fastforce
  next
    case None
    then show ?thesis
    proof -
      have "(case (eval_tree tree) of
                       None \<Rightarrow> None
                     | Some tree' \<Rightarrow>
                       (case (slice tree') of
                         None \<Rightarrow> None
                       | Some ref \<Rightarrow>
                          (case ref of
                           BlobRef b \<Rightarrow> None
                         | TreeRef t \<Rightarrow> (eval_tree t) <$> digest <$> HTreeObj))) = None"
      proof (rule ccontr)
        assume ASSM: "(case (eval_tree tree) of
                       None \<Rightarrow> None
                     | Some tree' \<Rightarrow>
                       (case (slice tree') of
                         None \<Rightarrow> None
                       | Some ref \<Rightarrow>
                          (case ref of
                           BlobRef b \<Rightarrow> None
                         | TreeRef t \<Rightarrow> (eval_tree t) <$> digest <$> HTreeObj))) \<noteq> None"
        then obtain tree' where 1: "eval_tree tree = Some tree'" by fastforce
        then obtain tree'' where 2: "slice tree' = Some (TreeRef tree'')"
          using ASSM
          by (metis (no_types, lifting) Ref.exhaust Ref.simps(5) option.case_eq_if option.exhaust option.sel)
        then obtain tree''' where 3: "eval_tree tree'' = Some tree'''"
          using 1 2 ASSM
          by auto
        then show False 
          using B None 1 2 3
          unfolding HTreeObj_def
          by force
      qed
      then show ?thesis
        using Digestion None by fastforce
    qed
  qed
qed

inductive value_tree :: "TreeName \<Rightarrow> bool"
and value_handle :: "handle \<Rightarrow> bool"
where
  tree[intro]:
    "list_all value_handle (get_tree_raw t) \<Longrightarrow> value_tree t"
| blob_obj_handle[intro]:
    "value_handle (Data (Object (BlobObj b)))"
| tree_obj_handle[intro]:
    "value_tree t \<Longrightarrow> value_handle (Data (Object (TreeObj t)))"
| ref_handle[intro]:
    "value_handle (Data (Ref r))"
| thunk_handle[intro]:
    "value_handle (Thunk t)"

lemma eval_with_fuel_to_value_handle:
  "eval_with_fuel f h = Some r \<Longrightarrow> value_handle r"
proof (induction f arbitrary: h r)
  case 0
  then show ?case 
  proof (cases "h") 
    case Thunk
    then show ?thesis using 0 by auto
  next
    case Encode
    then show ?thesis using 0 by auto
  next
    case (Data d)
    then show ?thesis using 0 
      by (cases d, metis Data.simps(5) Object.exhaust
          Object.simps(5,6) blob_obj_handle
          eval_with_fuel.simps(1) handle.simps(10) not_Some_eq
          option.inject, auto)
  qed
next
  case (Suc n)

  show ?case
  proof (cases "h") 
    case (Thunk) then show ?thesis using Suc by auto
  next
    case (Encode e)
    then obtain res where "execute_with_fuel n e = Some res"
                      and rdef: "eval_with_fuel n res = Some r"
      using Suc
      by (metis (no_types, lifting) eval_with_fuel.simps(2)
          handle.simps(12) not_None_eq option.case_eq_if
          option.sel)
    then show ?thesis using Suc.IH by auto
  next
    case (Data d)
    then show ?thesis
    proof (cases d)
      case Ref
      then show ?thesis
        using Data Suc.prems by auto
    next
      case (Object obj)
      then show ?thesis
      proof (cases obj)
        case (BlobObj)
        then show ?thesis
          using Data Object Suc.prems by auto
      next
        case (TreeObj t)
        then obtain ys where "eval_list_with_fuel n (get_tree_raw t) = Some ys"
                         and rdef: "r = (Data (Object (TreeObj (create_tree ys))))"
          using Suc Data Object
          by force 
        
        then have "list_all2 (\<lambda>x y. eval_with_fuel n x = Some y) (get_tree_raw t) ys"
          using eval_list_to_list_all by auto
        then have "list_all value_handle ys"
          using Suc.IH 
          by (metis (mono_tags, lifting) list_all2_conv_all_nth list_all_length)
        then have "value_handle r"
          using rdef
          by (simp add: value_tree_value_handle.tree value_tree_value_handle.tree_obj_handle)
        then show ?thesis by auto
      qed
    qed
  qed
qed

lemma eval_to_value_handle:
  "eval h = Some r \<Longrightarrow> value_handle r"
  using eval_with_fuel_to_value_handle
  using eval_some evals_to_def by blast

lemma eval_tree_to_value_handle:
  "eval_tree t1 = Some t2 \<Longrightarrow> value_handle (HTreeObj t2)"
  by (metis Data.simps(5) Object.simps(6) eval_hs eval_to_value_handle handle.simps(10) map_option_case option.simps(5))

lemma eval_tree_to_not_encode:
  "eval_tree t1 = Some t2 \<Longrightarrow> list_all not_encode (get_tree_raw t2)"
  by (metis (mono_tags, lifting) Data.distinct(1) Data.inject(1) HTreeObj_def Object.distinct(1) Object.inject(2) eval_tree_to_value_handle handle.distinct(1,3,5) handle.inject(1) list.pred_set slice.not_encode_def
      value_handle.simps value_tree.cases)

lemma value_handle_not_encode:
  assumes "value_handle h"
  shows "\<not> (\<exists>e. h = Encode e)"
  using assms value_handle.simps by blast

end