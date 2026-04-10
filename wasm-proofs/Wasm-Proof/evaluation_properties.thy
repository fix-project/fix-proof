theory evaluation_properties
  imports evaluation
begin

lemma value_tree_to_sametypedness:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_preserve_value_handle: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> 
         \<not> (\<exists>e. h1 = Encode e) \<Longrightarrow>
         \<not> (\<exists>e. h2 = Encode e) \<Longrightarrow>
         ((\<exists>b. h1 = HBlobObj b) \<longleftrightarrow> (\<exists>b. h2 = HBlobObj b))
       \<and> ((\<exists>t. h1 = HTreeObj t) \<longleftrightarrow> (\<exists>t. h2 = HTreeObj t))
       \<and> ((\<exists>b. h1 = HBlobRef b) \<longleftrightarrow> (\<exists>b. h2 = HBlobRef b))
       \<and> ((\<exists>t. h1 = HTreeRef t) \<longleftrightarrow> (\<exists>t. h2 = HTreeRef t))
       \<and> ((\<exists>th. h1 =  Thunk th) \<longleftrightarrow> (\<exists>th. h2 = Thunk th))"
  assumes VT1: "value_tree t1"
  shows "\<forall>t2. (X (HTreeObj t1) (HTreeObj t2) \<longrightarrow>
         value_tree t2 \<longrightarrow>
         same_typed_tree t1 t2)"
  using VT1
proof (induction t1 rule: wfp_induct[OF wfp_tree_child])
  case (1 x)
  show ?case
  proof
    fix t2
    show "X (HTreeObj x) (HTreeObj t2) \<longrightarrow>
          value_tree t2 \<longrightarrow> same_typed_tree x t2"
    proof (intro impI)
      assume Xtree: "X (HTreeObj x) (HTreeObj t2)"
      assume VT2: "value_tree t2"
      show "same_typed_tree x t2"
      proof -
        have L: "length (get_tree_raw x) = length (get_tree_raw t2)"
          using tree_cong Xtree list_all2_lengthD by blast

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
              using tree_cong list_all2_nthD by blast

            have VHL: "value_handle ?lhs"
              using "1.prems"
              by (simp add: assm list_all_length value_tree.simps)

            have VHR: "value_handle ?rhs"
              using VT2 L assm
              by (simp add: assm list_all_length value_tree.simps)

            from VHL
            show "same_typed_handle ?lhs ?rhs"
            proof (cases ?lhs)
              case (blob_obj_handle b)
              then show ?thesis
                using X_preserve_value_handle EQLR VHL VHR value_handle_not_encode
                using HBlobObj_def
                by (metis blob_obj)
            next
              case (thunk_handle t)
              then show ?thesis
                using X_preserve_value_handle EQLR VHL VHR value_handle_not_encode
                by (metis thunk)
            next
              case (tree_obj_handle t)
              then obtain t' where tree_handle': "?rhs = (HTreeObj t')"
                using X_preserve_value_handle EQLR VHL VHR value_handle_not_encode
                using HTreeObj_def
                by (metis)

              have "tree_child t x" 
                by (metis assm in_set_conv_nth local.tree_obj_handle(1)
                    tree_child_def)
              moreover have "value_tree t" using VHL
                using local.tree_obj_handle(2) by auto
              moreover have "X (HTreeObj t) (HTreeObj t')"
                using EQLR local.tree_obj_handle(1) tree_handle'
                by simp
              moreover have "value_tree t'"
                using VHR tree_handle' value_handle.simps by auto
              ultimately have "same_typed_tree t t'"
                using "1.IH" HTreeObj_def by blast

              then show ?thesis
                using local.tree_obj_handle(1) tree_handle' by auto
            next
              case (ref_handle)
              then show ?thesis
                by (metis EQLR Ref.exhaust VHR X_preserve_value_handle
                    blob_ref handle.distinct(3) tree_ref HBlobRef_def HTreeRef_def
                    value_handle_not_encode)
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
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes X_preserve_value_handle: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> 
         \<not> (\<exists>e. h1 = Encode e) \<Longrightarrow>
         \<not> (\<exists>e. h2 = Encode e) \<Longrightarrow>
         ((\<exists>b. h1 = HBlobObj b) \<longleftrightarrow> (\<exists>b. h2 = HBlobObj b))
       \<and> ((\<exists>t. h1 = HTreeObj t) \<longleftrightarrow> (\<exists>t. h2 = HTreeObj t))
       \<and> ((\<exists>b. h1 = HBlobRef b) \<longleftrightarrow> (\<exists>b. h2 = HBlobRef b))
       \<and> ((\<exists>t. h1 = HTreeRef t) \<longleftrightarrow> (\<exists>t. h2 = HTreeRef t))
       \<and> ((\<exists>th. h1 =  Thunk th) \<longleftrightarrow> (\<exists>th. h2 = Thunk th))"
  assumes X_preserve_value_handle: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> 
         \<not> (\<exists>e. h1 = Encode e) \<Longrightarrow>
         \<not> (\<exists>e. h2 = Encode e) \<Longrightarrow>
         ((\<exists>b. h1 = Data (Object (BlobObj b))) \<longleftrightarrow> (\<exists>b. h2 = (Data (Object (BlobObj b)))))
       \<and> ((\<exists>t. h1 = Data (Object (TreeObj t))) \<longleftrightarrow> (\<exists>t. h2 = (Data (Object (TreeObj t)))))
       \<and> ((\<exists>b. h1 = Data (Ref (BlobRef b))) \<longleftrightarrow> (\<exists>b. h2 = (Data (Ref (BlobRef b)))))
       \<and> ((\<exists>t. h1 = Data (Ref (TreeRef t))) \<longleftrightarrow> (\<exists>t. h2 = (Data (Ref (TreeRef t)))))
       \<and> ((\<exists>th. h1 =  Thunk th) \<longleftrightarrow> (\<exists>th. h2 = Thunk th))"
  assumes relX: "X h1 h2" 
      and VH1: "value_handle h1"
      and VH2: "value_handle h2"
    shows "same_typed_handle h1 h2"
  using VH1
proof (cases h1)
  case (blob_obj_handle b)
  then show ?thesis
    using VH2 X_preserve_value_handle assms(3) value_handle_not_encode HBlobObj_def relX
    by blast
next
  case (thunk_handle th)
  then show ?thesis
    using VH2 X_preserve_value_handle assms(3) value_handle_not_encode relX by blast
next
  case (tree_obj_handle t1)
  then obtain t2 where tree_handle': "h2 = (HTreeObj t2)"
    using VH1 VH2 X_preserve_value_handle assms(3) value_handle_not_encode relX  HTreeObj_def
    by metis

  have VT1: "value_tree t1"
    using local.tree_obj_handle(2) by auto
  have VT2: "value_tree t2"
    using VH2 tree_handle' value_handle.simps by fastforce
  have relX: "X (HTreeObj t1) (HTreeObj t2)"
    using local.tree_obj_handle(1) relX tree_handle' 
    by simp

  have "same_typed_tree t1 t2"
    using value_tree_to_sametypedness tree_cong X_preserve_value_handle VT1
    using VT2 relX 
    using assms(2) by blast

  then show ?thesis
    using tree_obj_handle tree_handle' tree_obj
    by simp
next 
  case (ref_handle r)
  then show ?thesis
    using VH2 X_preserve_value_handle relX
      value_handle_not_encode by (cases r; blast)
qed

lemma eq_tree_eval_fuel_n:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"

  assumes eval_cong_n: "\<And>h1 h2. X h1 h2 \<Longrightarrow>
      (\<forall>v1. eval_with_fuel n h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
     \<and>
      (\<forall>v2. eval_with_fuel n h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))"
  assumes E: "X (HTreeObj t1) (HTreeObj t2)"
  shows "(\<forall>v1. eval_tree_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. evals_tree_to t2 v2 \<and> X (HTreeObj v1) (HTreeObj v2)))
      \<and>
        (\<forall>v2. eval_tree_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. evals_tree_to t1 v1 \<and> X (HTreeObj v1) (HTreeObj v2)))"
proof -
  have LHS: "(\<forall>v1. eval_tree_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. evals_tree_to t2 v2 \<and> X (HTreeObj v1) (HTreeObj v2)))"
  proof (intro allI impI)
    fix v1

    let ?raw1 = "get_tree_raw t1"
    let ?raw2 = "get_tree_raw t2"
    let ?out1 = "get_tree_raw v1"

    assume "eval_tree_with_fuel n t1 = Some v1"
    then have eval_raw1: "eval_list_with_fuel n ?raw1 = Some ?out1" 
      by (cases "eval_list_with_fuel n ?raw1") auto

    have ASSM: "list_all2 (\<lambda>x y. X x y) ?raw1 ?raw2" 
      using tree_cong E by blast

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
    then have "X (HTreeObj (create_tree (get_tree_raw v1))) 
                 (HTreeObj (create_tree (get_tree_raw (create_tree ys'))))" 
      using tree_complete[of "get_tree_raw v1" "get_tree_raw(create_tree ys')"] by auto
    then have RHS: "X (HTreeObj v1) (HTreeObj ?v2)"
      using \<open>eval_tree_with_fuel n t1 = Some v1\<close> eval_raw1 by fastforce

    then show "(\<exists>v2. evals_tree_to t2 v2 \<and> X (HTreeObj v1) (HTreeObj v2))" using LHS by auto
  qed

  have RHS: "(\<forall>v2. eval_tree_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. evals_tree_to t1 v1 \<and> X (HTreeObj v1) (HTreeObj v2)))"
  proof (intro allI impI)
    fix v2

    let ?raw1 = "get_tree_raw t1"
    let ?raw2 = "get_tree_raw t2"
    let ?out2 = "get_tree_raw v2"

    assume "eval_tree_with_fuel n t2 = Some v2"
    then have eval_raw2: "eval_list_with_fuel n ?raw2 = Some ?out2" 
      by (cases "eval_list_with_fuel n ?raw2") auto

    have ASSM: "list_all2 (\<lambda>x y. X x y) ?raw1 ?raw2" 
      using tree_cong E by blast

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
    then have "X (HTreeObj ?v1) (HTreeObj v2)" 
      using tree_complete[of "get_tree_raw(create_tree xs')" "get_tree_raw v2"]
      using \<open>eval_tree_with_fuel n t2 = Some v2\<close> eval_raw2 by auto
    then show "(\<exists>v1. evals_tree_to t1 v1 \<and> X (HTreeObj v1) (HTreeObj v2))" using LHS by auto
  qed

  then show ?thesis using LHS RHS by blast
qed

definition encode_to_thunk :: "Encode \<Rightarrow> Thunk"
  where [simp]:
"encode_to_thunk e = 
   (case e of
    Shallow th \<Rightarrow> th
  | Strict th \<Rightarrow> th)"

definition relaxed_X :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> bool"
where
"relaxed_X X h1 h2 = (case h1 of
  Encode (Shallow e) \<Rightarrow> X (Encode (Strict e)) (lift h2)
| _ \<Rightarrow> X (lift h1) (lift h2))"

definition strengthen :: "(handle \<Rightarrow> handle \<Rightarrow> bool) \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> bool"
  where
"strengthen X h1 h2 =
  (case (h1, h2) of
 (Encode e1, Encode e2) \<Rightarrow> X (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2)) \<or> rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force (encode_to_thunk e2))
| (Encode e, Thunk th2) \<Rightarrow> X (Thunk (encode_to_thunk e)) (Thunk th2)
| (Thunk th1, Encode e) \<Rightarrow> X (Thunk th1) (Thunk (encode_to_thunk e))
| (_, _) \<Rightarrow> relaxed_X X h1 h2)"

lemma ref_to_relaxed:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
 assumes X_preserve_tree_ref: "\<And>t h.
    X (HTreeRef t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t'))"
  assumes X_preserve_blob_ref: "\<And>t h.
    X (HBlobRef t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t'))"
  assumes H: "X (Data (Ref r1)) (Data (Ref r2))"
  shows "relaxed_X X (Data (Ref r1)) (Data (Ref r2))"
proof (cases r1)
  case (BlobRef x1)
  then obtain x2 where "r2 = BlobRef x2"
    using H HBlobRef_def 
    using X_preserve_blob_ref by auto
  then show ?thesis
    using BlobRef H HBlobObj_def HBlobRef_def blob_ref_complete  relaxed_X_def 
    by simp
next
  case (TreeRef x1)
  then obtain x2 where "r2 = TreeRef x2"
    using H HTreeRef_def 
    using X_preserve_tree_ref by auto
  then show ?thesis
    using H TreeRef relaxed_X_def tree_ref_complete by force
qed

lemma data_to_relaxed:
 fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
  assumes X_preserve_tree_ref: "\<And>t h.
    X (HTreeRef t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t'))"
  assumes X_preserve_blob_ref: "\<And>t h.
    X (HBlobRef t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t'))"
  assumes X_preserve_tree: "\<And>t h.
    X (HTreeObj t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t'))"
  assumes X_preserve_blob: "\<And>t h.
    X (HBlobObj t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t'))"
  assumes "X (Data d1) (Data d2)"
  shows "relaxed_X X (Data d1) (Data d2)"
proof (cases d1)
  case (Object x1)
  then obtain x2 where "d2 = Object x2"
    by (metis HBlobObj_def HTreeObj_def Object.exhaust X_preserve_blob X_preserve_tree assms(13) handle.inject(1))
  then show ?thesis
    using Object
    using assms(13) relaxed_X_def by fastforce
next
  case (Ref x1)
  then obtain x2 where "d2 = Ref x2"
    by (metis HBlobRef_def HTreeRef_def Ref.exhaust X_preserve_blob_ref X_preserve_tree_ref assms(13) handle.inject(1))
  then show ?thesis
    using Ref ref_to_relaxed assms
    by blast
qed



lemma lower_to_lift:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
 assumes X_preserve_tree_ref: "\<And>t h.
    X (HTreeRef t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t'))"
  assumes X_preserve_blob_ref: "\<And>t h.
    X (HBlobRef t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t'))"
  assumes H: "X (lower (Data d1)) (lower (Data d2))"
  shows "X (lift (Data d1)) (lift (Data d2))"
proof (cases "lower (Data d1)")
  case (Data x1)
  then show ?thesis
  proof (cases x1)
    case (Object x1)
    then show ?thesis
      by (metis Data Data.distinct(1) handle.inject(1) lower.simps(1) lower_data.elims)
  next
    case (Ref x2)
    then show ?thesis
    proof (cases x2)
      case (BlobRef x1)
      then have "Data d1 = HBlobRef x1 \<or> Data d1 = HBlobObj x1"
        using Data Ref
        by (cases d1, case_tac x1b; simp_all)
      then have L1: "lift (Data d1) = HBlobObj x1"
        by fastforce
  
      obtain x2 where L2: "lower (Data d2) = HBlobRef x2"
        using BlobRef Data HBlobRef_def Ref X_preserve_blob_ref H by presburger
      then have "Data d2 = HBlobRef x2 \<or> Data d2 = HBlobObj x2"
        by (cases d2, case_tac x1; simp_all)
      then have "lift (Data d2) = HBlobObj x2"
        by fastforce
  
      then have "X (lift (Data d1)) (lift (Data d2))"
        using BlobRef Data L1 Ref H L2 blob_ref_complete by force
      then show ?thesis by simp
    next
      case (TreeRef x1)
      then have "Data d1 = HTreeRef x1 \<or> Data d1 = HTreeObj x1"
        using Data Ref
        by (cases d1, case_tac x1b; simp_all)
      then have L1: "lift (Data d1) = HTreeObj x1"
        by fastforce
  
      obtain x2 where L2: "lower (Data d2) = HTreeRef x2"
        using TreeRef Data HTreeRef_def Ref X_preserve_tree_ref H by presburger
      then have "Data d2 = HTreeRef x2 \<or> Data d2 = HTreeObj x2"
        by (cases d2, case_tac x1; simp_all)
      then have "lift (Data d2) = HTreeObj x2"
        by fastforce
  
      then have "X (lift (Data d1)) (lift (Data d2))"
        using TreeRef Data L1 Ref H L2 tree_ref_complete by force
      then show ?thesis
        by simp
    qed
  qed
next
  case Thunk then show ?thesis by simp
next
  case Encode then show ?thesis by simp
qed

lemma lift_to_lower:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
 assumes X_preserve_tree: "\<And>t h.
    X (HTreeObj t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t'))"
  assumes X_preserve_blob: "\<And>t h.
    X (HBlobObj t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t'))"
  assumes H: "X (lift (Data d1)) (lift (Data d2))"
  shows "X (lower (Data d1)) (lower (Data d2))"
proof (cases "lift (Data d1)")
  case (Data x1)
  then show ?thesis
  proof (cases x1)
    case (Ref x1)
    then show ?thesis
      by (metis Data Data.distinct(1) handle.inject(1) lift.simps(1) lift_data.elims)
  next
    case (Object x1)
    then show ?thesis
    proof (cases x1)
      case (BlobObj x1)
      then have "Data d1 = HBlobRef x1 \<or> Data d1 = HBlobObj x1"
        using Data Object
        apply (cases d1, case_tac x1c; simp_all)
        using lift_data.elims by auto

      then have L1: "lower (Data d1) = HBlobRef x1"
        by fastforce
  
      obtain x2 where L2: "lift (Data d2) = HBlobObj x2"
        using BlobObj Data HBlobObj_def Object X_preserve_blob H by presburger
      then have "Data d2 = HBlobRef x2 \<or> Data d2 = HBlobObj x2"
        apply (cases d2, case_tac x1; simp_all)
        by (metis Data.inject(1,2) Data.simps(4) Object.simps(4) lift_data.elims lower_data.simps(3))
      then have "lower (Data d2) = HBlobRef x2"
        by fastforce
  
      then have "X (lower (Data d1)) (lower (Data d2))"
        using BlobObj Data H L1 L2 Object blob_ref_cong by force
      then show ?thesis by simp
    next
      case (TreeObj x1)
      then have "Data d1 = HTreeRef x1 \<or> Data d1 = HTreeObj x1"
        using Data Object
        apply (cases d1, case_tac x1c; simp_all)
        using lift_data.elims by auto
      then have L1: "lower (Data d1) = HTreeRef x1"
        by fastforce
  
      obtain x2 where L2: "lift (Data d2) = HTreeObj x2"
        using Data H Object TreeObj X_preserve_tree by auto
      then have "Data d2 = HTreeRef x2 \<or> Data d2 = HTreeObj x2"
        apply (cases d2, case_tac x1; simp_all)
        using lift_data.elims by auto
      then have "lower (Data d2) = HTreeRef x2"
        by fastforce
  
      then have "X (lower (Data d1)) (lower (Data d2))"
        using Data H L1 L2 Object TreeObj tree_ref_cong by auto
      then show ?thesis
        by simp
    qed
  qed
next
  case Thunk then show ?thesis by simp
next
  case Encode then show ?thesis by simp
qed

lemma force_to_lift:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
 assumes X_preserve_tree_ref: "\<And>t h.
    X (HTreeRef t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t'))"
  assumes X_preserve_blob_ref: "\<And>t h.
    X (HBlobRef t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t'))"
  assumes H: "rel_opt X (force e1 <$> lower) (force e2 <$> lower)"
  shows "rel_opt (relaxed_X X) (force e1) (force e2)"
proof (cases "force e1")
  case None
  then show ?thesis
  using H rel_opt.elims(1) by force
next
  case (Some r1)
  then obtain r2 where "force e2 = Some r2"
    using assms by fastforce
  then obtain d1 d2 where D1: "force e1 = Some (Data d1)" and D2: "force e2 = Some (Data d2)"
    using Some force_data assms
    by fastforce
  then have Xlower: "X (lower (Data d1)) (lower (Data d2))"
    using H by auto
  then have "X (lift (Data d1)) (lift (Data d2))"
    using lower_to_lift assms
    by blast
    
  then show ?thesis
    by (simp add: D1 D2 relaxed_X_def)
qed

lemma eq_forces_to_induct:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
  assumes strict_encode_cong: "\<And>t1 t2. X (Thunk t1) (Thunk t2)
                                       \<Longrightarrow> X (Encode (Strict t1)) (Encode (Strict t2))"
  assumes shallow_encode_cong: "\<And>t1 t2. X (Thunk t1) (Thunk t2)
                                        \<Longrightarrow> X (Encode (Shallow t1)) (Encode (Shallow t2))"
  assumes application_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Application t1)) (Thunk (Application t2))"
  assumes selection_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Selection t1)) (Thunk (Selection t2))"
  assumes digestion_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Digestion t1)) (Thunk (Digestion t2))"
  assumes identification_thunk_cong: 
            "\<And> d1 d2. X (Data d1) (Data d2)
                      \<Longrightarrow> X (Thunk (Identification d1)) (Thunk (Identification d2))"
  assumes X_preserve_tree_ref: "\<And>t h.
    X (HTreeRef t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t'))"
  assumes X_preserve_tree_ref_or_encode_rev: "\<And>t h.
    X h (HTreeRef t) \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t')) \<or> (\<exists>t'. h = (Encode (Shallow t')))"
  assumes X_preserve_blob_ref: "\<And>t h.
    X (HBlobRef t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t'))"
  assumes X_preserve_blob_ref_or_encode_rev: "\<And>t h.
    X h (HBlobRef t) \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t')) \<or> (\<exists>t'. h = (Encode (Shallow t')))"
  assumes X_preserve_tree: "\<And>t h.
    X (HTreeObj t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t'))"
  assumes X_preserve_tree_or_encode_rev: "\<And>t h.
    X h (HTreeObj t) \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t')) \<or> (\<exists>t'. h = (Encode (Strict t')))"
  assumes X_preserve_blob: "\<And>t h.
    X (HBlobObj t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t'))"
  assumes X_preserve_blob_or_encode_rev: "\<And>t h.
    X h (HBlobObj t) \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t')) \<or> (\<exists>t'. h = (Encode (Strict t')))"
  assumes X_preserve_thunk: "\<And>h1 h2.
    X h1 h2 \<longrightarrow>
    ((\<exists>t1. h1 = (Thunk t1)) \<longleftrightarrow> (\<exists>t2. h2 = (Thunk t2)))"
  assumes X_encode_eval: "\<And>e h2. 
         X (Encode e) h2 \<Longrightarrow> 
         \<not> (\<exists>e2. h2 = Encode e2) \<Longrightarrow>
         executes_to e h2"
  assumes X_encode_reasons: "\<And>t1 t2. 
         X (Encode (Strict t1)) (Encode (Strict t2)) \<Longrightarrow> 
         X (Thunk t1) (Thunk t2) \<or>
         rel_opt X (execute (Strict t1)) (execute (Strict t2))"
  assumes X_shallow_encode_reasons: "\<And>t1 t2. 
         X (Encode (Shallow t1)) (Encode (Shallow t2)) \<Longrightarrow> 
         X (Thunk t1) (Thunk t2) \<or>
         rel_opt X (execute (Shallow t1)) (execute (Shallow t2))"
  assumes X_not_shallow_strict:
    "\<And> t1 t2. \<not> X (Encode (Shallow t1)) (Encode (Strict t2))"
  assumes X_not_strict_shallow:
    "\<And> t1 t2. \<not> X (Encode (Strict t1)) (Encode (Shallow t2))"
  assumes X_encode_eval_rev_does_not_exist: "\<And>e h1. 
         X h1 (Encode e) \<Longrightarrow> 
         \<not> (\<exists>e1. h1 = Encode e1) \<Longrightarrow>
         False"
  assumes X_thunk_reasons: "\<And>t1 t2. X (Thunk t1) (Thunk t2) \<Longrightarrow> (
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2) \<or>
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2) \<or>
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Digestion tree1 \<and> t2 = Digestion tree2) \<or>
     (\<exists>d1 d2. X (Data d1) (Data d2) \<and> t1 =  Identification d1 \<and> t2 = Identification d2) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> strengthen X r1 r2) \<or>
     (think t1 = Some (Thunk t2))) \<or>
     (think t1 = Some (Encode (Strict t2))) \<or>
     (think t1 = Some (Encode (Shallow t2)))"
  assumes X_self: "\<And>h. X h h"
  assumes E: "X h1 h2"
  shows
    "(
       ((\<exists>t1. h1 = Thunk t1) \<longrightarrow>
        (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v1. think_with_fuel n t1 = Some v1 \<longrightarrow> ((\<exists>v2. thinks_to t2 v2 \<and> strengthen X v1 v2) \<or> v1 = Thunk t2 \<or> v1 = Encode (Strict t2)) \<or> v1 = Encode (Shallow t2))))
      \<and>
       ((\<exists>t2. h2 = Thunk t2) \<longrightarrow>
        (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v2. think_with_fuel n t2 = Some v2 \<longrightarrow> ((\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2) \<or> thinks_to t1 (Thunk t2) \<or> thinks_to t1 (Encode (Strict t2)) \<or> thinks_to t1 (Encode (Shallow t2))))))
      \<and>
       ((\<exists>t1. h1 = Thunk t1) \<longrightarrow>
        (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v1. force_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> strengthen X v1 v2))))
      \<and>
       ((\<exists>t2. h2 = Thunk t2) \<longrightarrow>
        (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v2. force_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> strengthen X v1 v2))))
      \<and> 
        (\<forall>v1. eval_with_fuel n h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
      \<and>
        (\<forall>v2. eval_with_fuel n h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))
  )"
  using E
proof (induction n arbitrary: h1 h2)
  case 0

  have P1: "((\<exists>t1. h1 = Thunk t1) \<longrightarrow> (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v1. think_with_fuel 0 t1 = Some v1 \<longrightarrow> (\<exists>v2. thinks_to t2 v2 \<and> X v1 v2))))"
  proof
    assume ASSM: "\<exists>t1. h1 = Thunk t1" 
    show "\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v1. think_with_fuel 0 t1 = Some v1 \<longrightarrow> (\<exists>v2. thinks_to t2 v2 \<and> X v1 v2))"
    proof -
      obtain t1 where T1: "h1 = Thunk t1"
        using ASSM by auto
      then obtain t2 where T2: "h2 = Thunk t2"
        using 0 T1 X_preserve_thunk by blast
      then show ?thesis using T1 T2 by auto
    qed
  qed

  have P2: "((\<exists>t2. h2 = Thunk t2) \<longrightarrow> (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v2. think_with_fuel 0 t2 = Some v2 \<longrightarrow> (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2))))"
  proof
    assume ASSM: "\<exists>t2. h2 = Thunk t2" 
    show "\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v2. think_with_fuel 0 t2 = Some v2 \<longrightarrow> (\<exists>v1. thinks_to t1 v1 \<and> X v1 v2))"
    proof -
      obtain t2 where T2: "h2 = Thunk t2"
        using ASSM by auto
      then obtain t1 where T1: "h1 = Thunk t1"
        using 0 T2 X_preserve_thunk by blast
      then show ?thesis using T1 T2 by auto
    qed
  qed

  have P3: "(\<exists>t1. h1 = Thunk t1) \<longrightarrow> (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v1. force_with_fuel 0 t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2)))"
  proof
    assume ASSM: "\<exists>t1. h1 = Thunk t1" 
    show "\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v1. force_with_fuel 0 t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> X v1 v2))"
    proof -
      obtain t1 where T1: "h1 = Thunk t1"
        using ASSM by auto
      then obtain t2 where T2: "h2 = Thunk t2"
        using 0 T1 X_preserve_thunk by auto
      then show ?thesis using T1 T2 by auto
    qed
  qed

  have P4: "(\<exists>t2. h2 = Thunk t2) \<longrightarrow> (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v2. force_with_fuel 0 t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1 v2)))"
  proof
    assume ASSM: "\<exists>t2. h2 = Thunk t2" 
    show "\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v2. force_with_fuel 0 t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> X v1 v2))"
    proof -
      obtain t2 where T2: "h2 = Thunk t2"
        using ASSM by auto
      then have "\<exists>t1. h1 = Thunk t1"
        using 0 T2 X_preserve_thunk by blast
      then obtain t1 where T1: "h1 = Thunk t1" by auto
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
      case (Data d)
      then show ?thesis
      proof (cases d)
        case (Ref r1)
        then obtain r2 where "h2 = (Data (Ref r2))"
          by (metis "0" Data HBlobRef_def HTreeRef_def Ref.exhaust X_preserve_blob_ref X_preserve_tree_ref)
        then show ?thesis
          by (metis "0" ASSM Data Data.simps(6) Ref eval_with_fuel.simps(1) evals_to_def handle.simps(10) option.sel)
      next
        case (Object obj)
        then show ?thesis
        proof (cases obj)
          case (BlobObj b1)
          then obtain b2 where B2: "h2 = HBlobObj b2" 
            using "0" Data Object X_preserve_blob by auto
          then have "eval_with_fuel 0 h2 = Some h2" by auto
          then have "evals_to h2 h2" using evals_to_def by blast
          then show ?thesis
            using "0" ASSM BlobObj Data Object by auto
        next
          case (TreeObj t1)
          then show ?thesis
            using ASSM Data Object by force
        qed
      qed
    next
      case (Thunk t1)
      then obtain t2 where T2: "h2 = Thunk t2" using X_preserve_thunk 0 by auto
      then have "eval_with_fuel 0 h2 = Some h2" by auto
      then have E2: "evals_to h2 h2" using evals_to_def by blast

      have "v1 = h1" using ASSM Thunk by auto
      then have "X v1 h2" using 0 by auto
      then show ?thesis using E2 by auto
    next
      case Encode
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
      case (Data d)
      then show ?thesis
      proof (cases d)
        case (Ref r2)
        then have "(\<exists>r. h1 = (Data (Ref r))) \<or> (\<exists>e. h1 = Encode e)" 
          using 0 Data X_preserve_blob_ref_or_encode_rev HTreeRef_def X_preserve_tree_ref_or_encode_rev
          by (cases "r2") fastforce+
        then show ?thesis
        proof
          assume "\<exists>r1. h1 = (Data (Ref r1))"
          then obtain r1 where B1: "h1 = (Data (Ref r1))" by auto
          then show ?thesis
            by (metis "0" ASSM Data Data.simps(6) Ref eval_with_fuel.simps(1) evals_to_def handle.simps(10) option.sel)
        next
          assume "\<exists>e. h1 = Encode e"
          then obtain e where E: "h1 = Encode e" by auto
          then have "executes_to e h2"
            using "0" Data X_encode_eval by blast
          then have "evals_to h1 h2"
            by (simp add: Data E Ref eval_hs eval_some execute_unique)
          moreover have "X h2 h2"
            by (simp add: X_self)
          ultimately show ?thesis
            using ASSM Data Ref by auto
        qed
      next
        case (Object obj)
        then show ?thesis
        proof (cases obj)
          case (BlobObj x1)
          have "(\<exists>b. h1 = HBlobObj b) \<or> (\<exists>e. h1 = Encode e)" 
            using "0" BlobObj Data Object X_preserve_blob_or_encode_rev by auto
          then show ?thesis
          proof
            assume "\<exists>b1. h1 = HBlobObj b1"
            then obtain b1 where B1: "h1 = HBlobObj b1" by auto
            then have "eval_with_fuel 0 h1 = Some h1" by auto
            then have E1: "evals_to h1 h1" using evals_to_def by blast
            then show ?thesis
              using "0" ASSM BlobObj Data Object by auto
          next
            assume "\<exists>e. h1 = Encode e"
            then obtain e where E: "h1 = Encode e" by auto
            then have "executes_to e h2"
              using "0" Data X_encode_eval by blast
            then have "evals_to h1 h2"
              by (simp add: BlobObj Data E Object eval_hs eval_some execute_unique)
            moreover have "X h2 h2"
              by (simp add: X_self)
            ultimately show ?thesis
              using ASSM BlobObj Data Object by auto
          qed
        next
          case (TreeObj t2)
          then show ?thesis
            using ASSM Data Object by force
        qed
      qed
    next
      case (Thunk t2)
      then have "\<exists>t1. h1 = Thunk t1"
        using P2 by blast
      then obtain t1 where T1: "h1 = Thunk t1" by auto
      then have "eval_with_fuel 0 h1 = Some h1" by auto
      then have E1: "evals_to h1 h1" using evals_to_def by blast

      have "v2 = h2" using ASSM Thunk by auto
      then have "X h1 v2" using 0 by auto
      then show ?thesis using E1 by auto
    next
      case (Encode e)
      then show ?thesis using ASSM by auto
    qed
  qed

  show ?case using P1 P2 P3 P4 P5 P6 by auto
next
  case (Suc f')

  have X_preserve_value_handle: "\<And>h1 h2. 
         X h1 h2 \<Longrightarrow> 
         \<not> (\<exists>e. h1 = Encode e) \<Longrightarrow>
         \<not> (\<exists>e. h2 = Encode e) \<Longrightarrow>
         ((\<exists>b. h1 = HBlobObj b) \<longleftrightarrow> (\<exists>b. h2 = HBlobObj b))
       \<and> ((\<exists>t. h1 = HTreeObj t) \<longleftrightarrow> (\<exists>t. h2 = HTreeObj t))
       \<and> ((\<exists>b. h1 = HBlobRef b) \<longleftrightarrow> (\<exists>b. h2 = HBlobRef b))
       \<and> ((\<exists>t. h1 = HTreeRef t) \<longleftrightarrow> (\<exists>t. h2 = HTreeRef t))
       \<and> ((\<exists>th. h1 =  Thunk th) \<longleftrightarrow> (\<exists>th. h2 = Thunk th))"  
    by (meson X_preserve_blob X_preserve_blob_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_thunk X_preserve_tree
        X_preserve_tree_or_encode_rev X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev)

  have eval_cong_f': "\<And>h1 h2. X h1 h2 \<Longrightarrow>
      (\<forall>v1. eval_with_fuel f' h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
     \<and>
      (\<forall>v2. eval_with_fuel f' h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))"
    using Suc.IH by blast

  have relevant_IH_think:
      "\<And>h1 h2. X h1 h2 \<Longrightarrow>
       ((\<exists>t1. h1 = Thunk t1) \<longrightarrow>
         (\<exists>t1 t2.
             h1 = Thunk t1 \<and>
             h2 = Thunk t2 \<and>
             (\<forall>v1. think_with_fuel f' t1 = Some v1 \<longrightarrow>
                   (\<exists>v2. thinks_to t2 v2 \<and> strengthen X v1 v2) \<or>
                   v1 = Thunk t2 
                   \<or> v1 = Encode (Strict t2)
                   \<or> v1 = Encode (Shallow t2)))) \<and>
        ((\<exists>t2. h2 = Thunk t2) \<longrightarrow>
         (\<exists>t1 t2.
             h1 = Thunk t1 \<and>
             h2 = Thunk t2 \<and>
             (\<forall>v2. think_with_fuel f' t2 = Some v2 \<longrightarrow>
                   (\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2) \<or>
                   thinks_to t1 (Thunk t2)
                   \<or> thinks_to t1 (Encode (Strict t2))
                   \<or> thinks_to t1 (Encode (Shallow t2)))))"
      using Suc.IH by blast

  have relevant_IH_force:
      "\<And>h1 h2. X h1 h2 \<Longrightarrow>
      ((\<exists>t1. h1 = Thunk t1) \<longrightarrow>
         (\<exists>t1 t2.
             h1 = Thunk t1 \<and>
             h2 = Thunk t2 \<and>
             (\<forall>v1. force_with_fuel f' t1 =
                   Some v1 \<longrightarrow>
                   (\<exists>v2. forces_to t2 v2 \<and>
                         strengthen X v1 v2)))) \<and>
        ((\<exists>t2. h2 = Thunk t2) \<longrightarrow>
         (\<exists>t1 t2.
             h1 = Thunk t1 \<and>
             h2 = Thunk t2 \<and>
             (\<forall>v2. force_with_fuel f' t2 =
                   Some v2 \<longrightarrow>
                   (\<exists>v1. forces_to t1 v1 \<and>
                         strengthen X v1 v2))))"
      using Suc.IH by blast

  show ?case
  proof (intro conjI impI)
    assume "\<exists>t1. h1 = Thunk t1"
    then obtain t1 where T1: "h1 = Thunk t1" by auto
    then obtain t2 where T2: "h2 = Thunk t2" 
      using Suc.prems X_preserve_thunk by blast

    let ?case1 = "\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2"
    let ?case2 = "\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2"
    let ?case3 = "\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Digestion tree1 \<and> t2 = Digestion tree2"
    let ?case4 = "(\<exists>d1 d2. X (Data d1) (Data d2) \<and> t1 =  Identification d1 \<and> t2 = Identification d2)"
    let ?case5 = "think t1 = None \<and> think t2 = None"
    let ?case6 = "\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> strengthen X r1 r2"
    let ?case7 = "think t1 = Some (Thunk t2)"
    let ?case8 = "think t1 = Some (Encode (Strict t2))"
    let ?case9 = "think t1 = Some (Encode (Shallow t2))"

    have All: "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4 \<or> ?case5 \<or> ?case6 \<or> ?case7 \<or> ?case8 \<or> ?case9"
      using X_thunk_reasons[of t1 t2]
      using Suc.prems T1 T2 
      by argo

    let ?endgoal = "
       (\<forall>v1. think_with_fuel (Suc f') t1 =
             Some v1 \<longrightarrow>
             ((\<exists>v2. thinks_to t2 v2 \<and>
                    strengthen X v1 v2) \<or>
              v1 = Thunk t2 \<or>
              v1 = Encode (Strict t2) \<or>
             v1 = Encode (Shallow t2)))"

    have "?case1 \<longrightarrow> ?endgoal"
    proof (intro allI impI)
      fix v1
      assume EQTREE: "?case1"
      assume Think: "think_with_fuel (Suc f') t1 = Some v1"
      show "(\<exists>v2. thinks_to t2 v2 \<and>
                 strengthen X v1 v2) \<or>
           v1 = Thunk t2 \<or>
           v1 = Encode (Strict t2) \<or>
           v1 = Encode (Shallow t2)"
      proof
        obtain tree1 tree2 where EQTREE: "X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2"
          using EQTREE by blast

        then obtain tree' where EVTree1: "eval_tree_with_fuel f' tree1 = Some tree'"
                          and   Apply1: "apply_tree tree' = Some v1"
          by (metis (no_types, lifting) Think Thunk.simps(17) option.case_eq_if option.distinct(1) option.exhaust_sel think_with_fuel.simps(2))
        
        then obtain tree2' where EVTree2: "evals_tree_to tree2 tree2'"
                           and  EQApplyTree: "X (HTreeObj tree') (HTreeObj tree2')"
          using eq_tree_eval_fuel_n[OF tree_cong tree_complete] EQTREE eval_cong_f'
          by blast

        have VH1: "value_handle (HTreeObj tree')"
          using EVTree1 eval_with_fuel_to_value_handle
          by (metis Data.simps(5) Object.simps(6) eval_with_fuel.simps(2) handle.simps(10) option.simps(9))

        have VH2: "value_handle (HTreeObj tree2')"
          using EVTree2 eval_tree_to_value_handle
          using eval_tree_unique by blast

        have sametyped: "same_typed_tree tree' tree2'"
          using VH1 VH2 EQApplyTree tree_cong X_preserve_value_handle value_tree_to_sametypedness
          using value_handle.simps 
          by force

        have "rel_opt X (apply_tree tree') (apply_tree tree2') \<and> rel_opt same_typed_handle (apply_tree tree') (apply_tree tree2')"
          using apply_tree_X[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete strict_encode_cong shallow_encode_cong application_thunk_cong selection_thunk_cong digestion_thunk_cong identification_thunk_cong] sametyped EQApplyTree          
          by auto

        then obtain v2 where Apply2: "apply_tree tree2' = Some v2" 
                         and EQOUT: "X v1 v2"
                         and SAMETYPEOUT: "same_typed_handle v1 v2"
          using Apply1
          using rel_opt.elims(1) by force

        then have "thinks_to t2 v2"
          using EQTREE EVTree2 eval_tree_unique think_hs think_some by auto

        from SAMETYPEOUT
        have EQOUT: "strengthen X v1 v2"
        proof (cases)
          case (blob_obj b1 b2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def by force
        next
          case (blob_ref b1 b2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def blob_ref_complete 
            by force
        next
          case (tree_obj t1 t2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def
            by simp
        next
          case (tree_ref t1 t2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def tree_ref_complete 
            by force
        next
          case (thunk th1 th2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def
            by simp
        next
          case (encode_shallow e1 e2)
          have "X (Thunk e1) (Thunk e2) \<or> rel_opt X (execute (Shallow e1)) (execute (Shallow e2))"
            using EQOUT X_shallow_encode_reasons local.encode_shallow(1,2) by blast
          then show ?thesis
          proof 
            assume "X (Thunk e1) (Thunk e2)"
            then show "strengthen X v1 v2"
              using EQOUT relaxed_X_def strengthen_def encode_shallow
              by simp
          next
            assume "rel_opt X (execute (Shallow e1)) (execute (Shallow e2))"
            then have "rel_opt X (force e1 <$> lower) (force e2 <$> lower)"
              using execute_hs by simp
            then have "rel_opt (relaxed_X X) (force e1) (force e2)"
              using force_to_lift[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_blob_ref]
              by blast
            then show "strengthen X v1 v2"
              using EQOUT relaxed_X_def strengthen_def encode_shallow execute_hs
              by simp
          qed
        next
          case (encode_strict e1 e2)
          then have "X (Thunk e1) (Thunk e2) \<or> rel_opt X (execute (Strict e1)) (execute (Strict e2))"
            using EQOUT X_encode_reasons by blast
          then show ?thesis
          proof 
            assume "X (Thunk e1) (Thunk e2)"
            then show "strengthen X v1 v2"
              using EQOUT relaxed_X_def strengthen_def encode_strict
              by simp
          next
            assume "rel_opt X (execute (Strict e1)) (execute (Strict e2))"
            then have rel_lift: "rel_opt X (force e1 <$> lift) (force e2 <$> lift)"
              using execute_hs by simp
            then have "rel_opt (relaxed_X X) (force e1) (force e2)"
            proof (cases "force e1")
              case None
              then show ?thesis
                using rel_lift
                by (metis None_eq_map_option_iff option.distinct(1) rel_opt.elims(2) rel_opt.simps(1))
            next
              case (Some r1)
              then obtain d1 where D1: "force e1 = Some (Data d1)"
                using force_data by blast
              moreover obtain d2 where D2: "force e2 = Some (Data d2)"
                using force_data rel_lift Some
                by (metis None_eq_map_option_iff option.exhaust_sel rel_opt.elims(2))
              ultimately have "X (lift (Data d1)) (lift (Data d2))"
                using rel_lift by simp
              then have "relaxed_X X (Data d1) (Data d2)"
                using relaxed_X_def
                by simp
              then show ?thesis
                using D1 D2 by simp
            qed
            then show "strengthen X v1 v2"
              using EQOUT relaxed_X_def strengthen_def encode_strict execute_hs
              by simp
          qed
        qed

        then show "(\<exists>v2. thinks_to t2 v2 \<and>
                 strengthen X v1 v2)" 
          using EQOUT
          using \<open>thinks_to t2 v2\<close> by blast
       qed
     qed

     moreover have "?case2 \<longrightarrow> ?endgoal"
     proof (intro allI impI)
       fix v1
       assume EQTREE: "?case2"
       assume Think: "think_with_fuel (Suc f') t1 = Some v1"
       show "(\<exists>v2. thinks_to t2 v2 \<and>
                  strengthen X v1 v2) \<or>
            v1 = Thunk t2 \<or>
            v1 = Encode (Strict t2) \<or>
            v1 = Encode (Shallow t2)"
       proof
         obtain tree1 tree2 where EQTREE: "X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2"
           using EQTREE by blast
      
         then obtain tree' r1 where EVTree1: "eval_tree_with_fuel f' tree1 = Some tree'"
                              and   Slice1: "slice tree' = Some r1"
                              and   Result1: "v1 = (Data (Ref r1))"
           by (smt (verit, best) Think Thunk.simps(19)
               map_option_eq_Some option.case_eq_if option.exhaust_sel
               option.simps(3) think_with_fuel.simps(2))
         
         then obtain tree2' where EVTree2: "evals_tree_to tree2 tree2'"
                            and  EQApplyTree: "X (HTreeObj tree') (HTreeObj tree2')"
           using eq_tree_eval_fuel_n[OF tree_cong tree_complete] EQTREE eval_cong_f'
           by blast
      
         have "list_all not_encode (get_tree_raw tree')"
           using eval_tree_to_not_encode EVTree1
           using eval_tree_unique evals_tree_to_def by blast
         moreover have "list_all not_encode (get_tree_raw tree2')"
           using eval_tree_to_not_encode EVTree2 eval_tree_unique evals_tree_to_def
           by blast
         ultimately have "rel_opt (\<lambda>x y. X (Data (Ref x)) (Data (Ref y))) (slice tree') (slice tree2')"
           using slice_X[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev X_preserve_thunk] EQApplyTree
           by blast
         then obtain r2 where R2: "slice tree2' = Some r2"
                          and "X (Data (Ref r1)) (Data (Ref r2))"
           by (metis Slice1 not_Some_eq rel_opt.simps(2,3))
         then have "relaxed_X X (Data (Ref r1)) (Data (Ref r2))"
           using ref_to_relaxed[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_blob_ref]
           by blast
         then have "strengthen X (Data (Ref r1)) (Data (Ref r2))"
           using strengthen_def
           by simp
         moreover have "thinks_to t2 (Data (Ref r2))"
           using EQTREE EVTree2 eval_tree_unique think_hs think_some R2 by auto
         ultimately show "(\<exists>v2. thinks_to t2 v2 \<and> strengthen X v1 v2)"
           using Result1 by blast
       qed
     qed

     moreover have "?case3 \<longrightarrow> ?endgoal"
     proof (intro allI impI)
       fix v1
       assume "?case3"
       then obtain tree1 tree2 where EQTREE: "X (HTreeObj tree1) (HTreeObj tree2)"
                               and   T1: "t1 = Digestion tree1"
                               and   T2: "t2 = Digestion tree2"
         by auto
       assume Think: "think_with_fuel (Suc f') t1 = Some v1"
       show "(\<exists>v2. thinks_to t2 v2 \<and>
                  strengthen X v1 v2) \<or>
            v1 = Thunk t2 \<or>
            v1 = Encode (Strict t2) \<or>
            v1 = Encode (Shallow t2)"
       proof 
         obtain tree1' where EVTree1: "eval_tree_with_fuel f' tree1 = Some tree1'"
           using Think T1
           by fastforce
         then obtain r1 where Slice1: "slice tree1' = Some (TreeRef r1)"
           by (metis (no_types, lifting) Ref.exhaust Ref.simps(5) T1 Think Thunk.simps(20) option.case_eq_if
               option.distinct(1) option.exhaust_sel option.sel think_with_fuel.simps(2))
         then obtain tree1'' where EVR1: "eval_tree_with_fuel f' r1 = Some tree1''"
           using EVTree1 T1 Think by fastforce
         then have V1: "v1 = HTreeObj (digest tree1'')"
           using EVTree1 Slice1 T1 Think by fastforce

         obtain tree2' where EVTree2: "evals_tree_to tree2 tree2'"
                           and  EQApplyTree: "X (HTreeObj tree1') (HTreeObj tree2')"
          using eq_tree_eval_fuel_n[OF tree_cong tree_complete] EQTREE eval_cong_f' EVTree1
          by blast

         have "list_all not_encode (get_tree_raw tree1')"
           using eval_tree_to_not_encode EVTree1
           using eval_tree_unique evals_tree_to_def by blast
         moreover have "list_all not_encode (get_tree_raw tree2')"
           using eval_tree_to_not_encode EVTree2 eval_tree_unique evals_tree_to_def
           by blast
         ultimately have "rel_opt (\<lambda>x y. X (Data (Ref x)) (Data (Ref y))) (slice tree1') (slice tree2')"
           using slice_X[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev X_preserve_thunk] EQApplyTree
           by blast
         then obtain r2' where "slice tree2' = Some r2'"
                          and "X (HTreeRef r1) (Data (Ref r2'))"
           using Slice1 
           by (metis HTreeRef_def option.distinct(1) option.inject rel_opt.elims(2))
         then obtain r2 where Slice2: "slice tree2' = Some (TreeRef r2)"
                          and relslice: "X (HTreeRef r1) (HTreeRef r2)"
           using X_preserve_tree_ref by auto
         then obtain tree2'' where EVR2: "evals_tree_to r2 tree2''"
                             and   relR: "X (HTreeObj tree1'') (HTreeObj tree2'')"
           using eq_tree_eval_fuel_n[OF tree_cong tree_complete] eval_cong_f' EVR1 tree_ref_complete
           by blast
         then have Think2: "thinks_to t2 (HTreeObj (digest tree2''))"
           using EVTree2 Slice2 T2 eval_tree_unique think_hs think_some by auto

         have "list_all not_encode (get_tree_raw tree1'')"
           using EVR1
           using eval_tree_to_not_encode eval_tree_unique evals_tree_to_def by blast
         moreover have "list_all not_encode (get_tree_raw tree2'')"
           using EVR2
           using eval_tree_to_not_encode eval_tree_unique by blast
         ultimately have "X (HTreeObj (digest tree1'')) (HTreeObj (digest tree2''))"
           using digest_X[OF blob_cong tree_cong blob_complete tree_complete X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev
           X_preserve_thunk X_self] relR
           by (simp add: digest.not_encode_def list_all_length slice.not_encode_def)
         then show "(\<exists>v2. thinks_to t2 v2 \<and> strengthen X v1 v2)"
           using Think2 V1 strengthen_def relaxed_X_def HTreeObj_def
           by auto
       qed
     qed

     moreover have "?case4 \<longrightarrow> ?endgoal"
     proof (intro allI impI)
       fix v1
       assume "?case4"
       then obtain d1 d2 where EQTREE: "X (Data d1) (Data d2)"
                               and   T1: "t1 = Identification d1"
                               and   T2: "t2 = Identification d2"
         by auto
       assume Think: "think_with_fuel (Suc f') t1 = Some v1"
       show "(\<exists>v2. thinks_to t2 v2 \<and>
                  strengthen X v1 v2) \<or>
            v1 = Thunk t2 \<or>
            v1 = Encode (Strict t2) \<or>
            v1 = Encode (Shallow t2)"
       proof
         have Data1: "v1 = Data d1"
           using T1 Think by force
         moreover have "rel_opt X (identify d1) (identify d2)"
           using EQTREE by force
         ultimately obtain v2 where Data2: "v2 = Data d2" and "X v1 v2"
           by simp
         then have "strengthen X v1 v2"
           using strengthen_def data_to_relaxed[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_blob_ref X_preserve_tree X_preserve_blob] Data1 Data2
           by simp

         then show "\<exists>v2. thinks_to t2 v2 \<and> strengthen X v1 v2"
           by (metis Data2 T2 Thunk.simps(18) identify.elims think_hs think_some)
       qed
     qed

     moreover have "?case5 \<longrightarrow> ?endgoal"
       by (metis option.discI think_unique thinks_to_def)

     moreover have "?case6 \<longrightarrow> ?endgoal"
       by (metis option.sel think_some think_unique thinks_to_def)

     moreover have "?case7 \<longrightarrow> ?endgoal"
       using think_some thinks_to_def thinks_to_deterministic
       by blast

     moreover have "?case8 \<longrightarrow> ?endgoal"
       using think_deterministic think_unique thinks_to_def by blast

     moreover have "?case9 \<longrightarrow> ?endgoal"
       using think_deterministic think_unique thinks_to_def by blast

     ultimately have "?endgoal"
       using All
       by argo

     then show "\<exists>t1 t2.
       h1 = Thunk t1 \<and>
       h2 = Thunk t2 \<and>
       (\<forall>v1. think_with_fuel (Suc f') t1 =
             Some v1 \<longrightarrow>
             ((\<exists>v2. thinks_to t2 v2 \<and>
                    strengthen X v1 v2) \<or>
              v1 = Thunk t2 \<or>
              v1 = Encode (Strict t2)) \<or>
             v1 = Encode (Shallow t2))"
       using T1 T2
       by blast
  next
    assume "\<exists>t2. h2 = Thunk t2"
    then obtain t2 where T2: "h2 = Thunk t2" by auto
    then obtain t1 where T1: "h1 = Thunk t1"
      using Suc.prems X_preserve_thunk by blast

    let ?case1 = "\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2"
    let ?case2 = "\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2"
    let ?case3 = "\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Digestion tree1 \<and> t2 = Digestion tree2"
    let ?case4 = "(\<exists>d1 d2. X (Data d1) (Data d2) \<and> t1 =  Identification d1 \<and> t2 = Identification d2)"
    let ?case5 = "think t1 = None \<and> think t2 = None"
    let ?case6 = "\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> strengthen X r1 r2"
    let ?case7 = "think t1 = Some (Thunk t2)"
    let ?case8 = "think t1 = Some (Encode (Strict t2))"
    let ?case9 = "think t1 = Some (Encode (Shallow t2))"

    have All: "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4 \<or> ?case5 \<or> ?case6 \<or> ?case7 \<or> ?case8 \<or> ?case9"
      using X_thunk_reasons[of t1 t2]
      using Suc.prems T1 T2 
      by argo

    let ?endgoal = 
      "(\<forall>v2. think_with_fuel (Suc f') t2 = Some v2 \<longrightarrow>
         (\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2) \<or>
             thinks_to t1 (Thunk t2) \<or>
             thinks_to t1 (Encode (Strict t2)) \<or>
             thinks_to t1 (Encode (Shallow t2)))"

    have "?case1 \<longrightarrow> ?endgoal"
    proof (intro allI impI)
      fix v2
      assume EQTREE: "?case1"
      assume Think2: "think_with_fuel (Suc f') t2 = Some v2"
      show "(\<exists>v1. thinks_to t1 v1 \<and>
                 strengthen X v1 v2) \<or>
             thinks_to t1 (Thunk t2) \<or>
             thinks_to t1 (Encode (Strict t2)) \<or>
             thinks_to t1 (Encode (Shallow t2))"
      proof
        obtain tree1 tree2 where EQTREE: "X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2"
          using EQTREE by blast

        then obtain tree2' where EVTree2: "eval_tree_with_fuel f' tree2 = Some tree2'"
                          and   Apply2: "apply_tree tree2' = Some v2"
          by (metis (no_types, lifting) Think2 Thunk.simps(17) option.case_eq_if option.distinct(1) option.exhaust_sel think_with_fuel.simps(2))
        
        then obtain tree' where EVTree1: "evals_tree_to tree1 tree'"
                           and  EQApplyTree: "X (HTreeObj tree') (HTreeObj tree2')"
          using eq_tree_eval_fuel_n[OF tree_cong tree_complete] EQTREE eval_cong_f'
          by blast

        have VH1: "value_handle (HTreeObj tree')"
          using EVTree1 eval_with_fuel_to_value_handle
          using eval_tree_to_value_handle eval_tree_unique by blast

        have VH2: "value_handle (HTreeObj tree2')"
          using EVTree2 eval_with_fuel_to_value_handle
          using eval_tree_to_value_handle eval_tree_unique evals_tree_to_def by blast

        have sametyped: "same_typed_tree tree' tree2'"
          using VH1 VH2 EQApplyTree tree_cong X_preserve_value_handle value_tree_to_sametypedness
          using value_handle.simps 
          by force

        have "rel_opt X (apply_tree tree') (apply_tree tree2') \<and> rel_opt same_typed_handle (apply_tree tree') (apply_tree tree2')"
          using apply_tree_X[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete strict_encode_cong shallow_encode_cong application_thunk_cong selection_thunk_cong digestion_thunk_cong identification_thunk_cong] sametyped EQApplyTree          
          by auto

        then obtain v1 where Apply1: "apply_tree tree' = Some v1" 
                         and EQOUT: "X v1 v2"
                         and SAMETYPEOUT: "same_typed_handle v1 v2"
          using Apply2
          using rel_opt.elims(1) by force

        then have Think1: "thinks_to t1 v1"
          using EQTREE EVTree1 eval_tree_unique think_hs think_some by auto

        from SAMETYPEOUT
        have EQOUT: "strengthen X v1 v2"
        proof (cases)
          case (blob_obj b1 b2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def by force
        next
          case (blob_ref b1 b2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def blob_ref_complete 
            by force
        next
          case (tree_obj t1 t2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def
            by simp
        next
          case (tree_ref t1 t2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def tree_ref_complete 
            by force
        next
          case (thunk th1 th2)
          then show ?thesis
            using EQOUT relaxed_X_def strengthen_def
            by simp
        next
          case (encode_shallow e1 e2)
          have "X (Thunk e1) (Thunk e2) \<or> rel_opt X (execute (Shallow e1)) (execute (Shallow e2))"
            using EQOUT X_shallow_encode_reasons local.encode_shallow(1,2) by blast
          then show ?thesis
          proof 
            assume "X (Thunk e1) (Thunk e2)"
            then show "strengthen X v1 v2"
              using EQOUT relaxed_X_def strengthen_def encode_shallow
              by simp
          next
            assume "rel_opt X (execute (Shallow e1)) (execute (Shallow e2))"
            then have "rel_opt X (force e1 <$> lower) (force e2 <$> lower)"
              using execute_hs by simp
            then have "rel_opt (relaxed_X X) (force e1) (force e2)"
              using force_to_lift[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_blob_ref]
              by blast
            then show "strengthen X v1 v2"
              using EQOUT relaxed_X_def strengthen_def encode_shallow execute_hs
              by simp
          qed
        next
          case (encode_strict e1 e2)
          then have "X (Thunk e1) (Thunk e2) \<or> rel_opt X (execute (Strict e1)) (execute (Strict e2))"
            using EQOUT X_encode_reasons by blast
          then show ?thesis
          proof 
            assume "X (Thunk e1) (Thunk e2)"
            then show "strengthen X v1 v2"
              using EQOUT relaxed_X_def strengthen_def encode_strict
              by simp
          next
            assume "rel_opt X (execute (Strict e1)) (execute (Strict e2))"
            then have rel_lift: "rel_opt X (force e1 <$> lift) (force e2 <$> lift)"
              using execute_hs by simp
            then have "rel_opt (relaxed_X X) (force e1) (force e2)"
            proof (cases "force e1")
              case None
              then show ?thesis
                using rel_lift
                by (metis None_eq_map_option_iff option.distinct(1) rel_opt.elims(2) rel_opt.simps(1))
            next
              case (Some r1)
              then obtain d1 where D1: "force e1 = Some (Data d1)"
                using force_data by blast
              moreover obtain d2 where D2: "force e2 = Some (Data d2)"
                using force_data rel_lift Some
                by (metis None_eq_map_option_iff option.exhaust_sel rel_opt.elims(2))
              ultimately have "X (lift (Data d1)) (lift (Data d2))"
                using rel_lift by simp
              then have "relaxed_X X (Data d1) (Data d2)"
                using relaxed_X_def
                by simp
              then show ?thesis
                using D1 D2 by simp
            qed
            then show "strengthen X v1 v2"
              using EQOUT relaxed_X_def strengthen_def encode_strict execute_hs
              by simp
          qed
        qed

        then show "(\<exists>v1. thinks_to t1 v1 \<and>
                 strengthen X v1 v2)" 
          using EQOUT Think1
          by blast
       qed
     qed

     moreover have "?case2 \<longrightarrow> ?endgoal"
     proof (intro allI impI)
       fix v2
       assume EQTREE: "?case2"
       assume Think: "think_with_fuel (Suc f') t2 = Some v2"
       show "(\<exists>v1. thinks_to t1 v1 \<and>
                 strengthen X v1 v2) \<or>
             thinks_to t1 (Thunk t2) \<or>
             thinks_to t1 (Encode (Strict t2)) \<or>
             thinks_to t1 (Encode (Shallow t2))"
       proof
         obtain tree1 tree2 where EQTREE: "X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2"
           using EQTREE by blast
      
         then obtain tree2' r2 where EVTree2: "eval_tree_with_fuel f' tree2 = Some tree2'"
                              and   Slice2: "slice tree2' = Some r2"
                              and   Result2: "v2 = (Data (Ref r2))"
           by (smt (verit, best) Think Thunk.simps(19)
               map_option_eq_Some option.case_eq_if option.exhaust_sel
               option.simps(3) think_with_fuel.simps(2))
         
         then obtain tree1' where EVTree1: "evals_tree_to tree1 tree1'"
                            and  EQApplyTree: "X (HTreeObj tree1') (HTreeObj tree2')"
           using eq_tree_eval_fuel_n[OF tree_cong tree_complete] EQTREE eval_cong_f'
           by blast
      
         have "list_all not_encode (get_tree_raw tree1')"
           using eval_tree_to_not_encode EVTree1
           using eval_tree_unique evals_tree_to_def by blast
         moreover have "list_all not_encode (get_tree_raw tree2')"
           using eval_tree_to_not_encode EVTree2 eval_tree_unique evals_tree_to_def
           by blast
         ultimately have "rel_opt (\<lambda>x y. X (Data (Ref x)) (Data (Ref y))) (slice tree1') (slice tree2')"
           using slice_X[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev X_preserve_thunk] EQApplyTree
           by blast
         then obtain r1 where R1: "slice tree1' = Some r1"
                          and "X (Data (Ref r1)) (Data (Ref r2))"
           by (metis Slice2 option.exhaust_sel rel_opt.simps(2,4))

         then have "relaxed_X X (Data (Ref r1)) (Data (Ref r2))"
           using ref_to_relaxed[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_blob_ref]
           by blast
         
         then have "strengthen X (Data (Ref r1)) (Data (Ref r2))"
           using strengthen_def
           by simp
      
         moreover then have "thinks_to t1 (Data (Ref r1))"
           using EQTREE EVTree1 eval_tree_unique think_hs think_some R1 by auto
         ultimately show "(\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2)"
           using Result2 by blast
       qed
     qed

     moreover have "?case3 \<longrightarrow> ?endgoal"
     proof (intro allI impI)
       fix v2
       assume "?case3"
       then obtain tree1 tree2 where EQTREE: "X (HTreeObj tree1) (HTreeObj tree2)"
                               and   T1: "t1 = Digestion tree1"
                               and   T2: "t2 = Digestion tree2"
         by auto
       assume Think2: "think_with_fuel (Suc f') t2 = Some v2"
       show "(\<exists>v1. thinks_to t1 v1 \<and>
                 strengthen X v1 v2) \<or>
             thinks_to t1 (Thunk t2) \<or>
             thinks_to t1 (Encode (Strict t2)) \<or>
             thinks_to t1 (Encode (Shallow t2))"
       proof 
         obtain tree2' where EVTree2: "eval_tree_with_fuel f' tree2 = Some tree2'"
           using Think2 T2
           by fastforce
         then obtain r2 where Slice2: "slice tree2' = Some (TreeRef r2)"
           using T2 Think2
           by (metis (no_types, lifting) Ref.exhaust Ref.simps(5) Thunk.simps(20) option.case_eq_if option.distinct(1)
               option.exhaust option.sel think_with_fuel.simps(2))
         then obtain tree2'' where EVR2: "eval_tree_with_fuel f' r2 = Some tree2''"
           using EVTree2 T2 Think2 by fastforce
         then have V2: "v2 = HTreeObj (digest tree2'')"
           using EVTree2 Slice2 T2 Think2 by fastforce

         obtain tree1' where EVTree1: "evals_tree_to tree1 tree1'"
                           and  EQApplyTree: "X (HTreeObj tree1') (HTreeObj tree2')"
          using eq_tree_eval_fuel_n[OF tree_cong tree_complete] EQTREE eval_cong_f' EVTree2
          by blast

         have "list_all not_encode (get_tree_raw tree1')"
           using eval_tree_to_not_encode EVTree1
           using eval_tree_unique evals_tree_to_def by blast
         moreover have "list_all not_encode (get_tree_raw tree2')"
           using eval_tree_to_not_encode EVTree2 eval_tree_unique evals_tree_to_def
           by blast
         ultimately have "rel_opt (\<lambda>x y. X (Data (Ref x)) (Data (Ref y))) (slice tree1') (slice tree2')"
           using slice_X[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev X_preserve_thunk] EQApplyTree
           by blast
         then obtain r1' where "slice tree1' = Some r1'"
                          and "X (Data (Ref r1')) (HTreeRef r2)"
           using Slice2
           by (metis HTreeRef_def option.distinct(1) option.inject rel_opt.elims(2))
         then obtain r1 where Slice1: "slice tree1' = Some (TreeRef r1)"
                          and relslice: "X (HTreeRef r1) (HTreeRef r2)"
           using X_preserve_tree_ref
           by (metis Data.inject(2) HTreeRef_def X_preserve_tree_ref_or_encode_rev handle.distinct(3)
               handle.inject(1))
         then obtain tree1'' where EVR1: "evals_tree_to r1 tree1''"
                             and   relR: "X (HTreeObj tree1'') (HTreeObj tree2'')"
           using eq_tree_eval_fuel_n[OF tree_cong tree_complete] eval_cong_f' EVR2 tree_ref_complete
           by blast
         then have Think1: "thinks_to t1 (HTreeObj (digest tree1''))"
           using EVTree1 Slice1 T1 eval_tree_unique think_hs think_some by auto

         have "list_all not_encode (get_tree_raw tree1'')"
           using EVR1
           using eval_tree_to_not_encode eval_tree_unique evals_tree_to_def by blast
         moreover have "list_all not_encode (get_tree_raw tree2'')"
           using EVR2
           using eval_tree_to_not_encode eval_tree_unique 
           using evals_tree_to_def by blast
         ultimately have "X (HTreeObj (digest tree1'')) (HTreeObj (digest tree2''))"
           using digest_X[OF blob_cong tree_cong blob_complete tree_complete X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev
           X_preserve_thunk X_self] relR
           by (simp add: digest.not_encode_def list_all_length slice.not_encode_def)
         then show "(\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2)"
           using Think1 V2 strengthen_def relaxed_X_def HTreeObj_def
           by auto
       qed
     qed

     moreover have "?case4 \<longrightarrow> ?endgoal"
     proof (intro allI impI)
       fix v2
       assume "?case4"
       then obtain d1 d2 where EQTREE: "X (Data d1) (Data d2)"
                               and   T1: "t1 = Identification d1"
                               and   T2: "t2 = Identification d2"
         by auto
       assume Think2: "think_with_fuel (Suc f') t2 = Some v2"
       show "(\<exists>v1. thinks_to t1 v1 \<and>
                 strengthen X v1 v2) \<or>
             thinks_to t1 (Thunk t2) \<or>
             thinks_to t1 (Encode (Strict t2)) \<or>
             thinks_to t1 (Encode (Shallow t2))"
       proof
         have Data2: "v2 = Data d2"
           using T2 Think2 by force
         moreover have "rel_opt X (identify d1) (identify d2)"
           using EQTREE by force
         ultimately obtain v1 where Data1: "v1 = Data d1" and "X v1 v2"
           by simp
         then have "strengthen X v1 v2"
          using strengthen_def data_to_relaxed[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree_ref X_preserve_blob_ref X_preserve_tree X_preserve_blob] Data1 Data2
          by simp
         then show "\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2"
           by (metis Data1 T1 Thunk.simps(18) identify.simps think_hs think_some)
       qed
     qed

     moreover have "?case5 \<longrightarrow> ?endgoal"
       by (metis option.discI think_unique thinks_to_def)

     moreover have "?case6 \<longrightarrow> ?endgoal"
       by (metis option.sel think_some think_unique thinks_to_def)

     moreover have "?case7 \<longrightarrow> ?endgoal"
       using think_some thinks_to_def thinks_to_deterministic
       by blast

     moreover have "?case8 \<longrightarrow> ?endgoal"
       using think_deterministic think_unique thinks_to_def think_some by blast

     moreover have "?case9 \<longrightarrow> ?endgoal"
       using think_deterministic think_unique thinks_to_def think_some by blast

     ultimately have "?endgoal"
       using All
       by argo

     then show "\<exists>t1 t2.
       h1 = Thunk t1 \<and>
       h2 = Thunk t2 \<and>
       (\<forall>v2. think_with_fuel (Suc f') t2 = Some v2 \<longrightarrow>
       (\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2) \<or>
       thinks_to t1 (Thunk t2) \<or> thinks_to t1 (Encode (Strict t2)) \<or> thinks_to t1 (Encode (Shallow t2)))" 
       using T1 T2
       by blast
   next
     assume ASSM: "\<exists>t1. h1 = Thunk t1"
     then have
       "(\<exists>t1 t2.
             h1 = Thunk t1 \<and>
             h2 = Thunk t2 \<and>
             (\<forall>v1. think_with_fuel f' t1 = Some v1 \<longrightarrow>
                   (\<exists>v2. thinks_to t2 v2 \<and> strengthen X v1 v2) \<or>
                   v1 = Thunk t2 
                   \<or> v1 = Encode (Strict t2)
                   \<or> v1 = Encode (Shallow t2)))"
       using relevant_IH_think
       using Suc.prems by presburger
     then obtain t1 t2 where T1: "h1 = Thunk t1"
                         and T2: "h2 = Thunk t2"
                         and relevant_IH: "\<forall>v1. think_with_fuel f' t1 = Some v1 \<longrightarrow>
                                             (\<exists>v2. thinks_to t2 v2 \<and> strengthen X v1 v2) \<or>
                                             v1 = Thunk t2 
                                             \<or> v1 = Encode (Strict t2)
                                             \<or> v1 = Encode (Shallow t2)"
       by auto

     let ?endgoal = "\<forall>v1. force_with_fuel (Suc f') t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> strengthen X v1 v2)"
 
     have ?endgoal
     proof (intro allI impI)
       fix v1
       assume F1: "force_with_fuel (Suc f') t1 = Some v1"
       then obtain t1' where T1: "think_with_fuel f' t1 = Some t1'"
         by (cases "think_with_fuel f' t1") auto

       let ?case1 = "\<exists>v2. thinks_to t2 v2 \<and> strengthen X t1' v2"
       let ?case2 = "t1' = Thunk t2"
       let ?case3 = "t1' = Encode (Strict t2)"
       let ?case4 = "t1' = Encode (Shallow t2)"
       let ?endgoal = "\<exists>v2. forces_to t2 v2 \<and> strengthen X v1 v2"

       have "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4"
         using relevant_IH T1 T2 ASSM by auto

       moreover have "?case1 \<longrightarrow> ?endgoal"
       proof
         assume ?case1
         then obtain t2' where T2: "thinks_to t2 t2'" and EQOUT: "strengthen X t1' t2'" by auto

         show ?endgoal
         proof (cases t1')
           case (Data d1)
           then have EQV1: "v1 = t1'" using F1 T1 by auto

           have "relaxed_X X t1' t2'"
             using EQOUT strengthen_def Data
             by simp
           then have "X (lift t1') (lift t2')"
             using relaxed_X_def Data by auto
           moreover obtain d1' where "lift t1' = Data d1'"
             using Data
             by auto
           ultimately obtain d2' where "lift t2' = Data d2'"
             by (metis X_encode_eval_rev_does_not_exist X_preserve_thunk handle.distinct(2) handle.exhaust handle.simps(7))
           then obtain d2 where Data2: "t2' = Data d2"
             by (metis lift.elims)
           then show ?thesis
             using force_hs
             using EQOUT EQV1 T2 force_some think_unique by force
         next
           case (Thunk th1)
           then show ?thesis
           proof (cases "\<exists>e2. t2' = Encode e2")
             case False
             then have "X (Thunk th1) (lift t2')"
               using EQOUT strengthen_def relaxed_X_def Thunk
               by (cases t2'; simp)
             then obtain th2 where Th2: "t2' = Thunk th2" and EQOUT: "X (Thunk th1) (Thunk th2)"
               using EQOUT strengthen_def
               by (metis X_preserve_thunk handle.distinct(2) is_thunk.cases lift.simps(1,2,3))
             then have OUT: "\<forall>v1. force_with_fuel f' th1 = Some v1 \<longrightarrow> 
                                           (\<exists>v2. forces_to th2 v2 \<and> strengthen X v1 v2)"
               using relevant_IH_force[OF EQOUT] Thunk by auto

             have "force_with_fuel f' th1 = Some v1" using F1 T1 Thunk by auto
             then obtain v2 where "forces_to th2 v2" and EQV: "strengthen X v1 v2"
               using OUT by auto
             then have "forces_to t2 v2"
               by (metis (lifting) T2 Th2 force_hs force_some force_unique handle.simps(11) option.simps(5) think_unique)
             then show ?thesis
               using EQV by blast
           next
             case True
             then obtain e2 where Encode2: "t2' = Encode e2" by auto
             then have "X (Thunk th1) (Thunk (encode_to_thunk e2)) \<or> rel_opt (relaxed_X X) (force th1) (force (encode_to_thunk e2))"
               using EQOUT strengthen_def Thunk
               by simp
             then show ?thesis
             proof 
               assume "X (Thunk th1) (Thunk (encode_to_thunk e2))"
               moreover have "force_with_fuel f' th1 = Some v1" using F1 T1 Thunk by auto
               ultimately obtain v2 where "force (encode_to_thunk e2) = Some v2" and EQV: "strengthen X v1 v2"
                 using relevant_IH_force
                 using force_unique by blast
               then have "force t2 = Some v2"
                 using T2 Encode2 force_hs
                 by (metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) encode_to_thunk_def handle.simps(12) option.simps(5) think_unique)
               then show ?thesis
                 using EQV force_some by blast
             next
               assume "rel_opt (relaxed_X X) (force th1) (force (encode_to_thunk e2))"
               moreover have F1:"force_with_fuel f' th1 = Some v1" using F1 T1 Thunk by auto
               ultimately obtain v2 where F2:"force (encode_to_thunk e2) = Some v2" and relV: "relaxed_X X v1 v2"
                 by (metis force_unique forces_to_def not_Some_eq rel_opt.simps(2,3))
               then have "force t2 = Some v2"
                 using T2 Encode2 force_hs
                 by (metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) encode_to_thunk_def handle.simps(12) option.simps(5) think_unique)

               moreover have "strengthen X v1 v2"
                 using relV strengthen_def force_data forces_to_data F1 F2
                 using force_with_fuel_to_data handle.simps(10) by blast
               ultimately show ?thesis
                 using relV strengthen_def force_data forces_to_data force_some 
                 by blast
             qed
           qed
         next
           case (Encode e1)
           then have F1: "force_with_fuel f' (encode_to_thunk e1) = Some v1"
             using F1 T1 encode_to_thunk_def Encode
             by (simp add: Encode.case_distrib)
           have Encode1: "t1' = Encode e1"
             using Encode by blast
           show ?thesis
           proof (cases t2')
             case (Data d2)
             then have "relaxed_X X (Encode e1) (Data d2)"
               using EQOUT strengthen_def Encode
               by simp
             then have "X (Encode (Strict (encode_to_thunk e1))) (lift (Data d2))"
               using relaxed_X_def
               by (cases e1; simp_all)
             then have "execute (Strict (encode_to_thunk e1)) = Some (lift (Data d2))"
               by (simp add: X_encode_eval execute_unique)
             then obtain d1 where "force (encode_to_thunk e1) = Some (Data d1)" and L: "lift (Data d1) = lift (Data d2)"
               using execute_hs
               using force_data by force
             then have "Data d1 = v1"
               using forces_to_def forces_to_deterministic F1 force_some
               by (simp, meson)
             then have "strengthen X v1 (Data d2)"
               using strengthen_def L X_self relaxed_X_def
               by force

             then show ?thesis
               using Data T2 force_hs force_some think_unique by force
           next
             case (Thunk th2)
             then have "X (Thunk (encode_to_thunk e1)) (Thunk th2) \<or> rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force th2)"
               using EQOUT strengthen_def Encode by simp
             then show ?thesis
             proof
               assume "X (Thunk (encode_to_thunk e1)) (Thunk th2)"
               then have "\<exists>v2. forces_to th2 v2 \<and> strengthen X v1 v2"
                 using relevant_IH_force F1
                 by blast
               then show ?thesis
                 using force_hs T2
                 by (metis (no_types, lifting) Thunk force_some force_unique handle.simps(11) option.simps(5) think_unique)
             next
               assume "rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force th2)"
               then obtain v2 where "force th2 = Some v2" and "relaxed_X X v1 v2"
                 using F1
                 by (metis force_unique forces_to_def option.exhaust rel_opt.simps(2,3))
               then show ?thesis
                 using force_hs T2
                 by (metis (mono_tags, lifting) F1 Thunk force_some forces_to_data forces_to_def handle.simps(10,11) option.simps(5) prod.simps(2) strengthen_def think_unique)
             qed
           next
             case (Encode e2)
             then have "X (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2)) \<or> rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force (encode_to_thunk e2))"
               using EQOUT strengthen_def Encode1 
               by simp
             then show ?thesis
             proof
               assume "X (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2))"
               then obtain v2 where "forces_to (encode_to_thunk e2) v2 \<and> strengthen X v1 v2"
                 using relevant_IH_force F1
                 by blast
               then have "force t2 = Some v2 \<and> strengthen X v1 v2"
                 using force_hs T2 Encode
                 by (simp, metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) force_unique handle.simps(12) option.simps(5) think_unique)
               then show ?thesis
                 using force_some by blast
             next
               assume "rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force (encode_to_thunk e2))"
               then obtain v2 where "force (encode_to_thunk e2) = Some v2" and "relaxed_X X v1 v2"
                 using F1
                 by (metis force_unique forces_to_def option.exhaust rel_opt.simps(2,3))
               then have "force t2 = Some v2 \<and> relaxed_X X v1 v2"
                 using force_hs T2 Encode
                 by (simp, metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) handle.simps(12) option.simps(5) think_unique)
               then show ?thesis
                 using F1 force_some forces_to_data force_data forces_to_def strengthen_def by fastforce
             qed
           qed
         qed
       qed

       moreover have "(?case2 \<or> ?case3 \<or> ?case4) \<longrightarrow> ?endgoal"
       proof
         assume "?case2 \<or> ?case3 \<or> ?case4"
         then have "force_with_fuel f' t2 = Some v1" using F1 T1 by auto
         moreover then have "forces_to t2 v1" and "X v1 v1" using forces_to_def X_self by auto
         ultimately show ?endgoal 
           using forces_to_data strengthen_def relaxed_X_def
           using X_self relevant_IH_force
           by (metis handle.inject(2))
       qed
       ultimately show ?endgoal
         by meson
     qed

     then show "\<exists>t1 t2. h1 = Thunk t1 
                      \<and> h2 = Thunk t2 
                      \<and> (\<forall>v1. force_with_fuel (Suc f') t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> strengthen X v1 v2))"
       using T1 T2 by blast
   next
     assume ASSM: "\<exists>t2. h2 = Thunk t2"
     then have "(\<exists>t1 t2.
             h1 = Thunk t1 \<and>
             h2 = Thunk t2 \<and>
             (\<forall>v2. think_with_fuel f' t2 = Some v2 \<longrightarrow>
                   (\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2) \<or>
                   thinks_to t1 (Thunk t2)
                   \<or> thinks_to t1 (Encode (Strict t2))
                   \<or> thinks_to t1 (Encode (Shallow t2))))"
       using relevant_IH_think
       using Suc.prems by presburger
     then obtain t1 t2 where T1: "h1 = Thunk t1"
                         and T2: "h2 = Thunk t2"
                         and relevant_IH: 
                              "\<forall>v2. think_with_fuel f' t2 = Some v2 \<longrightarrow>
                                   (\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2) \<or>
                                   thinks_to t1 (Thunk t2)
                                   \<or> thinks_to t1 (Encode (Strict t2))
                                   \<or> thinks_to t1 (Encode (Shallow t2))"
       by auto

     let ?endgoal = "\<forall>v2. force_with_fuel (Suc f') t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> strengthen X v1 v2)"
 
     have ?endgoal
     proof (intro allI impI)
       fix v2
       assume F2: "force_with_fuel (Suc f') t2 = Some v2"
       then obtain t2' where Think2: "think_with_fuel f' t2 = Some t2'"
         by (cases "think_with_fuel f' t2") auto

       let ?case1 = "\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 t2'"
       let ?case2 = "thinks_to t1 (Thunk t2)"
       let ?case3 = "thinks_to t1 (Encode (Strict t2))"
       let ?case4 = "thinks_to t1 (Encode (Shallow t2))"
       let ?endgoal = "\<exists>v1. forces_to t1 v1 \<and> strengthen X v1 v2"

       have "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4"
         using relevant_IH T1 T2 Think2 
         by presburger

       moreover have "?case1 \<longrightarrow> ?endgoal"
       proof
         assume ?case1
         then obtain v1 where Think1: "thinks_to t1 v1" and EQOUT: "strengthen X v1 t2'" by auto

         show ?endgoal
         proof (cases v1)
           case (Data d1)
           have "relaxed_X X v1 t2'"
             using EQOUT strengthen_def Data
             by simp
           then have "X (lift v1) (lift t2')"
             using relaxed_X_def
             by (simp add: Data)
           moreover obtain d1' where "lift v1 = Data d1'"
             using Data
             by auto
           ultimately obtain d2' where "lift t2' = Data d2'"
             by (metis X_encode_eval_rev_does_not_exist X_preserve_thunk handle.distinct(2) handle.exhaust handle.simps(7))
           then obtain d2 where Data2: "t2' = Data d2"
             by (metis lift.elims)
           then have "v2 = t2'"
             using F2 Think2 by force
           then show ?thesis
             using force_hs
             using Data EQOUT Think1 force_some think_unique by force
         next
           case (Thunk th1)
           then show ?thesis
           proof (cases "\<exists>e2. t2' = Encode e2")
             case False
             then have "X (Thunk th1) (lift t2')"
               using EQOUT strengthen_def relaxed_X_def Thunk
               by (cases t2'; simp)
             then obtain th2 where Th2: "t2' = Thunk th2" and EQOUT: "X (Thunk th1) (Thunk th2)"
               using EQOUT strengthen_def
               by (metis X_preserve_thunk handle.distinct(2) is_thunk.cases lift.simps(1,2,3))

             have "force_with_fuel f' th2 = Some v2" 
               using F2 Th2 Think2 by force
               
             then obtain v1 where "forces_to th1 v1" and EQV: "strengthen X v1 v2"
               using relevant_IH_force
               using EQOUT by blast
             then have "forces_to t1 v1"
               by (metis (no_types, lifting) Think1 Thunk force_hs force_some force_unique handle.simps(11) option.simps(5) think_unique)
             then show ?thesis
               using EQV by blast
           next
             case True
             then obtain e2 where Encode2: "t2' = Encode e2" by auto
             then have "X (Thunk th1) (Thunk (encode_to_thunk e2)) \<or> rel_opt (relaxed_X X) (force th1) (force (encode_to_thunk e2))"
               using EQOUT strengthen_def Thunk
               by simp
             then show ?thesis
             proof 
               assume "X (Thunk th1) (Thunk (encode_to_thunk e2))"
               moreover have "force_with_fuel f' (encode_to_thunk e2) = Some v2"
                 using F2 Think2 Encode2
                 by (cases e2; simp)
               ultimately obtain v1 where "force th1 = Some v1" and EQV: "strengthen X v1 v2"
                 using relevant_IH_force
                 using force_unique by blast
               then have "force t1 = Some v1"
                 using Think1 Thunk force_hs think_unique by auto
               then show ?thesis
                 using EQV force_some by blast
             next
               assume "rel_opt (relaxed_X X) (force th1) (force (encode_to_thunk e2))"
               moreover have F1:"force_with_fuel f' (encode_to_thunk e2) = Some v2"
                 using F2 Think2 Encode2
                 by (cases e2; simp)
               ultimately obtain v1 where F2: "force th1 = Some v1" and relV: "relaxed_X X v1 v2"
                 using relevant_IH_force
                 by (metis force_unique forces_to_def option.distinct(1) option.sel rel_opt.elims(2))
               then have "force t1 = Some v1"
                 using Think1 Thunk force_hs think_unique by auto
               moreover have "strengthen X v1 v2"
                 using relV strengthen_def force_data forces_to_data F1 F2
                 using force_with_fuel_to_data handle.simps(10) by blast
               ultimately show ?thesis
                 using relV strengthen_def force_data forces_to_data force_some 
                 by blast
             qed
           qed
         next
           case (Encode e1)
           then have strX: "strengthen X (Encode e1) t2'"
                and  Think1: "thinks_to t1 (Encode e1)"
             using EQOUT Encode Think1 by auto
           then show ?thesis
           proof (cases t2')
             case (Data d2)
             then have "relaxed_X X (Encode e1) (Data d2)"
               using strX strengthen_def
               by simp
             then have "execute (Strict (encode_to_thunk e1)) = Some (lift (Data d2))"
               using relaxed_X_def X_encode_eval
               apply (cases e1; simp_all)
               using execute_unique handle.distinct(3) apply presburger
               by (simp add: execute_unique)
             then obtain d1 where ForceE: "force (encode_to_thunk e1) = Some (Data d1)" and relX: "lift (Data d1) = lift (Data d2)"
               using force_data execute_hs
               by force

             have "forces_to t1 (Data d1)"
               using Think1 force_hs ForceE
               by (metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) encode_to_thunk_def force_some  handle.simps(12) option.simps(5) think_unique)
             moreover have "strengthen X (Data d1) (Data d2)"
               using strengthen_def relX relaxed_X_def
               apply simp
               using X_self by blast
             ultimately show ?thesis
               using Data F2 Think2 by auto
           next
             case (Thunk th2)
             then have "X (Thunk (encode_to_thunk e1)) (Thunk th2) \<or> rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force th2)"
               using strX strengthen_def
               by force
             then show ?thesis
             proof 
               assume "X (Thunk (encode_to_thunk e1)) (Thunk th2)"
               moreover have "force_with_fuel f' th2 = Some v2"
                 using F2 Thunk Think2 by force

               ultimately obtain v1 where "forces_to (encode_to_thunk e1) v1" and EQV: "strengthen X v1 v2"
                 using relevant_IH_force
                 by blast

               then have "forces_to t1 v1"
                 using Think1
                 by (metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) encode_to_thunk_def force_hs force_some force_unique handle.simps(12) option.simps(5) think_unique)
               then show ?thesis
                 using EQV by blast
             next
               assume "rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force th2)"
               moreover have "force_with_fuel f' th2 = Some v2"
                 using F2 Thunk Think2 by force
               ultimately obtain v1 where "forces_to (encode_to_thunk e1) v1" and EQV: "relaxed_X X v1 v2"
                 by (metis force_some force_unique forces_to_def option.distinct(1) option.sel rel_opt.elims(2))
               then have "forces_to t1 v1"
                 using Think1
                 by (metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) encode_to_thunk_def force_hs force_some force_unique handle.simps(12) option.simps(5) think_unique)
               then show ?thesis
                 using EQV strengthen_def forces_to_data
                 using handle.simps(10) by blast
             qed
           next
             case (Encode e2)
             then have "X (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2)) \<or> rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force (encode_to_thunk e2))"
               using strX strengthen_def by fastforce
             then show ?thesis
             proof
               assume "X (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2))"
               moreover have "force_with_fuel f' (encode_to_thunk e2) = Some v2"
                 using F2 Think2 Encode
                 by (metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) encode_to_thunk_def force_with_fuel.simps(2) handle.simps(12) option.simps(5))
               ultimately obtain v1 where "forces_to (encode_to_thunk e1) v1 \<and> strengthen X v1 v2"
                 using relevant_IH_force by blast
               then have "force t1 = Some v1 \<and> strengthen X v1 v2"
                 using Think1 force_hs force_unique
                 by (simp, metis (lifting) Encode.exhaust Encode.simps(5,6) handle.simps(12) option.simps(5) think_unique)
               then show ?thesis
                 using force_some by blast
             next
               assume "rel_opt (relaxed_X X) (force (encode_to_thunk e1)) (force (encode_to_thunk e2))"
               moreover have "force_with_fuel f' (encode_to_thunk e2) = Some v2"
                 using F2 Think2 Encode
                 by (metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) encode_to_thunk_def force_with_fuel.simps(2) handle.simps(12) option.simps(5))
               ultimately obtain v1 where "force (encode_to_thunk e1) = Some v1" and "relaxed_X X v1 v2"
                 by (metis force_unique forces_to_def option.exhaust rel_opt.simps(2,4))
               then have "force t1 = Some v1 \<and> relaxed_X X v1 v2"
                 using force_hs Think1 Encode
                 by (simp, metis (no_types, lifting) Encode.exhaust Encode.simps(5,6) handle.simps(12) option.simps(5) think_unique)
               then show ?thesis
                 using force_some forces_to_data force_data forces_to_def strengthen_def by fastforce
             qed
           qed
         qed
       qed

       moreover have "(?case2 \<or> ?case3 \<or> ?case4) \<longrightarrow> ?endgoal"
       proof
         assume "?case2 \<or> ?case3 \<or> ?case4"
         then have "force t1 = Some v2"
           using force_hs F2 force_unique forces_to_def think_unique
           by (metis (mono_tags, lifting) Encode.simps(5,6) handle.simps(11,12) option.case_eq_if option.distinct(1) option.sel)
         moreover then have "relaxed_X X v2 v2"
           using X_self relaxed_X_def force_data
           apply simp
           using handle.simps(10) by blast
         ultimately show ?endgoal 
           using forces_to_data strengthen_def
           using force_some by fastforce
       qed

       ultimately show ?endgoal
         by meson
     qed

     then show "\<exists>t1 t2. h1 = Thunk t1 
                      \<and> h2 = Thunk t2 
                      \<and> (\<forall>v2. force_with_fuel (Suc f') t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> strengthen X v1 v2))"
       using T1 T2 by blast
   next
     let ?RHS = " \<forall>v1. eval_with_fuel (Suc f') h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2)"

     show ?RHS
     proof (intro allI impI)
       fix v1
       assume ASSM: "eval_with_fuel (Suc f') h1 = Some v1"
       show "\<exists>v2. evals_to h2 v2 \<and> X v1 v2"
         using ASSM
       proof (cases h1)
         case (Data x1)
         then show ?thesis
         proof (cases x1)
           case (Object obj1)
           then show ?thesis
           proof (cases obj1)
             case (BlobObj b1)
             then obtain b2 where "h2 = HBlobObj b2"
               using Data HBlobObj_def Object Suc.prems X_preserve_blob by presburger
             then have "evals_to h2 h2"
               using eval_hs eval_some
               by simp
             then show ?thesis
               using ASSM BlobObj Data Object Suc.prems by auto
           next
             case (TreeObj t1)
             then obtain t2 where T2: "h2 = HTreeObj t2"
               using Data HTreeObj_def Object Suc.prems X_preserve_tree by presburger
             then have XTree: "X (HTreeObj t1) (HTreeObj t2)"
               using Data Object Suc.prems TreeObj by force

             obtain tree' where "eval_tree_with_fuel f' t1 = Some tree'"
                          and   V1: "v1 = HTreeObj tree'"
               using ASSM Data Object TreeObj by (cases "eval_tree_with_fuel f' t1") auto
             then obtain tree2' where "evals_tree_to t2 tree2'"
                                and   EQTREE: "X (HTreeObj tree') (HTreeObj tree2')"
               using eq_tree_eval_fuel_n[OF tree_cong tree_complete eval_cong_f' XTree]
               by auto
             then have "evals_to h2 (HTreeObj tree2')" 
               using eval_some eval_hs T2 
               by (simp add: eval_tree_unique)
             then show ?thesis using V1 EQTREE by auto
           qed
         next
           case (Ref r1)
           then obtain r2 where "h2 = (Data (Ref r2))"
             using Data
             by (metis HBlobRef_def HTreeRef_def Ref.exhaust Suc.prems X_preserve_blob_ref X_preserve_tree_ref)
           then have "evals_to h2 h2"
             using eval_hs eval_some by simp
           then show ?thesis
             using ASSM Data Ref Suc.prems by auto
         qed
       next
         case (Thunk t1)
         then obtain t2 where "h2 = Thunk t2" 
           using X_preserve_thunk
           using Suc.prems by blast
         then have "evals_to h2 h2"
           using eval_hs eval_some by simp
         then show ?thesis 
           using ASSM Thunk Suc.prems by auto
       next
         case (Encode e1)
         then show ?thesis
         proof (cases "\<exists>e2. h2 = Encode e2")
          case True
          then obtain e2 where E2: "h2 = Encode e2" by auto
          show ?thesis
            proof (cases e1)
              case (Strict t1)
              then obtain t2 where "h2 = Encode (Strict t2)"
                by (metis Encode Encode.exhaust Suc.prems X_not_strict_shallow \<open>\<And>thesis. (\<And>e2. h2 = Encode e2 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
              then have "X (Thunk t1) (Thunk t2) \<or> rel_opt X (execute (Strict t1)) (execute (Strict t2))"
                using X_encode_reasons Encode Strict
                using Suc.prems by blast
              then show ?thesis
              proof
                assume rel_execute: "rel_opt X (execute (Strict t1)) (execute (Strict t2))"
  
                obtain h1' where "execute_with_fuel f' (Strict t1) = Some h1'"
                           and   Eval1: "eval_with_fuel f' h1' = Some v1"
                using ASSM Strict Encode
                by (cases "execute_with_fuel f' e1") auto
  
               then obtain h2' where "execute (Strict t2) = Some h2'"
                               and   EQ': "X h1' h2'"
                using rel_execute
                by (metis execute_unique executes_to_def not_Some_eq option.inject rel_opt.elims(2))
          
               moreover obtain v2 where "evals_to h2' v2" and EQRES: "X v1 v2"
                 using Suc.IH EQ' Eval1 by blast
               then have "evals_to (Encode (Strict t2)) v2"
                 by (metis calculation(1) eval_hs eval_some eval_unique handle.simps(12) option.simps(5))
               then show ?thesis
                 using EQRES
                 using \<open>h2 = Encode (Strict t2)\<close> by blast
              next
                assume rel_thunk: "X (Thunk t1) (Thunk t2)" 
  
                obtain h1' where "execute_with_fuel f' (Strict t1) = Some h1'"
                           and   Eval1: "eval_with_fuel f' h1' = Some v1"
                using ASSM Strict Encode
                by (cases "execute_with_fuel f' e1") auto
  
                then have "(force_with_fuel f' t1) <$> lift = Some h1'" by simp
  
                then obtain f1 where Force1: "force_with_fuel f' t1 = Some f1"
                               and L1: "h1' = lift f1"
                  by blast
  
                then obtain f2 where Force2: "forces_to t2 f2" 
                               and   strX: "strengthen X f1 f2"
                  using relevant_IH_force rel_thunk by force
  
                then have Execute2: "execute (Strict t2) = Some (lift f2)" 
                  using execute_hs force_unique by force
  
                have "relaxed_X X f1 f2"
                  using strX Force1 Force2 forces_to_data strengthen_def
                  using force_with_fuel_to_data by fastforce
                moreover have "\<exists>d. f1 = Data d"
                  using Force1 force_with_fuel_to_data by blast
                moreover have "\<exists>d. f2 = Data d"
                  using Force2 forces_to_data by blast
                ultimately have "X h1' (lift f2)"
                  using L1 relaxed_X_def by auto
  
                then obtain v2 where "evals_to (lift f2) v2" and "X v1 v2"
                  using Eval1 eval_cong_f' by force
                moreover then have "evals_to (Encode (Strict t2)) v2"
                  using Execute2 eval_hs
                  by (metis eval_some eval_unique handle.simps(12) option.simps(5))
  
                ultimately show ?thesis
                  using \<open>h2 = Encode (Strict t2)\<close> by blast
              qed
            next
              case (Shallow t1)
              then obtain t2 where "h2 = Encode (Shallow t2)"
                by (metis Encode Encode.exhaust Suc.prems X_not_shallow_strict \<open>\<And>thesis. (\<And>e2. h2 = Encode e2 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
              then have "X (Thunk t1) (Thunk t2) \<or> rel_opt X (execute (Shallow t1)) (execute (Shallow t2))"
                using X_shallow_encode_reasons Encode Shallow
                using Suc.prems by blast
              then show ?thesis
              proof
                assume rel_execute: "rel_opt X (execute (Shallow t1)) (execute (Shallow t2))"
  
                obtain h1' where "execute_with_fuel f' (Shallow t1) = Some h1'"
                           and   Eval1: "eval_with_fuel f' h1' = Some v1"
                using ASSM Shallow Encode
                by (cases "execute_with_fuel f' e1") auto
  
               then obtain h2' where "execute (Shallow t2) = Some h2'"
                               and   EQ': "X h1' h2'"
                using rel_execute
                by (metis execute_unique executes_to_def not_Some_eq option.inject rel_opt.elims(2))
          
               moreover obtain v2 where "evals_to h2' v2" and EQRES: "X v1 v2"
                 using Suc.IH EQ' Eval1 by blast
               then have "evals_to (Encode (Shallow t2)) v2"
                 by (metis calculation(1) eval_hs eval_some eval_unique handle.simps(12) option.simps(5))
               then show ?thesis
                 using EQRES
                 using \<open>h2 = Encode (Shallow t2)\<close> by blast
              next
                assume rel_thunk: "X (Thunk t1) (Thunk t2)" 
  
                obtain h1' where "execute_with_fuel f' (Shallow t1) = Some h1'"
                           and   Eval1: "eval_with_fuel f' h1' = Some v1"
                using ASSM Shallow Encode
                by (cases "execute_with_fuel f' e1") auto
  
                then have "(force_with_fuel f' t1) <$> lower = Some h1'" by simp
  
                then obtain f1 where Force1: "force_with_fuel f' t1 = Some f1"
                               and L1: "h1' = lower f1"
                  by blast
  
                then obtain f2 where Force2: "forces_to t2 f2" 
                               and   strX: "strengthen X f1 f2"
                  using relevant_IH_force rel_thunk by force
  
                then have Execute2: "execute (Shallow t2) = Some (lower f2)" 
                  using execute_hs force_unique by force
  
                have "relaxed_X X f1 f2"
                  using strX Force1 Force2 forces_to_data strengthen_def
                  using force_with_fuel_to_data by fastforce
                moreover have "\<exists>d. f1 = Data d"
                  using Force1 force_with_fuel_to_data by blast
                moreover have "\<exists>d. f2 = Data d"
                  using Force2 forces_to_data by blast
                ultimately have "X h1' (lower f2)"
                  using L1 relaxed_X_def lift_to_lower[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree X_preserve_blob]
                  by force
  
                then obtain v2 where "evals_to (lower f2) v2" and "X v1 v2"
                  using Eval1 eval_cong_f' by force
                moreover then have "evals_to (Encode (Shallow t2)) v2"
                  using Execute2 eval_hs
                  by (metis eval_some eval_unique handle.simps(12) option.simps(5))
  
                ultimately show ?thesis
                  using \<open>h2 = Encode (Shallow t2)\<close> by blast
              qed
            qed
         next
          case False
          then have "executes_to e1 h2"
            using Encode Suc.prems X_encode_eval by blast
          then have "evals_to h2 v1"
            by (metis ASSM Encode eval_hs eval_some eval_unique evals_to_def execute_unique handle.simps(12) option.simps(5))
          then show ?thesis
            using X_self by blast
        qed
      qed
    qed
  next
    let ?RHS = " \<forall>v2. eval_with_fuel (Suc f') h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2)"
    show ?RHS
    proof (intro allI impI)
      fix v2
      assume ASSM: "eval_with_fuel (Suc f') h2 = Some v2"
      show "\<exists>v1. evals_to h1 v1 \<and> X v1 v2"
        using ASSM
      proof (cases h2)
        case (Data x2)
        then show ?thesis
        proof (cases x2)
          case (Object obj2)
          then show ?thesis
          proof (cases obj2)
            case (BlobObj b2)
            then have "(\<exists>b1. h1 = HBlobObj b1) \<or> (\<exists>t1. h1 = Encode (Strict t1))"
              using Suc.prems X_preserve_blob_or_encode_rev Data Object
              by simp
            then show ?thesis
            proof
              assume "\<exists>b1. h1 = HBlobObj b1"
              then obtain b1 where "h1 = HBlobObj b1" by auto
              then have "evals_to h1 h1" 
                using eval_hs evals_to_def
                using eval_some by force
              then show ?thesis
                using ASSM BlobObj Data Object Suc.prems by auto
            next
              assume "\<exists>t1. h1 = Encode (Strict t1)"
              then obtain t1 where "h1 = Encode (Strict t1)" by auto
              then have "evals_to h1 h2"
                by (metis BlobObj Data Data.simps(5) Object Object.simps(5) Suc.prems X_encode_eval eval_hs eval_some execute_unique handle.simps(10,12) option.simps(5))
              then show ?thesis
                by (metis (no_types, lifting) ASSM BlobObj Data Data.simps(5) Object Object.simps(5) X_self eval_some eval_unique eval_with_fuel.simps(2) handle.simps(10))
            qed
          next
            case (TreeObj t2)
            then have "(\<exists>t1. h1 = HTreeObj t1) \<or> (\<exists>t1. h1 = Encode (Strict t1))"
              using Data Object Suc.prems X_preserve_tree_or_encode_rev by auto
            then show ?thesis
            proof 
              assume "\<exists>t1. h1 = HTreeObj t1"
              then obtain t1 where T1: "h1 = HTreeObj t1" by auto
              then have EQTREE: "X (HTreeObj t1) (HTreeObj t2)" 
                using Data Object Suc.prems TreeObj by fastforce

             obtain list2' where "eval_list_with_fuel f' (get_tree_raw t2) = Some list2'"
                           and   V2: "v2 = HTreeObj (create_tree list2')"
               using ASSM Data Object TreeObj by auto

             then have "list_all2 (\<lambda>x y. eval_with_fuel f' x = Some y) (get_tree_raw t2) list2'"
               using eval_list_to_list_all
               by simp

             moreover have "list_all2 (\<lambda>x y. X x y) (get_tree_raw t1) (get_tree_raw t2)"
               using EQTREE tree_cong by blast

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

             then have "X (HTreeObj (create_tree list1')) (HTreeObj (create_tree list2'))"
               using tree_complete by blast

             moreover have "evals_to h1 (HTreeObj (create_tree list1'))"
               by (metis Data.simps(5) HTreeObj_def Object.simps(6) T1 \<open>eval_list_with_fuel fuel' (get_tree_raw t1) = Some list1'\<close> eval_tree_with_fuel.simps eval_with_fuel.simps(2) evals_to_def handle.simps(10) map_option_case
                   option.simps(5))

             ultimately show ?thesis
               using V2
               by blast
           next
             assume "\<exists>t1. h1 = Encode (Strict t1)"
             then obtain t1 where "h1 = Encode (Strict t1)" by auto
             then have "executes_to (Strict t1) h2"
               using Data Suc.prems X_encode_eval by blast
             then have "evals_to h1 v2"
               by (metis ASSM \<open>h1 = Encode (Strict t1)\<close> eval_hs eval_some eval_unique evals_to_def execute_unique handle.simps(12) option.simps(5))
             then show ?thesis
               using X_self by blast
           qed
          qed
        next
          case (Ref r2)
          then show ?thesis
          proof (cases r2)
            case (BlobRef b2)
            then have "(\<exists>b1. h1 = HBlobRef b1) \<or> (\<exists>t1. h1 = Encode (Shallow t1))"
              using Suc.prems X_preserve_blob_ref_or_encode_rev Data Ref
              by simp
            then show ?thesis
            proof
              assume "\<exists>b1. h1 = HBlobRef b1"
              then have "evals_to h1 h1" 
                using eval_hs evals_to_def
                using eval_some by force
              then show ?thesis
                using ASSM BlobRef Data Ref Suc.prems by auto
            next
              assume "\<exists>t1. h1 = Encode (Shallow t1)"
              then obtain t1 where "h1 = Encode (Shallow t1)" by auto
              then have "evals_to h1 h2"
                by (metis Data Data.simps(6) Ref Suc.prems X_encode_eval eval_hs eval_some execute_unique handle.simps(10,12) option.simps(5))
              then show ?thesis
                using ASSM Data Ref X_self by auto
            qed
          next
            case (TreeRef t2)
            then have "(\<exists>t1. h1 = HTreeRef t1) \<or> (\<exists>t1. h1 = Encode (Shallow t1))"
              using Data Ref Suc.prems X_preserve_tree_ref_or_encode_rev by auto
            then show ?thesis
            proof 
              assume "\<exists>t1. h1 = HTreeRef t1"
              then obtain t1 where T1: "h1 = HTreeRef t1" by auto
              then have EQTREE: "X (HTreeRef t1) (HTreeRef t2)" 
                using Data Ref Suc.prems TreeRef by fastforce
              then show ?thesis
                using ASSM Data Ref Suc.prems \<open>\<exists>t1. h1 = HTreeRef t1\<close> eval_hs eval_some by force
            next
              assume "\<exists>t1. h1 = Encode (Shallow t1)"
              then obtain t1 where "h1 = Encode (Shallow t1)" by auto
              then have "executes_to (Shallow t1) h2"
                using Data Suc.prems X_encode_eval by blast
              then have "evals_to h1 v2"
                by (metis (no_types, lifting) ASSM \<open>h1 = Encode (Shallow t1)\<close> eval_hs eval_some eval_unique evals_to_def execute_unique handle.simps(12) option.simps(5))
              then show ?thesis
                using X_self by blast
           qed
         qed
       qed
     next
       case (Thunk t2)
       then have "\<exists>t1. h1 = Thunk t1"
         using Suc.prems relevant_IH_think by blast
       then obtain t1 where "h1 = Thunk t1" by auto
       then have "evals_to h1 h1" 
         by (simp add: eval_hs eval_some)
       then show ?thesis
         using ASSM Suc.prems Thunk by auto
     next
       case (Encode e2)
       then have "\<exists>e1. h1 = Encode e1"
         using Suc.prems X_encode_eval_rev_does_not_exist by blast

       then obtain e1 where E1: "h1 = Encode e1" by auto
       then have EQENCODE: "X (Encode e1) (Encode e2)" 
         using Encode Suc.prems by blast


       have "X (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2)) \<or> rel_opt X (execute e1) (execute e2)"
       proof (cases e1)
         case (Strict t1)
         then obtain t2 where "h2 = Encode (Strict t2)"
           by (metis E1 Encode Encode.exhaust Suc.prems X_not_strict_shallow)
         then have "X (Thunk t1) (Thunk t2) \<or> rel_opt X (execute (Strict t1)) (execute (Strict t2))"
           using X_encode_reasons Encode Strict
           using E1 Suc.prems by blast
         then show ?thesis
           using Encode Strict \<open>h2 = Encode (Strict t2)\<close> by force
       next
         case (Shallow t1)
         then obtain t2 where "h2 = Encode (Shallow t2)"
           by (metis E1 Encode Encode.exhaust Suc.prems X_not_shallow_strict)
         then show ?thesis
           using E1 Encode Shallow Suc.prems X_shallow_encode_reasons by auto
       qed

       then show ?thesis
       proof
         assume rel_execute: "rel_opt X (execute e1) (execute e2)"
           
         obtain h2' where "execute_with_fuel f' e2 = Some h2'"
                    and   Eval2: "eval_with_fuel f' h2' = Some v2"
           using ASSM Encode
           by (cases "execute_with_fuel f' e2") auto
           
         then obtain h1' where "execute e1 = Some h1'"
                         and   EQ': "X h1' h2'"
           using rel_execute
           by (metis execute_unique executes_to_def not_Some_eq option.inject rel_opt.elims(2))
           
         moreover obtain v1 where "evals_to h1' v1" and EQRES: "X v1 v2"
           using EQ' Eval2 eval_cong_f' by blast
         then have "evals_to h1 v1"
           by (metis E1 calculation(1) eval_hs eval_some eval_unique handle.simps(12) option.simps(5))
         then show ?thesis
           using EQRES by blast
         next
           assume rel_thunk: "X (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2))" 

           obtain h2' where Execute2: "execute_with_fuel f' e2 = Some h2'"
             using ASSM Encode
             by (cases "execute_with_fuel f' e2") simp
           then have Eval2: "eval_with_fuel f' h2' = Some v2"
             using ASSM using Encode by auto

           then show ?thesis
           proof (cases e1)
             case (Strict x1)
             then obtain x2 where Strict2: "e2 = Strict x2"
               by (metis E1 Encode Encode.exhaust Suc.prems X_not_strict_shallow)
             then have "(force_with_fuel f' x2) <$> lift = Some h2'"
               using Execute2 by auto

             then obtain f2 where Force2: "force_with_fuel f' x2 = Some f2"
                            and   L2: "h2' = lift f2"
                by blast
           
             then obtain f1 where Force1: "forces_to x1 f1" 
                             and   strX: "strengthen X f1 f2"
                using relevant_IH_force rel_thunk
                by (metis Encode.simps(5) Strict Strict2 encode_to_thunk_def handle.inject(2))
           
             then have Execute1: "execute (Strict x1) = Some (lift f1)" 
               using execute_hs force_unique by force
           
             have "relaxed_X X f1 f2"
               using strX Force1 Force2 forces_to_data strengthen_def
               using force_with_fuel_to_data by fastforce
             moreover have "\<exists>d. f1 = Data d"
               using Force1 forces_to_data by auto
             moreover have "\<exists>d. f2 = Data d"
               using Force2 force_with_fuel_to_data by blast
             then have "X (lift f1) h2'"
               using L2 calculation(1,2) relaxed_X_def by force
           
             then obtain v1 where "evals_to (lift f1) v1" and "X v1 v2"
                using Eval2 eval_cong_f' by force
             moreover then have "evals_to (Encode (Strict x1)) v1"
                using Execute1 eval_hs
                by (metis eval_some eval_unique handle.simps(12) option.simps(5))
           
             ultimately show ?thesis
               using E1 Strict by blast
           next
             case (Shallow x1)
             then obtain x2 where Shallow2: "h2 = Encode (Shallow x2)"
               by (metis E1 Encode Encode.exhaust Suc.prems X_not_shallow_strict)
             then have "(force_with_fuel f' x2) <$> lower = Some h2'" 
               using Encode Execute2 by auto
  
             then obtain f2 where Force2: "force_with_fuel f' x2 = Some f2"
                            and L2: "h2' = lower f2"
               by blast
  
             then obtain f1 where Force1: "forces_to x1 f1" 
                            and   strX: "strengthen X f1 f2"
               using Encode Shallow Shallow2 rel_thunk relevant_IH_force
               by (metis Encode.simps(6) encode_to_thunk_def handle.inject(2,3))
  
             then have Execute1: "execute (Shallow x1) = Some (lower f1)" 
               using execute_hs force_unique by force
  
             have "relaxed_X X f1 f2"
               using strX Force1 Force2 forces_to_data strengthen_def
               using force_with_fuel_to_data by fastforce
             moreover have "\<exists>d. f1 = Data d"
               using Force1 forces_to_data by auto
             moreover have "\<exists>d. f2 = Data d"
               using Force2 force_with_fuel_to_data by blast
             then have "X (lower f1) h2'"
               using L2 relaxed_X_def lift_to_lower[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete X_preserve_tree X_preserve_blob]
               using calculation(1,2) by force
  
             then obtain v1 where "evals_to (lower f1) v1" and "X v1 v2"
               using Eval2 eval_cong_f' by force
             moreover then have "evals_to (Encode (Shallow x1)) v1"
               using Execute1 eval_hs
               by (metis eval_some eval_unique handle.simps(12) option.simps(5))
  
             ultimately show ?thesis
               using E1 Encode
               using Shallow by blast
            qed
          qed
        qed
      qed
    qed
  qed
      
lemma forces_X:
 fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
  assumes strict_encode_cong: "\<And>t1 t2. X (Thunk t1) (Thunk t2)
                                       \<Longrightarrow> X (Encode (Strict t1)) (Encode (Strict t2))"
  assumes shallow_encode_cong: "\<And>t1 t2. X (Thunk t1) (Thunk t2)
                                        \<Longrightarrow> X (Encode (Shallow t1)) (Encode (Shallow t2))"
  assumes application_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Application t1)) (Thunk (Application t2))"
  assumes selection_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Selection t1)) (Thunk (Selection t2))"
  assumes digestion_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Digestion t1)) (Thunk (Digestion t2))"
  assumes identification_thunk_cong: 
            "\<And> d1 d2. X (Data d1) (Data d2)
                      \<Longrightarrow> X (Thunk (Identification d1)) (Thunk (Identification d2))"
  assumes X_preserve_tree_ref: "\<And>t h.
    X (HTreeRef t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t'))"
  assumes X_preserve_tree_ref_or_encode_rev: "\<And>t h.
    X h (HTreeRef t) \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t')) \<or> (\<exists>t'. h = (Encode (Shallow t')))"
  assumes X_preserve_blob_ref: "\<And>t h.
    X (HBlobRef t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t'))"
  assumes X_preserve_blob_ref_or_encode_rev: "\<And>t h.
    X h (HBlobRef t) \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t')) \<or> (\<exists>t'. h = (Encode (Shallow t')))"
  assumes X_preserve_tree: "\<And>t h.
    X (HTreeObj t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t'))"
  assumes X_preserve_tree_or_encode_rev: "\<And>t h.
    X h (HTreeObj t) \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t')) \<or> (\<exists>t'. h = (Encode (Strict t')))"
  assumes X_preserve_blob: "\<And>t h.
    X (HBlobObj t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t'))"
  assumes X_preserve_blob_or_encode_rev: "\<And>t h.
    X h (HBlobObj t) \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t')) \<or> (\<exists>t'. h = (Encode (Strict t')))"
  assumes X_preserve_thunk: "\<And>h1 h2.
    X h1 h2 \<longrightarrow>
    ((\<exists>t1. h1 = (Thunk t1)) \<longleftrightarrow> (\<exists>t2. h2 = (Thunk t2)))"
  assumes X_encode_eval: "\<And>e h2. 
         X (Encode e) h2 \<Longrightarrow> 
         \<not> (\<exists>e2. h2 = Encode e2) \<Longrightarrow>
         executes_to e h2"
  assumes X_encode_reasons: "\<And>t1 t2. 
         X (Encode (Strict t1)) (Encode (Strict t2)) \<Longrightarrow> 
         X (Thunk t1) (Thunk t2) \<or>
         rel_opt X (execute (Strict t1)) (execute (Strict t2))"
  assumes X_shallow_encode_reasons: "\<And>t1 t2. 
         X (Encode (Shallow t1)) (Encode (Shallow t2)) \<Longrightarrow> 
         X (Thunk t1) (Thunk t2) \<or>
         rel_opt X (execute (Shallow t1)) (execute (Shallow t2))"
  assumes X_not_shallow_strict:
    "\<And> t1 t2. \<not> X (Encode (Shallow t1)) (Encode (Strict t2))"
  assumes X_not_strict_shallow:
    "\<And> t1 t2. \<not> X (Encode (Strict t1)) (Encode (Shallow t2))"
  assumes X_encode_eval_rev_does_not_exist: "\<And>e h1. 
         X h1 (Encode e) \<Longrightarrow> 
         \<not> (\<exists>e1. h1 = Encode e1) \<Longrightarrow>
         False"
  assumes X_thunk_reasons: "\<And>t1 t2. X (Thunk t1) (Thunk t2) \<Longrightarrow> (
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2) \<or>
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2) \<or>
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Digestion tree1 \<and> t2 = Digestion tree2) \<or>
     (\<exists>d1 d2. X (Data d1) (Data d2) \<and> t1 =  Identification d1 \<and> t2 = Identification d2) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> strengthen X r1 r2) \<or>
     (think t1 = Some (Thunk t2))) \<or>
     (think t1 = Some (Encode (Strict t2))) \<or>
     (think t1 = Some (Encode (Shallow t2)))"
  assumes X_self: "\<And>h. X h h"
  assumes E: "X (Thunk h1) (Thunk h2)"
  shows "rel_opt (relaxed_X X) (force h1) (force h2)"
proof -
  have force_all_n: "\<And>h1 h2 n. X h1 h2 \<Longrightarrow>
       ((\<exists>t1. h1 = Thunk t1) \<longrightarrow>
        (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v1. force_with_fuel n t1 = Some v1 \<longrightarrow> (\<exists>v2. forces_to t2 v2 \<and> strengthen X v1 v2))))
      \<and>
       ((\<exists>t2. h2 = Thunk t2) \<longrightarrow>
        (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v2. force_with_fuel n t2 = Some v2 \<longrightarrow> (\<exists>v1. forces_to t1 v1 \<and> strengthen X v1 v2))))"
      using eq_forces_to_induct[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete strict_encode_cong shallow_encode_cong application_thunk_cong selection_thunk_cong digestion_thunk_cong identification_thunk_cong 
X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev 
           X_preserve_thunk 
           X_encode_eval X_encode_reasons X_shallow_encode_reasons X_not_shallow_strict X_not_strict_shallow X_encode_eval_rev_does_not_exist  X_thunk_reasons X_self
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

        obtain v1 where "forces_to h1 v1" and "strengthen X v1 v2"
          using force_all_n[of "Thunk h1" "Thunk h2"] E F2 by blast
        then have "force h1 = Some v1" using force_unique by auto
        then show ?thesis using None1 by auto
      qed
    next
      case (Some v1)
      then have Some1: "forces_to h1 v1" using force_some by auto
      then obtain n1 where F1: "force_with_fuel n1 h1 = Some v1"
        using forces_to_def by blast

      obtain v2 where "forces_to h2 v2" and EQRES: "strengthen X v1 v2"
        using force_all_n[of "Thunk h1" "Thunk h2"] E F1 by blast
      then have "force h2 = Some v2" using force_unique by auto
      then show ?thesis 
        using EQRES Some forces_to_data strengthen_def
        using Some1 by fastforce
    qed
  qed
 
lemma evals_X:
 fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
  assumes strict_encode_cong: "\<And>t1 t2. X (Thunk t1) (Thunk t2)
                                       \<Longrightarrow> X (Encode (Strict t1)) (Encode (Strict t2))"
  assumes shallow_encode_cong: "\<And>t1 t2. X (Thunk t1) (Thunk t2)
                                        \<Longrightarrow> X (Encode (Shallow t1)) (Encode (Shallow t2))"
  assumes application_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Application t1)) (Thunk (Application t2))"
  assumes selection_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Selection t1)) (Thunk (Selection t2))"
  assumes digestion_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Digestion t1)) (Thunk (Digestion t2))"
  assumes identification_thunk_cong: 
            "\<And> d1 d2. X (Data d1) (Data d2)
                      \<Longrightarrow> X (Thunk (Identification d1)) (Thunk (Identification d2))"
  assumes X_preserve_tree_ref: "\<And>t h.
    X (HTreeRef t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t'))"
  assumes X_preserve_tree_ref_or_encode_rev: "\<And>t h.
    X h (HTreeRef t) \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t')) \<or> (\<exists>t'. h = (Encode (Shallow t')))"
  assumes X_preserve_blob_ref: "\<And>t h.
    X (HBlobRef t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t'))"
  assumes X_preserve_blob_ref_or_encode_rev: "\<And>t h.
    X h (HBlobRef t) \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t')) \<or> (\<exists>t'. h = (Encode (Shallow t')))"
  assumes X_preserve_tree: "\<And>t h.
    X (HTreeObj t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t'))"
  assumes X_preserve_tree_or_encode_rev: "\<And>t h.
    X h (HTreeObj t) \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t')) \<or> (\<exists>t'. h = (Encode (Strict t')))"
  assumes X_preserve_blob: "\<And>t h.
    X (HBlobObj t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t'))"
  assumes X_preserve_blob_or_encode_rev: "\<And>t h.
    X h (HBlobObj t) \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t')) \<or> (\<exists>t'. h = (Encode (Strict t')))"
  assumes X_preserve_thunk: "\<And>h1 h2.
    X h1 h2 \<longrightarrow>
    ((\<exists>t1. h1 = (Thunk t1)) \<longleftrightarrow> (\<exists>t2. h2 = (Thunk t2)))"
  assumes X_encode_eval: "\<And>e h2. 
         X (Encode e) h2 \<Longrightarrow> 
         \<not> (\<exists>e2. h2 = Encode e2) \<Longrightarrow>
         executes_to e h2"
  assumes X_encode_reasons: "\<And>t1 t2. 
         X (Encode (Strict t1)) (Encode (Strict t2)) \<Longrightarrow> 
         X (Thunk t1) (Thunk t2) \<or>
         rel_opt X (execute (Strict t1)) (execute (Strict t2))"
  assumes X_shallow_encode_reasons: "\<And>t1 t2. 
         X (Encode (Shallow t1)) (Encode (Shallow t2)) \<Longrightarrow> 
         X (Thunk t1) (Thunk t2) \<or>
         rel_opt X (execute (Shallow t1)) (execute (Shallow t2))"
  assumes X_not_shallow_strict:
    "\<And> t1 t2. \<not> X (Encode (Shallow t1)) (Encode (Strict t2))"
  assumes X_not_strict_shallow:
    "\<And> t1 t2. \<not> X (Encode (Strict t1)) (Encode (Shallow t2))"
  assumes X_encode_eval_rev_does_not_exist: "\<And>e h1. 
         X h1 (Encode e) \<Longrightarrow> 
         \<not> (\<exists>e1. h1 = Encode e1) \<Longrightarrow>
         False"
  assumes X_thunk_reasons: "\<And>t1 t2. X (Thunk t1) (Thunk t2) \<Longrightarrow> (
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2) \<or>
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2) \<or>
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Digestion tree1 \<and> t2 = Digestion tree2) \<or>
     (\<exists>d1 d2. X (Data d1) (Data d2) \<and> t1 =  Identification d1 \<and> t2 = Identification d2) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> strengthen X r1 r2) \<or>
     (think t1 = Some (Thunk t2))) \<or>
     (think t1 = Some (Encode (Strict t2))) \<or>
     (think t1 = Some (Encode (Shallow t2)))"
  assumes X_self: "\<And>h. X h h"
  assumes E: "X h1 h2"
  shows "rel_opt X (eval h1) (eval h2)"
proof -
 have eval_all_n: "\<And>h1 h2 n. X h1 h2 \<Longrightarrow>
        (\<forall>v1. eval_with_fuel n h1 = Some v1 \<longrightarrow> (\<exists>v2. evals_to h2 v2 \<and> X v1 v2))
      \<and>
        (\<forall>v2. eval_with_fuel n h2 = Some v2 \<longrightarrow> (\<exists>v1. evals_to h1 v1 \<and> X v1 v2))"
      using eq_forces_to_induct[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete strict_encode_cong shallow_encode_cong application_thunk_cong selection_thunk_cong digestion_thunk_cong identification_thunk_cong 
X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev 
           X_preserve_thunk 
           X_encode_eval X_encode_reasons X_shallow_encode_reasons X_not_shallow_strict X_not_strict_shallow X_encode_eval_rev_does_not_exist  X_thunk_reasons X_self
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
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
  assumes strict_encode_cong: "\<And>t1 t2. X (Thunk t1) (Thunk t2)
                                       \<Longrightarrow> X (Encode (Strict t1)) (Encode (Strict t2))"
  assumes shallow_encode_cong: "\<And>t1 t2. X (Thunk t1) (Thunk t2)
                                        \<Longrightarrow> X (Encode (Shallow t1)) (Encode (Shallow t2))"
  assumes application_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Application t1)) (Thunk (Application t2))"
  assumes selection_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Selection t1)) (Thunk (Selection t2))"
  assumes digestion_thunk_cong: 
            "\<And> t1 t2. X (HTreeObj t1) (HTreeObj t2)
                      \<Longrightarrow> X (Thunk (Digestion t1)) (Thunk (Digestion t2))"
  assumes identification_thunk_cong: 
            "\<And> d1 d2. X (Data d1) (Data d2)
                      \<Longrightarrow> X (Thunk (Identification d1)) (Thunk (Identification d2))"
  assumes X_preserve_tree_ref: "\<And>t h.
    X (HTreeRef t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t'))"
  assumes X_preserve_tree_ref_or_encode_rev: "\<And>t h.
    X h (HTreeRef t) \<longrightarrow>
    (\<exists>t'. h = (HTreeRef t')) \<or> (\<exists>t'. h = (Encode (Shallow t')))"
  assumes X_preserve_blob_ref: "\<And>t h.
    X (HBlobRef t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t'))"
  assumes X_preserve_blob_ref_or_encode_rev: "\<And>t h.
    X h (HBlobRef t) \<longrightarrow>
    (\<exists>t'. h = (HBlobRef t')) \<or> (\<exists>t'. h = (Encode (Shallow t')))"
  assumes X_preserve_tree: "\<And>t h.
    X (HTreeObj t) h \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t'))"
  assumes X_preserve_tree_or_encode_rev: "\<And>t h.
    X h (HTreeObj t) \<longrightarrow>
    (\<exists>t'. h = (HTreeObj t')) \<or> (\<exists>t'. h = (Encode (Strict t')))"
  assumes X_preserve_blob: "\<And>t h.
    X (HBlobObj t) h \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t'))"
  assumes X_preserve_blob_or_encode_rev: "\<And>t h.
    X h (HBlobObj t) \<longrightarrow>
    (\<exists>t'. h = (HBlobObj t')) \<or> (\<exists>t'. h = (Encode (Strict t')))"
  assumes X_preserve_thunk: "\<And>h1 h2.
    X h1 h2 \<longrightarrow>
    ((\<exists>t1. h1 = (Thunk t1)) \<longleftrightarrow> (\<exists>t2. h2 = (Thunk t2)))"
  assumes X_encode_eval: "\<And>e h2. 
         X (Encode e) h2 \<Longrightarrow> 
         \<not> (\<exists>e2. h2 = Encode e2) \<Longrightarrow>
         executes_to e h2"
  assumes X_encode_reasons: "\<And>t1 t2. 
         X (Encode (Strict t1)) (Encode (Strict t2)) \<Longrightarrow> 
         X (Thunk t1) (Thunk t2) \<or>
         rel_opt X (execute (Strict t1)) (execute (Strict t2))"
  assumes X_shallow_encode_reasons: "\<And>t1 t2. 
         X (Encode (Shallow t1)) (Encode (Shallow t2)) \<Longrightarrow> 
         X (Thunk t1) (Thunk t2) \<or>
         rel_opt X (execute (Shallow t1)) (execute (Shallow t2))"
  assumes X_not_shallow_strict:
    "\<And> t1 t2. \<not> X (Encode (Shallow t1)) (Encode (Strict t2))"
  assumes X_not_strict_shallow:
    "\<And> t1 t2. \<not> X (Encode (Strict t1)) (Encode (Shallow t2))"
  assumes X_encode_eval_rev_does_not_exist: "\<And>e h1. 
         X h1 (Encode e) \<Longrightarrow> 
         \<not> (\<exists>e1. h1 = Encode e1) \<Longrightarrow>
         False"
  assumes X_thunk_reasons: "\<And>t1 t2. X (Thunk t1) (Thunk t2) \<Longrightarrow> (
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2) \<or>
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2) \<or>
     (\<exists>tree1 tree2. X (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Digestion tree1 \<and> t2 = Digestion tree2) \<or>
     (\<exists>d1 d2. X (Data d1) (Data d2) \<and> t1 =  Identification d1 \<and> t2 = Identification d2) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> strengthen X r1 r2) \<or>
     (think t1 = Some (Thunk t2))) \<or>
     (think t1 = Some (Encode (Strict t2))) \<or>
     (think t1 = Some (Encode (Shallow t2)))"
  assumes X_self: "\<And>h. X h h"
  assumes E: "X (Thunk h1) (Thunk h2)"
  shows "rel_opt (strengthen X) (think h1) (think h2) \<or> (think h1 = Some (Thunk h2)) \<or> (think h1 = Some (Encode (Strict h2))) \<or> (think h1 = Some (Encode (Shallow h2)))"
proof -
  have think_all_n: "\<And>h1 h2 n. X h1 h2 \<Longrightarrow>
       ((\<exists>t1. h1 = Thunk t1) \<longrightarrow>
        (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v1. think_with_fuel n t1 = Some v1 \<longrightarrow> ((\<exists>v2. thinks_to t2 v2 \<and> strengthen X v1 v2) \<or> v1 = Thunk t2 \<or> v1 = Encode (Strict t2)) \<or> v1 = Encode (Shallow t2))))
      \<and>
       ((\<exists>t2. h2 = Thunk t2) \<longrightarrow>
        (\<exists>t1 t2. h1 = Thunk t1 \<and> h2 = Thunk t2 \<and> (\<forall>v2. think_with_fuel n t2 = Some v2 \<longrightarrow> ((\<exists>v1. thinks_to t1 v1 \<and> strengthen X v1 v2) \<or> thinks_to t1 (Thunk t2) \<or> thinks_to t1 (Encode (Strict t2)) \<or> thinks_to t1 (Encode (Shallow t2))))))"
      using eq_forces_to_induct[OF blob_cong tree_cong blob_complete tree_complete blob_ref_cong tree_ref_cong blob_ref_complete tree_ref_complete strict_encode_cong shallow_encode_cong application_thunk_cong selection_thunk_cong digestion_thunk_cong identification_thunk_cong 
X_preserve_tree_ref X_preserve_tree_ref_or_encode_rev X_preserve_blob_ref X_preserve_blob_ref_or_encode_rev X_preserve_tree X_preserve_tree_or_encode_rev X_preserve_blob X_preserve_blob_or_encode_rev 
           X_preserve_thunk 
           X_encode_eval X_encode_reasons X_shallow_encode_reasons X_not_shallow_strict X_not_strict_shallow X_encode_eval_rev_does_not_exist  X_thunk_reasons X_self
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

        have "(\<exists>v1. thinks_to h1 v1 \<and> strengthen X v1 v2) \<or> thinks_to h1 (Thunk h2) \<or> thinks_to h1 (Encode (Strict h2)) \<or> thinks_to h1 (Encode (Shallow h2))"
          using think_all_n[of "Thunk h1" "Thunk h2"] E F2 by blast

        then show ?thesis
          using None1 think_unique by auto
      qed
    next
      case (Some v1)
      then have Some1: "thinks_to h1 v1" using think_some by auto
      then obtain n1 where F1: "think_with_fuel n1 h1 = Some v1"
        using thinks_to_def by blast

      have "(\<exists>v2. thinks_to h2 v2 \<and> strengthen X v1 v2) \<or> v1 = Thunk h2 \<or> v1 = Encode (Strict h2) \<or> v1 = (Encode (Shallow h2))"
        using think_all_n[of "Thunk h1" "Thunk h2"] E F1 by blast

      then show ?thesis
        using Some think_unique by fastforce
      qed
    qed

end