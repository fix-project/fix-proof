theory slice
  imports fix_handle
begin

fun list_slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list option"
  where
"list_slice l a b = 
  (if (a < length l \<and> b < length l \<and> a \<le> b) then
     Some (take (b - a) (drop a l))
   else
     None)"

fun tree_slice :: "TreeName \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> TreeName option"
  where
"tree_slice t x y = map_option create_tree (list_slice (get_tree_raw t) x y)"

fun blob_slice :: "BlobName \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> BlobName option"
  where
"blob_slice t x y = map_option create_blob (list_slice (get_blob_data t) x y)"

lemma blob_slice_X:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"  
  assumes blob_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2)
                              \<Longrightarrow> get_blob_data b1 = get_blob_data b2"
  assumes blob_complete: "\<And>d1 d2. d1 = d2
                                  \<Longrightarrow> X (HBlobObj (create_blob d1)) 
                                        (HBlobObj (create_blob d2))"
  assumes blob_ref_cong: "\<And>b1 b2. X (HBlobObj b1) (HBlobObj b2) 
                                  \<Longrightarrow> X (HBlobRef b1) (HBlobRef b2)"
  assumes blob_ref_complete: "\<And>b1 b2. X (HBlobRef b1) (HBlobRef b2) 
                                  \<Longrightarrow> X (HBlobObj b1) (HBlobObj b2)"

  assumes H: "X (HBlobObj b1) (HBlobObj b2)"
  shows "rel_opt (\<lambda>x y. X (Data (Ref x)) (Data (Ref y))) (map_option BlobRef (blob_slice b1 x y)) (map_option BlobRef (blob_slice b2 x y))"
proof -
  have L: "get_blob_size b1 = get_blob_size b2"
    using H blob_cong get_blob_size_def 
    by presburger

  let ?l1 = "list_slice (get_blob_data b1) x y"
  let ?l2 = "list_slice (get_blob_data b2) x y"
  have "rel_opt (\<lambda>x y. length x = length y) ?l1 ?l2"
    using L
    by (simp, metis get_blob_size_def)

  then have "?l1 = ?l2"
    using H blob_cong by force

  then show ?thesis 
    using rel_opt.elims(1) blob_complete blob_ref_cong by fastforce
qed

lemma tree_slice_X:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes tree_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                              \<Longrightarrow> list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
  assumes tree_complete: "\<And>xs ys. list_all2 X xs ys
                                  \<Longrightarrow> X (HTreeObj (create_tree xs)) 
                                        (HTreeObj (create_tree ys))"
  assumes tree_ref_cong: "\<And>t1 t2. X (Data (Object (TreeObj t1))) (Data (Object (TreeObj t2))) 
                                  \<Longrightarrow> X (Data (Ref (TreeRef t1))) (Data (Ref (TreeRef t2)))"
  assumes tree_ref_cong: "\<And>t1 t2. X (HTreeObj t1) (HTreeObj t2)
                                  \<Longrightarrow> X (HTreeRef t1) (HTreeRef t2)"
  assumes tree_ref_complete: "\<And>t1 t2. X (HTreeRef t1) (HTreeRef t2) 
                                  \<Longrightarrow> X (HTreeObj t1) (HTreeObj t2)"
  assumes H: "X (HTreeObj t1) (HTreeObj t2)"
  shows "rel_opt (\<lambda>x y. X (Data (Ref x)) (Data (Ref y))) (map_option TreeRef (tree_slice t1 x y)) (map_option TreeRef (tree_slice t2 x y))"
proof -
  have L: "get_tree_size t1 = get_tree_size t2"
    by (metis H get_tree_size_def list_all2_lengthD tree_cong)

  let ?l1 = "list_slice (get_tree_raw t1) x y"
  let ?l2 = "list_slice (get_tree_raw t2) x y"
  have "rel_opt (\<lambda>x y. length x = length y) ?l1 ?l2"
    using L
    by (simp, metis get_tree_size_def)

  then have "rel_opt (list_all2 X) ?l1 ?l2"
    using H tree_cong
    using L get_tree_size_def by force

  then show ?thesis 
    using rel_opt.elims(1) tree_complete tree_ref_cong by fastforce
qed


fun slice :: "TreeName \<Rightarrow> Ref option" where
"slice tree = 
  (if (get_tree_size tree = 3) then
   (case ((get_tree_data tree 1), (get_tree_data tree 2)) of
    (Data (Object (BlobObj b1)), Data (Object (BlobObj b2)))
    \<Rightarrow> (let (x, y) = (to_nat (get_blob_data b1), to_nat (get_blob_data b2)) in
          case (get_tree_data tree 0) of
           (Data (Ref (TreeRef t))) \<Rightarrow> map_option (\<lambda>t. (TreeRef t)) (tree_slice t x y)
         | (Data (Ref (BlobRef b))) \<Rightarrow> map_option (\<lambda>t. (BlobRef t)) (blob_slice b x y)
         | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)
else None)"

definition not_encode :: "handle \<Rightarrow> bool"
  where
"not_encode h = (\<not> ((\<exists>e. h = Encode e) ))"

lemma slice_X:
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
  assumes H: "X (HTreeObj t1) (HTreeObj t2) \<and> list_all not_encode (get_tree_raw t1) \<and> list_all not_encode (get_tree_raw t2)"
  shows "rel_opt (\<lambda>x y. X (Data (Ref x)) (Data (Ref y))) (slice t1) (slice t2)"
proof -
  have L: "get_tree_size t1 = get_tree_size t2"
    by (metis H get_tree_size_def list_all2_lengthD tree_cong)

  let ?same_type = "(\<lambda>x y. 
      ((\<exists>b1. x = HBlobObj b1) \<longleftrightarrow> (\<exists>b2. y = HBlobObj b2)) \<and>
      ((\<exists>b1. x = HBlobRef b1) \<longleftrightarrow> (\<exists>b2. y = HBlobRef b2)) \<and>
      ((\<exists>b1. x = HTreeObj b1) \<longleftrightarrow> (\<exists>b2. y = HTreeObj b2)) \<and>
      ((\<exists>b1. x = HTreeRef b1) \<longleftrightarrow> (\<exists>b2. y = HTreeRef b2)) \<and>
      ((\<exists>b1. x = Thunk b1) \<longleftrightarrow> (\<exists>b2. y = Thunk b2)))"

  let ?l1 = "get_tree_raw t1"
  let ?l2 = "get_tree_raw t2"

  have T': "\<forall>i < length ?l1. ?same_type (?l1 ! i) (?l2 ! i)"
  proof (intro allI impI)
    fix i
    assume "i < length ?l1" 
    have rel: "X (?l1 ! i) (?l2 ! i)"
      using H \<open>i < length (get_tree_raw t1)\<close> list_all2_nthD tree_cong by blast
    have NE1: "not_encode (?l1 ! i)"
      using H \<open>i < length (get_tree_raw t1)\<close> list_all_length by blast
    have NE2: "not_encode (?l2 ! i)"
      using H L \<open>i < length (get_tree_raw t1)\<close> get_tree_size_def list_all_length by auto

    show "?same_type (?l1 ! i) (?l2 ! i)"
      using X_preserve_thunk X_preserve_blob X_preserve_tree X_preserve_blob_ref X_preserve_tree_ref X_preserve_blob_or_encode_rev X_preserve_blob_ref_or_encode_rev X_preserve_tree_or_encode_rev X_preserve_tree_ref_or_encode_rev X_preserve_thunk NE1 NE2 rel
      unfolding not_encode_def
      apply (cases "?l1 ! i"; cases "?l2 ! i"; simp_all)
      apply (case_tac x1; case_tac x1a; simp_all; blast)
      apply (metis handle.distinct(2))
      by (metis (full_types) handle.distinct(2))
  qed
  then have T: "list_all2 ?same_type ?l1 ?l2"
    by (smt (verit, best) L get_tree_size_def list_all2_conv_all_nth)

    show ?thesis
    proof (cases "get_tree_size t1 = 3")
     case False
     then show ?thesis using L by simp
    next
     case True
     have True': "get_tree_size t1 = 3"
     using True by simp

     have ST0: "?same_type (?l1 ! 0) (?l2 ! 0)"
       using T' True' get_tree_size_def by auto
     have X0: "X (?l1 ! 0) (?l2 ! 0)"
       using H True' get_tree_size_def list_all2_nthD tree_cong
       by fastforce
     have ST1: "?same_type (?l1 ! 1) (?l2 ! 1)"
       using T' True' get_tree_size_def by auto
     have X1: "X (?l1 ! 1) (?l2 ! 1)"
       using H True' get_tree_size_def list_all2_nthD tree_cong
       by fastforce
     have ST2: "?same_type (?l1 ! 2) (?l2 ! 2)"
       using T' True' get_tree_size_def by auto
     have X2: "X (?l1 ! 2) (?l2 ! 2)"
       using H True' get_tree_size_def list_all2_nthD tree_cong
       by fastforce

     show ?thesis
     proof (cases "\<exists>b1 b2. get_tree_data t1 1 = (HBlobObj b1) 
                         \<and> get_tree_data t1 2 = (HBlobObj b2)")
      case False
      then have "slice t1 = None"
        using True get_tree_data_def
        apply simp
        apply (cases "?l1 ! 1"; cases "?l1 ! 2"; simp_all)
        apply (metis (no_types, lifting) Data.exhaust Data.simps(5,6) Object.exhaust Object.simps(5,6)
            handle.simps(10))
        apply (metis (no_types, lifting) Data.exhaust Data.simps(5,6) Object.exhaust Object.simps(5,6)
            handle.simps(11))
        by (metis H eval_nat_numeral(3) get_tree_size_def lessI list_all_length not_encode_def)

      have False': "\<not>(\<exists>b1 b2. get_tree_data t2 1 = (HBlobObj b1) 
                         \<and> get_tree_data t2 2 = (HBlobObj b2))"
        using ST1 ST2 False
        using get_tree_data_def by force

      then have "slice t2 = None"
        using True' L get_tree_data_def
        apply simp
        apply (cases "?l2 ! 1"; cases "?l2 ! 2"; simp_all)
        apply (metis (no_types, lifting) Data.exhaust Data.simps(5,6)
            Object.exhaust Object.simps(5,6) handle.simps(10))
        apply (metis (no_types, lifting) Data.exhaust Data.simps(5,6)
            Object.exhaust Object.simps(5,6) handle.simps(11))
        by (metis H get_tree_size_def lessI list_all_length
            not_encode_def numeral_2_eq_2 numeral_3_eq_3)

      then show ?thesis
        using \<open>slice t1 = None\<close> by auto
    next
      case True
      obtain b1 b2 where B1: "get_tree_data t1 1 = (HBlobObj b1)"
                     and B2: "get_tree_data t1 2 = (HBlobObj b2)" 
        using True
        by auto
      obtain b1' b2' where B1': "get_tree_data t2 1 = (HBlobObj b1')"
                       and B2': "get_tree_data t2 2 = (HBlobObj b2')" 
        using ST1 ST2 True
        using get_tree_data_def by auto

      have IDX0: "to_nat (get_blob_data b1) = to_nat (get_blob_data b1')"
        using X1 B1 B1'
        using blob_cong get_tree_data_def by force

      have IDX1: "to_nat (get_blob_data b2) = to_nat (get_blob_data b2')"
        using X2 B2 B2'
        using blob_cong get_tree_data_def by force

      have NE1: "not_encode (?l1 ! 0)"
        by (metis H True' get_tree_size_def list_all_length zero_less_numeral)
      have NE2: "not_encode (?l2 ! 0)"
        by (metis H L True' get_tree_size_def list_all_length zero_less_numeral)
      
      show ?thesis
        unfolding not_encode_def 
        using B1 B1' B2 B2' IDX0 IDX1 get_tree_data_def HBlobObj_def True True' ST0 NE1 NE2
      proof (cases "?l1 ! 0")
        case (Encode)
        then show  ?thesis using NE1  unfolding not_encode_def by auto
      next
        case (Thunk t1)
        then obtain t2 where "?l2 ! 0 = Thunk t2"
          using ST0 by auto
        then show ?thesis using Thunk
          using B1 B1' B2 B2' True' L get_tree_data_def
          by simp
      next
        case (Data d1)
        then show ?thesis
        proof (cases d1)
          case (Object o1)
          then show ?thesis
          proof (cases o1)
            case (BlobObj b1)
            then obtain b2 where "?l2 ! 0 = HBlobObj b2"
              using ST0 
              using Data Object by auto
            then show ?thesis using BlobObj B1 B1' B2 B2' True' L get_tree_data_def Data Object
              by simp
          next
            case (TreeObj tree1)
            then obtain tree2 where "?l2 ! 0 = HTreeObj tree2"
              using ST0 
              using Data Object by auto
            then show ?thesis using TreeObj B1 B1' B2 B2' True' L get_tree_data_def Data Object
              by simp
          qed
        next
          case (Ref r1)
          then show ?thesis
          proof (cases r1)
            case (BlobRef b1)
            then obtain b2 where BlobRef': "?l2 ! 0 = HBlobRef b2"
              using Data Ref ST0 by auto
            then have "\<And>x y. blob_slice b1 x y = blob_slice b2 x y"
              using BlobRef Ref blob_slice_X blob_cong blob_ref_cong blob_complete blob_ref_complete X0
              by (metis Data HBlobRef_def blob_slice.simps)
            then show ?thesis 
              using Data Ref BlobRef BlobRef' B1 B1' B2 B2' True' L get_tree_data_def IDX0 IDX1
              using blob_complete blob_ref_cong
              unfolding HBlobRef_def
              by (simp del: blob_slice.simps, auto)
          next
            case (TreeRef t1)
            then obtain t2 where TreeRef': "?l2 ! 0 = HTreeRef t2"
              using Data Ref ST0 by auto
            then have "\<And>x y. rel_opt (\<lambda>x y. X (Data (Ref x)) (Data (Ref y))) (map_option TreeRef (tree_slice t1 x y)) (map_option TreeRef (tree_slice t2 x y))"
              using TreeRef Ref Data tree_slice_X[of X] tree_cong tree_ref_cong tree_complete tree_ref_complete X0 
              unfolding HTreeRef_def HTreeObj_def
              by presburger
            then show ?thesis 
              using Data Ref TreeRef TreeRef' B1 B1' B2 B2' True' L get_tree_data_def IDX0 IDX1
              using tree_complete tree_ref_cong
              unfolding HTreeRef_def
              by (simp del: tree_slice.simps)
          qed
        qed
      qed
    qed
  qed
qed

end