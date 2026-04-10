theory digest
  imports fix_handle
begin

fun get_type :: "handle \<Rightarrow> nat" 
  where
  "get_type (Data (Object (BlobObj _))) = 0"
| "get_type (Data (Object (TreeObj _))) = 1"
| "get_type (Data (Ref (BlobRef _))) = 2"
| "get_type (Data (Ref (TreeRef _))) = 3"
| "get_type (Thunk _) = 4"
| "get_type (Encode _) = 5"

definition not_encode :: "handle \<Rightarrow> bool"
  where
"not_encode h = (\<not> ((\<exists>e. h = Encode e) ))"

fun digest :: "TreeName \<Rightarrow> TreeName"
  where
"digest t = create_tree 
   (map 
     (\<lambda>x. 
       (Data (Object (BlobObj (create_blob (from_nat (get_type x))))))
     )
   (get_tree_raw t))"

lemma digest_X: 
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
  assumes X_self: "\<And>h. X h h"
  assumes H: "X (HTreeObj t1) (HTreeObj t2) \<and> list_all not_encode (get_tree_raw t1) \<and> list_all not_encode (get_tree_raw t2)"
  shows "X (HTreeObj (digest t1)) (HTreeObj (digest t2))"
proof -
  have allX: "list_all2 X (get_tree_raw t1) (get_tree_raw t2)"
    using H tree_cong by blast
  
  have "\<forall>i < length (get_tree_raw t1). get_type (get_tree_raw t1 ! i) = get_type (get_tree_raw t2 ! i)"
  proof (intro allI impI)
    fix i
    assume "i < length (get_tree_raw t1)"
    moreover then have "i < length (get_tree_raw t2)"
      using allX list_all2_lengthD by fastforce
    ultimately have "X (get_tree_raw t1 ! i) (get_tree_raw t2 ! i)"
                and "not_encode (get_tree_raw t1 ! i)"
                and "not_encode (get_tree_raw t2 ! i)"
      using allX list_all2_nthD2 list_all_length H by blast+
    then show "get_type (get_tree_raw t1 ! i) = get_type (get_tree_raw t2 ! i)"
      unfolding not_encode_def 
      using X_preserve_blob X_preserve_tree X_preserve_blob_or_encode_rev X_preserve_tree_or_encode_rev X_preserve_thunk X_preserve_blob_ref X_preserve_tree_ref
      apply (cases "get_tree_raw t1 ! i"; cases "get_tree_raw t2 ! i"; simp)
      apply (case_tac x1; case_tac x1a; simp)
      apply (metis Object.exhaust
          get_type.simps(1,2))
      apply (metis Data.distinct(1) Object.exhaust
          handle.inject(1))
      apply (metis Data.simps(4) Object.exhaust
          handle.inject(1) handle.simps(7))
      apply (metis Ref.exhaust get_type.simps(3,4))
      apply blast
      using X_preserve_blob_ref_or_encode_rev
            X_preserve_tree_ref_or_encode_rev
      unfolding HBlobRef_def HTreeRef_def
      by blast
  qed

  then have "list_all2 (\<lambda>x y. get_type x = get_type y) (get_tree_raw t1) (get_tree_raw t2)"
    by (meson allX list_all2_conv_all_nth)

  then have "digest t1 = digest t2"
    apply (simp del: get_type.simps)
    by (smt (verit, best) list_all2_conv_all_nth
        map_equality_iff)

  then show ?thesis
    using X_self
    by presburger
qed

end