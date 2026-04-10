theory equivalence
  imports evaluation_properties
begin

fun squash :: "handle \<Rightarrow> handle"
  where
  "squash (Data d) = (Data d)"
| "squash (Thunk t) = (Thunk t)"
| "squash (Encode (Strict t)) = (Thunk t)"
| "squash (Encode (Shallow t)) = (Thunk t)"

coinductive R :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  RBlob[intro]:
  "(get_blob_data b1 = get_blob_data b2) 
   \<Longrightarrow> R (HBlobObj b1) (HBlobObj b2)"
| RBlobRef[intro]:
  "R (HBlobObj b1) (HBlobObj b2) \<Longrightarrow> R (HBlobRef b1) (HBlobRef b2)"
| RTree[intro]:
  "list_all2 R (get_tree_raw t1) (get_tree_raw t2) 
   \<Longrightarrow> R (HTreeObj t1) (HTreeObj t2)"
| RTreeRef[intro]:
  "R (HTreeObj t1) (HTreeObj t2)
   \<Longrightarrow> R (HTreeRef t1) (HTreeRef t2)"
| RThunkNone[intro]:
  "think t1 = None \<Longrightarrow> 
   think t2 = None \<Longrightarrow>
   R (Thunk t1) (Thunk t2)"
| RThunkSomeResData[intro]:
  "think t1 = Some (Data d1) \<Longrightarrow>
   think t2 = Some (Data d2) \<Longrightarrow>
   R (lift (Data d1)) (lift (Data d2)) \<Longrightarrow>
   R (Thunk t1) (Thunk t2)"
| RThunkSomeResNotData[intro]:
  "think t1 = Some h1 \<Longrightarrow>
   think t2 = Some h2 \<Longrightarrow>
   \<not> (\<exists>d. h1 = Data d) \<Longrightarrow>
   \<not> (\<exists>d. h2 = Data d) \<Longrightarrow>
   R (squash h1) (squash h2) \<Longrightarrow>
   R (Thunk t1) (Thunk t2)"
| RThunkSomeResEncodeData[intro]:
  "think t1 = Some (Encode e1) \<Longrightarrow>
   think t2 = Some (Data d2) \<Longrightarrow>
   R (Encode (Strict (encode_to_thunk e1))) (lift (Data d2)) \<Longrightarrow>
   R (Thunk t1) (Thunk t2)"
| RThunkSomeResEncodeEncode[intro]:
  "think t1 = Some (Encode e1) \<Longrightarrow>
   think t2 = Some (Encode e2) \<Longrightarrow>
   R (Encode (Strict (encode_to_thunk e1))) (Encode (Strict (encode_to_thunk e2))) \<Longrightarrow>
   R (Thunk t1) (Thunk t2)"
| RThinkSingleStepThunk[intro]:
  "think t1 = Some (Thunk t2) \<Longrightarrow>
   R (Thunk t1) (Thunk t2)"
| RThunkSingleStepEncodeShallow[intro]:
  "think t1 = Some (Encode (Shallow t2)) \<Longrightarrow>
   R (Thunk t1) (Thunk t2)"
| RThunkSingleStepEncodeStrict[intro]:
  "think t1 = Some (Encode (Strict t2)) \<Longrightarrow>
   R (Thunk t1) (Thunk t2)"
| REvalStrictNone[intro]:
  "execute (Strict h1) = None \<Longrightarrow> 
   execute (Strict h2) = None \<Longrightarrow>
   R (Encode (Strict h1)) (Encode (Strict h2))"
| REvalShallowNone[intro]:
  "execute (Shallow h1) = None \<Longrightarrow> 
   execute (Shallow h2) = None \<Longrightarrow>
   R (Encode (Shallow h1)) (Encode (Shallow h2))"
| REvalSomeRes[intro]:
  "execute h1 = Some r1 \<Longrightarrow>
   execute h2 = Some r2 \<Longrightarrow>
   R r1 r2 \<Longrightarrow>
   R (Encode h1) (Encode h2)"
| REvalStep[intro]:
  "execute h1 = Some r1 \<Longrightarrow>
   R (Encode h1) r1"
| RSelf[intro]:
  "R h h"

coinductive R' :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  R'_from_R[intro]:
    "R h1 h2 \<Longrightarrow> R' h1 h2"
| R'_Tree[intro]:
    "list_all2 (\<lambda>x y. R' x y \<or> R x y) (get_tree_raw t1) (get_tree_raw t2)
     \<Longrightarrow> R' (HTreeObj t1) (HTreeObj t2)"
| R'_TreeRef[intro]:
    "R' (HTreeObj t1) (HTreeObj t2)
     \<Longrightarrow> R' (HTreeRef t1) (HTreeRef t2)"
| R'_tree_to_application_thunk[intro]:
    "R' (HTreeObj t1) (HTreeObj t2)
     \<Longrightarrow> R' (Thunk (Application t1)) (Thunk (Application t2))"
| R'_tree_to_selection_thunk[intro]:
    "R' (HTreeObj t1) (HTreeObj t2)
     \<Longrightarrow> R' (Thunk (Selection t1)) (Thunk (Selection t2))"
| R'_tree_to_digestion_thunk[intro]:
    "R' (HTreeObj t1) (HTreeObj t2)
     \<Longrightarrow> R' (Thunk (Digestion t1)) (Thunk (Digestion t2))"
| R'_data_to_identification_thunk[intro]:
    "R' (Data d1) (Data d2)
     \<Longrightarrow> R' (Thunk (Identification d1)) (Thunk (Identification d2))"
| R'_thunk_data[intro]:
  "think t1 = Some (Data d1) \<Longrightarrow>
   think t2 = Some (Data d2) \<Longrightarrow>
   R' (lift (Data d1)) (lift (Data d2)) \<Longrightarrow>
   R' (Thunk t1) (Thunk t2)"
| R'_thunk_not_data[intro]:
  "think t1 = Some h1 \<Longrightarrow>
   think t2 = Some h2 \<Longrightarrow>
   \<not> (\<exists>d. h1 = Data d) \<Longrightarrow>
   \<not> (\<exists>d. h2 = Data d) \<Longrightarrow>
   R' (squash h1) (squash h2) \<Longrightarrow>
   R' (Thunk t1) (Thunk t2)"
| R'_thunk_encode_data[intro]:
  "think t1 = Some (Encode e1) \<Longrightarrow>
   think t2 = Some (Data d2) \<Longrightarrow>
   R' (Encode (Strict (encode_to_thunk e1))) (lift (Data d2)) \<Longrightarrow>
   R' (Thunk t1) (Thunk t2)"
| R'_thunk_encode_encode[intro]:
  "think t1 = Some (Encode e1) \<Longrightarrow>
   think t2 = Some (Encode e2) \<Longrightarrow>
   R' (Encode (Strict (encode_to_thunk e1))) (Encode (Strict (encode_to_thunk e2))) \<Longrightarrow>
   R' (Thunk t1) (Thunk t2)"
| R'_thunk_to_encode_strict[intro]:
  "R' (Thunk t1) (Thunk t2) \<Longrightarrow>
   R' (Encode (Strict t1)) (Encode (Strict t2))"
| R'_thunk_to_encode_shallow[intro]:
  "R' (Thunk t1) (Thunk t2) \<Longrightarrow>
   R' (Encode (Shallow t1)) (Encode (Shallow t2))"
| R'_encode_some_res[intro]:
  "execute h1 = Some r1 \<Longrightarrow>
   execute h2 = Some r2 \<Longrightarrow>
   R' r1 r2 \<Longrightarrow>
   R' (Encode h1) (Encode h2)"

lemma list_all2_R'_to_R:
  assumes IH: "\<And>x y. R' x y \<Longrightarrow> R x y"
  assumes L:  "list_all2 (\<lambda>x y. R' x y \<or> R x y) xs ys"
  shows       "list_all2 R xs ys"
  using L
  by (rule list_all2_mono) (auto dest: IH)

lemma R_to_R':
  assumes "R x y"
  shows "R' x y"
  using assms
  by auto

lemma R'orR_to_R':
  assumes "R' x y \<or> R x y"
  shows "R' x y"
  using assms by auto

lemma list_all2_R'orR_to_R':
  assumes "list_all2 (\<lambda>x y. R' x y \<or> R x y) xs ys"
  shows   "list_all2 R' xs ys"
  using assms
  by (rule list_all2_mono) (auto intro: R'orR_to_R')

lemma list_all2_R_to_R':
  assumes "list_all2 (\<lambda>x y. R x y) xs ys"
  shows   "list_all2 R' xs ys"
  using assms
  by (rule list_all2_mono) (auto intro: R_to_R')

lemma list_all2_R_imp_R'orR:
  assumes H: "list_all2 R xs ys"
  shows "list_all2 (\<lambda>x y. R' x y \<or> R x y) xs ys"
  using assms list_all2_mono by fastforce

lemma list_all2_R'_imp_R'orR:
  assumes "list_all2 R' xs ys"
  shows "list_all2 (\<lambda>x y. R' x y \<or> R x y) xs ys"
  using assms
  by (induction xs ys rule: list_all2_induct) auto

lemma R'_refl: "R' h h"
  by blast

lemma list_all2_R'_self:
"list_all2 R' xs xs"
  using R'_refl
  by (induction xs) auto

lemma blob_cong_R:
  assumes "R (HBlobObj b1) (HBlobObj b2)"
  shows "get_blob_data b1 = get_blob_data b2"
  using assms by (cases rule: R.cases) auto

lemma blob_cong_R':
  assumes "R' (HBlobObj b1) (HBlobObj b2)"
  shows "get_blob_data b1 = get_blob_data b2"
  using assms blob_cong_R
  by (cases rule: "R'.cases") auto

lemma tree_cong_R:
  assumes "R (HTreeObj t1) (HTreeObj t2)"
  shows "list_all2 R (get_tree_raw t1) (get_tree_raw t2)"
  using assms list.rel_refl
  unfolding HTreeObj_def
  apply (cases rule: R.cases; simp_all)
  using RSelf by blast

lemma tree_cong_R':
  assumes "R' (HTreeObj t1) (HTreeObj t2)"
  shows "list_all2 R' (get_tree_raw t1) (get_tree_raw t2)"
  using assms
  apply (cases rule: R'.cases; simp_all) 
  apply (simp add: list_all2_R_to_R' tree_cong_R)
  using list_all2_R'orR_to_R' by blast

lemma blob_complete_R:
  assumes "d1 = d2"
  shows "R (HBlobObj (create_blob d1)) (HBlobObj (create_blob d2))"
  using assms by blast

lemma blob_complete_R':
  assumes "d1 = d2"
  shows "R' (HBlobObj (create_blob d1)) (HBlobObj (create_blob d2))"
  using assms by blast

lemma tree_complete_R:
  assumes "list_all2 R xs ys" 
  shows "R (HTreeObj (create_tree xs)) (HTreeObj (create_tree ys))"
  using assms by fastforce

lemma tree_complete_R':
  assumes "list_all2 R' xs ys" 
  shows "R' (HTreeObj (create_tree xs)) (HTreeObj (create_tree ys))"
  using R'_Tree assms list_all2_R'_imp_R'orR by auto

lemma blob_ref_cong_R:
  assumes "R (HBlobObj b1) (HBlobObj b2)"
  shows "R (HBlobRef b1) (HBlobRef b2)"
  using assms by blast

lemma blob_ref_cong_R':
  assumes "R' (HBlobObj b1) (HBlobObj b2)"
  shows "R' (HBlobRef b1) (HBlobRef b2)"
  using assms blob_cong_R' by blast

lemma tree_ref_cong_R:
  assumes "R (HTreeObj b1) (HTreeObj b2)"
  shows "R (HTreeRef b1) (HTreeRef b2)"
  using assms by blast

lemma tree_ref_cong_R':
  assumes "R' (HTreeObj b1) (HTreeObj b2)"
  shows "R' (HTreeRef b1) (HTreeRef b2)"
  using assms by blast

lemma blob_ref_complete_R:
  assumes "R (HBlobRef b1) (HBlobRef b2)"
  shows "R (HBlobObj b1) (HBlobObj b2)"
  using assms
  apply (cases rule: R.cases; simp_all)
  by blast

lemma blob_ref_complete_R':
  assumes "R' (HBlobRef b1) (HBlobRef b2)"
  shows "R' (HBlobObj b1) (HBlobObj b2)"
  using assms
  apply (cases rule: R'.cases; simp_all)
  using blob_ref_complete_R by auto

lemma tree_ref_complete_R:
  assumes "R (HTreeRef b1) (HTreeRef b2)"
  shows "R (HTreeObj b1) (HTreeObj b2)"
  using assms
  apply (cases rule: R.cases; simp_all)
  by blast

lemma tree_ref_complete_R':
  assumes "R' (HTreeRef b1) (HTreeRef b2)"
  shows "R' (HTreeObj b1) (HTreeObj b2)"
  using assms
  apply (cases rule: R'.cases; simp_all)
  using HTreeObj_def HTreeRef_def R'_from_R tree_ref_complete_R by presburger

lemma strict_encode_cong_R':
  assumes "R' (Thunk th1) (Thunk th2)"
  shows "R' (Encode (Strict th1)) (Encode (Strict th2))"
  using assms
  by blast

lemma shallow_encode_cong_R':
  assumes "R' (Thunk th1) (Thunk th2)"
  shows "R' (Encode (Shallow th1)) (Encode (Shallow th2))"
  using assms
  by blast

lemma application_thunk_cong_R':
  assumes "R' (HTreeObj th1) (HTreeObj th2)"
  shows "R' (Thunk (Application th1)) (Thunk (Application th2))"
  using assms
  by blast

lemma selection_thunk_cong_R':
  assumes "R' (HTreeObj th1) (HTreeObj th2)"
  shows "R' (Thunk (Selection th1)) (Thunk (Selection th2))"
  using assms
  by blast

lemma digestion_thunk_cong_R':
  assumes "R' (HTreeObj th1) (HTreeObj th2)"
  shows "R' (Thunk (Digestion th1)) (Thunk (Digestion th2))"
  using assms
  by blast

lemma identification_thunk_cong_R':
  assumes "R' (Data d1) (Data d2)"
  shows "R' (Thunk (Identification d1)) (Thunk (Identification d2))"
  using assms
  by blast

lemma R_preserve_thunk:
  assumes "R h1 h2"
  shows "(\<exists>th. h1 = Thunk th) \<longleftrightarrow> (\<exists>th. h2 = Thunk th)"
proof
  assume "\<exists>th. h1 = Thunk th"
  then obtain th where "h1 = Thunk th" by auto
  then have "R (Thunk th) h2"
    using assms by simp
  then show "\<exists>th. h2 = Thunk th"
    by (cases rule: R.cases; simp_all) 
next
  assume "\<exists>th. h2 = Thunk th"
  then obtain th where "h2 = Thunk th" by auto
  then have "R h1 (Thunk th)"
    using assms by simp
  then show "\<exists>th. h1 = Thunk th"
    apply (cases rule: R.cases; simp_all)
    using execute_hs force_data
    apply (case_tac h1a; fastforce)
    by blast
qed

lemma R'_preserve_thunk:
  assumes "R' h1 h2"
  shows "(\<exists>th. h1 = Thunk th) \<longleftrightarrow> (\<exists>th. h2 = Thunk th)"
proof
  assume "\<exists>th. h1 = Thunk th"
  then obtain th where "h1 = Thunk th" by auto
  then have "R' (Thunk th) h2"
    using assms by simp
  then show "\<exists>th. h2 = Thunk th"
    using R_preserve_thunk
    by (cases rule: R'.cases; simp_all; blast) 
next
  assume "\<exists>th. h2 = Thunk th"
  then obtain th where "h2 = Thunk th" by auto
  then have "R' h1 (Thunk th)"
    using assms by simp
  then show "\<exists>th. h1 = Thunk th"
    using R_preserve_thunk
    by (cases rule: R'.cases; simp_all)
qed

lemma R_preserve_blob:
  assumes "R h1 h2"
  shows "((\<exists>b. h1 = HBlobObj b) \<longrightarrow> (\<exists>b. h2 = HBlobObj b))"
proof
  assume "\<exists>b. h1 = HBlobObj b"
  then obtain b where "R (HBlobObj b) h2" using assms by auto
  then show "\<exists>b. h2 = HBlobObj b"
    by (cases rule: R.cases; simp_all)
qed

lemma R'_preserve_blob:
  assumes "R' h1 h2"
  shows "((\<exists>b. h1 = HBlobObj b) \<longrightarrow> (\<exists>b. h2 = HBlobObj b))"
proof
  assume "\<exists>b. h1 = HBlobObj b"
  then obtain b where "R' (HBlobObj b) h2" using assms by auto
  then show "\<exists>b. h2 = HBlobObj b"
    using R_preserve_blob
    by (cases rule: R'.cases; simp_all)
qed

lemma R_preserve_blob_ref:
  assumes "R h1 h2"
  shows "((\<exists>b. h1 = HBlobRef b) \<longrightarrow> (\<exists>b. h2 = HBlobRef b))"
proof
  assume "\<exists>b. h1 = HBlobRef b"
  then obtain b where "R (HBlobRef b) h2" using assms by auto
  then show "\<exists>b. h2 = HBlobRef b"
    by (cases rule: R.cases; simp_all)
qed

lemma R'_preserve_blob_ref:
  assumes "R' h1 h2"
  shows "((\<exists>b. h1 = HBlobRef b) \<longrightarrow> (\<exists>b. h2 = HBlobRef b))"
proof
  assume "\<exists>b. h1 = HBlobRef b"
  then obtain b where "R' (HBlobRef b) h2" using assms by auto
  then show "\<exists>b. h2 = HBlobRef b"
    using R_preserve_blob_ref
    by (cases rule: R'.cases; simp_all)
qed

lemma lower_not_obj:
  assumes "h = lower h'"
  shows "\<not> (\<exists>obj. h = Data (Object obj))"
  using assms
  by (metis Data.distinct(1) handle.distinct(2) handle.inject(1) handle.simps(7) lower.elims lower_data.elims)

lemma lift_not_ref:
  assumes "h = lift h'"
  shows "\<not> (\<exists>obj. h = Data (Ref obj))"
  using assms
  by (metis Data.distinct(1) handle.distinct(2) handle.inject(1) handle.simps(7) lift.elims lift_data.elims)

lemma R_preserve_blob_or_encode_rev:
  assumes "R h1 h2"
  shows "(\<exists>b. h2 = HBlobObj b) \<longrightarrow> ((\<exists>b. h1 = HBlobObj b) \<or> (\<exists>e. h1 = Encode (Strict e)))"
proof
  assume "\<exists>b. h2 = HBlobObj b"
  then obtain b where "R h1 (HBlobObj b)" using assms by auto
  then show "(\<exists>b. h1 = HBlobObj b) \<or> (\<exists>e. h1 = (Encode (Strict e)))"
    using lower_not_obj execute_hs
    apply (cases rule: R.cases; simp_all)
    apply (case_tac h1a; simp add: execute_hs)
    by blast
qed

lemma R'_preserve_blob_or_encode_rev:
  assumes "R' h1 h2"
  shows "(\<exists>b. h2 = HBlobObj b) \<longrightarrow> ((\<exists>b. h1 = HBlobObj b) \<or> (\<exists>e. h1 = Encode (Strict e)))"
proof
  assume "\<exists>b. h2 = HBlobObj b"
  then obtain b where "R' h1 (HBlobObj b)" using assms by auto
  then show "(\<exists>b. h1 = HBlobObj b) \<or> (\<exists>e. h1 = (Encode (Strict e)))"
    apply (cases rule: R'.cases; simp_all)
    using R_preserve_blob_or_encode_rev by auto
qed

lemma R_preserve_blob_ref_or_encode_rev:
  assumes "R h1 h2"
  shows "(\<exists>b. h2 = HBlobRef b) \<longrightarrow> ((\<exists>b. h1 = HBlobRef b) \<or> (\<exists>e. h1 = Encode (Shallow e)))"
proof
  assume "\<exists>b. h2 = HBlobRef b"
  then obtain b where "R h1 (HBlobRef b)" using assms by auto
  then show "(\<exists>b. h1 = HBlobRef b) \<or> (\<exists>e. h1 = (Encode (Shallow e)))"
    using lift_not_ref execute_hs
    apply (cases rule: R.cases; simp_all)
    apply (case_tac h1a; simp add: execute_hs)
    by blast
qed

lemma R'_preserve_blob_ref_or_encode_rev:
  assumes "R' h1 h2"
  shows "(\<exists>b. h2 = HBlobRef b) \<longrightarrow> ((\<exists>b. h1 = HBlobRef b) \<or> (\<exists>e. h1 = Encode (Shallow e)))"
proof
  assume "\<exists>b. h2 = HBlobRef b"
  then obtain b where "R' h1 (HBlobRef b)" using assms by auto
  then show "(\<exists>b. h1 = HBlobRef b) \<or> (\<exists>e. h1 = (Encode (Shallow e)))"
    apply (cases rule: R'.cases; simp_all)
    using R_preserve_blob_ref_or_encode_rev by auto
qed

lemma R_preserve_tree:
  assumes "R h1 h2"
  shows "((\<exists>b. h1 = HTreeObj b) \<longrightarrow> (\<exists>b. h2 = HTreeObj b))"
proof
  assume "\<exists>b. h1 = HTreeObj b"
  then obtain b where "R (HTreeObj b) h2" using assms by auto
  then show "\<exists>b. h2 = HTreeObj b"
    by (cases rule: R.cases, simp_all)
qed

lemma R'_preserve_tree:
  assumes "R' h1 h2"
  shows "((\<exists>b. h1 = HTreeObj b) \<longrightarrow> (\<exists>b. h2 = HTreeObj b))"
proof
  assume "\<exists>b. h1 = HTreeObj b"
  then obtain b where "R' (HTreeObj b) h2" using assms by auto
  then show "\<exists>b. h2 = HTreeObj b"
    using R_preserve_tree
    by (cases rule: R'.cases, simp_all)
qed

lemma R_preserve_tree_ref:
  assumes "R h1 h2"
  shows "((\<exists>b. h1 = HTreeRef b) \<longrightarrow> (\<exists>b. h2 = HTreeRef b))"
proof
  assume "\<exists>b. h1 = HTreeRef b"
  then obtain b where "R (HTreeRef b) h2" using assms by auto
  then show "\<exists>b. h2 = HTreeRef b"
    by (cases rule: R.cases, simp_all)
qed

lemma R'_preserve_tree_ref:
  assumes "R' h1 h2"
  shows "((\<exists>b. h1 = HTreeRef b) \<longrightarrow> (\<exists>b. h2 = HTreeRef b))"
proof
  assume "\<exists>b. h1 = HTreeRef b"
  then obtain b where "R' (HTreeRef b) h2" using assms by auto
  then show "\<exists>b. h2 = HTreeRef b"
    using R_preserve_tree_ref
    by (cases rule: R'.cases, simp_all)
qed

lemma R_preserve_tree_or_encode_rev:
  assumes "R h1 h2"
  shows "(\<exists>b. h2 = HTreeObj b) \<longrightarrow> ((\<exists>b. h1 = HTreeObj b) \<or> (\<exists>e. h1 = Encode (Strict e)))"
proof
  assume "\<exists>b. h2 = HTreeObj b"
  then obtain b where "R h1 (HTreeObj b)" using assms by auto
  then show "(\<exists>b. h1 = HTreeObj b) \<or> (\<exists>e. h1 = (Encode (Strict e)))"
    using lower_not_obj execute_hs
    apply (cases rule: R.cases; simp_all)
    apply (case_tac h1a; simp add: execute_hs)
    by blast
qed

lemma R'_preserve_tree_or_encode_rev:
  assumes "R' h1 h2"
  shows "(\<exists>b. h2 = HTreeObj b) \<longrightarrow> ((\<exists>b. h1 = HTreeObj b) \<or> (\<exists>e. h1 = Encode (Strict e)))"
proof
  assume "\<exists>b. h2 = HTreeObj b"
  then obtain b where "R' h1 (HTreeObj b)" using assms by auto
  then show "(\<exists>b. h1 = HTreeObj b) \<or> (\<exists>e. h1 = (Encode (Strict e)))"
    apply (cases rule: R'.cases; simp_all)
    using R_preserve_tree_or_encode_rev by auto
qed

lemma R_preserve_tree_ref_or_encode_rev:
  assumes "R h1 h2"
  shows "(\<exists>b. h2 = HTreeRef b) \<longrightarrow> ((\<exists>b. h1 = HTreeRef b) \<or> (\<exists>e. h1 = Encode (Shallow e)))"
proof
  assume "\<exists>b. h2 = HTreeRef b"
  then obtain b where "R h1 (HTreeRef b)" using assms by auto
  then show "(\<exists>b. h1 = HTreeRef b) \<or> (\<exists>e. h1 = (Encode (Shallow e)))"
    using lift_not_ref execute_hs
    apply (cases rule: R.cases; simp_all)
    apply (case_tac h1a; simp add: execute_hs)
    by blast
qed

lemma R'_preserve_tree_ref_or_encode_rev:
  assumes "R' h1 h2"
  shows "(\<exists>b. h2 = HTreeRef b) \<longrightarrow> ((\<exists>b. h1 = HTreeRef b) \<or> (\<exists>e. h1 = Encode (Shallow e)))"
proof
  assume "\<exists>b. h2 = HTreeRef b"
  then obtain b where "R' h1 (HTreeRef b)" using assms by auto
  then show "(\<exists>b. h1 = HTreeRef b) \<or> (\<exists>e. h1 = (Encode (Shallow e)))"
    apply (cases rule: R'.cases; simp_all)
    using R_preserve_tree_ref_or_encode_rev by auto
qed

lemma R_encode_execute: 
  assumes "R (Encode e) h"
      and "\<not> (\<exists>e'. h = Encode e')"
    shows "executes_to e h"
  using assms execute_some
  by (cases rule: R.cases; simp_all)

lemma R'_encode_execute: 
  assumes "R' (Encode e) h"
      and "\<not> (\<exists>e'. h = Encode e')"
    shows "executes_to e h"
  using assms execute_some R_encode_execute
  by (cases rule: R'.cases; simp_all)

lemma R_strict_encode_reasons: 
  assumes "R (Encode (Strict e1)) (Encode (Strict e2))"
    shows "rel_opt R (execute (Strict e1)) (execute (Strict e2))"
  using assms
  apply (cases rule: R.cases; simp_all)
  using execute_hs force_data apply fastforce
  by (simp add: RSelf endpoint_def execute_def)

lemma R'_strict_encode_reasons: 
  assumes "R' (Encode (Strict e1)) (Encode (Strict e2))"
    shows "R' (Thunk e1) (Thunk e2) \<or> rel_opt R' (execute (Strict e1)) (execute (Strict e2))"
  using assms
  apply (cases rule: R'.cases)
  using R_strict_encode_reasons[of e1 e2] apply (cases "execute (Strict e1)"; simp)
  apply (metis not_Some_eq rel_opt.simps(1,4))
  apply (metis R'_from_R rel_opt.elims(2) rel_opt.simps(2))
  apply (simp_all)
  done

lemma R_shallow_encode_reasons: 
  assumes "R (Encode (Shallow e1)) (Encode (Shallow e2))"
    shows "rel_opt R (execute (Shallow e1)) (execute (Shallow e2))"
  using assms
  apply (cases rule: R.cases; simp_all)
  using execute_hs force_data apply fastforce
  by (simp add: RSelf endpoint_def execute_def)

lemma R'_shallow_encode_reasons: 
  assumes "R' (Encode (Shallow e1)) (Encode (Shallow e2))"
    shows "R' (Thunk e1) (Thunk e2) \<or> rel_opt R' (execute (Shallow e1)) (execute (Shallow e2))"
  using assms
  apply (cases rule: R'.cases)
  using R_shallow_encode_reasons[of e1 e2] apply (cases "execute (Shallow e1)"; simp)
  apply (metis not_Some_eq rel_opt.simps(1,4))
  apply (metis R'_from_R rel_opt.elims(2) rel_opt.simps(2))
  apply (simp_all)
  done

lemma R_encode_execute_rev_does_not_exist:
  assumes "R h1 (Encode e)"
      and "\<not> (\<exists>e1. h1 = Encode e1)"
    shows "False"
  using assms
  apply (cases rule: R.cases; simp_all)
  by force

lemma R'_encode_execute_rev_does_not_exist:
  assumes "R' h1 (Encode e)"
      and "\<not> (\<exists>e1. h1 = Encode e1)"
    shows "False"
  using assms R_encode_execute_rev_does_not_exist
  by (cases rule: R'.cases, simp_all)

lemma execute_strict_to_obj:
  assumes "execute (Strict t) = Some h"
  shows "\<exists>obj. h = (Data (Object obj))"
  using assms execute_hs force_data lift_not_ref
  by (simp, metis Data.exhaust lift.simps(1))

lemma execute_shallow_to_ref:
  assumes "execute (Shallow t) = Some h"
  shows "\<exists>obj. h = (Data (Ref obj))"
  using assms execute_hs force_data lower_not_obj
  by (simp, metis Data.exhaust lower.simps(1))

lemma R_not_shallow_strict:
  assumes "R (Encode (Shallow t1)) (Encode (Strict t2))"
  shows "False"
  using assms
  apply (cases rule: R.cases)
  apply simp+
  using execute_strict_to_obj[of t2] execute_shallow_to_ref[of t1]
  apply simp
  apply (erule exE, erule exE, simp)
  apply (cases rule: R.cases; simp; force)
  using execute_shallow_to_ref by blast

lemma R_not_strict_shallow:
  assumes "R (Encode (Strict t1)) (Encode (Shallow t2))"
  shows "False"
  using assms
  apply (cases rule: R.cases)
  apply simp+
  using execute_strict_to_obj[of t1] execute_shallow_to_ref[of t2]
  apply simp
  apply (erule exE, erule exE, simp)
  apply (cases rule: R.cases; simp; force)
  using execute_strict_to_obj by blast

lemma R'_not_shallow_strict:
  assumes "R' (Encode (Shallow t1)) (Encode (Strict t2))"
  shows "False"
  using assms R_not_shallow_strict
  apply (cases rule: R'.cases)
  apply blast
  apply simp+
  using execute_strict_to_obj[of t2] execute_shallow_to_ref[of t1]
  apply simp
  apply (erule exE, erule exE, simp)
  by (cases rule: R'.cases; simp; force)

lemma R'_not_strict_shallow:
  assumes "R' (Encode (Strict t1)) (Encode (Shallow t2))"
  shows "False"
  using assms R_not_strict_shallow
  apply (cases rule: R'.cases, blast)
  apply simp+
  using execute_strict_to_obj[of t1] execute_shallow_to_ref[of t2]
  apply simp
  apply (erule exE, erule exE, simp)
  by (cases rule: R'.cases; simp; force)

lemma R_lower_to_lift_data:
  assumes "R (lower (Data d1)) (lower (Data d2))"
  shows "R (lift (Data d1)) (lift (Data d2))"
  apply (rule_tac lower_to_lift)
  using blob_cong_R apply blast
  using tree_cong_R apply presburger
  apply blast+
  using tree_complete_R apply force
  apply blast+
  using blob_ref_complete_R apply blast
  using tree_ref_complete_R apply blast
  using R_preserve_tree_ref apply blast
  using R_preserve_blob_ref apply blast
  using assms by auto

lemma R'_lower_to_lift_data:
  assumes "R' (lower (Data d1)) (lower (Data d2))"
  shows "R' (lift (Data d1)) (lift (Data d2))"
  apply (rule_tac lower_to_lift)
  using blob_cong_R' apply blast
  using tree_cong_R' apply presburger
  apply auto[1]
  using tree_complete_R' apply force
  apply auto
  using blob_ref_cong_R' apply auto[1]
  using R'_TreeRef apply force
  using blob_ref_complete_R' apply auto[1]
  using tree_ref_complete_R' apply auto
  using R'_preserve_tree_ref apply auto
  using R'_preserve_blob_ref apply auto
  using assms by auto

lemma R'_lift_to_lower_data:
  assumes "R' (lift (Data d1)) (lift (Data d2))"
  shows "R' (lower (Data d1)) (lower (Data d2))"
  apply (rule_tac lift_to_lower)
  using blob_cong_R' apply blast
  using tree_cong_R' apply presburger
  apply auto[1]
  using tree_complete_R' apply force
  apply auto
  using blob_ref_cong_R' apply auto[1]
  using R'_TreeRef apply force
  using blob_ref_complete_R' apply auto[1]
  using tree_ref_complete_R' apply auto
  using R'_preserve_tree apply auto
  using R'_preserve_blob apply auto
  using assms by auto

lemma R_encode_to_force:
  assumes "R (Encode e1) (Encode e2)"
  shows "rel_opt (relaxed_X R) (force (encode_to_thunk e1)) (force (encode_to_thunk e2))"
  using assms
  apply (cases rule: R.cases; simp_all add: execute_hs) 
  apply (cases e1; cases e2; simp; erule exE; erule exE; simp add: relaxed_X_def)
  using force_data apply fastforce
  using R_not_strict_shallow apply blast
  using R_not_shallow_strict apply blast
  using force_data R_lower_to_lift_data apply (case_tac z; case_tac za; simp_all; blast)
  apply (cases e1; cases e2; simp)
  using force_data apply force
  using R_not_strict_shallow apply blast
  using R_not_shallow_strict apply blast
  using force_data lower.elims apply blast
  apply (cases e1; simp_all)
  apply (case_tac "force x1"; simp_all; case_tac a; simp_all add: relaxed_X_def)
  using RSelf apply presburger
  using RSelf apply presburger
  using force_data apply blast
  apply (case_tac "force x2"; simp_all; case_tac a; simp_all add: relaxed_X_def)
  apply blast
  using RSelf apply presburger
  using force_data by blast

lemma strengthen_R_self:
  "strengthen R h h"
  by (cases h; simp_all add: strengthen_def relaxed_X_def) blast+

lemma strengthen_R'_self:
  "strengthen R' h h"
  by (cases h; simp_all add: strengthen_def relaxed_X_def) blast+

lemma R_thunk_reasons:
  assumes "R (Thunk t1) (Thunk t2)"
  shows "(think t1 = None \<and> think t2 = None) \<or>
         (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> strengthen R r1 r2) \<or>
         (think t1 = Some (Thunk t2)) \<or>
         (think t1 = Some (Encode (Strict t2))) \<or>
         (think t1 = Some (Encode (Shallow t2)))"
  using assms
proof (cases rule: R.cases)
  case (RBlob b1 b2)
  then show ?thesis by auto
next
  case (RBlobRef b1 b2)
  then show ?thesis by auto
next
  case (RTree t1 t2)
  then show ?thesis by auto
next
  case (RTreeRef t1 t2)
  then show ?thesis by auto
next
  case RThunkNone
  then show ?thesis by auto
next
  case (RThunkSomeResData d1 d2)
  moreover then have "strengthen R (Data d1) (Data d2)"
    by (simp add: relaxed_X_def strengthen_def)
  ultimately show ?thesis
    by blast
next
  case (RThunkSomeResNotData h1 h2)
  moreover then have "strengthen R h1 h2"
    apply (cases h1; cases h2; simp_all add: strengthen_def relaxed_X_def)
    apply (case_tac x3; simp_all)
    apply (case_tac x3; simp_all)
    apply (case_tac x3; case_tac x3a; simp_all)
    done
  ultimately show ?thesis
    by blast
next
  case (RThunkSomeResEncodeData e1 d2)
  moreover then have "strengthen R (Encode e1) (Data d2)"
    by (cases e1; simp add: strengthen_def relaxed_X_def)
  ultimately show ?thesis 
    by blast
next
  case (RThunkSomeResEncodeEncode e1 e2)
  moreover then have "strengthen R (Encode e1) (Encode e2)"
    apply (cases e1; cases e2; simp add: strengthen_def relaxed_X_def)
    apply (case_tac "force x1"; case_tac "force x1a"; simp_all)
    using R_strict_encode_reasons execute_hs apply fastforce
    apply (metis Encode.simps(5) R_encode_to_force
        encode_to_thunk_def rel_opt.simps(3))
    using force_data 
    apply (metis Encode.simps(5) R_encode_to_force
        encode_to_thunk_def rel_opt.simps(2))
    apply (case_tac "force x1"; case_tac "force x2"; simp_all)
    using R_encode_to_force apply fastforce+
    done
  ultimately show ?thesis 
    by blast
next
  case RThinkSingleStepThunk
  then show ?thesis by blast
next
  case RThunkSingleStepEncodeShallow
  then show ?thesis by blast
next
  case RThunkSingleStepEncodeStrict
  then show ?thesis by blast
next
  case RSelf
  then show ?thesis 
    using strengthen_R_self by auto
qed

lemma strengthen_R_to_R':
  assumes "strengthen R h1 h2"
  shows "strengthen R' h1 h2"
  using assms
  apply (cases h1; cases h2; simp add: strengthen_def relaxed_X_def R_to_R'; case_tac x3; simp_all)
  apply blast
  apply blast
  apply (case_tac x3a; simp_all)
  apply (case_tac "force x1"; case_tac "force x1a"; simp_all)
  using R_to_R' apply presburger+
  using force_data 
  using relaxed_X_def apply fastforce
  apply (case_tac "force x1"; case_tac "force x2"; simp_all)
  using R_to_R' apply presburger+
  using force_data 
  using relaxed_X_def apply fastforce
  apply (case_tac x3a; simp_all)
  apply (case_tac "force x1"; case_tac "force x2"; simp_all)
  using R_to_R' apply presburger+
  using force_data 
  using relaxed_X_def apply fastforce
  apply (case_tac "force x2"; case_tac "force x2a"; simp_all)
  using R_to_R' apply presburger+
  using force_data 
  using relaxed_X_def apply fastforce
  done

lemma R'_thunk_reasons:
  assumes "R' (Thunk t1) (Thunk t2)"
  shows 
    "(\<exists>tree1 tree2. R' (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Application tree1 \<and> t2 = Application tree2) \<or>
     (\<exists>tree1 tree2. R' (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Selection tree1 \<and> t2 = Selection tree2) \<or>
     (\<exists>tree1 tree2. R' (HTreeObj tree1) (HTreeObj tree2) \<and> t1 = Digestion tree1 \<and> t2 = Digestion tree2) \<or>
     (\<exists>d1 d2. R' (Data d1) (Data d2) \<and> t1 =  Identification d1 \<and> t2 = Identification d2) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> strengthen R' r1 r2) \<or>
     (think t1 = Some (Thunk t2)) \<or>
     (think t1 = Some (Encode (Strict t2))) \<or>
     (think t1 = Some (Encode (Shallow t2)))"
  using assms
proof (cases rule: R'.cases)
  case R'_from_R
  then show ?thesis using R_thunk_reasons[of t1 t2] 
    apply simp
    apply (erule disjE, meson)
    apply (erule disjE)
    using strengthen_R_to_R' apply force
    apply (erule disjE, meson)
    apply (erule disjE, meson)
    by blast
next
  case R'_Tree
  then show ?thesis by simp
next
  case (R'_TreeRef t1 t2)
  then show ?thesis by simp
next
  case (R'_tree_to_application_thunk t1 t2)
  then show ?thesis
    by auto
next
  case (R'_tree_to_selection_thunk t1 t2)
  then show ?thesis by auto
next
  case (R'_tree_to_digestion_thunk t1 t2)
  then show ?thesis by auto
next
  case (R'_data_to_identification_thunk t1 t2)
  then show ?thesis by auto
next
  case (R'_thunk_data d1 d2)
  then have "strengthen R' (Data d1) (Data d2)"
    using strengthen_def relaxed_X_def by simp
  then show ?thesis 
    using local.R'_thunk_data(1,2) by blast
next
  case (R'_thunk_not_data h1 h2)
  then show ?thesis
    apply (cases h1; cases h2; simp_all add: strengthen_def relaxed_X_def)
    apply (case_tac x3; simp)
    apply (case_tac x3; simp)
    by (case_tac x3; case_tac x3a; simp)
next
  case (R'_thunk_encode_data e1 d2)
  then have "relaxed_X R' (Encode e1) (Data d2)"
    using relaxed_X_def
    by (cases e1; simp_all)
  then have "strengthen R' (Encode e1) (Data d2)"
    using strengthen_def
    by simp
  then show ?thesis
    using local.R'_thunk_encode_data(1,2) by blast
next
  case (R'_thunk_encode_encode e1 e2)
  let ?x1 = "encode_to_thunk e1"
  let ?x2 = "encode_to_thunk e2"

  have "R' (Thunk ?x1) (Thunk ?x2) \<or> rel_opt R' (execute (Strict ?x1)) (execute (Strict ?x2))"
    using R'_thunk_encode_encode R'_strict_encode_reasons
    by simp
  then show ?thesis
  proof
    assume "R' (Thunk ?x1) (Thunk ?x2)"
    then have "strengthen R' (Encode e1) (Encode e2)"
      using strengthen_def by auto
    then show ?thesis
      using R'_thunk_encode_encode by blast
  next
    assume "rel_opt R' (execute (Strict ?x1)) (execute (Strict ?x2))"
    then have "rel_opt R' (force ?x1 <$> lift) (force ?x2 <$> lift)"
      by (simp add: execute_hs)

    then have "rel_opt (relaxed_X R') (force ?x1) (force ?x2)"
    proof (cases "force ?x1")
      case None
      then show ?thesis
        by (metis \<open>rel_opt R' (force ?x1 <$> lift) (force ?x2 <$> lift)\<close> map_option_case option.case_eq_if rel_opt.simps(1,4))
    next
      case (Some r1)
      then obtain d1 where "force ?x1 = Some (Data d1)"
        using force_data
        by blast
      then obtain d2 where "force ?x2 = Some (Data d2)"
        by (metis \<open>rel_opt R' (force (encode_to_thunk e1) <$> lift) (force (encode_to_thunk e2) <$> lift)\<close> force_data map_option_case not_Some_eq option.case_eq_if
            rel_opt.simps(3))
      then show ?thesis
        using \<open>force (encode_to_thunk e1) = Some (Data d1)\<close> \<open>rel_opt R' (force (encode_to_thunk e1) <$> lift) (force (encode_to_thunk e2) <$> lift)\<close> relaxed_X_def by fastforce
    qed

    then have "strengthen R' (Encode e1) (Encode e2)"
      by (simp add: strengthen_def)
    then show ?thesis
      using local.R'_thunk_encode_encode(1,2) by blast
  qed
qed

lemma R'_thunk_think:
  assumes "R' (Thunk t1) (Thunk t2)"
  shows "rel_opt (strengthen R') (think t1)
   (think t2) \<or>
  think t1 = Some (Thunk t2) \<or>
  think t1 = Some (Encode (Strict t2)) \<or>
  think t1 = Some (Encode (Shallow t2))"
  apply (rule_tac think_X)
  using blob_cong_R' apply blast
  using tree_cong_R' apply blast
  using blob_complete_R' apply blast
  using tree_complete_R' apply blast
  using blob_ref_cong_R' apply blast
  using tree_ref_cong_R' apply blast
  using blob_ref_complete_R' apply blast
  using tree_ref_complete_R' apply blast
  apply blast+
  using R'_preserve_tree_ref apply blast
  using R'_preserve_tree_ref_or_encode_rev apply blast
  using R'_preserve_blob_ref apply blast
  using R'_preserve_blob_ref_or_encode_rev apply blast
  using R'_preserve_tree apply blast
  using R'_preserve_tree_or_encode_rev apply blast
  using R'_preserve_blob apply blast
  using R'_preserve_blob_or_encode_rev apply blast
  using R'_preserve_thunk apply blast
  using R'_encode_execute apply blast
  using R'_strict_encode_reasons apply blast
  using R'_shallow_encode_reasons apply blast
  using R'_not_shallow_strict apply blast
  using R'_not_strict_shallow apply blast
  using R'_encode_execute_rev_does_not_exist apply blast
  using R'_thunk_reasons apply blast
  apply blast
  using assms apply blast
  done

lemma R'_thunk_force:
  assumes "R' (Thunk t1) (Thunk t2)"
  shows "rel_opt (relaxed_X R') (force t1) (force t2)"
  apply (rule_tac forces_X)
  using blob_cong_R' apply blast
  using tree_cong_R' apply blast
  using blob_complete_R' apply blast
  using tree_complete_R' apply blast
  using blob_ref_cong_R' apply blast
  using tree_ref_cong_R' apply blast
  using blob_ref_complete_R' apply blast
  using tree_ref_complete_R' apply blast
  apply blast+
  using R'_preserve_tree_ref apply blast
  using R'_preserve_tree_ref_or_encode_rev apply blast
  using R'_preserve_blob_ref apply blast
  using R'_preserve_blob_ref_or_encode_rev apply blast
  using R'_preserve_tree apply blast
  using R'_preserve_tree_or_encode_rev apply blast
  using R'_preserve_blob apply blast
  using R'_preserve_blob_or_encode_rev apply blast
  using R'_preserve_thunk apply blast
  using R'_encode_execute apply blast
  using R'_strict_encode_reasons apply blast
  using R'_shallow_encode_reasons apply blast
  using R'_not_shallow_strict apply blast
  using R'_not_strict_shallow apply blast
  using R'_encode_execute_rev_does_not_exist apply blast
  using R'_thunk_reasons apply blast
  apply blast
  using assms apply blast
  done

lemma R'_impl_R:
  assumes "R' h1 h2"
  shows "R h1 h2"
  using assms
proof (coinduction arbitrary: h1 h2 rule: R.coinduct)
  case R
  then show ?case
  proof -
    have thunk_cases: "\<And>th1 th2. R' h1 h2 \<Longrightarrow> h1 = Thunk th1 \<Longrightarrow> h2 = Thunk th2 \<Longrightarrow> ?thesis"
    proof -
      fix th1 th2
      assume "R' h1 h2"
      assume "h1 = Thunk th1"
      assume "h2 = Thunk th2"
      have R'thunk: "R' (Thunk th1) (Thunk th2)"
        using R \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close> by blast

      have "rel_opt (strengthen R') (think th1) (think th2) \<or>
          think th1 = Some (Thunk th2) \<or>
          think th1 = Some (Encode (Strict th2)) \<or> 
          think th1 = Some (Encode (Shallow th2))"
        using R'_thunk_think[OF R'thunk] .
      then show ?case
      proof
        assume ASSM: "rel_opt (strengthen R') (think th1) (think th2)"
        then show ?thesis
        proof (cases "think th1")
          case None
          then have "think th2 = None"
            using ASSM
            using rel_opt.elims(2) by auto
          then show ?thesis using None 
            by (simp add: \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close>)
        next
          case (Some r1)
          then obtain r2 where R2: "think th2 = Some r2" and str: "strengthen R' r1 r2"
            using ASSM
            using rel_opt.elims(2) by force
          then show ?thesis
          proof (cases r1)
            case (Data x1)
            then have "relaxed_X R' (Data x1) r2"
              using str strengthen_def by auto
            then have "R' (lift (Data x1)) (lift r2)"
              using relaxed_X_def by simp
            then obtain d2 where "r2 = Data d2"
              by (metis R'_encode_execute_rev_does_not_exist R'_preserve_thunk handle.distinct(2) handle.exhaust handle.simps(7) lift.simps(1,2,3))
            then show ?thesis
              using Data R2 Some \<open>R' (lift (Data x1)) (lift r2)\<close>
                \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close> by auto
          next
            case (Thunk t1)
            then have str: "strengthen R' (Thunk t1) r2"
              using str strengthen_def by meson
            then show ?thesis 
            proof (cases "\<exists>e. r2 = Encode e")
              case True
              then obtain e where R2E: "r2 = Encode e" 
                by auto
              then have "R' (Thunk t1) (Thunk (encode_to_thunk e))"
                using str strengthen_def relaxed_X_def
                by simp
              moreover have "squash r1 = Thunk t1"
                by (simp add: Thunk)
              moreover have "squash r2 = Thunk (encode_to_thunk e)"
                using R2E
                by (cases e; simp_all)
              ultimately have "R' (squash r1) (squash r2)"
                by presburger
              then have ?RThunkSomeResNotData
                using R2 R2E Thunk Some R'_tree_to_application_thunk
                using \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close> by blast
              then show ?thesis by blast
            next
              case False
              then have "relaxed_X R' (Thunk t1) r2"
                using str strengthen_def
                by (simp, metis handle.exhaust handle.simps(10,11))
              then have "R' (Thunk t1) (lift r2)"
                by (simp add: relaxed_X_def)
              then obtain t2 where R2T: "r2 = Thunk t2" and "R' (Thunk t1) (Thunk t2)"
                using R'_preserve_thunk
                by (cases r2) auto
              then have ?RThunkSomeResNotData
                using R2 R2T Thunk Some
                by (simp add: \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close>)
              then show ?thesis by blast
            qed
          next
            case (Encode e1)
            then have str: "strengthen R' (Encode e1) r2"
              using str strengthen_def by auto
            then show ?thesis
            proof (cases r2)
              case (Data d2)
              then have "relaxed_X R' (Encode e1) (Data d2)"
                using str strengthen_def by auto
          
              then have ?RThunkSomeResEncodeData
                using R2 Some Encode Data R'_tree_to_application_thunk relaxed_X_def
                by (cases e1; simp_all add: \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close>) 
              then show ?thesis by blast
            next
              case (Thunk t2)
              then have "strengthen R' (Encode e1) (Thunk t2)"
                using str by blast
              then have "R' (squash r1) (squash r2)"
                using Some Encode Thunk strengthen_def
                by (cases e1; simp)
              then have ?RThunkSomeResNotData
                using Encode R2 Some Thunk \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close>
                by blast
              then show ?thesis by blast
            next
              case (Encode e2)
              then have "strengthen R' (Encode e1) (Encode e2)"
                using str by blast
              then have "R' (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2)) \<or> rel_opt (relaxed_X R') (force (encode_to_thunk e1)) (force (encode_to_thunk e2))"
                using strengthen_def by simp
              then show ?thesis
              proof
                assume "R' (Thunk (encode_to_thunk e1)) (Thunk (encode_to_thunk e2))"
                then have "R' (squash r1) (squash r2)"
                  using Some Encode R2 \<open>r1 = Encode e1\<close> strengthen_def
                  by (cases e1; cases e2; simp_all)
                then have ?RThunkSomeResNotData
                  using \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close> R2 Encode \<open>r1 = Encode e1\<close> Some
                  by blast
                then show ?thesis
                  by blast
              next
                assume REL: "rel_opt (relaxed_X R') (force (encode_to_thunk e1)) (force (encode_to_thunk e2))"
                then show ?thesis
                proof (cases "force (encode_to_thunk e1)")
                  case None
                  moreover then have "force (encode_to_thunk e2) = None"
                    using REL
                    using rel_opt.elims(2) by auto
                  ultimately have "R' (Encode (Strict (encode_to_thunk e1))) (Encode (Strict (encode_to_thunk e2)))"
                    by (simp add: R'_from_R REvalStrictNone execute_hs)
                  then have ?RThunkSomeResEncodeEncode
                    using \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close> R2 Encode \<open>r1 = Encode e1\<close> Some
                    by blast
                  then show ?thesis
                    by blast
                next
                  case (Some r1')
                  then obtain d1 where "force (encode_to_thunk e1) = Some (Data d1)"
                    using force_data by blast
                  moreover then obtain d2 where "force (encode_to_thunk e2) = Some (Data d2)"
                    using REL force_data
                    by (metis rel_opt.elims(2))
                  ultimately have "relaxed_X R' (Data d1) (Data d2)"
                    using REL by auto

                  have "execute (Strict (encode_to_thunk e1)) = Some (lift (Data d1))"
                    using execute_hs
                    using \<open>force (encode_to_thunk e1) = Some (Data d1)\<close> by auto
                  moreover have "execute (Strict (encode_to_thunk e2)) = Some (lift (Data d2))"
                    using execute_hs
                    using \<open>force (encode_to_thunk e2) = Some (Data d2)\<close> by auto
                  ultimately have "R' (Encode (Strict (encode_to_thunk e1))) (Encode (Strict (encode_to_thunk e2)))"
                    using \<open>relaxed_X R' (Data d1) (Data d2)\<close> relaxed_X_def by auto
                  then have ?RThunkSomeResEncodeEncode
                    using \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close> \<open>think th1 = Some r1\<close>  R2 Encode Some \<open>r1 = Encode e1\<close>
                    by blast
                  then show ?thesis
                    by blast
                qed
              qed
            qed
          qed
        qed
      next
        assume "think th1 = Some (Thunk th2) \<or>
    think th1 =
    Some (Encode (Strict th2)) \<or>
    think th1 =
    Some (Encode (Shallow th2))"
        then show ?case
          using \<open>h1 = Thunk th1\<close> \<open>h2 = Thunk th2\<close> by auto
      qed
    qed
      
    from R
    show ?case
    proof (cases rule: R'.cases)
      case R'_from_R
      then show ?thesis
      using list_all2_R_imp_R'orR
      by (cases rule: R.cases; simp_all)
    next
      case (R'_Tree t1 t2)
      then show ?thesis by simp
    next
      case (R'_TreeRef t1 t2)
      then show ?thesis by simp
    next
      case (R'_tree_to_application_thunk t1 t2)
      then show ?thesis
        using thunk_cases
        using R by presburger
    next
      case (R'_tree_to_selection_thunk t1 t2)
      then show ?thesis
        using thunk_cases
        using R by presburger
    next
      case (R'_tree_to_digestion_thunk t1 t2)
      then show ?thesis
        using thunk_cases
        using R by presburger
    next
      case (R'_data_to_identification_thunk d1 d2)
      then show ?thesis
        using thunk_cases
        using R by presburger
    next
      case (R'_thunk_data t1 d1 t2 d2)
      then show ?thesis by auto
    next
      case (R'_thunk_not_data t1 h1 t2 h2)
      then show ?thesis by auto
    next
      case (R'_thunk_encode_data t1 e1 t2 d2)
      then show ?thesis by auto
    next
      case (R'_thunk_encode_encode t1 e1 t2 e2)
      then show ?thesis by auto
    next
      case (R'_thunk_to_encode_strict t1 t2)
      then have REL: "rel_opt (relaxed_X R') (force t1) (force t2)"
        using R'_thunk_force by blast
      then have "rel_opt R' (execute (Strict t1)) (execute (Strict t2))" 
      proof (cases "force t1")
        case None
        moreover then have "force t2 = None"
          using REL
          using rel_opt.elims(2) by auto
        ultimately show ?thesis
          using execute_hs by simp
      next
        case (Some r1)
        moreover then obtain r2 where "force t2 = Some r2" and "R' (lift r1) (lift r2)"
          using REL
          by (metis force_data handle.simps(10) option.sel option.simps(3) rel_opt.elims(2) relaxed_X_def)
        then show ?thesis
          using execute_hs 
          by (simp add: calculation)
      qed
      then show ?thesis 
        by (metis (lifting) local.R'_thunk_to_encode_strict(1,2) rel_opt.elims(2))
    next
      case (R'_thunk_to_encode_shallow t1 t2)
      then have REL: "rel_opt (relaxed_X R') (force t1) (force t2)"
        using R'_thunk_force by blast
      then have "rel_opt R' (execute (Shallow t1)) (execute (Shallow t2))" 
      proof (cases "force t1")
        case None
        moreover then have "force t2 = None"
          using REL
          using rel_opt.elims(2) by auto
        ultimately show ?thesis
          using execute_hs by simp
      next
        case (Some r1)
        moreover then obtain r2 where "force t2 = Some r2" and "R' (lift r1) (lift r2)"
          using REL
          by (metis force_data handle.simps(10) option.sel option.simps(3) rel_opt.elims(2) relaxed_X_def)
        then have "R' (lower r1) (lower r2)"
          by (metis R'_lift_to_lower_data calculation force_data)
        then show ?thesis
          using execute_hs 
          by (simp add: \<open>force t2 = Some r2\<close> calculation)
      qed
      then show ?thesis
        by (metis (lifting) local.R'_thunk_to_encode_shallow(1,2) rel_opt.elims(2))
    next
      case (R'_encode_some_res h1 r1 h2 r2)
      then show ?thesis by auto
    qed
  qed
qed

end
