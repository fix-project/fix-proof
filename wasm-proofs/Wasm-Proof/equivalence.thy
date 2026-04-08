theory equivalence
  imports evaluation
begin

coinductive R :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  RBlob[intro]:
  "(get_blob_data b1 = get_blob_data b2) 
   \<Longrightarrow> R (HBlobHandle b1) (HBlobHandle b2)"
| RTree[intro]:
  "list_all2 R (get_tree_raw t1) (get_tree_raw t2) 
   \<Longrightarrow> R (HTreeHandle t1) (HTreeHandle t2)"
| RThunkNone[intro]:
  "think t1 = None \<Longrightarrow> 
   think t2 = None \<Longrightarrow>
   R (HThunkHandle t1) (HThunkHandle t2)"
| RThunkSomeRes[intro]:
  "think t1 = Some r1 \<Longrightarrow>
   think t2 = Some r2 \<Longrightarrow>
   R r1 r2 \<Longrightarrow>
   R (HThunkHandle t1) (HThunkHandle t2)"
| RThinkSingleStepThunk[intro]:
  "think t1 = Some (HThunkHandle t2) \<Longrightarrow>
   R (HThunkHandle t1) (HThunkHandle t2)"
| RThunkSingleStepEncode[intro]:
  "think t1 = Some (HEncodeHandle t2) \<Longrightarrow>
   R (HThunkHandle t1) (HThunkHandle (get_encode_thunk t2))"
| REvalNone[intro]:
  "execute h1 = None \<Longrightarrow> 
   execute h2 = None \<Longrightarrow>
   R (HEncodeHandle h1) (HEncodeHandle h2)"
| REvalSomeRes[intro]:
  "execute h1 = Some r1 \<Longrightarrow>
   execute h2 = Some r2 \<Longrightarrow>
   R r1 r2 \<Longrightarrow>
   R (HEncodeHandle h1) (HEncodeHandle h2)"
| REvalStep[intro]:
  "execute h1 = Some r1 \<Longrightarrow>
   R (HEncodeHandle h1) r1"
| RSelf[intro]:
  "R h h"

coinductive R' :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  R'_from_R[intro]:
    "R h1 h2 \<Longrightarrow> R' h1 h2"
| R'_Tree[intro]:
    "list_all2 (\<lambda>x y. R' x y \<or> R x y) (get_tree_raw t1) (get_tree_raw t2)
     \<Longrightarrow> R' (HTreeHandle t1) (HTreeHandle t2)"
| R'_tree_to_thunk[intro]:
    "R' (HTreeHandle t1) (HTreeHandle t2)
     \<Longrightarrow> R' (HThunkHandle (create_thunk t1)) (HThunkHandle (create_thunk t2))"
| R'_thunk_some_res[intro]:
  "think t1 = Some r1 \<Longrightarrow>
   think t2 = Some r2 \<Longrightarrow>
   R' r1 r2 \<Longrightarrow>
   R' (HThunkHandle t1) (HThunkHandle t2)"
| R'_thunk_to_encode[intro]:
  "R' (HThunkHandle t1) (HThunkHandle t2) \<Longrightarrow>
   R' (HEncodeHandle (create_encode t1)) (HEncodeHandle (create_encode t2))"
| R'_encode_some_res[intro]:
  "execute h1 = Some r1 \<Longrightarrow>
   execute h2 = Some r2 \<Longrightarrow>
   R' r1 r2 \<Longrightarrow>
   R' (HEncodeHandle h1) (HEncodeHandle h2)"

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

lemma get_blob_data_cong_R:
  assumes "R (HBlobHandle b1) (HBlobHandle b2)"
  shows "get_blob_data b1 = get_blob_data b2"
  using assms by (cases rule: R.cases) auto

lemma get_blob_data_cong_R':
  assumes "R' (HBlobHandle b1) (HBlobHandle b2)"
  shows "get_blob_data b1 = get_blob_data b2"
  using assms get_blob_data_cong_R
  by (cases rule: "R'.cases") auto

lemma R_tree_children:
  assumes "R (HTreeHandle t1) (HTreeHandle t2)"
  shows "list_all2 R (get_tree_raw t1) (get_tree_raw t2)"
  using assms
proof (cases rule: R.cases) 
  case RTree
  then show ?thesis by blast
next
  case RSelf
  then show ?thesis
    using R.RSelf list.rel_refl by blast
qed

lemma R'_tree_children:
  assumes "R' (HTreeHandle t1) (HTreeHandle t2)"
  shows "list_all2 R' (get_tree_raw t1) (get_tree_raw t2)"
  using assms
proof (cases rule: R'.cases) 
  case R'_Tree
  then show ?thesis
    using list_all2_R'orR_to_R' by blast
next
  case R'_from_R
  then show ?thesis
    using R_tree_children list_all2_R_to_R' by blast
qed

lemma get_tree_size_cong_R:
  assumes "R (HTreeHandle t1) (HTreeHandle t2)"
  shows "get_tree_size t1 = get_tree_size t2"
  using R_tree_children[OF assms]
  by (simp add: get_tree_size_def list_all2_lengthD)

lemma get_tree_size_cong_R':
  assumes "R' (HTreeHandle t1) (HTreeHandle t2)"
  shows "get_tree_size t1 = get_tree_size t2"
  using R'_tree_children[OF assms]
  by (simp add: get_tree_size_def list_all2_lengthD)

lemma get_tree_data_cong_R:
  assumes "R (HTreeHandle t1) (HTreeHandle t2)" and "i < get_tree_size t1"
  shows "R (get_tree_data t1 i) (get_tree_data t2 i)"
  by (metis R_tree_children assms(1,2) get_tree_data_def get_tree_size_def list_all2_conv_all_nth)

lemma get_tree_data_cong_R':
  assumes "R' (HTreeHandle t1) (HTreeHandle t2)" and "i < get_tree_size t1"
  shows "R' (get_tree_data t1 i) (get_tree_data t2 i)"
  by (metis R'_tree_children assms(1,2) get_tree_data_def get_tree_size_def list_all2_conv_all_nth)

lemma create_blob_cong_R:
  assumes "d1 = d2"
  shows "R (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
  using assms by blast

lemma create_blob_cong_R':
  assumes "d1 = d2"
  shows "R' (HBlobHandle (create_blob d1)) (HBlobHandle (create_blob d2))"
  using assms by blast

lemma create_tree_cong_R:
  assumes "list_all2 R xs ys"
  shows "R (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
  by (simp add: RTree assms)

lemma create_tree_cong_R':
  assumes "list_all2 R' xs ys"
  shows "R' (HTreeHandle (create_tree xs)) (HTreeHandle (create_tree ys))"
  by (simp add: R'_Tree assms list_all2_R'_imp_R'orR)

lemma create_thunk_cong_R':
  assumes "R' (HTreeHandle th1) (HTreeHandle th2)"
  shows "R' (HThunkHandle (create_thunk th1)) (HThunkHandle (create_thunk th2))"
  using assms
  by blast

lemma create_encode_cong_R':
  assumes "R' (HThunkHandle th1) (HThunkHandle th2)"
  shows "R' (HEncodeHandle (create_encode th1)) (HEncodeHandle (create_encode th2))"
  using assms
  by blast

lemma R_preserve_thunk:
  assumes "R h1 h2"
  shows "(\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th)"
proof
  assume "\<exists>th. h1 = HThunkHandle th"
  then obtain th where "h1 = HThunkHandle th" by auto
  then have "R (HThunkHandle th) h2"
    using assms by simp
  then show "\<exists>th. h2 = HThunkHandle th"
    by (cases rule: R.cases) blast+
next
  assume "\<exists>th. h2 = HThunkHandle th"
  then obtain th where "h2 = HThunkHandle th" by auto
  then have "R h1 (HThunkHandle th)"
    using assms by simp
  then show "\<exists>th. h1 = HThunkHandle th"
    by (cases rule: R.cases, blast+, metis execute_some execute_with_fuel.simps executes_to_def force_with_fuel_not_thunk handle.distinct(3,7), blast)
qed

lemma R'_preserve_thunk:
  assumes "R' h1 h2"
  shows "(\<exists>th. h1 = HThunkHandle th) \<longleftrightarrow> (\<exists>th. h2 = HThunkHandle th)"
proof
  assume "\<exists>th. h1 = HThunkHandle th"
  then obtain th where "h1 = HThunkHandle th" by auto
  then have "R' (HThunkHandle th) h2"
    using assms by simp
  then show "\<exists>th. h2 = HThunkHandle th"
    using R_preserve_thunk
    by (cases rule: R'.cases, blast+) 
next
  assume "\<exists>th. h2 = HThunkHandle th"
  then obtain th where "h2 = HThunkHandle th" by auto
  then have "R' h1 (HThunkHandle th)"
    using assms by simp
  then show "\<exists>th. h1 = HThunkHandle th"
    using R_preserve_thunk
    by (cases rule: R'.cases, blast+)
qed

lemma R_preserve_blob:
  assumes "R h1 h2"
  shows "((\<exists>b. h1 = HBlobHandle b) \<longrightarrow> (\<exists>b. h2 = HBlobHandle b))"
proof
  assume "\<exists>b. h1 = HBlobHandle b"
  then obtain b where "R (HBlobHandle b) h2" using assms by auto
  then show "\<exists>b. h2 = HBlobHandle b"
    by (cases rule: R.cases, blast+)
qed

lemma R'_preserve_blob:
  assumes "R' h1 h2"
  shows "((\<exists>b. h1 = HBlobHandle b) \<longrightarrow> (\<exists>b. h2 = HBlobHandle b))"
proof
  assume "\<exists>b. h1 = HBlobHandle b"
  then obtain b where "R' (HBlobHandle b) h2" using assms by auto
  then show "\<exists>b. h2 = HBlobHandle b"
    using R_preserve_blob
    by (cases rule: R'.cases, blast+)
qed

lemma R_preserve_blob_or_encode_rev:
  assumes "R h1 h2"
  shows "(\<exists>b. h2 = HBlobHandle b) \<longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e))"
proof
  assume "\<exists>b. h2 = HBlobHandle b"
  then obtain b where "R h1 (HBlobHandle b)" using assms by auto
  then show "(\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)"
    by (cases rule: R.cases, blast+)
qed

lemma R'_preserve_blob_or_encode_rev:
  assumes "R' h1 h2"
  shows "(\<exists>b. h2 = HBlobHandle b) \<longrightarrow> ((\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e))"
proof
  assume "\<exists>b. h2 = HBlobHandle b"
  then obtain b where "R' h1 (HBlobHandle b)" using assms by auto
  then show "(\<exists>b. h1 = HBlobHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)"
    using R_preserve_blob_or_encode_rev
    by (cases rule: R'.cases, blast+)
qed

lemma R_preserve_tree:
  assumes "R h1 h2"
  shows "((\<exists>b. h1 = HTreeHandle b) \<longrightarrow> (\<exists>b. h2 = HTreeHandle b))"
proof
  assume "\<exists>b. h1 = HTreeHandle b"
  then obtain b where "R (HTreeHandle b) h2" using assms by auto
  then show "\<exists>b. h2 = HTreeHandle b"
    by (cases rule: R.cases, blast+)
qed

lemma R'_preserve_tree:
  assumes "R' h1 h2"
  shows "((\<exists>b. h1 = HTreeHandle b) \<longrightarrow> (\<exists>b. h2 = HTreeHandle b))"
proof
  assume "\<exists>b. h1 = HTreeHandle b"
  then obtain b where "R' (HTreeHandle b) h2" using assms by auto
  then show "\<exists>b. h2 = HTreeHandle b"
    using R_preserve_tree
    by (cases rule: R'.cases, blast+)
qed

lemma R_preserve_tree_or_encode_rev:
  assumes "R h1 h2"
  shows "(\<exists>b. h2 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e))"
proof
  assume "\<exists>b. h2 = HTreeHandle b"
  then obtain b where "R h1 (HTreeHandle b)" using assms by auto
  then show "(\<exists>b. h1 = HTreeHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)"
    by (cases rule: R.cases, blast+)
qed

lemma R'_preserve_tree_or_encode_rev:
  assumes "R' h1 h2"
  shows "(\<exists>b. h2 = HTreeHandle b) \<longrightarrow> ((\<exists>b. h1 = HTreeHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e))"
proof
  assume "\<exists>b. h2 = HTreeHandle b"
  then obtain b where "R' h1 (HTreeHandle b)" using assms by auto
  then show "(\<exists>b. h1 = HTreeHandle b) \<or> (\<exists>e. h1 = HEncodeHandle e)"
    using R_preserve_tree_or_encode_rev
    by (cases rule: R'.cases, blast+)
qed

lemma R_encode_execute: 
  assumes "R (HEncodeHandle e) h"
      and "\<not> (\<exists>e'. h = HEncodeHandle e')"
    shows "executes_to e h"
  using assms execute_some
  by (cases rule: R.cases, blast+)

lemma R'_encode_execute: 
  assumes "R' (HEncodeHandle e) h"
      and "\<not> (\<exists>e'. h = HEncodeHandle e')"
    shows "executes_to e h"
  using assms execute_some R_encode_execute
  by (cases rule: R'.cases, blast+)

lemma R_encode_reasons: 
  assumes "R (HEncodeHandle e1) (HEncodeHandle e2)"
    shows "rel_opt R (execute e1) (execute e2)"
  using assms
  by (cases rule: R.cases, fastforce+, metis execute_some execute_with_fuel.simps executes_to_def force_with_fuel_not_thunk handle.distinct(5,9), simp add: RSelf endpoint_def execute_def)

lemma R'_encode_reasons: 
  assumes "R' (HEncodeHandle e1) (HEncodeHandle e2)"
    shows "R' (HThunkHandle (get_encode_thunk e1)) (HThunkHandle (get_encode_thunk e2)) \<or> rel_opt R' (execute e1) (execute e2)"
  using assms
  by (cases rule: R'.cases, metis (full_types) R'orR_to_R' R_encode_reasons rel_opt.elims(2) rel_opt.simps(1,2), simp+)

lemma R_encode_execute_rev_does_not_exist:
  assumes "R h1 (HEncodeHandle e)"
      and "\<not> (\<exists>e1. h1 = HEncodeHandle e1)"
    shows "False"
  using assms
  by (cases rule: R.cases, blast+)

lemma R'_encode_execute_rev_does_not_exist:
  assumes "R' h1 (HEncodeHandle e)"
      and "\<not> (\<exists>e1. h1 = HEncodeHandle e1)"
    shows "False"
  using assms R_encode_execute_rev_does_not_exist
  by (cases rule: R'.cases, blast+)

lemma R_blob_complete:
  assumes "get_blob_data b1 = get_blob_data b2"
  shows "R (HBlobHandle b1) (HBlobHandle b2)"
  using assms by blast

lemma R'_blob_complete:
  assumes "get_blob_data b1 = get_blob_data b2"
  shows "R' (HBlobHandle b1) (HBlobHandle b2)"
  using assms by blast

lemma R_thunk_reasons:
  assumes "R (HThunkHandle t1) (HThunkHandle t2)"
  shows "R (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> R r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2)) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  using assms
  by (cases rule: R.cases, blast+, auto)

lemma R'_thunk_reasons:
  assumes "R' (HThunkHandle t1) (HThunkHandle t2)"
  shows "R' (HTreeHandle (get_thunk_tree t1)) (HTreeHandle (get_thunk_tree t2)) \<or>
     (think t1 = None \<and> think t2 = None) \<or>
     (\<exists>r1 r2. think t1 = Some r1 \<and> think t2 = Some r2 \<and> R' r1 r2) \<or>
     (think t1 = Some (HThunkHandle t2)) \<or>
     (think t1 = Some (HEncodeHandle (create_encode t2)))"
  using assms R_thunk_reasons
  by (cases rule: R'.cases, blast, auto)

lemma R'_impl_R:
  assumes "R' h1 h2"
  shows "R h1 h2"
  using assms
proof (coinduction arbitrary: h1 h2 rule: R.coinduct)
  case R
  then show ?case
  proof (cases rule: R'.cases)
    case R'_from_R
    then show ?thesis
      using list_all2_R_imp_R'orR
      by (cases rule: R.cases, auto)
  next
    case (R'_Tree t1 t2)
    then show ?thesis by simp
  next
    case (R'_thunk_some_res)
    then show ?thesis by auto
  next
    case (R'_tree_to_thunk t1 t2)

    let ?th1 = "create_thunk t1"
    let ?th2 = "create_thunk t2"

    have "rel_opt R' (think ?th1) (think ?th2) \<or> think ?th1 = Some (HThunkHandle ?th2) \<or> think ?th1 = Some (HEncodeHandle (create_encode ?th2))"
      using get_blob_data_cong_R' 
      using get_tree_size_cong_R'
      using get_tree_data_cong_R'
      using create_tree_cong_R'
      using R'_tree_children
      using R'_preserve_thunk
      using R'_preserve_blob
      using R'_preserve_blob_or_encode_rev
      using R'_preserve_tree
      using R'_preserve_tree_or_encode_rev
      using R'_encode_execute
      using R'_encode_reasons
      using R'_encode_execute_rev_does_not_exist
      using R'_thunk_reasons
      using R local.R'_tree_to_thunk(1,2) 
      apply (rule_tac X=R' in think_X, blast, blast, blast, blast, blast, blast, blast, blast, presburger+, meson, blast, presburger, blast+)
      done

    then show ?thesis
    proof
      assume "rel_opt R' (think ?th1) (think ?th2)"
      then show ?thesis
        by (metis (lifting) local.R'_tree_to_thunk(1,2) rel_opt.elims(2))
    next
      assume "think ?th1 = Some (HThunkHandle ?th2) \<or> think ?th1 = Some (HEncodeHandle (create_encode ?th2))"
      then show ?thesis
      proof
        assume "think ?th1 = Some (HThunkHandle ?th2)"
        then show ?thesis
          using local.R'_tree_to_thunk(1,2) by auto
      next
        assume "think ?th1 = Some (HEncodeHandle (create_encode ?th2))"
        then show ?thesis
          using local.R'_tree_to_thunk(1,2) by auto
      qed
    qed
  next
    case R'_encode_some_res
    then show ?thesis
      by force
  next
    case (R'_thunk_to_encode th1 th2)

    let ?e1 = "create_encode th1"
    let ?e2 = "create_encode th2"

    have "rel_opt R' (force th1) (force th2)"
      using get_blob_data_cong_R' 
      using get_tree_size_cong_R'
      using get_tree_data_cong_R'
      using create_tree_cong_R'
      using R'_tree_children
      using R'_preserve_thunk
      using R'_preserve_blob
      using R'_preserve_blob_or_encode_rev
      using R'_preserve_tree
      using R'_preserve_tree_or_encode_rev
      using R'_encode_execute
      using R'_encode_reasons
      using R'_encode_execute_rev_does_not_exist
      using R'_thunk_reasons
      using local.R'_thunk_to_encode(3)
      apply (rule_tac X=R' in forces_X, blast, blast, blast, blast, blast, blast, blast, blast, presburger+, meson, blast, presburger, blast, force)
      done

    have "execute ?e1 = force th1"
      by (metis execute_some execute_unique execute_with_fuel.simps executes_to_def force_some force_unique forces_to_def get_thunk_encode_create_encode not_Some_eq)
    moreover have "execute ?e2 = force th2"
      by (metis execute_some execute_unique execute_with_fuel.simps executes_to_def force_some force_unique forces_to_def get_thunk_encode_create_encode not_Some_eq)
    ultimately have "rel_opt R' (execute ?e1) (execute ?e2)"
      using \<open>rel_opt R' (force th1) (force th2)\<close> by presburger

    then show ?thesis 
      by (metis (lifting) local.R'_thunk_to_encode(1,2) rel_opt.elims(2))
  qed
qed

