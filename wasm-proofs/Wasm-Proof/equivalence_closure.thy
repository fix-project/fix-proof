theory equivalence_closure
  imports equivalence
begin

definition eq :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  where [simp, intro]:
"eq h1 h2 = equivclp R h1 h2"

lemma R_tree_update1:
  assumes "R a b"
  shows
    "R (HTreeObj (create_tree (pre @ a # post)))
       (HTreeObj (create_tree (pre @ b # post)))"
proof -
  have H0: "list_all2 R post post"
    by (simp add: RSelf list.rel_refl)
  then have H1: "list_all2 R (a # post) (b # post)"
    using list_all2_append assms
    by force

  have H2: "list_all2 R pre pre" 
    by (simp add: RSelf list.rel_refl)

  have "list_all2 R (pre @ a # post) (pre @ b # post)"
  proof (induction pre)
    case Nil
    then show ?case using H1 by auto
  next
    case (Cons x xs)
    have "R x x" using eq_refl by auto
    then show ?case using Cons by auto
  qed

  then have "list_all2 R (get_tree_raw (create_tree (pre @ a # post)))
                         (get_tree_raw (create_tree (pre @ b # post)))"
    by simp
  then show ?thesis 
    by blast
qed

lemma equivclp_tree_update1:
  assumes "eq a b"
  shows "eq (HTreeObj (create_tree (pre @ (a # post))))
            (HTreeObj (create_tree (pre @ (b # post))))"
  using assms unfolding eq_def
proof (induction rule: equivclp_induct)
  case base 
  then show ?case by (rule equivclp_refl) 
next
  case (step y z)
  have X: "R y z \<or> R z y" using step by auto
  then show ?case
    using R_tree_update1
    by (meson equivclp_into_equivclp step.IH)
qed

lemma equivclp_tree_list_all2_prefix:
  assumes LA: "list_all2 eq xs ys"
  shows
    "eq (HTreeObj (create_tree (pre @ xs)))
        (HTreeObj (create_tree (pre @ ys)))"
  using LA
proof (induction xs ys arbitrary: pre rule: list_all2_induct)
  case Nil
  then show ?case by simp 
next
  case (Cons x xs y ys)
  have head_step:
    "eq (HTreeObj (create_tree (pre @ x # xs)))
        (HTreeObj (create_tree (pre @ y # xs)))"
    using Cons.hyps(1)
    using equivclp_tree_update1 by blast

  have tail_steps:
    "eq (HTreeObj (create_tree ((pre @ [y]) @ xs)))
        (HTreeObj (create_tree ((pre @ [y]) @ ys)))"
    using Cons.IH[of "pre @ [y]"]
    by blast

  have tail_steps':
    "eq (HTreeObj (create_tree (pre @ y # xs)))
        (HTreeObj (create_tree (pre @ y # ys)))"
    using tail_steps by simp

  show ?case
    using head_step tail_steps'
    by (meson eq_def equivclp_trans)
qed

lemma eq_tree_list_all2:
  assumes "list_all2 eq xs ys"
  shows   "eq (HTreeObj (create_tree xs))
              (HTreeObj (create_tree ys))"
  using equivclp_tree_list_all2_prefix[where pre="[]", OF assms]
  by simp

lemma eq_preserve_thunk:
  assumes "eq h1 h2"
  shows "(\<exists>th. h1 = Thunk th) \<longleftrightarrow> (\<exists>th. h2 = Thunk th)"
  using assms
  unfolding eq_def
  using R_preserve_thunk
  by (induction rule: equivclp_induct) blast+

lemma R_or_preserve_tree:
  assumes assm': "R y z \<or> R z y" 
  assumes assm: "\<exists>t. y = (HTreeObj t)"
  shows "(\<exists>t2. z = (HTreeObj t2)) \<or>
         (\<exists>t2 tree. z = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HTreeObj tree))"
  using assm' R_preserve_tree R_preserve_tree_or_encode_rev
  unfolding HTreeObj_def
  by (metis HTreeObj_def R_encode_execute assm execute_unique handle.distinct(3))

lemma R_or_preserve_blob:
  assumes assm': "R y z \<or> R z y" 
  assumes assm: "\<exists>t. y = (HBlobObj t)"
  shows "(\<exists>t2. z = (HBlobObj t2)) \<or>
         (\<exists>t2 tree. z = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HBlobObj tree))"
  using assm' R_preserve_blob R_preserve_blob_or_encode_rev
  unfolding HBlobObj_def
  by (metis HBlobObj_def R_encode_execute assm execute_unique handle.distinct(3))

lemma R_or_preserve_tree_ref:
  assumes assm': "R y z \<or> R z y" 
  assumes assm: "\<exists>t. y = (HTreeRef t)"
  shows "(\<exists>t2. z = (HTreeRef t2)) \<or>
         (\<exists>t2 tree. z = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (HTreeRef tree))"
  using assm' R_preserve_tree_ref R_preserve_tree_ref_or_encode_rev
  unfolding HTreeRef_def
  by (metis HTreeRef_def R_encode_execute assm execute_unique handle.distinct(3))

lemma R_or_preserve_blob_ref:
  assumes assm': "R y z \<or> R z y" 
  assumes assm: "\<exists>t. y = (HBlobRef t)"
  shows "(\<exists>t2. z = (HBlobRef t2)) \<or>
         (\<exists>t2 tree. z = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (HBlobRef tree))"
  using assm' R_preserve_blob_ref R_preserve_blob_ref_or_encode_rev
  unfolding HBlobRef_def
  by (metis HBlobRef_def R_encode_execute assm execute_unique handle.distinct(3))

lemma R_or_preserve_obj_or_encode_rev:
  fixes make_obj :: "'a \<Rightarrow> Data"
  assumes R_preserve_obj: "\<And>h1 h2. R h1 h2 \<Longrightarrow> (\<exists>b. h1 = Data (make_obj b)) \<longrightarrow> (\<exists>b. h2 = Data (make_obj b))"
  assumes R_preserve_obj_or_encode_rev:  "\<And>h1 h2. R h1 h2 \<Longrightarrow> (\<exists>b. h2 = Data (make_obj b)) \<longrightarrow> (\<exists>b. h1 = Data (make_obj b)) \<or> (\<exists>e. h1 = Encode (Strict e))"
  assumes assm': "R y z \<or> R z y" 
  assumes assm: "(\<exists>t2 tree. y = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (Data (make_obj tree)))"
  shows "(\<exists>t2. z = (Data (make_obj t2))) \<or>
         (\<exists>t2 tree. z = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (Data (make_obj tree)))"
  using assm'
proof  
  assume assm': "R y z"
  then show ?thesis
  proof (cases z)
    case Data
    then show ?thesis
      using R_encode_execute assm assm' execute_some
        executes_to_deterministic by blast
  next
    case Thunk
    then show ?thesis
      using R_preserve_thunk assm assm' by blast
  next
    case Encode
    obtain t1 tree where assm1: "y = Encode (Strict t1)" 
                   and assm2: "execute (Strict t1) = Some (Data (make_obj tree))"
      using assm by auto
    obtain t2 where "z = Encode (Strict t2)"
      using Encode
      by (metis Encode.exhaust R_not_strict_shallow assm assm')
    moreover then obtain r2 where "execute (Strict t2) = Some r2" and "R (Data (make_obj tree)) r2"
      using assm' assm1 assm2 R_strict_encode_reasons
      by (simp, metis option.exhaust rel_opt.simps(2,3))
    ultimately show ?thesis
      using R_preserve_obj by auto
  qed
next
  assume assm': "R z y"
  show ?thesis
  proof (cases z)
    case (Data)
    then show ?thesis
      using R'_encode_execute_rev_does_not_exist assm assm' by blast
  next
    case (Thunk)
    then show ?thesis 
      using R_preserve_thunk assm assm' by blast
  next
    case Encode
    obtain t1 tree where assm1: "y = Encode (Strict t1)" 
                   and assm2: "execute (Strict t1) = Some (Data (make_obj tree))"
      using assm by auto
    obtain t2 where "z = Encode (Strict t2)"
      using Encode
      by (metis Encode.exhaust R_not_shallow_strict assm assm')
    moreover then obtain r2 where "execute (Strict t2) = Some r2" and "R r2 (Data (make_obj tree))"
      using assm' assm1 assm2 R_strict_encode_reasons
      apply simp
      by (metis not_None_eq rel_opt.simps(2,4)) 
    ultimately show ?thesis
      using R_preserve_obj_or_encode_rev execute_strict_to_obj
      by blast
  qed
qed

lemma R_or_preserve_ref_or_encode_rev:
  fixes make_ref :: "'a \<Rightarrow> Data"
  assumes R_preserve_ref: "\<And>h1 h2. R h1 h2 \<Longrightarrow> (\<exists>b. h1 = Data (make_ref b)) \<longrightarrow> (\<exists>b. h2 = Data (make_ref b))"
  assumes R_preserve_ref_or_encode_rev:  "\<And>h1 h2. R h1 h2 \<Longrightarrow> (\<exists>b. h2 = Data (make_ref b)) \<longrightarrow> (\<exists>b. h1 = Data (make_ref b)) \<or> (\<exists>e. h1 = Encode (Shallow e))"
  assumes assm': "R y z \<or> R z y" 
  assumes assm: "(\<exists>t2 tree. y = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (Data (make_ref tree)))"
  shows "(\<exists>t2. z = (Data (make_ref t2))) \<or>
         (\<exists>t2 tree. z = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (Data (make_ref tree)))"
  using assm'
proof  
  assume assm': "R y z"
  then show ?thesis
  proof (cases z)
    case Data
    then show ?thesis
      using R_encode_execute assm assm' execute_some
        executes_to_deterministic by blast
  next
    case Thunk
    then show ?thesis
      using R_preserve_thunk assm assm' by blast
  next
    case Encode
    obtain t1 tree where assm1: "y = Encode (Shallow t1)" 
                   and assm2: "execute (Shallow t1) = Some (Data (make_ref tree))"
      using assm by auto
    obtain t2 where "z = Encode (Shallow t2)"
      using Encode
      by (metis Encode.exhaust R_not_shallow_strict assm assm')
    moreover then obtain r2 where "execute (Shallow t2) = Some r2" and "R (Data (make_ref tree)) r2"
      using assm' assm1 assm2 R_shallow_encode_reasons
      by (simp, metis option.exhaust rel_opt.simps(2,3))
    ultimately show ?thesis
      using R_preserve_ref by auto
  qed
next
  assume assm': "R z y"
  show ?thesis
  proof (cases z)
    case (Data)
    then show ?thesis
      using R'_encode_execute_rev_does_not_exist assm assm' by blast
  next
    case (Thunk)
    then show ?thesis 
      using R_preserve_thunk assm assm' by blast
  next
    case Encode
    obtain t1 tree where assm1: "y = Encode (Shallow t1)" 
                   and assm2: "execute (Shallow t1) = Some (Data (make_ref tree))"
      using assm by auto
    obtain t2 where "z = Encode (Shallow t2)"
      using Encode
      by (metis Encode.exhaust R_not_strict_shallow assm assm')
    moreover then obtain r2 where "execute (Shallow t2) = Some r2" and "R r2 (Data (make_ref tree))"
      using assm' assm1 assm2 R_shallow_encode_reasons
      apply simp
      by (metis not_None_eq rel_opt.simps(2,4)) 
    ultimately show ?thesis
      using R_preserve_ref_or_encode_rev execute_shallow_to_ref
      by blast
  qed
qed

lemma R_or_preserve_tree_or_encode_rev:
  assumes "R y z \<or> R z y" 
  assumes "(\<exists>t2 tree. y = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HTreeObj tree))"
  shows "(\<exists>t2. z = (HTreeObj t2)) \<or>
         (\<exists>t2 tree. z = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HTreeObj tree))"
  using R_or_preserve_obj_or_encode_rev[of "\<lambda>r. Object (TreeObj r)"] assms R_preserve_tree R_preserve_tree_or_encode_rev
  unfolding HTreeObj_def
  by blast

lemma R_or_preserve_tree_ref_or_encode_rev:
  assumes "R y z \<or> R z y" 
  assumes "(\<exists>t2 tree. y = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (HTreeRef tree))"
  shows "(\<exists>t2. z = (HTreeRef t2)) \<or>
         (\<exists>t2 tree. z = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (HTreeRef tree))"
  using R_or_preserve_ref_or_encode_rev[of "\<lambda>r. Ref (TreeRef r)"] assms R_preserve_tree_ref R_preserve_tree_ref_or_encode_rev
  unfolding HTreeRef_def
  by blast

lemma R_or_preserve_blob_or_encode_rev:
  assumes "R y z \<or> R z y" 
  assumes "(\<exists>t2 tree. y = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HBlobObj tree))"
  shows "(\<exists>t2. z = (HBlobObj t2)) \<or>
         (\<exists>t2 tree. z = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HBlobObj tree))"
  using R_or_preserve_obj_or_encode_rev[of "\<lambda>r. Object (BlobObj r)"] assms R_preserve_blob R_preserve_blob_or_encode_rev
  unfolding HBlobObj_def
  by blast

lemma R_or_preserve_blob_ref_or_encode_rev:
  assumes "R y z \<or> R z y" 
  assumes "(\<exists>t2 tree. y = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (HBlobRef tree))"
  shows "(\<exists>t2. z = (HBlobRef t2)) \<or>
         (\<exists>t2 tree. z = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (HBlobRef tree))"
  using R_or_preserve_ref_or_encode_rev[of "\<lambda>r. Ref (BlobRef r)"] assms R_preserve_blob_ref R_preserve_blob_ref_or_encode_rev
  unfolding HBlobRef_def
  by blast

lemma eq_preserve_tree_or_encode:
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = HTreeObj t1 \<Longrightarrow> 
         (\<exists>t2. h2 = HTreeObj t2) \<or>
         (\<exists>t2 tree. h2 = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HTreeObj tree))"
  using H
  unfolding eq_def
  by (induction rule: equivclp_induct, blast, metis R_or_preserve_tree R_or_preserve_tree_or_encode_rev)

lemma eq_preserve_blob_or_encode:
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = HBlobObj t1 \<Longrightarrow> 
         (\<exists>t2. h2 = HBlobObj t2) \<or>
         (\<exists>t2 tree. h2 = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HBlobObj tree))"
  using H
  unfolding eq_def
  by (induction rule: equivclp_induct, blast, metis R_or_preserve_blob R_or_preserve_blob_or_encode_rev)

lemma eq_preserve_tree_ref_or_encode:
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = HTreeRef t1 \<Longrightarrow> 
         (\<exists>t2. h2 = HTreeRef t2) \<or>
         (\<exists>t2 tree. h2 = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (HTreeRef tree))"
  using H
  unfolding eq_def
  by (induction rule: equivclp_induct, blast, metis R_or_preserve_tree_ref R_or_preserve_tree_ref_or_encode_rev)

lemma eq_preserve_blob_ref_or_encode:
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = HBlobRef t1 \<Longrightarrow> 
         (\<exists>t2. h2 = HBlobRef t2) \<or>
         (\<exists>t2 tree. h2 = (Encode (Shallow t2)) \<and> execute (Shallow t2) = Some (HBlobRef tree))"
  using H
  unfolding eq_def
  by (induction rule: equivclp_induct, blast, metis R_or_preserve_blob_ref R_or_preserve_blob_ref_or_encode_rev)

lemma eval_with_fuel_to_R_single:
  "\<And>r. eval_with_fuel n h = Some r \<Longrightarrow> eq h r"
proof (induction n arbitrary: h)
  case 0
  then show ?case
  proof (cases h)
    case (Data d1)
    then show ?thesis 
    proof (cases d1)
      case (Object obj1)
      then show ?thesis
      proof (cases obj1)
        case (BlobObj b1)
        then have Blob1: "r = HBlobObj b1" and R1: "h = r"
          using "0" Data Object by auto
        show ?thesis
          by (simp add: R1)
      next
        case (TreeObj)
        then show ?thesis
          using "0" Data Object by auto
      qed
    next
      case (Ref ref1)
      then have Ref1: "r = Data (Ref ref1)" and R1: "h = r"
        using "0" Data Ref by auto
      show ?thesis sledgehammer
        by (simp add: R1)
    qed
  next
    case (Thunk th1)
    then have Thunk1: "r = Thunk th1" and Thunk1': "h = r"
      using "0" by auto
    show ?thesis
      by (simp add: Thunk1')
  next
    case (Encode e1)
    then show ?thesis 
      using "0" by auto
  qed
next
  case (Suc n)

  have "(\<exists>r. h = (Data (Ref r))) \<or> (\<exists>b. h = HBlobObj b) \<or> (\<exists>th. h = Thunk th) \<Longrightarrow> ?case"
  proof -
    assume "(\<exists>r. h = (Data (Ref r))) \<or> (\<exists>b. h = HBlobObj b) \<or> (\<exists>th. h = Thunk th)"
    then have R1: "h = r"
      using Suc.prems by auto
    then show "eq h r"
      by auto
  qed

  moreover have "\<exists>e. h = Encode e \<Longrightarrow> ?case"
  proof -
    assume "\<exists>e. h = Encode e"
    then obtain e where "h = Encode e" by auto
    then obtain r1' where "execute_with_fuel n e = Some r1'" and "eval_with_fuel n r1' = Some r"
      by (metis (no_types, lifting) Suc.prems eval_with_fuel.simps(2)
          handle.simps(12) option.case_eq_if option.distinct(1)
          option.exhaust_sel)
    then have "R h r1'"
      using \<open>h = Encode e\<close> execute_unique executes_to_def
      by blast
    moreover have "eq r1' r"
      using Suc.IH \<open>eval_with_fuel n r1' = Some r\<close> by force
    ultimately show "eq h r"
      by (meson eq_def equivclp_trans r_into_equivclp)
  qed

  moreover have "\<exists>t. h = HTreeObj t \<Longrightarrow> ?case"
  proof -
    assume "\<exists>t. h = HTreeObj t" 
    then obtain t where T: "h = HTreeObj t" sledgehammer
      by blast
    then obtain t' where T': "r = HTreeObj t'"
      using Suc.prems eval_tree_to_eval_entry eval_unique evals_to_def
      by blast
    then have "eval_list_with_fuel n (get_tree_raw t) = Some (get_tree_raw t')"
      using \<open>eval_with_fuel (Suc n) h = Some r\<close> T T'
      apply simp
      by fastforce
    then have "list_all2 (\<lambda>i r. eval_with_fuel n i = Some r) (get_tree_raw t) (get_tree_raw t')"
      using eval_list_to_list_all by blast

    then have "list_all2 (\<lambda>i r. eq i r) (get_tree_raw t) (get_tree_raw t')"
      using Suc.IH list_all2_mono by blast
    then show "eq h r"
      using T T'
      by (metis (full_types) RSelf RTree eq_def eq_tree_list_all2
          equivclp_into_equivclp equivclp_refl equivclp_trans
          get_tree_raw_create_tree tree_cong_R)
  qed

  ultimately show ?case
    by (metis HBlobObj_def HTreeObj_def get_type.cases)
qed

lemma eval_to_eq: 
"eval h = Some r \<Longrightarrow> eq h r"
  using eval_some eval_with_fuel_to_R_single evals_to_def
  by blast

lemma eval_both_to_eq:
  assumes "eval h1 = Some r1"
  assumes "eval h2 = Some r2"
  assumes "eq r1 r2"
  shows "eq h1 h2"
  by (meson assms(1,2,3) eq_def equivclp_sym equivclp_trans
      eval_to_eq)

lemma eq_eval:
  assumes H: "eq h1 h2"
  shows "rel_opt eq (eval h1) (eval h2)"
  using H
  unfolding eq_def
proof (induction rule: equivclp_induct)
  case base
  then show ?case 
    by (simp add: endpoint_def evaluation.eval_def)
next
  case (step y z)
  then have "rel_opt R (eval y) (eval z) \<or> rel_opt R (eval z) (eval y)"
    using eval_R by blast
  then have "rel_opt eq (eval y) (eval z)"
    by (cases "eval y"; cases "eval z"; simp_all; blast)
  then show ?case
    using step
    by (cases "eval h1"; cases "eval z"; cases "eval y" ; simp_all; metis equivclp_trans)
qed

lemma eq_encode_not_encode:
  assumes "eq h1 h2"
  shows "\<And>e. h1 = Encode e
         \<Longrightarrow> 
         (((\<not>(\<exists>e. h2 = Encode e)) \<longrightarrow> (\<exists>r1. execute e = Some r1 \<and> eq r1 h2))
         \<and>
         ((\<exists>e. h2 = Encode e) \<longrightarrow> (\<exists>e2. h2 = Encode e2 \<and> rel_opt eq (execute e) (execute e2))))"
  using assms
  unfolding eq_def
proof (induction rule: equivclp_induct)
  case base
  then show ?case
  proof (cases "\<exists>e. h2 = Encode e")
    case True
    then show ?thesis
      by (metis base equivclp_refl option.exhaust
          rel_opt.simps(1,2))
  next
    case False
    then show ?thesis
      using base rel_opt.elims(3) by fastforce
  qed
next
  case (step y z)
  then show ?case 
  proof (cases "\<exists>e. y = Encode e")
    case True
    then obtain e1 where E1: "y = Encode e1"
      by blast
    then have "rel_opt eq (execute e) (execute e1)"
      using eq_def handle.inject(3) step.IH step.prems
      by presburger

    show ?thesis
    proof (cases "\<exists>e. z = Encode e")
      case True
      then obtain e2 where "z = Encode e2" by auto
      then have "rel_opt R (execute e1) (execute e2) \<or> rel_opt R (execute e2) (execute e1)"
        using E1 local.step(2) R_strict_encode_reasons R_shallow_encode_reasons R_not_strict_shallow R_not_shallow_strict
        by (cases e1; cases e2; simp_all; blast)
      then have "rel_opt eq (execute e1) (execute e2)"
        by (cases "execute e1"; cases "execute e2"; simp_all; blast)
      then have "rel_opt eq (execute e) (execute e2)"
        using \<open>rel_opt eq (execute e) (execute e1)\<close>
        apply (cases "execute e1"; cases "execute e2"; cases "execute e"; simp_all)
        by (meson equivclp_trans)
      then show ?thesis
      proof -
        { have "eq = equivclp R"
            using eq_def by presburger
          then have "\<exists>ea. rel_opt (equivclp R) (execute e) (execute ea) \<and> z = Encode ea"
            by (simp add: \<open>rel_opt eq (execute e) (execute e2)\<close> \<open>z = Encode e2\<close>) }
        then show ?thesis
          by blast
      qed
    next
      case False
      then have "R y z"
        using E1 R_encode_execute_rev_does_not_exist step.hyps(2)
        by blast
      then have "execute e1 = Some z"
        using E1 False R_encode_execute execute_unique by blast
      then show ?thesis
        using False \<open>rel_opt eq (execute e) (execute e1)\<close>
          rel_opt.elims(2) by fastforce
    qed
  next
    case False
    then obtain r1 where "execute e = Some r1" and "eq r1 y"
      using step.IH step.prems by auto

    show ?thesis
    proof (cases "\<exists>e. z = Encode e")
      case True
      then obtain e2 where "z = Encode e2"
        by auto
      then have "R z y"
        using False R_encode_execute_rev_does_not_exist step.hyps(2)
        by blast
      then have "execute e2 = Some y"
        by (simp add: False R_encode_execute \<open>z = Encode e2\<close>
            execute_unique)
      then show ?thesis
        using \<open>eq r1 y\<close> \<open>execute e = Some r1\<close> \<open>z = Encode e2\<close>
        by auto
    next
      case False
      then show ?thesis
        by (meson
            \<open>\<And>thesis. (\<And>r1. execute e = Some r1 \<Longrightarrow> eq r1 y \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
            eq_def equivclp_into_equivclp step.hyps(2))
    qed
  qed
qed

lemma eq_tree_to_thunk:
  fixes make_thunk :: "TreeName \<Rightarrow> Thunk"
  assumes R_tree_to_thunk: "\<And>t1 t2. R (HTreeObj t1) (HTreeObj t2) \<Longrightarrow> R (Thunk (make_thunk t1)) (Thunk (make_thunk t2))"
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = HTreeObj t1 \<Longrightarrow> 
                (\<exists>t2. h2 = HTreeObj t2 \<and> eq (Thunk (make_thunk t1)) (Thunk (make_thunk t2)))
           \<or>    (\<exists>e2 t2. h2 = Encode e2 \<and> execute e2 = Some (HTreeObj t2) \<and> eq (Thunk (make_thunk t1)) (Thunk (make_thunk t2)))"
  using H
  unfolding eq_def
proof (induction rule: equivclp_induct)
  case base
  then show ?case
    by simp
next
  case (step y z)
  have "(\<exists>t2. y = HTreeObj t2) \<or>
        (\<exists>t2 tree. y = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HTreeObj tree))"
    using eq_def eq_preserve_tree_or_encode step.hyps(1) step.prems by blast
  then show ?case
  proof
    assume assm: "\<exists>t2. y = HTreeObj t2"
    then obtain t where T: "y = HTreeObj t"
      by blast

    then show ?thesis
    proof (cases "\<exists>e. z = Encode e")
      case False
      then obtain t2 where T2: "z = HTreeObj t2"
        using R_or_preserve_tree T step.hyps(2) by blast
      then have "R (Thunk (make_thunk t)) (Thunk (make_thunk t2)) \<or> R (Thunk (make_thunk t2)) (Thunk (make_thunk t))"
        using R_tree_to_thunk T step.hyps(2) by presburger
      then show ?thesis
        using T T2
        by (metis HTreeObj_def R_tree_to_thunk equivclp_into_equivclp handle.distinct(3) step.IH step.hyps(2) step.prems)
    next
      case True
      then obtain e where E: "z = Encode e" by auto
      then have "execute e = Some y"
        using R_encode_execute R_encode_execute_rev_does_not_exist T
          execute_unique step.hyps(2) by auto
      then show ?thesis
        using T E step.IH step.prems by auto
    qed
  next
    assume "(\<exists>t2 tree. y = (Encode (Strict t2)) \<and> execute (Strict t2) = Some (HTreeObj tree))"
    then obtain t tree where T: "y = (Encode (Strict t)) \<and> execute (Strict t) = Some (HTreeObj tree)"
      by blast
    then have EQYH: "eq (Thunk (make_thunk t1)) (Thunk (make_thunk tree))"
      using step.IH step.prems by fastforce

    show ?thesis
    proof (cases "\<exists>e. z = Encode e")
      case True
      then obtain e where E: "z = Encode e" by blast
      then obtain t2 where E': "execute e = Some (HTreeObj t2)" and "R (HTreeObj tree) (HTreeObj t2) \<or> R (HTreeObj t2) (HTreeObj tree)"
        by (metis HTreeObj_def R_or_preserve_tree_or_encode_rev
            R_strict_encode_reasons T
            handle.distinct(3)
            handle.inject(3) rel_opt.simps(2)
            step.hyps(2))
      then have "eq (Thunk (make_thunk tree)) (Thunk (make_thunk t2))"
        using R_tree_to_thunk by auto
      then show ?thesis
        using EQYH 
        by (meson E E' eq_def equivclp_trans)
    next
      case False
      then have "z = HTreeObj tree"
        by (metis R_encode_execute R_encode_execute_rev_does_not_exist T
            execute_some executes_to_deterministic step.hyps(2))
      then show ?thesis
        using T step.IH step.prems by auto
    qed
  qed
qed

lemma eq_tree_to_application_thunk:
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = HTreeObj t1 \<Longrightarrow> 
                (\<exists>t2. h2 = HTreeObj t2 \<and> eq (Thunk (Application t1)) (Thunk (Application t2)))
           \<or>    (\<exists>e2 t2. h2 = Encode e2 \<and> execute e2 = Some (HTreeObj t2) \<and> eq (Thunk (Application t1)) (Thunk (Application t2)))"
  using R'_impl_R R'_tree_to_application_thunk R'orR_to_R' assms eq_tree_to_thunk by presburger

lemma eq_tree_to_selection_thunk:
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = HTreeObj t1 \<Longrightarrow> 
                (\<exists>t2. h2 = HTreeObj t2 \<and> eq (Thunk (Selection t1)) (Thunk (Selection t2)))
           \<or>    (\<exists>e2 t2. h2 = Encode e2 \<and> execute e2 = Some (HTreeObj t2) \<and> eq (Thunk (Selection t1)) (Thunk (Selection t2)))"
  using R'_impl_R R'_tree_to_selection_thunk R'orR_to_R' assms eq_tree_to_thunk by presburger

lemma eq_tree_to_digestion_thunk:
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = HTreeObj t1 \<Longrightarrow> 
                (\<exists>t2. h2 = HTreeObj t2 \<and> eq (Thunk (Digestion t1)) (Thunk (Digestion t2)))
           \<or>    (\<exists>e2 t2. h2 = Encode e2 \<and> execute e2 = Some (HTreeObj t2) \<and> eq (Thunk (Digestion t1)) (Thunk (Digestion t2)))"
  using R'_impl_R R'_tree_to_digestion_thunk R'orR_to_R' assms eq_tree_to_thunk by presburger

lemma force_eq:
  assumes H: "eq h1 h2"
  shows "\<And>t1. h1 = Thunk t1 \<Longrightarrow> 
         \<exists>t2. h2 = Thunk t2 \<and> rel_opt (relaxed_X eq) (force t1) (force t2)"
  using H
  unfolding eq_def
proof (induction rule: equivclp_induct)
  case base
  then have "rel_opt (relaxed_X (equivclp R)) (force t1) (force t1)"
    using relaxed_X_def force_data eq_def handle.simps(10)
    by (cases "force t1"; simp_all; blast)
  then show ?case
    using base by blast
next
  case (step y z)
  then obtain ty where TY: "y = Thunk ty" 
                 and YH: "rel_opt (relaxed_X eq) (force t1) (force ty)"
    unfolding eq_def
    by blast
  then obtain tz where TZ: "z = Thunk tz"
                 and "rel_opt (relaxed_X R) (force ty) (force tz) \<or> rel_opt (relaxed_X R) (force tz) (force ty)"
    using step force_R
    by (metis R_preserve_thunk)
  then have "rel_opt (relaxed_X eq) (force ty) (force tz)"
    using eq_def
    by (cases "force ty"; cases "force tz"; simp_all; metis converse_r_into_equivclp eq_def force_data handle.simps(10) r_into_equivclp relaxed_X_def)
  then have "rel_opt (relaxed_X eq) (force t1) (force tz)"
    using YH
    apply (cases "force t1"; cases "force tz"; cases "force ty"; simp_all)
    using force_data relaxed_X_def
    by (simp, metis eq_def equivclp_trans handle.simps(10))
  then show ?case
    unfolding eq_def 
    using TZ
    by blast
qed

lemma force_with_fuel_to_the_last_thunk:
  "\<And>th h. force_with_fuel n th = Some h 
  \<Longrightarrow> \<exists>th'. think th' = Some h \<and> eq (Thunk th) (Thunk th')"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof (cases "think_with_fuel n th")
    case None
    then show ?thesis using Suc by auto
  next
    case (Some r)
    then show ?thesis
    proof (cases r)
      case (Data x1)
      then have "h = r"
        using Some Suc.prems by force
      then show ?thesis
        using Some eq_def think_unique thinks_to_def by blast
    next
      case (Thunk th1)
      then have "force_with_fuel n th1 = Some h"
        using Some Suc.prems by force
      then obtain th1' where "think th1' = Some h" and "eq (Thunk th1) (Thunk th1')"
        using Suc.IH
        by blast
      moreover have "R (Thunk th) (Thunk th1)"
        using Some Thunk think_unique thinks_to_def by blast
      ultimately show ?thesis 
        by (meson eq_def equivclp_into_equivclp equivclp_sym)
    next
      case (Encode e1)
      let ?th = "encode_to_thunk e1"
      have "force_with_fuel n ?th = Some h"
        using Encode Some Suc.prems
        by (cases e1; force)
      then obtain th1' where "think th1' = Some h" and "eq (Thunk ?th) (Thunk th1')"
        using Suc.IH
        by blast
      moreover have "R (Thunk th) (Thunk ?th)"
        by (metis Encode Encode.exhaust Encode.simps(5,6) RThunkSingleStepEncodeShallow
            RThunkSingleStepEncodeStrict Some encode_to_thunk_def think_unique
            thinks_to_def)
      then show ?thesis
        by (meson calculation(1,2) converse_r_into_equivclp eq_def equivclp_sym
            equivclp_trans)
    qed
  qed
qed

lemma force_to_the_last_thunk:
  "\<And>th h. force th = Some h 
  \<Longrightarrow> \<exists>th'. think th' = Some h \<and> eq (Thunk th) (Thunk th')"
  by (meson force_some force_with_fuel_to_the_last_thunk forces_to_def)

lemma thunk_for_all_data:
"\<exists>th. think th = Some (Data d)"
proof -
  have "think (Identification d) = Some (Data d)"
    by (simp add: think_hs)
  then show ?thesis
    by blast
qed

lemma data_to_lift:
  assumes "R (Data d1) (Data d2)"
  shows "relaxed_X R (Data d1) (Data d2)"
  apply (rule_tac data_to_relaxed)
  using blob_cong_R apply blast
  using tree_cong_R apply blast
  using blob_complete_R apply blast
  using tree_complete_R apply blast
  apply blast+
  using blob_ref_complete_R apply blast
  using tree_ref_complete_R apply presburger
  using R_preserve_tree_ref apply blast
  using R_preserve_blob_ref apply blast
  using R_preserve_tree apply blast
  using R_preserve_blob apply blast
  by (simp add: assms)

lemma lower_to_lift:
  assumes "R (lower (Data d1)) (lower (Data d2))"
  shows "R (lift (Data d1)) (lift (Data d2))"
  apply (rule_tac lower_to_lift)
  using blob_cong_R apply blast
  using tree_cong_R apply blast
  using blob_complete_R apply blast
  using tree_complete_R apply blast
  apply blast+
  using blob_ref_complete_R apply blast
  using tree_ref_complete_R apply presburger
  using R_preserve_tree_ref apply blast
  using R_preserve_blob_ref apply blast
  using assms by auto

lemma lower_to_lift_cancel:
  assumes "lower (Data d) = Data d'"
  shows "lift (Data d) = lift (Data d')"
  using assms
  apply (cases d; cases d'; simp_all)
  apply (case_tac x1; case_tac x1a; simp_all)
  by (metis Object.exhaust lift_data.simps(1,2)
      lower_data.simps(2,3))

lemma lift_to_lower_cancel:
  assumes "lift (Data d) = Data d'"
  shows "lower (Data d) = lower (Data d')"
  using assms
  apply (cases d; cases d'; simp_all)
  apply (case_tac x2; case_tac x1; simp_all)
  apply (case_tac x2; case_tac x2a; simp_all)
  done

lemma execute_shallow_to_lift:
  assumes "execute (Shallow x) = Some (Data d)"
  shows "execute (Strict x) = Some (lift (Data d))"
  using assms
proof -
  obtain inter where "force x = Some inter" and "lower inter = Data d"
    using assms execute_hs
    by auto
  moreover then have "lift inter = lift (Data d)"
    using force_data lower_to_lift_cancel by blast
  ultimately show ?thesis
    by (simp add: execute_hs)
qed

lemma execute_strict_to_lower:
  assumes "execute (Strict x) = Some (Data d)"
  shows "execute (Shallow x) = Some (lower (Data d))"
  using assms
proof -
  obtain inter where "force x = Some inter" and "lift inter = Data d"
    using assms execute_hs
    by auto
  moreover then have "lower inter = lower (Data d)"
    using force_data lift_to_lower_cancel by blast
  ultimately show ?thesis
    by (simp add: execute_hs)
qed

lemma shallow_to_relaxed:
  assumes "execute (Shallow x) = Some (Data d)"
  shows "relaxed_X R (Encode (Shallow x)) (Data d)"
  by (simp add: REvalStep assms execute_shallow_to_lift
      relaxed_X_def)

lemma shallow_to_relaxed_strict:
  assumes "execute (Shallow x) = Some (Data d)"
  shows "relaxed_X R (Encode (Strict x)) (Data d)"
  by (simp add: REvalStep assms execute_shallow_to_lift
      relaxed_X_def)

lemma strict_to_relaxed:
  assumes "execute (Strict x) = Some (Data d)"
  shows "relaxed_X R (Encode (Strict x)) (Data d)"
  using assms execute_strict_to_obj relaxed_X_def by fastforce


lemma think_to_eq:
  assumes "eq h1 h2"
  shows "\<And>th1 th2 d1 d2.
           think th1 = Some (Data d1) \<Longrightarrow>
           think th2 = Some (Data d2) \<Longrightarrow>
           (((relaxed_X R h1 (Data d1)) \<or> (relaxed_X R (Data d1) h1))
          \<and> (relaxed_X R h2 (Data d2) \<or> (relaxed_X R (Data d2) h2)) \<longrightarrow>
           eq (Thunk th1) (Thunk th2))"
  using assms
  unfolding eq_def
proof (induction rule: equivclp_induct)
  case base
  show ?case
  proof (intro impI)
    assume assm: "(relaxed_X R h1 (Data d1) \<or> relaxed_X R (Data d1) h1) \<and>
    (relaxed_X R h1 (Data d2) \<or> relaxed_X R (Data d2) h1)"
    then have reld1: "relaxed_X R h1 (Data d1) \<or> relaxed_X R (Data d1) h1"
         and  reld2: "relaxed_X R h1 (Data d2) \<or> relaxed_X R (Data d2) h1"
      by auto

    show "equivclp R (Thunk th1) (Thunk th2)"
    proof (cases h1)
      case (Data h1d)
      then obtain h1th where Thinkh1: "think h1th = Some (Data h1d)"
        using thunk_for_all_data by blast

      have "eq (Thunk th1) (Thunk h1th)"
        using reld1 relaxed_X_def Data base(1) RThunkSomeResData Thinkh1 by auto
      moreover have "eq (Thunk th2) (Thunk h1th)"
        using reld2 relaxed_X_def Data base(2) RThunkSomeResData Thinkh1 by auto
      ultimately show ?thesis
        by (metis eq_def equivp_def equivp_evquivclp)
    next
      case (Thunk)
      then show ?thesis
        using R_preserve_thunk reld1 relaxed_X_def 
        by (simp, blast)
    next
      case (Encode e)
      then have reld1: "relaxed_X R (Encode e) (Data d1)"
           and  reld2: "relaxed_X R (Encode e) (Data d2)"
        using reld1 reld2
        using Encode R_encode_execute_rev_does_not_exist relaxed_X_def
        by auto
      then have "lift (Data d1) = lift (Data d2)"
        using relaxed_X_def
        by (cases e; simp_all; metis R_encode_execute executes_to_deterministic handle.inject(1) handle.simps(7))
      then show ?thesis 
        using base RThunkSomeResData
        by (simp add: RSelf r_into_equivclp)
    qed
  qed
next
  case (step y z)
  show ?case
  proof (intro impI)
    assume assm: "(relaxed_X R h1 (Data d1) \<or> relaxed_X R (Data d1) h1) \<and>
    (relaxed_X R z (Data d2) \<or>  relaxed_X R (Data d2) z)"
    then have reld1: "relaxed_X R h1 (Data d1) \<or> relaxed_X R (Data d1) h1"
         and  reld2: "relaxed_X R z (Data d2) \<or> relaxed_X R (Data d2) z"
      by auto

    show "equivclp R (Thunk th1) (Thunk th2)"
    proof (cases z)
      case (Data dz)
      then have Dataz: "z = Data dz" .
      obtain tz where TZ: "think tz = Some (Data dz)"
        using thunk_for_all_data by blast
      have reld2: "R (lift z) (lift (Data d2)) \<or> R (lift (Data d2)) (lift z)"
        using reld2 relaxed_X_def Dataz
        by simp
      
      show ?thesis
      proof (cases y)
        case (Data dy)
        then have "R (Data dy) (Data dz) \<or> R (Data dz) (Data dy)"
        using step.hyps(2) Dataz by simp
        then have "relaxed_X R y (Data dz) \<or> relaxed_X R (Data dz) y"
          using relaxed_X_def Data
          using data_to_lift by blast
        then have "equivclp R (Thunk th1) (Thunk tz)"
          using step.IH TZ reld1 step.prems(1) by presburger

        moreover have "R (Thunk tz) (Thunk th2) \<or> R (Thunk th2) (Thunk tz)"
          using reld2 TZ relaxed_X_def RThunkSomeResData
          using Dataz step.prems(2) by fastforce

        ultimately show ?thesis
          by (meson equivclp_into_equivclp)
      next
        case (Thunk)
        then show ?thesis
          by (metis Dataz R_preserve_thunk handle.distinct(1) step.hyps(2))
      next
        case (Encode ey)
        then have rel: "R (Encode ey) (Data dz)"
          using Dataz R_encode_execute_rev_does_not_exist step.hyps(2)
          by blast

        have "relaxed_X R (Encode ey) (Data dz)"
        proof (cases ey)
          case (Strict x)
          then have "execute (Strict x) = Some (Data dz)"
            using rel R_encode_execute execute_unique by blast
          then show ?thesis
            using relaxed_X_def Strict
            using strict_to_relaxed by presburger
        next
          case (Shallow x)
          then have "execute (Shallow x) = Some (Data dz)"
            using rel R_encode_execute execute_unique by blast
          then have "execute (Strict x) = Some (lift (Data dz))"
            using execute_shallow_to_lift by blast
          then show ?thesis
            using Shallow relaxed_X_def
            by (simp, blast)
        qed

        then have "equivclp R (Thunk th1) (Thunk tz)"
          using step.IH Encode TZ reld1 step.prems(1) by blast

        moreover have "eq (Thunk tz) (Thunk th2)"
          using reld2 Dataz TZ
          using eq_def step.prems(2) by blast

        ultimately show ?thesis
          by (meson eq_def equivclp_trans)
      qed
    next
      case (Thunk)
      then show ?thesis
        using R_preserve_thunk relaxed_X_def reld2 by auto
    next
      case (Encode ez)
      then have Encodez: "z = Encode ez" by auto
      then have reld2: "relaxed_X R (Encode ez) (Data d2)"
        using reld2
        using R_encode_execute_rev_does_not_exist relaxed_X_def by auto

      show ?thesis
      proof (cases y)
        case (Data dy)
        then have "R (Encode ez) (Data dy)"
          using Encodez R_encode_execute_rev_does_not_exist step.hyps(2) by blast

        then have reldy: "relaxed_X R (Encode ez) (Data dy)"
          using R_encode_execute execute_unique strict_to_relaxed shallow_to_relaxed
          by (cases ez; blast)

        have "lift (Data dy) = lift (Data d2)"
        proof (cases ez)
          case Strict
          have "execute ez = Some (lift (Data dy))"
            using reldy relaxed_X_def
            by (simp add: R_encode_execute Strict execute_unique)
          moreover have "execute ez = Some (lift (Data d2))"
            using reld2 relaxed_X_def
            by (simp add: R_encode_execute Strict execute_unique)
          ultimately show ?thesis
            by simp
        next
          case (Shallow shalz)
          have "execute (Strict shalz) = Some (lift (Data dy))"
            using reldy relaxed_X_def
            by (simp add: R_encode_execute Shallow execute_unique)
          moreover have "execute (Strict shalz) = Some (lift (Data d2))"
            using reld2 relaxed_X_def
            by (simp add: R_encode_execute Shallow execute_unique)
          ultimately show ?thesis
            by simp
        qed

        moreover obtain ty where TY: "think ty = Some (Data dy)"
          using thunk_for_all_data by presburger

        ultimately have "eq (Thunk ty) (Thunk th2)"
          using step.prems(2) RThunkSomeResData
          by (simp add: RSelf r_into_equivclp)

        moreover have "equivclp R (Thunk th1) (Thunk ty)"
          using step.IH TY
          using Data RSelf data_to_lift reld1 step.prems(1) by presburger

        then show ?thesis
          by (meson calculation eq_def equivclp_trans)
      next
        case (Thunk x2)
        then show ?thesis
          using R_preserve_thunk Encodez step.hyps(2)
          by blast
      next
        case (Encode ey)
        then have rele: "R (Encode ez) (Encode ey) \<or> R (Encode ey) (Encode ez)"
          using Encodez step.hyps(2) by blast
        then have relout: "rel_opt R (execute ez) (execute ey) \<or> rel_opt R (execute ey) (execute ez)"
          by (metis Encode.exhaust R_not_shallow_strict R_not_strict_shallow
              R_shallow_encode_reasons R_strict_encode_reasons)

        show ?thesis
        proof (cases ez)
          case (Strict strz)
          then obtain stry where Stricty: "ey = Strict stry"
            using rele
            by (metis Encode.exhaust R'_from_R R'_not_strict_shallow
                R_not_shallow_strict)
          have "R (Encode ez) (lift (Data d2))"
            using Strict relaxed_X_def reld2 by auto
          then have EZ: "execute ez = Some (lift (Data d2))"
            by (simp add: R_encode_execute execute_unique)
          then obtain dy where EY: "execute ey = Some (lift (Data dy))"
            using relout Stricty execute_strict_to_obj
            by (cases "execute ey"; simp; metis lift_data.simps(3))
          then have "relaxed_X R (Encode ey) (Data dy)"
            using relaxed_X_def Stricty
            by (simp add: REvalStep)
          moreover obtain tdy where TY: "think tdy = Some (Data dy)"
            using thunk_for_all_data by blast
          ultimately have "equivclp R (Thunk th1) (Thunk tdy)"
            using step.IH Encode reld1 reld2
            using step.prems(1) by blast

          have "R (lift (Data d2)) (lift (Data dy)) \<or> R (lift (Data dy)) (lift (Data d2))"
            using relout
            by (simp add: EZ EY)
          then have "R (Thunk th2) (Thunk tdy) \<or> R (Thunk tdy) (Thunk th2)"
            using RThunkSomeResData TY
            using step.prems(2) by presburger
          then have "equivclp R (Thunk th1) (Thunk th2)"
            by (metis \<open>equivclp R (Thunk th1) (Thunk tdy)\<close>
                converse_r_into_equivclp equivp_def equivp_evquivclp)
          then show ?thesis by blast
        next
          case (Shallow shalz)
          then obtain shaly where Shallowy: "ey = Shallow shaly"
            using rele
            by (metis Encode.exhaust R'_from_R R'_not_strict_shallow
                R_not_shallow_strict)
          have "R (Encode (Strict shalz)) (lift (Data d2))"
            using reld2 relaxed_X_def Shallow
            by simp
          then have "execute (Shallow shalz) = Some (lower (Data d2))"
            by (metis R_encode_execute execute_strict_to_lower execute_unique handle.simps(7)
                lift.simps(1) lift_to_lower_cancel)
          then obtain dy where "execute ey = Some (lower (Data dy))"
            using relout Shallowy execute_shallow_to_ref Shallow
            by (cases "execute ey"; simp; metis lower_data.simps(1))
          then have "execute (Strict shaly) = Some (lift (Data dy))"
            using Shallowy execute_shallow_to_lift lower_to_lift_cancel by auto
          then have "relaxed_X R (Encode ey) (Data dy)"
            using relaxed_X_def Shallowy
            by (simp add: REvalStep)

          moreover obtain tdy where TY: "think tdy = Some (Data dy)"
            using thunk_for_all_data by blast
          ultimately have equivtdy: "equivclp R (Thunk th1) (Thunk tdy)"
            using step.IH
            using Encode reld1 step.prems(1) by blast

          have "R (lower (Data d2)) (lower (Data dy)) \<or> R (lower (Data dy)) (lower (Data d2))"
            using relout
            by (simp add: Shallow \<open>execute (Shallow shalz) = Some (lower (Data d2))\<close>
                \<open>execute ey = Some (lower (Data dy))\<close>)
          then have "R (lift (Data d2)) (lift (Data dy)) \<or> R (lift (Data dy)) (lift (Data d2))"
            using lower_to_lift
            by blast
          then have "eq (Thunk th2) (Thunk tdy)"
            using RThunkSomeResData TY
            by (meson converse_r_into_equivclp eq_def r_into_equivclp step.prems(2))
          then show ?thesis
            using equivtdy
            by (meson eq_def equivclp_sym equivclp_trans)
        qed
      qed
    qed
  qed
qed

theorem force_some_to_eq:
  assumes "force th1 = Some r1"
  assumes "force th2 = Some r2"
  assumes "eq r1 r2"
  shows "eq (Thunk th1) (Thunk th2)"
proof -
  obtain d1 d2 where Data1: "r1 = Data d1" and Data2: "r2 = Data d2"
    using force_data assms
    by blast

  obtain th1' where "think th1' = Some (Data d1)" and Thunk1: "eq (Thunk th1) (Thunk th1')"
    using Data1 assms(1)
    using force_to_the_last_thunk by blast

  moreover obtain th2' where "think th2' = Some (Data d2)" and Thunk2: "eq (Thunk th2) (Thunk th2')"
    using Data2 assms(2)
    using force_to_the_last_thunk by blast

  ultimately have "eq (Thunk th1') (Thunk th2')"
    using think_to_eq
    using Data1 Data2 assms(3) data_to_lift by blast

  then show ?thesis
    using Thunk1 Thunk2
    by (meson eq_def equivclp_sym equivclp_trans)
qed

end
