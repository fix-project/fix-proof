theory coupon
  imports equivalence_closure
begin

inductive coupon_force :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_storage :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_apply :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_slice :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_identify :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_think :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_eval :: "handle \<Rightarrow> handle \<Rightarrow> bool"
and coupon_eq :: "handle \<Rightarrow> handle \<Rightarrow> bool" where
  CouponForce:
  "force t = Some r \<Longrightarrow> coupon_force (Thunk t) r"
| CouponStorage:
  "(get_blob_data b1 = get_blob_data b2) \<Longrightarrow>
   coupon_storage (HBlobObj b1) (HBlobObj b2)"
| CouponApply:
  "apply_tree t = Some h \<Longrightarrow> coupon_apply (HTreeObj t) h"
| CouponSlice:
  "slice t = Some h \<Longrightarrow> coupon_slice (HTreeObj t) (Data (Ref h))"
| CouponIdentify:
  "identify d = Some h \<Longrightarrow> coupon_identify (Data d) h"
| CouponThinkApplication:
  "coupon_eval (HTreeObj t) (HTreeObj t') \<Longrightarrow>
   coupon_apply (HTreeObj t') h \<Longrightarrow>
   coupon_think (Thunk (Application t)) h"
| CouponThinkSelection:
  "coupon_eval (HTreeObj t) (HTreeObj t') \<Longrightarrow>
   coupon_slice (HTreeObj t') h \<Longrightarrow>
   coupon_think (Thunk (Selection t)) h"
| CouponThinkIdentification:
  "coupon_identify (Data d) h \<Longrightarrow>
   coupon_think (Thunk (Identification d)) h"
| CouponThunkEq:
  "coupon_think (Thunk t1) (Thunk t2) \<Longrightarrow>
   coupon_eq (Thunk t1) (Thunk t2)"
| CouponThunkEncodeEq:
  "coupon_think (Thunk t1) (Encode (Strict t2)) \<Longrightarrow>
   coupon_eq (Thunk t1) (Thunk t2)"
| CouponThunkEncodeShallowEq:
  "coupon_think (Thunk t1) (Encode (Shallow t2)) \<Longrightarrow>
   coupon_eq (Thunk t1) (Thunk t2)" 
| CouponThinktoForce:
  "coupon_think (Thunk t1) (Data d) \<Longrightarrow>
   coupon_force (Thunk t1) (Data d)"
| CouponForceEq:
  "coupon_eq h1 h2 \<Longrightarrow>
   coupon_force h1 h3 \<Longrightarrow>
   coupon_force h2 h3"
| CouponForceResultEq:
  "coupon_force h1 h1' \<Longrightarrow>
   coupon_force h2 h2' \<Longrightarrow>
   coupon_eq h1' h2' \<Longrightarrow>
   coupon_eq h1 h2"
| CouponForcetoEncodeStrict:
  "coupon_force (Thunk th1) h2 \<Longrightarrow>
   coupon_eq (Encode (Strict th1)) (lift h2)"
| CouponForcetoEncodeShallow:
  "coupon_force (Thunk th1) h2 \<Longrightarrow>
   coupon_eq (Encode (Shallow th1)) (lower h2)"
| CouponEvalBlobObj:
  "coupon_eval (HBlobObj b) (HBlobObj b)"
| CouponEvalTreeObj:
  "list_all2 (\<lambda>h1 h2. coupon_eval h1 h2) (get_tree_raw t1) (get_tree_raw t2) 
   \<Longrightarrow> coupon_eval (HTreeObj t1) (HTreeObj t2)"
| CouponEvalRef:
  "coupon_eval (Data (Ref r)) (Data (Ref r))"
| CouponEvalThunk:
  "coupon_eval (Thunk t) (Thunk t)"
| CouponEvalEncode:
  "coupon_eq (Encode d) h \<Longrightarrow>
   coupon_eval h h' \<Longrightarrow>
   coupon_eval (Encode d) h'"
| CouponEqApplication:
  "coupon_eq (HTreeObj t1) (HTreeObj t2) \<Longrightarrow>
   coupon_eq (Thunk (Application t1)) (Thunk (Application t2))"
| CouponEqSelection:
  "coupon_eq (HTreeObj t1) (HTreeObj t2) \<Longrightarrow>
   coupon_eq (Thunk (Selection t1)) (Thunk (Selection t2))"
| CouponEqIdentification:
  "coupon_eq (Data d1) (Data d2) \<Longrightarrow>
   coupon_eq (Thunk (Identification d1)) (Thunk (Identification d2))"
| CouponEqEncodeStrict:
  "coupon_eq (Thunk t1) (Thunk t2) \<Longrightarrow>
   coupon_eq (Encode (Strict t1)) (Encode (Strict t2))"
| CouponEqEncodeShallow:
  "coupon_eq (Thunk t1) (Thunk t2) \<Longrightarrow>
   coupon_eq (Encode (Shallow t1)) (Encode (Shallow t2))"
| CouponEvalResultEq:
  "coupon_eval h1 h2 \<Longrightarrow>
   coupon_eq h1 h2"
| CouponEvalEq:
  "coupon_eval h1 h2 \<Longrightarrow>
   coupon_eq h1 h3 \<Longrightarrow>
   coupon_eval h3 h2"
| CouponTreeRefEq:
  "coupon_eq (HTreeObj t1) (HTreeObj t2) \<Longrightarrow>
   coupon_eq (HTreeRef t1) (HTreeRef t2)"
| CouponBlobRefEq:
  "coupon_eq (HBlobObj t1) (HBlobObj t2) \<Longrightarrow>
   coupon_eq (HBlobRef t1) (HBlobRef t2)"
| CouponTreeEq:
  "list_all2 (\<lambda> h1 h2. coupon_eq h1 h2) (get_tree_raw t1) (get_tree_raw t2) 
   \<Longrightarrow> coupon_eq (HTreeObj t1) (HTreeObj t2)"
| CouponStorageEq:
  "coupon_storage h1 h2 \<Longrightarrow> coupon_eq h1 h2"
| CouponSelf:
   "coupon_eq h h"
| CouponSym:
   "coupon_eq h1 h2 \<Longrightarrow> coupon_eq h2 h1"
| CouponTrans:
   "coupon_eq h1 h2 \<Longrightarrow> coupon_eq h2 h3 \<Longrightarrow> coupon_eq h1 h3"

lemmas coupon_induct = coupon_force_coupon_storage_coupon_apply_coupon_slice_coupon_identify_coupon_think_coupon_eval_coupon_eq.induct

lemma eval_list_helper:
  "list_all (\<lambda>h1. \<exists>r. eval h1 = Some r) l \<Longrightarrow> 
          \<exists>l'. list_all2 (\<lambda>h1 h2. evals_to h1 h2) l l'"
  proof (induction l)
    case Nil
    then show ?case
      by fastforce
  next
    case (Cons a l)
    then show ?case
      using eval_some by auto
  qed

lemma coupon_sound:
 "(coupon_force h r \<longrightarrow> 
  (\<exists>th res d. h = Thunk th \<and> force th = Some res \<and> relaxed_X eq r res \<and> r = (Data d))) 
\<and> (coupon_storage h1 h2 \<longrightarrow> (\<exists>b1 b2. h1 = HBlobObj b1 \<and> h2 = HBlobObj b2 \<and> get_blob_data b1 = get_blob_data b2)) 
\<and> (coupon_apply h1 h2 \<longrightarrow> (\<exists>t. h1 = HTreeObj t \<and> apply_tree t = Some h2))
\<and> (coupon_slice h1 h2 \<longrightarrow> (\<exists>t r. h1 = HTreeObj t \<and> h2 = (Data (Ref r)) \<and> slice t = Some r))
\<and> (coupon_identify h1 h2 \<longrightarrow> (\<exists>d. h1 = Data d \<and> identify d = Some h2))
\<and> (coupon_think h1 h2 \<longrightarrow> (\<exists>th th'. h1 = Thunk th \<and> think th' = Some h2 \<and> eq h1 (Thunk th'))) 
\<and> (coupon_eval h1 h2 \<longrightarrow> 
  (\<exists>r. eval h1 = Some r \<and> eq h2 r \<and> value_handle h2))
\<and> (coupon_eq h1 h2 \<longrightarrow> eq h1 h2)"
proof (induction rule: coupon_induct)
  case (CouponForce t r)
  then show ?case 
    by (metis eq_def equivclp_refl force_data force_eq handle.inject(2)
        rel_opt.simps(2))
next
  case (CouponStorage b1 b2)
  then show ?case by auto
next
  case (CouponApply t h)
  then show ?case by auto
next
  case (CouponSlice t h)
  then show ?case by auto
next
  case (CouponIdentify d h)
  then show ?case by auto
next
  case (CouponThinkApplication t t' h)
  then have assm: "\<exists>t''. eval (HTreeObj t) = Some (HTreeObj t'') \<and> eq (HTreeObj t') (HTreeObj t'') \<and> value_handle (HTreeObj t')"
       and  "apply_tree t' = Some h"
    using eq_preserve_tree_or_encode eval_to_value_handle value_handle_not_encode
    apply blast
    using CouponThinkApplication.IH(2) by auto
  moreover then have "eval_tree t' = Some t'"
    using eval_hs value_handle_eval_to_itself by fastforce
  ultimately have Think: "think (Application t') = Some h"
    using think_hs
    by simp

  have "eq (HTreeObj t) (HTreeObj t')"
    using assm
    by (meson eq_def equivclp_sym eval_both_to_eq value_handle_eval_to_itself)
  then have "eq (Thunk (Application t)) (Thunk (Application t'))"
    using eq_tree_to_application_thunk by auto

  then show ?case
    using Think
    by blast
next
  case (CouponThinkSelection t t' h)
  then have assm: "\<exists>t''. eval (HTreeObj t) = Some (HTreeObj t'') \<and> eq (HTreeObj t') (HTreeObj t'') \<and> value_handle (HTreeObj t')"
       and  "\<exists>r. slice t' = Some r \<and> h = (Data (Ref r))"
    using eq_preserve_tree_or_encode eval_to_value_handle value_handle_not_encode
    apply blast
    using CouponThinkSelection.IH(2) by force
  moreover then have "eval_tree t' = Some t'"
    using eval_hs value_handle_eval_to_itself by fastforce
  ultimately have Think: "think (Selection t') = Some h"
    using think_hs
    by fastforce

  have "eq (HTreeObj t) (HTreeObj t')"
    using assm
    by (meson eq_def equivclp_sym eval_both_to_eq value_handle_eval_to_itself)
  then have "eq (Thunk (Selection t)) (Thunk (Selection t'))"
    using eq_tree_to_selection_thunk by auto

  then show ?case
    using Think
    by blast
next
  case (CouponThinkIdentification d h)
  then have "identify d = Some h"
    by blast
  then show ?case
    using think_hs by force
next
  case (CouponThunkEq t1 t2)
  then show ?case
    by (meson RThinkSingleStepThunk eq_def equivclp_into_equivclp)
next
  case (CouponThunkEncodeEq t1 t2)
  then show ?case
    by (meson RThunkSingleStepEncodeStrict eq_def equivclp_into_equivclp)
next
  case (CouponThunkEncodeShallowEq t1 t2)
  then show ?case
    by (meson RThunkSingleStepEncodeShallow eq_def equivclp_into_equivclp)
next
  case (CouponThinktoForce t1 d)
  then obtain th' where T1: "think th' = Some (Data d) \<and> eq (Thunk t1) (Thunk th')"
    by blast
  moreover then have T2: "force th' = Some (Data d)"
    using force_hs by simp
  ultimately obtain res where "force t1 = Some res" and "relaxed_X eq res (Data d)"
    by (metis force_eq handle.inject(2) option.distinct(1) option.inject
        rel_opt.elims(2))
  then show ?case
    using T1 T2
    by (metis eq_def equivclp_sym force_eq handle.inject(2) rel_opt.simps(2))
next
  case (CouponForceEq h1 h2 h3)
  moreover then obtain th dr d where force1: "h1 = Thunk th \<and> force th = Some (Data dr)" 
                               and  relout: "relaxed_X eq h3 (Data dr) \<and> h3 = Data d"
    using force_data
    by blast
  
  obtain th' dr' where force2: "h2 = Thunk th' \<and> force th' = Some (Data dr')"
    using force_data force_eq force1 CouponForceEq(3) eq_preserve_thunk
    by (metis rel_opt.elims(2))
  then have "relaxed_X eq (Data dr) (Data dr')"
    using force1 CouponForceEq(3)
    using force_eq by fastforce
  then have "relaxed_X eq (Data dr') h3"
    using relout relaxed_X_def eq_def equivclp_trans
    by (smt (verit, del_insts) equivclp_sym handle.simps(10))
  then show ?case 
    by (metis eq_def equivclp_sym force2 handle.simps(10) relaxed_X_def relout)
next
  case (CouponForceResultEq h1 h1' h2 h2')
  obtain th1 res1 d1 where force1: "h1 = Thunk th1 \<and> force th1 = Some res1" 
                     and   rel1: "relaxed_X eq h1' res1 \<and> h1' = Data d1"
    using CouponForceResultEq
    by blast
  obtain th2 res2 d2 where force2: "h2 = Thunk th2 \<and> force th2 = Some res2"
                     and   rel2: "relaxed_X eq h2' res2 \<and> h2' = Data d2"
    using CouponForceResultEq
    by blast

  have "eq (lift (Data d1)) (lift res1)"
    using force1 force_data rel1
    using relaxed_X_def by force
  moreover have "eq (lift (Data d2)) (lift res2)"
    using force2 force_data rel2
    using relaxed_X_def by force
  moreover have "eq (lift (Data d1)) (lift (Data d2))"
    using CouponForceResultEq(6) rel1 rel2
    by (metis eq_to_lift lift_data_and_encode.simps(2))
  ultimately have "eq (lift res1) (lift res2)"
    by (meson eq_def equivclp_sym equivclp_trans)
  then have "relaxed_X eq res1 res2"
    using force1 force_data relaxed_X_def by fastforce
  then have "eq (Thunk th1)(Thunk th2)"
    using force1 force2 force_some_to_eq
    by presburger
  then show ?case 
    using force1 force2 by force
next
  case (CouponForcetoEncodeStrict th1 h2)
  then obtain res d where force: "force th1 = Some res \<and> relaxed_X eq h2 res \<and> h2 = Data d"
    by blast
  then have "execute (Strict th1) = Some (lift res)"
    by (simp add: execute_hs)
  then have "eq (Encode (Strict th1)) (lift res)"
    by (simp add: REvalStep r_into_equivclp)
  moreover have "eq (lift h2) (lift res)"
    using force relaxed_X_def force_data
    by force
  ultimately show ?case
    by (meson eq_def equivclp_sym equivclp_trans)
next
  case (CouponForcetoEncodeShallow th1 h2)
  then obtain res d where force: "force th1 = Some res \<and> relaxed_X eq h2 res \<and> h2 = Data d"
    by blast
  then have "execute (Shallow th1) = Some (lower res)"
    by (simp add: execute_hs)
  then have "eq (Encode (Shallow th1)) (lower res)"
    by (simp add: REvalStep r_into_equivclp)
  moreover have "eq (lower h2) (lower res)"
    using force relaxed_X_def force_data
    by (metis eq_to_lower handle.simps(10) lift.simps(1)
        lift_to_lower_cancel lower_data_and_encode.simps(2))
  ultimately show ?case
    by (meson eq_def equivclp_sym equivclp_trans)
next
  case (CouponEvalBlobObj b)
  then show ?case
    by (simp add: value_handle.simps
        value_handle_eval_to_itself)
next
  case (CouponEvalTreeObj t1 t2)
  then have "list_all (\<lambda>h1. \<exists>r. eval h1 = Some r) (get_tree_raw t1)"
    by (smt (verit, best) list_all2_conv_all_nth
        list_all_length)

  then obtain list3 where "list_all2 (\<lambda>h1 h3. evals_to h1 h3) (get_tree_raw t1) list3"
    using eval_list_helper by blast
  then have "list_all2 (\<lambda>h2 h3. eq h2 h3) (get_tree_raw t2) list3"
    using CouponEvalTreeObj
    by (smt (verit, ccfv_threshold) eval_unique list_all2_conv_all_nth option.inject)

  have "list_all value_handle (get_tree_raw t2)"
    using CouponEvalTreeObj
    by (smt (verit, best) list_all2_conv_all_nth list_all_length)
  then have "value_handle (HTreeObj t2)"
    by auto

  moreover have "eval (HTreeObj t1) = Some (HTreeObj (create_tree list3))"
    using \<open>list_all2 evals_to (get_tree_raw t1) list3\<close> eval_entry_to_eval_tree by fastforce
  moreover have "eq (HTreeObj t2) (HTreeObj (create_tree list3))"
    by (metis \<open>list_all2 eq (get_tree_raw t2) list3\<close> create_tree_get_tree_raw eq_tree_list_all2)
  ultimately show ?case by blast
next
  case (CouponEvalRef r)
  then show ?case
    by (simp add: ref_handle value_handle_eval_to_itself)
next
  case (CouponEvalThunk t)
  then show ?case
    by (simp add: thunk_handle value_handle_eval_to_itself)
next
  case (CouponEvalEncode d h h')
  then have "rel_opt eq (eval (Encode d)) (eval h)"
    using eq_eval by presburger
  then obtain r' where "eval (Encode d) = Some r'" and "eq r' h'"
    using CouponEvalEncode 
    apply (cases "eval (Encode d)"; simp)
    by (force, metis eq_def equivclp_sym equivclp_trans
        rel_opt.simps(2))
  then show ?case
    by (meson CouponEvalEncode.IH(2) eq_def equivclp_sym)
next
  case (CouponEqApplication t1 t2)
  then show ?case
    using eq_tree_to_application_thunk by auto
next
  case (CouponEqSelection t1 t2)
  then show ?case
    using eq_tree_to_selection_thunk by auto
next
  case (CouponEqIdentification d1 d2)
  then show ?case
    using RSelf data_to_lift think_hs think_to_eq by force
next
  case (CouponEqEncodeStrict t1 t2)
  then show ?case
    using eq_thunk_to_strict_encode by force
next
  case (CouponEqEncodeShallow t1 t2)
  then show ?case
    using eq_strict_to_shallow eq_thunk_to_strict_encode by auto
next
  case (CouponEvalResultEq h1 h2)
  then show ?case
    by (meson eq_def equivclp_sym eval_both_to_eq
        value_handle_eval_to_itself)
next
  case (CouponEvalEq h1 h2 h3)
  then have "rel_opt eq (eval h1) (eval h3)"
    using eq_eval by presburger
  moreover obtain r where "eval h1 = Some r" and "eq h2 r" and "value_handle h2"
    using CouponEvalEq by auto
  ultimately obtain r' where "eval h3 = Some r'" and "eq h2 r'" 
    using CouponEvalEncode 
    apply (cases "(eval h3)"; simp)
    by (meson equivclp_trans)
  then show ?case
    using CouponEvalEq.IH(1) by blast
next
  case (CouponTreeRefEq t1 t2)
  then show ?case
    using eq_tree_to_ref by blast
next
  case (CouponBlobRefEq t1 t2)
  then show ?case
    using eq_blob_to_ref by blast
next
  case (CouponTreeEq t1 t2)
  then show ?case
    by (metis (mono_tags, lifting) create_tree_get_tree_raw
        eq_tree_list_all2 list_all2_mono)
next
  case (CouponStorageEq h1 h2)
  then show ?case
    using RBlob by auto
next
  case (CouponSelf h)
  then show ?case
    by simp
next
  case (CouponSym h1 h2)
  then show ?case
    by (meson eq_def equivclp_sym)
next
  case (CouponTrans h1 h2 h3)
  then show ?case 
    by (meson eq_def equivclp_trans)
qed

corollary coupon_blob_same_data:
  assumes "coupon_eq (HBlobObj b1) (HBlobObj b2)"
  shows "get_blob_data b1 = get_blob_data b2"
  using assms
proof -
  have "eq (HBlobObj b1) (HBlobObj b2)"
    using coupon_sound assms by presburger
  then show ?thesis
    using eq_blob_same_data by auto
qed

end
