theory eval_blobobj_coupon
  imports custom_method isabelle_coupon
begin

lemma make_some:
  assumes "make_eval_blob_coupon coupons l r = Some res"
  shows "get_type l = 0 \<and> is_equal l r \<and> res = create_coupon Eval l r"
  by (metis assms if_Some_None_eq_None make_eval_blob_coupon.simps
      option.inject)

lemma make_none:
  assumes "make_eval_blob_coupon coupons l r = None" 
  shows "\<not> get_type l = 0 \<or> \<not>is_equal l r "
  using assms by force

lemma plus_20:
"n + 20 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))))))))))))))))"
  by auto

lemma make_eval_blob_coupon_run_iter:
  assumes "make_eval_blob_coupon coupons l r = Some res"
  shows  "run_iter (n + 20)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_eval_blobobj_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref res)) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  have "get_type r = 0"
    using make_some[OF assms]
    by auto

  then show ?thesis
    using make_some[OF assms]
          fixpoint_is_equal_impl[of ?state]
          fixpoint_create_eval_coupon_impl[of ?state]
          fixpoint_is_blob_obj_impl[of ?state]
    apply (invoke_coupon_func fuel_idx_def: plus_20 func_make_eval_blobobj_coupon_idx_def)
    apply (call_api_func)
    apply (if_block)
    apply (call_api_func)
    apply (if_block)
    apply (call_api_func)
    done
qed

lemma make_eval_blobobj_coupon_run_invoke_none:
  assumes "make_eval_blob_coupon coupons l r = None"
  shows "\<exists>msg cfg.
         run_iter (n + 20)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_eval_blobobj_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 = (cfg, RTrap msg)"
proof -
  let ?A = "\<not>get_type l = 0"
  let ?B = "get_type l = 0 \<and> \<not>is_equal l r"

  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  have assms: "?A \<or> ?B" 
    using make_none[OF assms] 
    by meson

  show ?thesis
    using assms
  proof
    assume ?A
    then show ?thesis
      using fixpoint_is_blob_obj_impl[of ?state]
      apply (invoke_coupon_func fuel_idx_def: plus_20 func_make_eval_blobobj_coupon_idx_def)
      apply (call_api_func)
      apply (if_block)
      done
  next
    assume ?B
    then show ?thesis
      using fixpoint_is_equal_impl[of ?state]
            fixpoint_create_eval_coupon_impl[of ?state]
            fixpoint_is_blob_obj_impl[of ?state]
      apply (invoke_coupon_func fuel_idx_def: plus_20 func_make_eval_blobobj_coupon_idx_def)
      apply (call_api_func)
      apply (if_block)
      apply (call_api_func)
      apply (if_block)
      done
  qed
qed

end