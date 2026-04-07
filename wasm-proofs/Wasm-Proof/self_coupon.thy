theory self_coupon
  imports Wasm_Proof_Playground isabelle_coupon
begin

lemma ms_some:
  assumes "make_self_coupon_raw coupons l r = Some res"
  shows "is_equal l r \<and> res = (create_eq_coupon l r)"
  by (metis assms make_self_coupon_raw.simps option.distinct(1) option.sel)

lemma make_self_coupon_raw_run_iter:
  assumes "make_self_coupon_raw coupons l r = Some res"
  shows "run_iter  
  (n + 14)
  (Config 
   (Suc n')
   (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
   (Frame_context 
      (Redex ((V_ref (ConstRefExtern (to_externref r))) #
              (V_ref (ConstRefExtern (to_externref l))) #
              rest_vs)
             [Invoke func_make_self_coupon_idx]
             b_es)
    lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
  =
   run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  have 1: "is_equal l r" using ms_some[OF assms] by blast
  have 2: "res = create_eq_coupon l r" using ms_some[OF assms] by blast

  let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  have 3: "n + 14 =
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))))))))))"
    by auto

  show ?thesis
    using fixpoint_is_equal_correct_externref[of "to_externref l" "to_externref r" ?state] 1
    fixpoint_create_eq_coupon_impl[of ?state "to_externref l" "to_externref r"]
    by (auto split: cl.splits simp del: split_n.simps simp add: init_def func_make_self_coupon_idx_def app_f_call_def sfunc_ind_def n_zeros_def split_n_0 split_n_1 split_n_2 app_f_v_s_local_get_def 2 typeof_def typeof_ref_def typeof_num_def tab_coupons_idx_def app_v_s_if_def se tb_tf_def 3)
qed

lemma ms_none:
  assumes "make_self_coupon_raw coupons l r = None"
  shows "\<not> is_equal l r"
  using assms by force

lemma make_self_coupon_raw_run_invoke_none:
  assumes "make_self_coupon_raw coupons l r = None"
  shows "\<exists>msg cfg.
         run_iter (fuel50 n)
         (Config
          (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_self_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
        = (cfg, RTrap msg)"
proof -
  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  have 1: "\<not>is_equal l r"
    using ms_none[OF assms] .

  show ?thesis
    using fixpoint_is_equal_correct_externref_neq[of "to_externref l" "to_externref r" ?state] 1    
    by (auto split: cl.splits simp del: split_n.simps simp add:  init_def func_make_self_coupon_idx_def n_zeros_def bitzero_def tab_coupons_idx_def app_s_f_v_s_table_get_def stab_ind_def load_tabs1_def
    app_f_v_s_local_set_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def  se tb_tf_def typeof_ref_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def split_n_0 split_n_1 split_n_2 app_v_s_if_def sf)
qed

end