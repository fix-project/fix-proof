theory make_coupon
  imports self_coupon storage_coupon
begin

datatype request =
  Blob | Self

fun request_to_nat :: "request \<Rightarrow> nat" where
  "request_to_nat Blob = 0"
| "request_to_nat Self = 1"

fun request_to_func_idx :: "request \<Rightarrow> nat" where
  "request_to_func_idx Blob = func_make_blob_coupon_idx"
| "request_to_func_idx Self = func_make_self_coupon_idx"

fun make_coupon :: "request \<Rightarrow> handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_coupon Blob coupons l r = make_blob_coupon_raw coupons l r"
| "make_coupon Self coupons l r = make_self_coupon_raw coupons l r"

lemma make_coupon_blob_some:
  assumes "make_coupon Blob coupons l r = Some res"
  shows "make_blob_coupon_raw coupons l r = Some res"
  using assms by auto

lemma make_coupon_blob_none:
  assumes "make_coupon Blob coupons l r = None"
  shows "make_blob_coupon_raw coupons l r = None"
  using assms by auto

lemma make_coupon_self_some:
  assumes "make_coupon Self coupons l r = Some res"
  shows "make_self_coupon_raw coupons l r = Some res"
  using assms by auto

lemma make_coupon_self_none:
  assumes "make_coupon Blob coupons l r = None"
  shows "make_blob_coupon_raw coupons l r = None"
  using assms by auto

lemma make_coupon_prologue:
  "run_invoke_v 
         (n + 10)
         (Suc depth)
         (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>,
         [(V_num (ConstInt32 (I32.int_of_nat (request_to_nat request)))),
          (V_ref (ConstRefExtern (to_externref l))),
          (V_ref (ConstRefExtern (to_externref r)))],
         func_make_coupon_idx) = (case run_iter n
          (Config depth
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context
              (Redex
                [V_ref (ConstRefExtern (to_externref r)),
                 V_ref (ConstRefExtern (to_externref l))]
                [Invoke (request_to_func_idx request)] [])
              [Label_context [] [] (Suc 0) [],
               Label_context [] [] (Suc 0) []]
              (Suc 0)
              \<lparr>f_locs =
                 [V_num (ConstInt32 (I32.int_of_nat (request_to_nat request))),
                  V_ref (ConstRefExtern (to_externref l)),
                  V_ref (ConstRefExtern (to_externref r))],
               f_inst = exp_inst \<rparr>)
            [Frame_context (Redex [] [] []) [] 0 empty_frame]) of
    (Config d s fc fcs, res) \<Rightarrow> (s, res))"  
proof -
  have 1: "n + 10 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))))))" by auto
  show ?thesis
  by (cases "request", auto simp add: I32.int_of_nat_def init_def tab_coupons_idx_def func_make_coupon_idx_def n_zeros_def app_f_v_s_local_get_def app_s_f_v_s_table_size_def stab_ind_def app_v_s_relop_def app_relop_def app_relop_i_def app_relop_i_v_def int_lt_u_i32_def I32.int_lt_u_def int_of_nat_i32.rep_eq I32.rep_abs app_v_s_if_def wasm_bool_def zero_i32_def int_eq_i32.abs_eq I32.int_eq_def tb_tf_def app_s_f_v_s_call_indirect_def tab_cl_ind_def nat_of_int_i32.abs_eq stypes_def cl_type_def func_make_blob_coupon_idx_def func_make_self_coupon_idx_def 1)
qed

lemma make_coupon_epilog:
"run_iter (n + 4)
    (Config depth s
      (Frame_context (Redex [V_ref (ConstRefExtern (to_externref (create_eq_coupon l r)))] [] [])  
      [Label_context [] [] (Suc 0) [], Label_context [] [] (Suc 0) []] 
      (Suc 0) f)
    [Frame_context (Redex [] [] []) [] 0 empty_frame]) 
  = 
    ((Config (Suc depth) s
    (Frame_context (Redex [V_ref (ConstRefExtern (to_externref (create_eq_coupon l r)))] [] []) [] 0 empty_frame) [])
    , RValue [V_ref (ConstRefExtern (to_externref (create_eq_coupon l r)))])"
proof -
  have 1: "4 = (Suc (Suc (Suc (Suc 0))))" by auto
  show ?thesis by (simp add: Let_def 1)
qed

lemma make_coupon_some:
  assumes "make_coupon request coupons l r = Some res"
  shows "\<exists>fuel depth. run_invoke_v
         fuel
         depth
         (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>,
         [(V_num (ConstInt32 (I32.int_of_nat (request_to_nat request)))),
          (V_ref (ConstRefExtern (to_externref l))),
          (V_ref (ConstRefExtern (to_externref r)))],
         func_make_coupon_idx)
         = (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>, RValue [V_ref (ConstRefExtern (to_externref (create_eq_coupon l r)))])"
proof (cases "request")
  case Blob
  show ?thesis
    using make_coupon_prologue[of 35 1 coupons "Blob"]
          make_blob_coupon_raw_run_iter[of coupons l r res 4 0 "[]"] assms
          make_coupon_epilog[of 0 1] Blob
    by (intro exI[where x=45]  exI[where x = "Suc (Suc 0)"]) auto
next
  case Self
  show ?thesis
    using make_coupon_prologue[of 18 1 coupons "Self"]
          make_self_coupon_raw_run_iter[of coupons l r res 4 0 "[]"] assms
          make_coupon_epilog[of 0 1] Self
    by (intro exI[where x=28]  exI[where x = "Suc (Suc 0)"]) auto
qed

lemma make_coupon_none:
  assumes "make_coupon request coupons l r = None"
  shows "\<exists>fuel depth cfg msg. run_invoke_v
         fuel
         depth
         (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>,
         [(V_num (ConstInt32 (I32.int_of_nat (request_to_nat request)))),
          (V_ref (ConstRefExtern (to_externref l))),
          (V_ref (ConstRefExtern (to_externref r)))],
         func_make_coupon_idx)
         = (cfg, RTrap msg)"
proof -
  have "\<exists>msg cfg. run_iter (fuel50 0)
          (Config 
           (Suc 1)
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      [])
                     [Invoke (request_to_func_idx request)]
                     [])
              [Label_context [] [] (Suc 0) [],
               Label_context [] [] (Suc 0) []]
              (Suc 0)
              \<lparr>f_locs =
                 [V_num (ConstInt32 (I32.int_of_nat (request_to_nat request))),
                  V_ref (ConstRefExtern (to_externref l)),
                  V_ref (ConstRefExtern (to_externref r))],
               f_inst = exp_inst \<rparr>)
            [Frame_context (Redex [] [] []) [] 0 empty_frame])
        = (cfg, RTrap msg)"
    using make_blob_coupon_raw_run_invoke_none make_self_coupon_raw_run_invoke_none assms
    by (cases "request") auto

  then have "\<exists>msg cfg. (run_invoke_v
         ((fuel50 0) + 10)
         (Suc (Suc 1))
         (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>,
         [(V_num (ConstInt32 (I32.int_of_nat (request_to_nat request)))),
          (V_ref (ConstRefExtern (to_externref l))),
          (V_ref (ConstRefExtern (to_externref r)))],
         func_make_coupon_idx))
         = (case (cfg, RTrap msg) of (Config d s fc fcs, res) \<Rightarrow> (s, res))"
    by (simp only: make_coupon_prologue) metis

  then show ?thesis
    by (metis (mono_tags, lifting) case_prod_conv config.case config.exhaust)
qed

end