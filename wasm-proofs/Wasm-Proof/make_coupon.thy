theory make_coupon
  imports self_coupon sym_coupon trans_coupon eq_application_coupon eq_encode_strict_coupon eq_tree_coupon eval_blobobj_coupon eval_tree_coupon force_result_eq_coupon force_to_encode_strict_coupon think_application_coupon think_to_force_coupon eval_eq_coupon
begin

fun request_to_nat :: "request \<Rightarrow> nat" where
  "request_to_nat TreeEq = 0"
| "request_to_nat EqApplication = 1"
| "request_to_nat ForceResultEq = 2"
| "request_to_nat EqEncodeStrict = 3"
| "request_to_nat ThinkApplication = 4"
| "request_to_nat ThinkToForce = 5"
| "request_to_nat ForceToEncodeStrict = 6"
| "request_to_nat EvalEq = 7"
| "request_to_nat EvalBlobObj = 8"
| "request_to_nat EvalTreeObj = 9"
| "request_to_nat Sym = 10"
| "request_to_nat Trans = 11"
| "request_to_nat Self = 12"

fun request_to_func_idx :: "request \<Rightarrow> nat" where
  "request_to_func_idx TreeEq = func_make_eq_tree_coupon_idx"
| "request_to_func_idx EqApplication = func_make_eq_application_coupon_idx"
| "request_to_func_idx ForceResultEq = func_make_force_result_eq_coupon_idx"
| "request_to_func_idx EqEncodeStrict = func_make_eq_encode_strict_coupon_idx"
| "request_to_func_idx ThinkApplication = func_make_think_application_coupon_idx"
| "request_to_func_idx ThinkToForce = func_make_think_to_force_coupon_idx"
| "request_to_func_idx ForceToEncodeStrict = func_make_force_to_encode_strict_coupon_idx"
| "request_to_func_idx EvalEq = func_make_eval_eq_coupon_idx"
| "request_to_func_idx EvalBlobObj = func_make_eval_blobobj_coupon_idx"
| "request_to_func_idx EvalTreeObj = func_make_eval_tree_coupon_idx"
| "request_to_func_idx Sym = func_make_sym_coupon_idx"
| "request_to_func_idx Trans = func_make_trans_coupon_idx"
| "request_to_func_idx Self = func_make_self_coupon_idx"

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
    by (cases "request", simp_all add: I32.int_of_nat_def init_def tab_coupons_idx_def func_make_coupon_idx_def n_zeros_def app_f_v_s_local_get_def app_s_f_v_s_table_size_def stab_ind_def app_v_s_relop_def app_relop_def app_relop_i_def app_relop_i_v_def int_lt_u_i32_def I32.int_lt_u_def int_of_nat_i32.rep_eq I32.rep_abs app_v_s_if_def wasm_bool_def zero_i32_def int_eq_i32.abs_eq I32.int_eq_def tb_tf_def app_s_f_v_s_call_indirect_def tab_cl_ind_def nat_of_int_i32.abs_eq stypes_def cl_type_def 
    func_make_eq_tree_coupon_idx_def
    func_make_eq_application_coupon_idx_def
    func_make_force_result_eq_coupon_idx_def
    func_make_eq_encode_strict_coupon_idx_def
    func_make_think_application_coupon_idx_def
    func_make_think_to_force_coupon_idx_def
    func_make_force_to_encode_strict_coupon_idx_def
    func_make_eval_eq_coupon_idx_def
    func_make_eval_blobobj_coupon_idx_def
    func_make_eval_tree_coupon_idx_def
    func_make_sym_coupon_idx_def
    func_make_trans_coupon_idx_def
    func_make_self_coupon_idx_def
    1)
qed

lemma make_coupon_epilog:
"run_iter (n + 4)
    (Config depth s
      (Frame_context (Redex [V_ref (ConstRefExtern (to_externref res))] [] [])  
      [Label_context [] [] (Suc 0) [], Label_context [] [] (Suc 0) []] 
      (Suc 0) f)
    [Frame_context (Redex [] [] []) [] 0 empty_frame]) 
  = 
    ((Config (Suc depth) s
    (Frame_context (Redex [V_ref (ConstRefExtern (to_externref res))] [] []) [] 0 empty_frame) [])
    , RValue [V_ref (ConstRefExtern (to_externref res))])"
proof -
  have 1: "4 = (Suc (Suc (Suc (Suc 0))))" by auto
  show ?thesis by (simp add: Let_def 1)
qed

lemma make_coupon_some:
  assumes "make_coupon request coupons l r = Some res"
  assumes "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<exists>fuel depth. run_invoke_v
         fuel
         depth
         (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>,
         [(V_num (ConstInt32 (I32.int_of_nat (request_to_nat request)))),
          (V_ref (ConstRefExtern (to_externref l))),
          (V_ref (ConstRefExtern (to_externref r)))],
         func_make_coupon_idx)
         = (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>, RValue [V_ref (ConstRefExtern (to_externref res))])"
proof (cases "request")
  case TreeEq
  show ?thesis
    using make_coupon_prologue[of "45 + 54 * (length coupons)" 1 coupons "TreeEq"]
          make_tree_coupon_raw_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] TreeEq
    by (intro exI[of _ "55 + 54 * (length coupons)"] exI[of _ "Suc (Suc 0)"]) auto
next
  case EvalTreeObj
  show ?thesis
    using make_coupon_prologue[of "45 + 54 * (length coupons)" 1 coupons "EvalTreeObj"]
          make_eval_tree_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] EvalTreeObj
    by (intro exI[of _ "55 + 54 * (length coupons)"] exI[of _ "Suc (Suc 0)"]) auto
next
  case ForceResultEq
  show ?thesis
    using make_coupon_prologue[of 75 1 coupons "ForceResultEq"]
          make_force_result_eq_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] ForceResultEq
    by (intro exI[of _ 85] exI[of _ "Suc (Suc 0)"]) auto
next
  case ThinkApplication
  show ?thesis
    using make_coupon_prologue[of 58 1 coupons "ThinkApplication"]
          make_think_application_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] ThinkApplication
    by (intro exI[of _ 68] exI[of _ "Suc 1"]) auto
next
  case ThinkToForce
  show ?thesis
    using make_coupon_prologue[of 45 1 coupons "ThinkToForce"]
          make_think_to_force_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] ThinkToForce
    by (intro exI[of _ 55] exI[of _ "Suc 1"]) auto
next
  case EqApplication
  show ?thesis
    using make_coupon_prologue[of 41 1 coupons "EqApplication"]
          make_eq_application_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] EqApplication
    by (intro exI[of _ 51] exI[of _ "Suc 1"]) auto
next
  case EvalBlobObj
  show ?thesis
    using make_coupon_prologue[of 24 1 coupons "EvalBlobObj"]
          make_eval_blob_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] EvalBlobObj
    by (intro exI[of _ 34] exI[of _ "Suc 1"]) auto
next
  case ForceToEncodeStrict
  show ?thesis
    using make_coupon_prologue[of 47 1 coupons "ForceToEncodeStrict"]
          make_force_to_encode_strict_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] ForceToEncodeStrict
    by (intro exI[of _ 57] exI[of _ "Suc 1"]) auto
next
  case EvalEq
  show ?thesis
    using make_coupon_prologue[of 56 1 coupons "EvalEq"]
          make_eval_eq_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] EvalEq
    by (intro exI[of _ 66] exI[of _ "Suc 1"]) auto
next
  case EqEncodeStrict
  show ?thesis
    using make_coupon_prologue[of 41 1 coupons "EqEncodeStrict"]
          make_eq_encode_strict_coupon_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] EqEncodeStrict
    by (intro exI[of _ 51] exI[of _ "Suc 1"]) auto
next
  case Self
  show ?thesis
    using make_coupon_prologue[of 18 1 coupons "Self"]
          make_self_coupon_raw_run_iter[of coupons l r res 4 0 "[]"] assms
          make_coupon_epilog[of 0 1] Self
    by (intro exI[where x=28]  exI[where x = "Suc (Suc 0)"]) auto
next
  case Sym
  show ?thesis
    using make_coupon_prologue[of 37 1 coupons "Sym"]
          make_sym_coupon_run_iter[of coupons l r res 4 0 "[]"]
          assms
          make_coupon_epilog[of 0 1] Sym
    by (intro exI[where x=47] exI[where x = "Suc (Suc 0)"]) auto
next
  case Trans
  show ?thesis
    using make_coupon_prologue[of 56 1 coupons "Trans"]
          make_trans_coupon_run_iter[of coupons l r res 4 0 "[]"]
          assms
          make_coupon_epilog[of 0 1] Trans
    by (intro exI[of _ 66] exI[of _ "Suc (Suc 0)"]) auto
qed

lemma make_coupon_none:
  assumes "make_coupon request coupons l r = None"
  assumes "length coupons < 2^(LENGTH(i32) - 1)"
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
  have "\<exists>fuel cfg msg. run_iter fuel
          (Config
           (Suc 0)
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
  proof (cases "request")
    case TreeEq
    show ?thesis
      using make_tree_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            TreeEq
      by force
  next
    case ForceResultEq
    then show ?thesis
      using make_force_result_eq_coupon_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms 
      by force
  next
    case ThinkApplication
    then show ?thesis
      using make_think_application_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case ThinkToForce
    then show ?thesis
      using make_think_to_force_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case EqApplication
    then show ?thesis
      using make_eq_application_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case EvalBlobObj
    then show ?thesis
      using make_eval_blobobj_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case EvalTreeObj
    then show ?thesis
      using make_eval_tree_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case ForceToEncodeStrict
    then show ?thesis
      using make_force_to_encode_strict_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case EvalEq
    then show ?thesis
      using make_eval_eq_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case EqEncodeStrict
    then show ?thesis
      using make_eq_encode_strict_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case Sym
    then show ?thesis
      using make_sym_coupon_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case Trans
    then show ?thesis
      using make_trans_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  next
    case Self
    then show ?thesis
      using make_self_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"]
            assms
      by force
  qed

  then have "\<exists>fuel msg cfg. (run_invoke_v
         (fuel + 10)
         (Suc (Suc 0))
         (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>,
         [(V_num (ConstInt32 (I32.int_of_nat (request_to_nat request)))),
          (V_ref (ConstRefExtern (to_externref l))),
          (V_ref (ConstRefExtern (to_externref r)))],
         func_make_coupon_idx))
         = (case (cfg, RTrap msg) of (Config d s fc fcs, res) \<Rightarrow> (s, res))"
    by (simp only: make_coupon_prologue, metis)

  then show ?thesis
    by (metis (mono_tags, lifting) case_prod_conv config.case config.exhaust)
qed

end