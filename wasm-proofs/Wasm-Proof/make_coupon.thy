theory make_coupon
  imports self_coupon storage_coupon tree_coupon thunk_coupon thunktree_coupon thunkforce_coupon encode_coupon sym_coupon trans_coupon
begin

fun request_to_nat :: "request \<Rightarrow> nat" where
  "request_to_nat Storage = 0"
| "request_to_nat Tree = 1"
| "request_to_nat Thunk = 2"
| "request_to_nat ThunkTree = 3"
| "request_to_nat ThunkForce = 4"
| "request_to_nat Encode = 5"
| "request_to_nat Sym = 6"
| "request_to_nat Trans = 7"
| "request_to_nat Self = 8"

fun request_to_func_idx :: "request \<Rightarrow> nat" where
  "request_to_func_idx Storage = func_make_storage_coupon_idx"
| "request_to_func_idx Tree = func_make_tree_coupon_idx"
| "request_to_func_idx Thunk = func_make_thunk_coupon_idx"
| "request_to_func_idx ThunkTree = func_make_thunktree_coupon_idx"
| "request_to_func_idx ThunkForce = func_make_thunkforce_coupon_idx"
| "request_to_func_idx Encode = func_make_encode_coupon_idx"
| "request_to_func_idx Self = func_make_self_coupon_idx"
| "request_to_func_idx Sym = func_make_sym_coupon_idx"
| "request_to_func_idx Trans = func_make_trans_coupon_idx"

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
    func_make_storage_coupon_idx_def
    func_make_tree_coupon_idx_def 
    func_make_thunk_coupon_idx_def
    func_make_thunktree_coupon_idx_def
    func_make_thunkforce_coupon_idx_def
    func_make_encode_coupon_idx_def
    func_make_sym_coupon_idx_def
    func_make_trans_coupon_idx_def
    func_make_self_coupon_idx_def 
    1)
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
  assumes "length coupons < 2^(LENGTH(i32) - 1)"
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
  case Storage
  show ?thesis
    using make_coupon_prologue[of 37 1 coupons "Storage"]
          make_storage_coupon_raw_run_iter[of coupons l r res 4 0 "[]"] assms
          make_coupon_epilog[of 0 1] Storage
    by (intro exI[where x=47]  exI[where x = "Suc (Suc 0)"]) auto
next
  case Tree
  show ?thesis
    using make_coupon_prologue[of "45 + 54 * (length coupons)" 1 coupons "Tree"]
          make_tree_coupon_raw_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] Tree
    by (intro exI[of _ "55 + 54 * (length coupons)"] exI[of _ "Suc (Suc 0)"]) auto
next
  case Thunk
  show ?thesis
    using make_coupon_prologue[of 75 1 coupons "Thunk"]
          make_thunk_coupon_raw_run_iter[of coupons l r res 4 0 "[]"]
          assms
          make_coupon_epilog[of 0 1] Thunk
    by (intro exI[where x=85] exI[where x = "Suc (Suc 0)"]) auto
next
  case ThunkTree
  show ?thesis
    using make_coupon_prologue[of 41 1 coupons "ThunkTree"]
          make_thunktree_coupon_raw_run_iter[of coupons l r res 4 0 "[]"] assms
          make_coupon_epilog[of 0 1] ThunkTree
    by (intro exI[of _ 51] exI[of _ "Suc (Suc 0)"]) auto
next
  case ThunkForce
  show ?thesis
    using make_coupon_prologue[of 75 1 coupons "ThunkForce"]
          make_thunkforce_coupon_raw_run_iter[of coupons l r res 4 0 "[]"] 
          assms
          make_coupon_epilog[of 0 1] ThunkForce
    by (intro exI[of _ 85] exI[of _ "Suc (Suc 0)"]) auto
next
  case Encode
  show ?thesis
    using make_coupon_prologue[of 41 1 coupons "Encode"]
          make_encode_coupon_raw_run_iter[of coupons l r res 4 0 "[]"]
          assms
          make_coupon_epilog[of 0 1] Encode
    by (intro exI[of _ 51] exI[of _ "Suc (Suc 0)"]) auto
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
          make_sym_coupon_raw_run_iter[of coupons l r res 4 0 "[]"]
          assms
          make_coupon_epilog[of 0 1] Sym
    by (intro exI[where x=47] exI[where x = "Suc (Suc 0)"]) auto
next
  case Trans
  show ?thesis
    using make_coupon_prologue[of 56 1 coupons "Trans"]
          make_trans_coupon_raw_run_iter[of coupons l r res 4 0 "[]"]
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
    case Storage
    show ?thesis
      using make_storage_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] assms
            Storage
      by force
  next
    case Tree
    show ?thesis
      using make_tree_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            Tree
      by force
  next
    case Thunk
    show ?thesis
      using make_thunk_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            Thunk
      by force
  next
    case ThunkTree
    show ?thesis
      using make_thunktree_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            ThunkTree
      by force
  next
    case ThunkForce
    show ?thesis
      using make_thunkforce_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            ThunkForce
      by force
  next
    case Encode
    show ?thesis
      using make_encode_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            Encode
      by force
  next
    case Self
    show ?thesis
      using make_self_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            Self
      by force
  next
    case Sym
    show ?thesis
      using make_sym_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            Sym
      by force
  next
    case Trans
    show ?thesis
      using make_trans_coupon_raw_run_invoke_none[of coupons l r 4 0 "[]"] 
            assms
            Trans
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