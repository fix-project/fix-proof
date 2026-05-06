theory force_to_encode_strict_coupon
  imports custom_method isabelle_coupon
begin

lemma make_some:
  assumes "make_force_to_encode_strict_coupon coupons l r = Some res"
  shows "\<exists>t xs tl.
         coupons = t # xs
       \<and> is_force_coupon t
       \<and> get_coupon_lhs t = Some tl
       \<and> get_coupon_rhs t = Some r
       \<and> create_strict_encode_api tl = Some l
       \<and> (get_type r = 0 \<or> get_type r = 1)
       \<and> res = create_coupon Eq l r"
proof -
  obtain t xs where 1: "coupons = t # xs \<and> is_force_coupon t"
    using assms
    apply (cases coupons; simp_all)
    by fastforce

  then obtain tl tr where 2: "get_coupon_lhs t = Some tl \<and> get_coupon_rhs t = Some tr"
    using force_lhs_exist force_rhs_exist
    by presburger

  show ?thesis
    using 1 2 assms
    apply simp
    apply (cases "create_strict_encode_api tl"; simp_all)
    by (metis option.distinct(1) option.sel)
qed

lemma make_none:
  assumes "make_force_to_encode_strict_coupon coupons l r = None" 
  shows "(length coupons = 0) \<or>
         (\<exists>t xs. coupons = t # xs \<and> \<not> is_force_coupon t) \<or>
         (\<exists>t xs tl tr. 
           coupons = t # xs 
         \<and> is_force_coupon t
         \<and> get_coupon_lhs t = Some tl
         \<and> get_coupon_rhs t = Some tr
         \<and> create_strict_encode_api tl = None) \<or>
         (\<exists>t xs tl tr encode. 
           coupons = t # xs 
         \<and> is_force_coupon t
         \<and> get_coupon_lhs t = Some tl
         \<and> get_coupon_rhs t = Some tr
         \<and> create_strict_encode_api tl = Some encode
         \<and> ((get_type tr = 0 \<or> get_type tr = 1) \<longrightarrow> (\<not> is_equal encode l \<or> \<not> is_equal tr r)))"
proof (cases "length coupons = 0")
  case True then show ?thesis by auto
next
  case False
  then obtain t xs where 1: "coupons = t # xs"
    by (metis list.exhaust list.size(3))
  then show ?thesis
  proof (cases "is_force_coupon t")
    case False then show ?thesis
      using 1 by blast
  next
    case True
    then obtain tl tr where
         "get_coupon_lhs t = Some tl
        \<and> get_coupon_rhs t = Some tr"
      using force_lhs_exist force_rhs_exist
      by presburger

    then show ?thesis
      using 1 assms
      by fastforce
  qed
qed

lemma plus_43:
"n + 43 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 
(Suc (Suc (Suc (Suc (Suc (Suc (Suc(Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))))))))))))))"
  by auto

lemma make_force_to_encode_strict_coupon_run_iter:
  assumes "make_force_to_encode_strict_coupon coupons l r = Some res"
  shows  "run_iter (n + 43)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_force_to_encode_strict_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref res)) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  obtain t xs tl where
         1: "coupons = t # xs
       \<and> is_force_coupon t
       \<and> get_coupon_lhs t = Some tl
       \<and> get_coupon_rhs t = Some r
       \<and> create_strict_encode_api tl = Some l
       \<and> (get_type r = 0 \<or> get_type r = 1)
       \<and> res = create_coupon Eq l r"
    using make_some[OF assms] by auto

  let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  show ?thesis
    using 1 
          fixpoint_is_force_coupon_impl[of ?state]
          fixpoint_get_coupon_lhs_impl[of ?state]
          fixpoint_get_coupon_rhs_impl[of ?state]
          fixpoint_is_equal_impl[of ?state]
          fixpoint_is_object_impl[of ?state]
          fixpoint_create_eq_coupon_impl[of ?state]
          fixpoint_create_strict_encode_impl[of ?state]
    apply (invoke_coupon_func fuel_idx_def: plus_43 func_make_force_to_encode_strict_coupon_idx_def)
    apply (table_get_local_set)
    apply (call_api_func)
    apply (if_block)
    apply (call_api_func)
    apply (if_block)
    apply (call_api_func)
    apply (if_block)
    apply (call_api_func)
    apply (if_block)
    apply (call_api_func)
    done
qed

lemma make_force_to_encode_strict_coupon_run_invoke_none:
  assumes "make_force_to_encode_strict_coupon coupons l r = None"
  shows "\<exists>msg cfg.
         run_iter (n + 43)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_force_to_encode_strict_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 = (cfg, RTrap msg)"
proof -
  let ?A = "(length coupons = 0)"
  let ?B = "(\<exists>t xs. coupons = t # xs \<and> \<not> is_force_coupon t)"
  let ?C = "(\<exists>t xs tl tr. 
           coupons = t # xs 
         \<and> is_force_coupon t
         \<and> get_coupon_lhs t = Some tl
         \<and> get_coupon_rhs t = Some tr
         \<and> create_strict_encode_api tl = None)"
  let ?D = "(\<exists>t xs tl tr encode. 
           coupons = t # xs 
         \<and> is_force_coupon t
         \<and> get_coupon_lhs t = Some tl
         \<and> get_coupon_rhs t = Some tr
         \<and> create_strict_encode_api tl = Some encode
         \<and> ((get_type tr = 0 \<or> get_type tr = 1) \<longrightarrow> (\<not> is_equal encode l \<or> \<not> is_equal tr r)))"

  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  have assms: "?A \<or> ?B \<or> ?C \<or> ?D" 
    using make_none[OF assms] by blast

  show ?thesis
    using assms
  proof
    assume ?A
    then have "\<not> nat_of_int (I32.lift0 0) < length coupons"
      by (simp add: nat_of_int_i32.abs_eq)
    then show ?thesis
      apply (invoke_coupon_func fuel_idx_def: plus_43 func_make_force_to_encode_strict_coupon_idx_def)
      apply (table_get_local_set)
      done
  next
    assume "?B \<or> ?C \<or> ?D"
    then show ?thesis
    proof
      assume ?B
      then obtain t xs where
        "coupons = t # xs"
     and "\<not>is_force_coupon t" by blast

      then show ?thesis
        using fixpoint_is_force_coupon_impl[of ?state]
        apply (invoke_coupon_func fuel_idx_def: plus_43 func_make_force_to_encode_strict_coupon_idx_def)
        apply (table_get_local_set)
        apply (call_api_func)
        apply (if_block)
        done
    next
      assume "?C \<or> ?D"
      then show ?thesis
      proof
        assume ?C
        then obtain t xs tl tr where
           "coupons = t # xs 
         \<and> is_force_coupon t
         \<and> get_coupon_lhs t = Some tl
         \<and> get_coupon_rhs t = Some tr
         \<and> create_strict_encode_api tl = None"
          by blast
        
        then show ?thesis
          using fixpoint_is_force_coupon_impl[of ?state]
            fixpoint_get_coupon_lhs_impl[of ?state]
            fixpoint_get_coupon_rhs_impl[of ?state]
            fixpoint_is_equal_impl[of ?state]
            fixpoint_is_object_impl[of ?state]
            fixpoint_create_eq_coupon_impl[of ?state]
            fixpoint_create_strict_encode_impl[of ?state]
          apply (invoke_coupon_func fuel_idx_def: plus_43 func_make_force_to_encode_strict_coupon_idx_def)
          apply (table_get_local_set)
          apply (call_api_func)
          apply (if_block)
          apply (call_api_func)
          apply (if_block)
          apply (call_api_func)
          apply (if_block)
          apply (call_api_func)
          done
      next
        assume ?D
        then obtain t xs tl tr encode where
           1: "coupons = t # xs 
         \<and> is_force_coupon t
         \<and> get_coupon_lhs t = Some tl
         \<and> get_coupon_rhs t = Some tr
         \<and> create_strict_encode_api tl = Some encode"
         and 2: "(get_type tr = 0 \<or> get_type tr = 1) \<longrightarrow> (\<not> is_equal encode l \<or> \<not> is_equal tr r)"
          by blast
      
        show ?thesis
        proof (cases "get_type tr = 0 \<or> get_type tr = 1")
          case False
          then have "host_func_apply_impl ?state type_r_i32 fixpoint_is_object
  [(V_ref (ConstRefExtern (to_externref tr)))] 
  = Some (?state, [V_num (ConstInt32 (wasm_bool False))])"
          using fixpoint_is_object_impl[of ?state]
          using to_handle_to_externref by presburger

          then show ?thesis
            using 1 
                  fixpoint_is_force_coupon_impl[of ?state]
                  fixpoint_get_coupon_lhs_impl[of ?state]
                  fixpoint_get_coupon_rhs_impl[of ?state]
                  fixpoint_is_equal_impl[of ?state]
                  fixpoint_create_eq_coupon_impl[of ?state]
                  fixpoint_create_strict_encode_impl[of ?state]
            apply (invoke_coupon_func fuel_idx_def: plus_43 func_make_force_to_encode_strict_coupon_idx_def)
            apply (table_get_local_set)
            apply (call_api_func)
            apply (if_block)
            apply (call_api_func)
            apply (if_block)
            done
        next
          case True
          then have 3: "host_func_apply_impl ?state type_r_i32 fixpoint_is_object
  [(V_ref (ConstRefExtern (to_externref tr)))] 
  = Some (?state, [V_num (ConstInt32 (wasm_bool True))])"
            using fixpoint_is_object_impl[of ?state]
            using to_handle_to_externref by presburger

          moreover have 4: "(\<not> is_equal encode l \<or> \<not> is_equal tr r)"
            using 2 True
            by blast

          ultimately show ?thesis
            using 1 
                  fixpoint_is_force_coupon_impl[of ?state]
                  fixpoint_get_coupon_lhs_impl[of ?state]
                  fixpoint_get_coupon_rhs_impl[of ?state]
                  fixpoint_is_equal_impl[of ?state]
                  fixpoint_is_object_impl[of ?state]
                  fixpoint_create_eq_coupon_impl[of ?state]
                  fixpoint_create_strict_encode_impl[of ?state]
            apply (invoke_coupon_func fuel_idx_def: plus_43 func_make_force_to_encode_strict_coupon_idx_def)
            apply (table_get_local_set)
            apply (call_api_func)
            apply (if_block)
            apply (call_api_func)
            apply (if_block)
            apply (call_api_func)
            apply (if_block)
            apply (call_api_func)
            apply (if_block)
            done
        qed
      qed
    qed
  qed
qed

end