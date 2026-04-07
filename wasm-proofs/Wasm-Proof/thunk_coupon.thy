theory thunk_coupon
  imports custom_method isabelle_coupon
begin

lemma mt_some:
  assumes "make_thunk_coupon_raw coupons l r = Some res"
  shows "(\<exists>f1 f2 e xs f1l f1r f2l f2r el er.
          coupons = f1 # f2 # e # xs
        \<and> is_force_coupon_api f1
        \<and> is_force_coupon_api f2
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs f1 = Some f1l
        \<and> get_coupon_rhs f1 = Some f1r
        \<and> get_coupon_lhs f2 = Some f2l
        \<and> get_coupon_rhs f2 = Some f2r
        \<and> get_coupon_lhs e = Some el
        \<and> get_coupon_rhs e = Some er
        \<and> is_equal f1r el
        \<and> is_equal f2r er
        \<and> is_equal f1l l
        \<and> is_equal f2l r
        \<and> res = (create_eq_coupon l r))"
proof -
  obtain f1 f2 e xs f1l f1r f2l f2r el er where
          1: "coupons = f1 # f2 # e # xs
        \<and> is_force_coupon_api f1
        \<and> is_force_coupon_api f2
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs f1 = Some f1l
        \<and> get_coupon_rhs f1 = Some f1r
        \<and> get_coupon_lhs f2 = Some f2l
        \<and> get_coupon_rhs f2 = Some f2r
        \<and> get_coupon_lhs e = Some el
        \<and> get_coupon_rhs e = Some er"
  by (metis assms is_coupon_lhs is_coupon_rhs is_force_coupon_api_def is_eq_coupon_api_def make_thunk_coupon_raw.elims option.simps(3))

  then have "make_thunk_coupon_raw coupons l r
   = (if (is_equal f1r el \<and> is_equal f2r er \<and> is_equal f1l l \<and> is_equal f2l r) then Some (create_eq_coupon l r) else None)"
    by (auto)

  then show ?thesis
    by (metis (no_types, lifting) 1 assms handy_if_lemma)
qed

lemma mt_some_rev:
  assumes "(\<exists>f1 f2 e xs f1l f1r f2l f2r el er.
          coupons = f1 # f2 # e # xs
        \<and> is_force_coupon_api f1
        \<and> is_force_coupon_api f2
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs f1 = Some f1l
        \<and> get_coupon_rhs f1 = Some f1r
        \<and> get_coupon_lhs f2 = Some f2l
        \<and> get_coupon_rhs f2 = Some f2r
        \<and> get_coupon_lhs e = Some el
        \<and> get_coupon_rhs e = Some er
        \<and> is_equal f1r el
        \<and> is_equal f2r er
        \<and> is_equal f1l l
        \<and> is_equal f2l r)"
  shows "make_thunk_coupon_raw coupons l r = Some (create_eq_coupon l r)"
  using assms by fastforce

lemma mt_none:
  assumes "make_thunk_coupon_raw coupons l r = None"
  shows "(length coupons < 3) \<or>
         (\<exists>f1 f2 e xs. coupons = f1 # f2 # e # xs \<and>
          (\<not>is_force_coupon_api f1 \<or> \<not>is_force_coupon_api f2 \<or> \<not> is_eq_coupon_api e)) \<or>
         (\<exists>f1 f2 e xs f1l f1r f2l f2r el er.
          coupons = f1 # f2 # e # xs
        \<and> is_force_coupon_api f1
        \<and> is_force_coupon_api f2
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs f1 = Some f1l
        \<and> get_coupon_rhs f1 = Some f1r
        \<and> get_coupon_lhs f2 = Some f2l
        \<and> get_coupon_rhs f2 = Some f2r
        \<and> get_coupon_lhs e = Some el
        \<and> get_coupon_rhs e = Some er
        \<and> (\<not>is_equal f1r el \<or> \<not>is_equal f2r er \<or> \<not>is_equal f1l l \<or> \<not>is_equal f2l r))"
proof (cases "length coupons < 3")
  case True then show ?thesis by auto
next
  case False
  then obtain f1 f2 e xs where 1: "coupons = f1 # f2 # e # xs"
    using list_length_3 by blast

  then show ?thesis
  proof (cases "\<not>(is_force_coupon_api f1 \<and> is_force_coupon_api f2 \<and> is_eq_coupon_api e)")
    case True then show ?thesis using 1 by blast
  next
    case False
    then have "is_force_coupon_api f1 \<and> is_force_coupon_api f2 \<and> is_eq_coupon_api e" by auto

    then obtain f1l f1r f2l f2r el er where
          "get_coupon_lhs f1 = Some f1l
        \<and> get_coupon_rhs f1 = Some f1r
        \<and> get_coupon_lhs f2 = Some f2l
        \<and> get_coupon_rhs f2 = Some f2r
        \<and> get_coupon_lhs e = Some el
        \<and> get_coupon_rhs e = Some er"
      by (metis is_coupon_lhs is_coupon_rhs is_force_coupon_api_def is_eq_coupon_api_def)

    then show ?thesis
      using "1" assms by auto
  qed
qed

lemma plus_71:
"n + 71 =  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 
(Suc (Suc (Suc (Suc (Suc (Suc (Suc(Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
  by auto

lemma make_thunk_coupon_raw_run_iter:
  assumes "make_thunk_coupon_raw coupons l r = Some res"
  shows  "run_iter (n + 71)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_thunk_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  obtain f1 f2 e xs f1l f1r f2l f2r el er where 
         1: "(coupons = f1 # f2 # e # xs
        \<and> is_force_coupon_api f1
        \<and> is_force_coupon_api f2
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs f1 = Some f1l
        \<and> get_coupon_rhs f1 = Some f1r
        \<and> get_coupon_lhs f2 = Some f2l
        \<and> get_coupon_rhs f2 = Some f2r
        \<and> get_coupon_lhs e = Some el
        \<and> get_coupon_rhs e = Some er
        \<and> is_equal f1r el
        \<and> is_equal f2r er
        \<and> is_equal f1l l
        \<and> is_equal f2l r
        \<and> res = (create_eq_coupon l r))" 
    using mt_some[OF assms] by auto

  let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  show ?thesis
    using 1 
          fixpoint_is_force_coupon_impl[of ?state]
          fixpoint_is_eq_coupon_impl[of ?state]
          fixpoint_get_coupon_lhs_impl[of ?state]
          fixpoint_get_coupon_rhs_impl[of ?state]
          fixpoint_is_equal_impl[of ?state]
          fixpoint_create_eq_coupon_impl[of ?state]
    apply (invoke_coupon_func fuel_idx_def: plus_71 func_make_thunk_coupon_idx_def)
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
     apply (if_block)
     apply (call_api_func)
     apply (if_block)
     apply (call_api_func)
     apply (if_block)
     apply (call_api_func)
     done
qed

lemma make_thunk_coupon_raw_run_invoke_none:
  assumes "make_thunk_coupon_raw coupons l r = None"
  shows "\<exists>msg cfg.
          run_iter (n + 71)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_thunk_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
        = (cfg, RTrap msg)"
proof -
  let ?A = "length coupons < 3"
  let ?B = "(\<exists>f1 f2 e xs. coupons = f1 # f2 # e # xs \<and>
          (\<not>is_force_coupon_api f1 \<or> \<not>is_force_coupon_api f2 \<or> \<not> is_eq_coupon_api e))"
  let ?C = "(\<exists>f1 f2 e xs f1l f1r f2l f2r el er.
          coupons = f1 # f2 # e # xs
        \<and> is_force_coupon_api f1
        \<and> is_force_coupon_api f2
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs f1 = Some f1l
        \<and> get_coupon_rhs f1 = Some f1r
        \<and> get_coupon_lhs f2 = Some f2l
        \<and> get_coupon_rhs f2 = Some f2r
        \<and> get_coupon_lhs e = Some el
        \<and> get_coupon_rhs e = Some er
        \<and> (\<not>is_equal f1r el \<or> \<not>is_equal f2r er \<or> \<not>is_equal f1l l \<or> \<not>is_equal f2l r))"

  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  have assms: "?A \<or> ?B \<or> ?C" using mt_none[OF assms] by blast

  show ?thesis
    using assms
  proof
    assume "?A"
    then have "\<not> 2 < length coupons"
      by simp
    then have "\<not> nat_of_int (I32.lift0 2) < length coupons"
      by (simp add: nat_of_int_i32.abs_eq)

    then show ?thesis
      apply (invoke_coupon_func fuel_idx_def: plus_71  func_make_thunk_coupon_idx_def)
      apply (table_get_local_set)
      done
  next
    assume "?B \<or> ?C"
    then show ?thesis
    proof
      assume "?B"

      then obtain f1 f2 e xs where "coupons = f1 # f2 # e # xs \<and>
          (\<not>is_force_coupon_api f1 \<or> \<not>is_force_coupon_api f2 \<or> \<not> is_eq_coupon_api e)"
        by auto

      then show ?thesis
        using fixpoint_is_force_coupon_impl[of ?state]
              fixpoint_is_eq_coupon_impl[of ?state]
        apply (invoke_coupon_func fuel_idx_def: plus_71  func_make_thunk_coupon_idx_def)
        apply (table_get_local_set)
        apply (call_api_func)
        apply (if_block)
        apply (call_api_func)
        apply (if_block)
        apply (call_api_func)
        apply (if_block)
        done
  next
    assume "?C"

    then obtain f1 f2 e xs f1l f1r f2l f2r el er where
          1: "coupons = f1 # f2 # e # xs
        \<and> is_force_coupon_api f1
        \<and> is_force_coupon_api f2
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs f1 = Some f1l
        \<and> get_coupon_rhs f1 = Some f1r
        \<and> get_coupon_lhs f2 = Some f2l
        \<and> get_coupon_rhs f2 = Some f2r
        \<and> get_coupon_lhs e = Some el
        \<and> get_coupon_rhs e = Some er"
        and 2: "(\<not>is_equal f1r el \<or> \<not>is_equal f2r er \<or> \<not>is_equal f1l l \<or> \<not>is_equal f2l r)"
      by auto

    show ?thesis
      using 1 2
            fixpoint_is_force_coupon_impl[of ?state]
            fixpoint_is_eq_coupon_impl[of ?state]
            fixpoint_get_coupon_lhs_impl[of ?state]
            fixpoint_get_coupon_rhs_impl[of ?state]
            fixpoint_is_equal_impl[of ?state]
   apply (invoke_coupon_func fuel_idx_def: plus_71 func_make_thunk_coupon_idx_def)
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
        apply (if_block)
        apply (call_api_func)
        apply (if_block)
        apply (call_api_func)
        apply (if_block)
        done
    qed
  qed
qed

end