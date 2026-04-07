theory thunkforce_coupon
  imports custom_method isabelle_coupon
begin

lemma make_some:
  assumes "make_thunkforce_coupon_raw coupons l r = Some res"
  shows "\<exists>e f1 f2 xs el er f1l f1r f2l f2r.
         coupons = e # f1 # f2 # xs
       \<and> is_eq_coupon_api e
       \<and> is_force_coupon_api f1
       \<and> is_force_coupon_api f2
       \<and> get_coupon_lhs e = Some el
       \<and> get_coupon_rhs e = Some er
       \<and> get_coupon_lhs f1 = Some f1l
       \<and> get_coupon_rhs f1 = Some f1r
       \<and> get_coupon_lhs f2 = Some f2l
       \<and> get_coupon_rhs f2 = Some f2r
       \<and> is_equal f1l el
       \<and> is_equal f2l er
       \<and> is_equal f1r l
       \<and> is_equal f2r r
       \<and> res = create_eq_coupon l r"
proof -
 obtain e f1 f2 xs el er f1l f1r f2l f2r where
         1: "coupons = e # f1 # f2 # xs
       \<and> is_eq_coupon_api e
       \<and> is_force_coupon_api f1
       \<and> is_force_coupon_api f2
       \<and> get_coupon_lhs e = Some el
       \<and> get_coupon_rhs e = Some er
       \<and> get_coupon_lhs f1 = Some f1l
       \<and> get_coupon_rhs f1 = Some f1r
       \<and> get_coupon_lhs f2 = Some f2l
       \<and> get_coupon_rhs f2 = Some f2r"
  by (metis assms is_coupon_lhs is_coupon_rhs is_force_coupon_api_def is_eq_coupon_api_def make_thunkforce_coupon_raw.elims option.simps(3))

  then have "make_thunkforce_coupon_raw coupons l r = (if (is_equal f1l el \<and> is_equal f2l er \<and> is_equal f1r l \<and> is_equal f2r r) then Some (create_eq_coupon l r) else None)"
    by simp
  then show ?thesis
    by (metis "1" assms option.inject option.simps(3))
qed

lemma make_some_rev:
  assumes "\<exists>e f1 f2 xs el er f1l f1r f2l f2r.
         coupons = e # f1 # f2 # xs
       \<and> is_eq_coupon_api e
       \<and> is_force_coupon_api f1
       \<and> is_force_coupon_api f2
       \<and> get_coupon_lhs e = Some el
       \<and> get_coupon_rhs e = Some er
       \<and> get_coupon_lhs f1 = Some f1l
       \<and> get_coupon_rhs f1 = Some f1r
       \<and> get_coupon_lhs f2 = Some f2l
       \<and> get_coupon_rhs f2 = Some f2r
       \<and> is_equal f1l el
       \<and> is_equal f2l er
       \<and> is_equal f1r l
       \<and> is_equal f2r r
       \<and> res = create_eq_coupon l r"
  shows "make_thunkforce_coupon_raw coupons l r = Some res"
  using assms by fastforce

lemma make_none:
  assumes "make_thunkforce_coupon_raw coupons l r = None"
  shows "length coupons < 3 \<or>
        (\<exists>e f1 f2 xs. coupons = e # f1 # f2 # xs \<and> (\<not>is_eq_coupon_api e \<or> \<not>is_force_coupon_api f1 \<or> \<not>is_force_coupon_api f2)) \<or>
        (\<exists>e f1 f2 xs el er f1l f1r f2l f2r.
         coupons = e # f1 # f2 # xs
       \<and> is_eq_coupon_api e
       \<and> is_force_coupon_api f1
       \<and> is_force_coupon_api f2
       \<and> get_coupon_lhs e = Some el
       \<and> get_coupon_rhs e = Some er
       \<and> get_coupon_lhs f1 = Some f1l
       \<and> get_coupon_rhs f1 = Some f1r
       \<and> get_coupon_lhs f2 = Some f2l
       \<and> get_coupon_rhs f2 = Some f2r
       \<and> \<not>(is_equal f1l el
       \<and> is_equal f2l er
       \<and> is_equal f1r l
       \<and> is_equal f2r r))"
proof (cases "length coupons < 3")
  case True then show ?thesis by auto
next
  case False
  then obtain e f1 f2 xs where 1: "coupons = e # f1 # f2 # xs" using list_length_3 by blast

  then show ?thesis
  proof (cases "\<not>(is_eq_coupon_api e \<and> is_force_coupon_api f1 \<and> is_force_coupon_api f2)")
    case True then show ?thesis using 1 by auto
  next
    case False
    then obtain f1l f1r f2l f2r el er where
         "get_coupon_lhs e = Some el
       \<and> get_coupon_rhs e = Some er
       \<and> get_coupon_lhs f1 = Some f1l
       \<and> get_coupon_rhs f1 = Some f1r
       \<and> get_coupon_lhs f2 = Some f2l
       \<and> get_coupon_rhs f2 = Some f2r"
      by (metis is_coupon_lhs is_coupon_rhs is_force_coupon_api_def is_eq_coupon_api_def)

    then show ?thesis using "1" assms by auto
  qed
qed

lemma plus_71:
"n + 71 =  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 
(Suc (Suc (Suc (Suc (Suc (Suc (Suc(Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
  by auto

lemma make_thunkforce_coupon_raw_run_iter:
  assumes "make_thunkforce_coupon_raw coupons l r = Some res"
  shows  "run_iter (n + 71)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_thunkforce_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
 obtain e f1 f2 xs el er f1l f1r f2l f2r where
         1: "coupons = e # f1 # f2 # xs
       \<and> is_eq_coupon_api e
       \<and> is_force_coupon_api f1
       \<and> is_force_coupon_api f2
       \<and> get_coupon_lhs e = Some el
       \<and> get_coupon_rhs e = Some er
       \<and> get_coupon_lhs f1 = Some f1l
       \<and> get_coupon_rhs f1 = Some f1r
       \<and> get_coupon_lhs f2 = Some f2l
       \<and> get_coupon_rhs f2 = Some f2r
       \<and> is_equal f1l el
       \<and> is_equal f2l er
       \<and> is_equal f1r l
       \<and> is_equal f2r r
       \<and> res = create_eq_coupon l r"
   using make_some[OF assms] by auto

   let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

   show ?thesis
     using 1
     fixpoint_is_force_coupon_impl[of ?state]
     fixpoint_is_eq_coupon_impl[of ?state]
     fixpoint_get_coupon_lhs_impl[of ?state]
     fixpoint_get_coupon_rhs_impl[of ?state]
     fixpoint_is_equal_impl[of ?state]
     fixpoint_create_eq_coupon_impl[of ?state]
     apply (invoke_coupon_func fuel_idx_def: plus_71 func_make_thunkforce_coupon_idx_def)
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

lemma make_thunkforce_coupon_raw_run_invoke_none:
  assumes "make_thunkforce_coupon_raw coupons l r = None"
  shows "\<exists>msg cfg.
          run_iter (n + 71)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_thunkforce_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
        = (cfg, RTrap msg)"
proof -
  let ?A = "length coupons < 3"
  let ?B = "(\<exists>e f1 f2 xs. coupons = e # f1 # f2 # xs \<and> (\<not>is_eq_coupon_api e \<or> \<not>is_force_coupon_api f1 \<or> \<not>is_force_coupon_api f2))"
  let ?C = "(\<exists>e f1 f2 xs el er f1l f1r f2l f2r.
         coupons = e # f1 # f2 # xs
       \<and> is_eq_coupon_api e
       \<and> is_force_coupon_api f1
       \<and> is_force_coupon_api f2
       \<and> get_coupon_lhs e = Some el
       \<and> get_coupon_rhs e = Some er
       \<and> get_coupon_lhs f1 = Some f1l
       \<and> get_coupon_rhs f1 = Some f1r
       \<and> get_coupon_lhs f2 = Some f2l
       \<and> get_coupon_rhs f2 = Some f2r
       \<and> \<not>(is_equal f1l el
       \<and> is_equal f2l er
       \<and> is_equal f1r l
       \<and> is_equal f2r r))"

  have assms: "?A \<or> ?B \<or> ?C" using make_none[OF assms] by auto

  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  show ?thesis
    using assms
  proof
    assume "?A"
    then have "\<not> nat_of_int (I32.lift0 2) < length coupons"
      by (simp add: nat_of_int_i32.abs_eq)
    then show ?thesis
      apply (invoke_coupon_func fuel_idx_def: plus_71  func_make_thunkforce_coupon_idx_def)
      apply (table_get_local_set)
      done
  next
    assume "?B \<or> ?C"
    then show ?thesis
    proof
      assume "?B"
      then obtain f1 f2 e xs where "coupons = e # f1 # f2 # xs \<and> (\<not>is_eq_coupon_api e \<or> \<not>is_force_coupon_api f1 \<or> \<not>is_force_coupon_api f2)" by auto

      then show ?thesis
        using fixpoint_is_eq_coupon_impl[of ?state]
              fixpoint_is_force_coupon_impl[of ?state]
        apply (invoke_coupon_func fuel_idx_def: plus_71  func_make_thunkforce_coupon_idx_def)
        apply (table_get_local_set)
        apply (call_api_func)
        apply (if_block)
        apply (call_api_func)
        apply (if_block)
        apply (call_api_func)
        apply (if_block)
        done
    next
      assume ?C
      then obtain e f1 f2 xs el er f1l f1r f2l f2r where
         "coupons = e # f1 # f2 # xs
       \<and> is_eq_coupon_api e
       \<and> is_force_coupon_api f1
       \<and> is_force_coupon_api f2
       \<and> get_coupon_lhs e = Some el
       \<and> get_coupon_rhs e = Some er
       \<and> get_coupon_lhs f1 = Some f1l
       \<and> get_coupon_rhs f1 = Some f1r
       \<and> get_coupon_lhs f2 = Some f2l
       \<and> get_coupon_rhs f2 = Some f2r
       \<and> \<not>(is_equal f1l el
       \<and> is_equal f2l er
       \<and> is_equal f1r l
       \<and> is_equal f2r r)"
        by auto

      then show ?thesis
        using fixpoint_is_force_coupon_impl[of ?state]
              fixpoint_is_eq_coupon_impl[of ?state]
              fixpoint_get_coupon_lhs_impl[of ?state]
              fixpoint_get_coupon_rhs_impl[of ?state]
              fixpoint_is_equal_impl[of ?state]
              fixpoint_create_eq_coupon_impl[of ?state]
        apply (invoke_coupon_func fuel_idx_def: plus_71 func_make_thunkforce_coupon_idx_def)
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