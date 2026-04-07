theory trans_coupon
  imports custom_method isabelle_coupon
begin

lemma make_some:
  assumes "make_trans_coupon_raw coupons l r = Some res"
  shows "\<exists>e1 e2 xs e1l e1r e2l e2r.
         coupons = (e1 # e2 # xs)
       \<and> is_eq_coupon_api e1
       \<and> is_eq_coupon_api e2
       \<and> get_coupon_lhs e1 = Some e1l
       \<and> get_coupon_rhs e1 = Some e1r
       \<and> get_coupon_lhs e2 = Some e2l
       \<and> get_coupon_rhs e2 = Some e2r
       \<and> is_equal e1r e2l
       \<and> is_equal l e1l
       \<and> is_equal r e2r
       \<and> res = create_eq_coupon l r"
proof -
  obtain e1 e2 xs e1l e1r e2l e2r where
    1:  "coupons = (e1 # e2 # xs)
       \<and> is_eq_coupon_api e1
       \<and> is_eq_coupon_api e2
       \<and> get_coupon_lhs e1 = Some e1l
       \<and> get_coupon_rhs e1 = Some e1r
       \<and> get_coupon_lhs e2 = Some e2l
       \<and> get_coupon_rhs e2 = Some e2r"
  by (metis assms is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def make_trans_coupon_raw.elims option.simps(3))

  then have "make_trans_coupon_raw coupons l r = (if (is_equal e1r e2l \<and> is_equal l e1l \<and> is_equal r e2r) then Some (create_eq_coupon l r) else None)"
    by simp

  then show ?thesis by (metis "1" assms option.inject option.simps(3))
qed

lemma make_some_rev:
  assumes "\<exists>e1 e2 xs e1l e1r e2l e2r.
         coupons = (e1 # e2 # xs)
       \<and> is_eq_coupon_api e1
       \<and> is_eq_coupon_api e2
       \<and> get_coupon_lhs e1 = Some e1l
       \<and> get_coupon_rhs e1 = Some e1r
       \<and> get_coupon_lhs e2 = Some e2l
       \<and> get_coupon_rhs e2 = Some e2r
       \<and> is_equal e1r e2l
       \<and> is_equal l e1l
       \<and> is_equal r e2r"
  shows "make_trans_coupon_raw coupons l r = Some (create_eq_coupon l r)"
  using assms by fastforce

lemma make_none:
  assumes "make_trans_coupon_raw coupons l r = None"
  shows "length coupons < 2 \<or>
        (\<exists>e1 e2 xs.
         coupons = e1 # e2 # xs \<and>
         ((\<not> is_eq_coupon_api e1 \<or> \<not>is_eq_coupon_api e2) \<or>
          (is_eq_coupon_api e1 \<and> is_eq_coupon_api e2 \<and>
          (\<exists>e1l e1r e2l e2r.
           get_coupon_lhs e1 = Some e1l
         \<and> get_coupon_rhs e1 = Some e1r
         \<and> get_coupon_lhs e2 = Some e2l
         \<and> get_coupon_rhs e2 = Some e2r
         \<and> (\<not>is_equal e1r e2l \<or> \<not>is_equal l e1l \<or> \<not>is_equal r e2r)))))"
proof (cases "length coupons < 2")
  case True then show ?thesis by auto
next
  case False
  then obtain e1 e2 xs where 1: "coupons = e1 # e2 # xs" 
    using list_length_2[of coupons] by auto
  then show ?thesis
  proof (cases "\<not> (is_eq_coupon_api e1 \<and> is_eq_coupon_api e2)")
    case True then show ?thesis using 1 by auto
  next
    case False
    then obtain e1l e1r e2l e2r where 
          "get_coupon_lhs e1 = Some e1l
         \<and> get_coupon_rhs e1 = Some e1r
         \<and> get_coupon_lhs e2 = Some e2l
         \<and> get_coupon_rhs e2 = Some e2r"
      using is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def
      by meson
    then show ?thesis
      using "1" assms by force
  qed
qed

lemma plus_52:
"n + 52 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 
(Suc (Suc (Suc (Suc (Suc (Suc (Suc(Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))))))))))))))))))))))))))))))))))))))))))))))))"
  by auto

lemma make_trans_coupon_raw_run_iter:
  assumes "make_trans_coupon_raw coupons l r = Some res"
  shows "run_iter (n + 52)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_trans_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  obtain e1 e2 xs e1l e1r e2l e2r where
     1: "coupons = (e1 # e2 # xs)
       \<and> is_eq_coupon_api e1
       \<and> is_eq_coupon_api e2
       \<and> get_coupon_lhs e1 = Some e1l
       \<and> get_coupon_rhs e1 = Some e1r
       \<and> get_coupon_lhs e2 = Some e2l
       \<and> get_coupon_rhs e2 = Some e2r
       \<and> is_equal e1r e2l
       \<and> is_equal l e1l
       \<and> is_equal r e2r
       \<and> res = create_eq_coupon l r"
    using make_some[OF assms] by auto

  let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  show ?thesis
    using 1
    fixpoint_is_eq_coupon_impl[of ?state]
    fixpoint_get_coupon_lhs_impl[of ?state]
    fixpoint_get_coupon_rhs_impl[of ?state]
    fixpoint_is_equal_impl[of ?state]
    fixpoint_create_eq_coupon_impl[of ?state]
    apply (invoke_coupon_func fuel_idx_def: plus_52 func_make_trans_coupon_idx_def)
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
    done
qed

lemma make_trans_coupon_raw_run_invoke_none:
  assumes "make_trans_coupon_raw coupons l r = None"
  shows "\<exists>msg cfg.
          run_iter (n + 52)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_trans_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
        = (cfg, RTrap msg)" 
proof -
  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  have "length coupons < 2 \<longrightarrow> \<not> 1 < length coupons" by auto
  then have 1: "length coupons < 2 \<longrightarrow> \<not> nat_of_int (I32.lift0 1) < length coupons"
    using nat_of_int_i32.abs_eq by fastforce

  show ?thesis
    using make_none[OF assms]
    fixpoint_is_eq_coupon_impl[of ?state]
    fixpoint_get_coupon_lhs_impl[of ?state]
    fixpoint_get_coupon_rhs_impl[of ?state]
    fixpoint_is_equal_impl[of ?state]
    1

    apply (invoke_coupon_func fuel_idx_def: plus_52 func_make_trans_coupon_idx_def)
    apply (table_get_local_set)
    apply (erule disjE, simp)

    apply (erule exE, erule exE, erule conjE, erule exE)
    apply (call_api_func, if_block)
    apply (call_api_func, if_block)

    apply (intro impI, erule impE, assumption)
    apply (erule impE, assumption)

    apply (erule exE, erule conjE, erule exE, erule conjE, erule exE, erule conjE, erule exE, erule conjE)

    apply (call_api_func, if_block)
    apply (call_api_func, if_block)
    apply (call_api_func, if_block)
    done
qed

end
