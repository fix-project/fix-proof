theory sym_coupon
  imports custom_method isabelle_coupon
begin

lemma make_some:
  assumes "make_sym_coupon_raw coupons l r = Some res"
  shows "\<exists>e xs l' r'.
         coupons = (e # xs)
      \<and>  is_eq_coupon_api e
      \<and>  get_coupon_lhs e = Some l'
      \<and>  get_coupon_rhs e = Some r'
      \<and>  is_equal r' l
      \<and>  is_equal l' r
      \<and>  res = create_eq_coupon l r"
proof -
  obtain e xs l' r' where
    1: "coupons = (e # xs)
      \<and>  is_eq_coupon_api e
      \<and>  get_coupon_lhs e = Some l'
      \<and>  get_coupon_rhs e = Some r'"
    by (metis assms is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def make_sym_coupon_raw.elims option.simps(3))

  then have "make_sym_coupon_raw coupons l r =
        (if (is_equal r' l \<and> is_equal l' r) then Some (create_eq_coupon l r) else None)"
    by simp

  then show ?thesis 
    by (metis "1" assms option.inject option.simps(3))
qed

lemma make_some_rev:
  assumes "\<exists>e xs l' r'.
         coupons = (e # xs)
      \<and>  is_eq_coupon_api e
      \<and>  get_coupon_lhs e = Some l'
      \<and>  get_coupon_rhs e = Some r'
      \<and>  is_equal r' l
      \<and>  is_equal l' r"
  shows "make_sym_coupon_raw coupons l r = Some (create_eq_coupon l r)"
  using assms by fastforce

lemma make_none:
  assumes "make_sym_coupon_raw coupons l r = None"
  shows "coupons = [] \<or>
        (\<exists>e xs. coupons = e # xs \<and>
          (\<not>is_eq_coupon_api e \<or>
           (\<exists>l' r'.
            is_eq_coupon_api e \<and>
            get_coupon_lhs e = Some l' \<and>
            get_coupon_rhs e = Some r' \<and>
            (\<not>is_equal r' l \<or> \<not>is_equal l' r))))"
proof (cases "coupons = []")
  case True then show ?thesis by auto
next
  case False
  then obtain e xs where 1: "coupons = e # xs"
    by (meson list.exhaust)
  then show ?thesis
  proof (cases "is_eq_coupon_api e")
    case False
    then show ?thesis using 1 by auto
  next
    case True
    then obtain l' r' where "get_coupon_lhs e = Some l' \<and> get_coupon_rhs e = Some r'"
      by (meson is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def)
    then show ?thesis
      using "1" assms by force
  qed
qed

lemma plus_33:
"n + 33 = (Suc (Suc (Suc 
(Suc (Suc (Suc (Suc (Suc (Suc (Suc(Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))))"
  by auto

lemma make_sym_coupon_raw_run_iter:
  assumes "make_sym_coupon_raw coupons l r = Some res"
  shows "run_iter (n + 33)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_sym_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  obtain e xs l' r' where
       1: "coupons = (e # xs)
      \<and>  is_eq_coupon_api e
      \<and>  get_coupon_lhs e = Some l'
      \<and>  get_coupon_rhs e = Some r'
      \<and>  is_equal r' l
      \<and>  is_equal l' r
      \<and>  res = create_eq_coupon l r"
    using make_some[OF assms] by auto

    let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

    show ?thesis
      using 1
        fixpoint_is_eq_coupon_impl[of ?state]
        fixpoint_get_coupon_lhs_impl[of ?state]
        fixpoint_get_coupon_rhs_impl[of ?state] 
        fixpoint_is_equal_impl[of ?state]
        fixpoint_create_eq_coupon_impl[of ?state]
      apply (invoke_coupon_func fuel_idx_def: plus_33 func_make_sym_coupon_idx_def)
      apply (table_get_local_set)
      apply (call_api_func)
      apply (if_block)
      apply (call_api_func)
      apply (if_block)
      apply (call_api_func)
      apply (if_block)
      apply (call_api_func)
      done
qed

lemma make_sym_coupon_raw_run_invoke_none:
  assumes "make_sym_coupon_raw coupons l r = None"
  shows "\<exists>msg cfg.
          run_iter (n + 33)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_sym_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
        = (cfg, RTrap msg)" 
proof -
  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  show ?thesis
    using make_none[OF assms]
      fixpoint_is_eq_coupon_impl[of ?state]
      fixpoint_get_coupon_lhs_impl[of ?state]
      fixpoint_get_coupon_rhs_impl[of ?state]
      fixpoint_is_equal_impl[of ?state]
    apply (invoke_coupon_func fuel_idx_def: plus_33 func_make_sym_coupon_idx_def)
    apply (table_get_local_set)
    (* coupons = [] *) apply (erule disjE, simp)
    (* coupons = e # xs*) apply (erule exE, erule conjE, erule exE)

    apply (call_api_func, if_block)
    (* is_eq_coupon_api e *) apply (intro impI, erule impE, assumption)
    (* get_coupon_lhs e = l' \<and> get_coupon_rhs e = r'*) apply(erule exE, erule conjE, erule exE, erule conjE)
    apply (call_api_func, if_block)
    apply (call_api_func, if_block)
    done
qed

end