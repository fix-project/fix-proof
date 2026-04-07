theory thunktree_coupon
  imports custom_method isabelle_coupon
begin

lemma make_some:
  assumes "make_thunktree_coupon_raw coupons l r = Some res"
  shows "(\<exists>e xs l' r' l'' r''.
          coupons = e # xs
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs e = Some l'
        \<and> get_coupon_rhs e = Some r'
        \<and> create_thunk_api l' = Some l''
        \<and> create_thunk_api r' = Some r''
        \<and> is_equal l l''
        \<and> is_equal r r''
        \<and> res = create_eq_coupon l r)"
proof -
  obtain e xs where
       1: "coupons = e # xs
         \<and> is_eq_coupon_api e"
    by (metis assms  make_thunktree_coupon_raw.elims option.simps(3))
  then obtain l' r' where
       2: "get_coupon_lhs e = Some l'"
   and 3: "get_coupon_rhs e = Some r'"
    by (metis is_eq_coupon_api_def is_coupon_lhs is_coupon_rhs)

  have "make_thunktree_coupon_raw coupons l r =
    (case (create_thunk_api l', create_thunk_api r') of
           (Some l'', Some r'') \<Rightarrow> 
           (if (is_equal l l'' \<and> is_equal r r'') then Some(create_eq_coupon l r) else None)
          | _ \<Rightarrow> None)"
    by (simp add: 1 2 3)
  then obtain l'' r'' where
       4: "create_thunk_api l' = Some l''"
   and 5: "create_thunk_api r' = Some r''"
    by (metis (no_types, lifting) assms case_prod_conv option.exhaust option.simps(4,5))
  then have "make_thunktree_coupon_raw coupons l r = 
           (if (is_equal l l'' \<and> is_equal r r'') then Some(create_eq_coupon l r) else None)"
    by (simp add: 1 2 3 4 5)

  then show ?thesis
    by (metis (no_types, lifting) "1" "2" "3" "4" "5" assms handy_if_lemma)
qed

lemma make_some_rev: 
  assumes "(\<exists>e xs l' r' l'' r''.
          coupons = e # xs
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs e = Some l'
        \<and> get_coupon_rhs e = Some r'
        \<and> create_thunk_api l' = Some l''
        \<and> create_thunk_api r' = Some r''
        \<and> is_equal l l''
        \<and> is_equal r r'')"
  shows "make_thunktree_coupon_raw coupons l r = Some (create_eq_coupon l r)"
  using assms by fastforce

lemma make_none:
  assumes "make_thunktree_coupon_raw coupons l r = None"
  shows "(coupons = [] \<or>
         (\<exists>e xs. coupons = e # xs \<and> \<not>is_eq_coupon_api e) \<or>
         (\<exists>e xs l' r'. coupons = e # xs
                     \<and> is_eq_coupon_api e
                     \<and> get_coupon_lhs e = Some l'
                     \<and> get_coupon_rhs e = Some r'
                     \<and> create_thunk_api l' = None) \<or>
         (\<exists>e xs l' r' l''. coupons = e # xs
                     \<and> is_eq_coupon_api e
                     \<and> get_coupon_lhs e = Some l'
                     \<and> get_coupon_rhs e = Some r'
                     \<and> create_thunk_api l' = l'' 
                     \<and> create_thunk_api r' = None) \<or>
         (\<exists>e xs l' r' l'' r''.
                   coupons = e # xs
                 \<and> is_eq_coupon_api e
                 \<and> get_coupon_lhs e = Some l'
                 \<and> get_coupon_rhs e = Some r'
                 \<and> create_thunk_api l' = Some l''
                 \<and> create_thunk_api r' = Some r''
                 \<and> (\<not>is_equal l l'' \<or> \<not>is_equal r r'')))"
proof (cases "coupons = []")
  case True then show ?thesis by auto
next
  case False
  then obtain e xs where 1: "coupons = e # xs" using list.exhaust_sel by blast

  then show ?thesis
  proof (cases "\<not>is_eq_coupon_api e")
    case True then show ?thesis using 1 by auto
  next
    case False
    then obtain l' r' where 2: "get_coupon_lhs e = Some l' \<and> get_coupon_rhs e = Some r'"
      by (metis is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def)

    show ?thesis
      by (metis "1" "2" assms make_some_rev not_Some_eq)
  qed
qed

lemma plus_37:
"n + 37 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc 
(Suc (Suc (Suc (Suc (Suc (Suc (Suc(Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))))))))"
  by auto

lemma make_thunktree_coupon_raw_run_iter:
  assumes "make_thunktree_coupon_raw coupons l r = Some res"
  shows  "run_iter (n + 37)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_thunktree_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  obtain e xs l' r' l'' r'' where
          1: "coupons = e # xs
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs e = Some l'
        \<and> get_coupon_rhs e = Some r'
        \<and> create_thunk_api l' = Some l''
        \<and> create_thunk_api r' = Some r''
        \<and> is_equal l l''
        \<and> is_equal r r''
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
    fixpoint_create_thunk_impl[of ?state]

    apply (invoke_coupon_func fuel_idx_def: plus_37 func_make_thunktree_coupon_idx_def)
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

lemma make_thunktree_coupon_raw_run_invoke_none:
  assumes "make_thunktree_coupon_raw coupons l r = None"
  shows "\<exists>msg cfg.
          run_iter (n + 37)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_thunktree_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
        = (cfg, RTrap msg)"
proof -
  let ?A = "coupons = []"
  let ?B = "(\<exists>e xs. coupons = e # xs \<and> \<not>is_eq_coupon_api e)" 
  let ?C = "(\<exists>e xs l' r'. coupons = e # xs
                     \<and> is_eq_coupon_api e
                     \<and> get_coupon_lhs e = Some l'
                     \<and> get_coupon_rhs e = Some r'
                     \<and> create_thunk_api l' = None)"
  let ?D = "(\<exists>e xs l' r' l''. coupons = e # xs
                     \<and> is_eq_coupon_api e
                     \<and> get_coupon_lhs e = Some l'
                     \<and> get_coupon_rhs e = Some r'
                     \<and> create_thunk_api l' = Some l''
                     \<and> create_thunk_api r' = None)"
  let ?E = "(\<exists>e xs l' r' l'' r''.
                   coupons = e # xs
                 \<and> is_eq_coupon_api e
                 \<and> get_coupon_lhs e = Some l'
                 \<and> get_coupon_rhs e = Some r'
                 \<and> create_thunk_api l' = Some l''
                 \<and> create_thunk_api r' = Some r''
                 \<and> (\<not>is_equal l l'' \<or> \<not>is_equal r r''))"

  have assms: "?A \<or> ?B \<or> ?C \<or> ?D \<or> ?E" using make_none[OF assms] by auto

  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  show ?thesis
    using assms
  proof
    assume ?A
    then show ?thesis
      by (invoke_coupon_func fuel_idx_def: plus_37 func_make_thunktree_coupon_idx_def, table_get_local_set)
  next
    assume "?B \<or> ?C \<or> ?D \<or> ?E"
    then show ?thesis
    proof
      assume ?B
      then obtain e xs where "coupons = e # xs \<and> (\<not>is_eq_coupon_api e)" by auto
      then show ?thesis
        using fixpoint_is_eq_coupon_impl[of ?state]
        by (invoke_coupon_func fuel_idx_def: plus_37 func_make_thunktree_coupon_idx_def, table_get_local_set, call_api_func, if_block)
    next
      assume "?C \<or> ?D \<or> ?E"
      then show ?thesis
      proof
        assume ?C
        then obtain e xs l' r' where
          "coupons = e # xs
          \<and> is_eq_coupon_api e
          \<and> get_coupon_lhs e = Some l'
          \<and> get_coupon_rhs e = Some r'
          \<and> create_thunk_api l' = None"
          by auto

        then show ?thesis
          using fixpoint_is_eq_coupon_impl[of ?state]
                fixpoint_get_coupon_lhs_impl[of ?state]
                fixpoint_get_coupon_rhs_impl[of ?state]
                fixpoint_create_thunk_impl[of ?state]
          by (invoke_coupon_func fuel_idx_def: plus_37 func_make_thunktree_coupon_idx_def, table_get_local_set, call_api_func, if_block, call_api_func)
      next
        assume "?D \<or> ?E"
        then show ?thesis
        proof
          assume ?D
          then obtain e xs l' r' l'' where
            "coupons = e # xs
            \<and> is_eq_coupon_api e
            \<and> get_coupon_lhs e = Some l'
            \<and> get_coupon_rhs e = Some r'
            \<and> create_thunk_api l' = Some l''
            \<and> create_thunk_api r' = None"
            by auto

          then show ?thesis
            using fixpoint_is_eq_coupon_impl[of ?state]
                  fixpoint_get_coupon_lhs_impl[of ?state]
                  fixpoint_get_coupon_rhs_impl[of ?state]
                  fixpoint_create_thunk_impl[of ?state]
                  fixpoint_is_equal_impl[of ?state]
            apply (invoke_coupon_func fuel_idx_def: plus_37 func_make_thunktree_coupon_idx_def)
            apply (table_get_local_set)
            apply (call_api_func)
            apply (if_block)
            apply (call_api_func)
            apply (if_block)
            apply (call_api_func)
            done
        next
          assume ?E
          then obtain e xs l' r' l'' r'' where
                   "coupons = e # xs
                 \<and> is_eq_coupon_api e
                 \<and> get_coupon_lhs e = Some l'
                 \<and> get_coupon_rhs e = Some r'
                 \<and> create_thunk_api l' = Some l''
                 \<and> create_thunk_api r' = Some r''
                 \<and> (\<not>is_equal l l'' \<or> \<not>is_equal r r'')"
            by auto

          then show ?thesis
            using fixpoint_is_eq_coupon_impl[of ?state]
                  fixpoint_get_coupon_lhs_impl[of ?state]
                  fixpoint_get_coupon_rhs_impl[of ?state]
                  fixpoint_create_thunk_impl[of ?state]
                  fixpoint_is_equal_impl[of ?state]
            apply (invoke_coupon_func fuel_idx_def: plus_37 func_make_thunktree_coupon_idx_def)
            apply (table_get_local_set)
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