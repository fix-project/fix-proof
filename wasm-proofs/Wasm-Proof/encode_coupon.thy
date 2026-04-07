theory encode_coupon
  imports custom_method isabelle_coupon
begin

lemma make_some:
  assumes "make_encode_coupon_raw coupons l r = Some res"
  shows "(\<exists>e xs l' r' l'' r''.
          coupons = e # xs
        \<and> is_eq_coupon_api e
        \<and> get_coupon_lhs e = Some l'
        \<and> get_coupon_rhs e = Some r'
        \<and> create_encode_api l' = Some l''
        \<and> create_encode_api r' = Some r''
        \<and> is_equal l l''
        \<and> is_equal r r''
        \<and> res = create_eq_coupon l r)"
proof -
  obtain e xs where 1: "coupons = e # xs \<and> is_eq_coupon_api e"
    by (metis assms make_encode_coupon_raw.elims option.simps(3))
  then obtain l' r' where 2: "get_coupon_lhs e = Some l'" and 3: "get_coupon_rhs e = Some r'"
    by (metis is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def)

  have "make_encode_coupon_raw coupons l r =
       (case (create_encode_api l', create_encode_api r') of
         (Some l'', Some r'') \<Rightarrow>
           (if (is_equal l l'' \<and> is_equal r r'') then Some (create_eq_coupon l r) else None)
        | _ \<Rightarrow> None)"
    by (simp add: 1 2 3)
  then obtain l'' r'' where 4: "create_encode_api l' = Some l''" and 5: "create_encode_api r' = Some r''"
    by (metis (no_types, lifting) assms case_prod_conv option.exhaust option.simps(4,5))

  have "make_encode_coupon_raw coupons l r = 
        (if (is_equal l l'' \<and> is_equal r r'') then Some (create_eq_coupon l r) else None)"
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
        \<and> create_encode_api l' = Some l''
        \<and> create_encode_api r' = Some r''
        \<and> is_equal l l''
        \<and> is_equal r r'')"
  shows"make_encode_coupon_raw coupons l r = Some (create_eq_coupon l r)"
  using assms by fastforce

term " (\<exists>l'' r''.
                create_encode_api l' = Some l'' \<and>
                create_encode_api r' = Some r'' \<and>
                (\<not>is_equal l l'' \<or> \<not>is_equal r r''))"

lemma make_none:
  assumes "make_encode_coupon_raw coupons l r = None"
  shows "coupons = [] \<or>
         (\<exists>e xs. coupons = e # xs \<and>
          (\<not>is_eq_coupon_api e \<or>
           (\<exists>l' r'. 
             is_eq_coupon_api e \<and>
             get_coupon_lhs e = Some l' \<and>
             get_coupon_rhs e = Some r' \<and>
             ((create_encode_api l' = None \<or>
              (\<exists>l''. create_encode_api l' = Some l'' \<and>
               ((create_encode_api r' = None \<or>
               (\<exists>r''. create_encode_api r' = Some r'' \<and>
                (\<not>is_equal l l'' \<or> \<not>is_equal r r''))))))))))"
proof (cases "coupons = []")
  case True then show ?thesis by auto
next
  case False
  then obtain e xs where 1: "coupons = e # xs" using list.exhaust_sel by blast

  then show ?thesis
  proof (cases "\<not>is_eq_coupon_api e")
    case True then show ?thesis using 1 by auto
  next
    case False then obtain l' r' where 2: "get_coupon_lhs e = Some l' \<and> get_coupon_rhs e = Some r'"
      by (metis is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def)

    show ?thesis
      using 1 2 assms by fastforce
  qed
qed

lemma plus_37:
"n + 37 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc 
(Suc (Suc (Suc (Suc (Suc (Suc (Suc(Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))))))))"
  by auto

lemma make_encode_coupon_raw_run_iter:
  assumes "make_encode_coupon_raw coupons l r = Some res"
  shows "run_iter (n + 37)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_encode_coupon_idx]
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
        \<and> create_encode_api l' = Some l''
        \<and> create_encode_api r' = Some r''
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
    fixpoint_create_encode_impl[of ?state]
    apply (invoke_coupon_func fuel_idx_def: plus_37 func_make_encode_coupon_idx_def)
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

lemma make_encode_coupon_raw_run_invoke_none:
  assumes "make_encode_coupon_raw coupons l r = None"
  shows "\<exists>msg cfg.
          run_iter (n + 37)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_encode_coupon_idx]
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
    fixpoint_create_encode_impl[of ?state]
    apply (invoke_coupon_func fuel_idx_def: plus_37 func_make_encode_coupon_idx_def)
    apply (table_get_local_set)
    (* split on coupon = [] *)
    apply (erule disjE, simp)

    apply (erule exE, erule conjE, erule exE)
    apply (call_api_func)
    apply (if_block)

    apply (intro impI, erule impE, assumption)
    apply (erule exE)
    apply (erule conjE)
    apply (erule exE)
    apply (erule conjE)

    apply (erule disjE)
    apply (call_api_func)
    apply (erule exE, erule conjE)

    apply (erule disjE)
    apply (call_api_func)
    apply (if_block)
    apply (call_api_func)

    apply (erule exE, erule conjE)
    apply (call_api_func)
    apply (if_block)
    apply (call_api_func)
    apply (if_block)
    apply (auto)
    done
qed

end