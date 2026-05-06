theory think_application_coupon
  imports custom_method isabelle_coupon
begin

lemma make_some:
  assumes "make_think_application_coupon coupons l r = Some res"
  shows "\<exists>c1 c2 xs c1l c1r.
         coupons = c1 # c2 # xs
       \<and> is_eval_coupon c1
       \<and> is_apply_coupon c2
       \<and> get_coupon_lhs c1 = Some c1l
       \<and> get_coupon_rhs c1 = Some c1r
       \<and> get_coupon_lhs c2 = Some c1r
       \<and> get_coupon_rhs c2 = Some r
       \<and> create_application_thunk_api c1l = Some l
       \<and> res = create_coupon Think l r"
proof - 
  obtain c1 c2 xs where
       1: "coupons = c1 # c2 # xs \<and> is_eval_coupon c1 \<and> is_apply_coupon c2"
    using assms
    apply (cases coupons; simp_all; case_tac list; simp_all)
    by (meson option.distinct(1))

  then obtain c1l c1r c2l c2r where 2: "get_coupon_lhs c1 = Some c1l
        \<and> get_coupon_rhs c1 = Some c1r
        \<and> get_coupon_lhs c2 = Some c2l
        \<and> get_coupon_rhs c2 = Some c2r"
    using eval_lhs_exist eval_rhs_exist apply_lhs_exist apply_rhs_exist
    by presburger

  then show ?thesis
    using 1 2 assms
    apply simp
    apply (cases "c1r = c2l"; simp_all)
    apply (cases "create_application_thunk_api c1l"; simp_all)
    by (simp add: handy_if_lemma)
qed

lemma make_some_rev:
  assumes "\<exists>c1 c2 xs c1l c1r.
         coupons = c1 # c2 # xs
       \<and> is_eval_coupon c1
       \<and> is_apply_coupon c2
       \<and> get_coupon_lhs c1 = Some c1l
       \<and> get_coupon_rhs c1 = Some c1r
       \<and> get_coupon_lhs c2 = Some c1r
       \<and> get_coupon_rhs c2 = Some r
       \<and> create_application_thunk_api c1l = Some l"
  shows "make_think_application_coupon coupons l r = Some (create_coupon Think l r)"
  using assms by fastforce

lemma make_none:
  assumes "make_think_application_coupon coupons l r = None"
  shows "(length coupons < 2) \<or>
         (\<exists>c1 c2 xs. coupons = c1 # c2 # xs \<and>
          (\<not>is_eval_coupon c1 \<or> \<not>is_apply_coupon c2)) \<or>
         (\<exists>c1 c2 xs c1l c1r c2l c2r.
          coupons = c1 # c2 # xs
        \<and> is_eval_coupon c1
        \<and> is_apply_coupon c2
        \<and> get_coupon_lhs c1 = Some c1l
        \<and> get_coupon_rhs c1 = Some c1r
        \<and> get_coupon_lhs c2 = Some c2l
        \<and> get_coupon_rhs c2 = Some c2r
        \<and> (create_application_thunk_api c1l = None \<or>
           (\<exists>thunk. create_application_thunk_api c1l = Some thunk
             \<and> (\<not>is_equal c1r c2l 
             \<or> \<not>is_equal thunk l 
             \<or> \<not>is_equal c2r r)))
       )"
proof (cases "length coupons < 2")
  case True then show ?thesis by auto
next
  case False
  then obtain c1 c2 xs where 1 : "coupons = c1 # c2 # xs"
    using list_length_2 by blast
  then show ?thesis
  proof (cases "(\<not>is_eval_coupon c1 \<or> \<not>is_apply_coupon c2)")
    case True then show ?thesis using 1 by blast
  next
    case False
    then obtain c1l c1r c2l c2r where
         "get_coupon_lhs c1 = Some c1l
        \<and> get_coupon_rhs c1 = Some c1r
        \<and> get_coupon_lhs c2 = Some c2l
        \<and> get_coupon_rhs c2 = Some c2r"
      using eval_lhs_exist eval_rhs_exist apply_lhs_exist apply_rhs_exist
      by presburger

    then show ?thesis
      using 1 assms
      by fastforce
  qed
qed

lemma plus_54:
"n + 54 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 
(Suc (Suc (Suc (Suc (Suc (Suc (Suc(Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))))))))))))))))))))))))))))))))))))))))))))))))))"
  by auto

lemma make_think_application_coupon_run_iter:
  assumes "make_think_application_coupon coupons l r = Some res"
  shows  "run_iter (n + 54)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_think_application_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref res)) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  obtain c1 c2 xs c1l c1r where
         1: "coupons = c1 # c2 # xs
       \<and> is_eval_coupon c1
       \<and> is_apply_coupon c2
       \<and> get_coupon_lhs c1 = Some c1l
       \<and> get_coupon_rhs c1 = Some c1r
       \<and> get_coupon_lhs c2 = Some c1r
       \<and> get_coupon_rhs c2 = Some r
       \<and> create_application_thunk_api c1l = Some l
       \<and> res = create_coupon Think l r"
    using make_some[OF assms] by auto

  let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  show ?thesis
    using 1 
          fixpoint_is_eval_coupon_impl[of ?state]
          fixpoint_is_apply_coupon_impl[of ?state]
          fixpoint_get_coupon_lhs_impl[of ?state]
          fixpoint_get_coupon_rhs_impl[of ?state]
          fixpoint_is_equal_impl[of ?state]
          fixpoint_create_think_coupon_impl[of ?state]
          fixpoint_create_application_thunk_impl[of ?state]
    apply (invoke_coupon_func fuel_idx_def: plus_54 func_make_think_application_coupon_idx_def)
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

lemma make_think_application_coupon_run_invoke_none:
  assumes "make_think_application_coupon coupons l r = None"
  shows "\<exists>msg cfg.
         run_iter (n + 54)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_think_application_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 = (cfg, RTrap msg)"
proof -
  let ?A = "length coupons < 2"
  let ?B = "\<exists>c1 c2 xs. coupons = c1 # c2 # xs \<and>
          (\<not>is_eval_coupon c1 \<or> \<not>is_apply_coupon c2)"
  let ?C = "(\<exists>c1 c2 xs c1l c1r c2l c2r.
          coupons = c1 # c2 # xs
        \<and> is_eval_coupon c1
        \<and> is_apply_coupon c2
        \<and> get_coupon_lhs c1 = Some c1l
        \<and> get_coupon_rhs c1 = Some c1r
        \<and> get_coupon_lhs c2 = Some c2l
        \<and> get_coupon_rhs c2 = Some c2r
        \<and> (create_application_thunk_api c1l = None \<or>
           (\<exists>thunk. create_application_thunk_api c1l = Some thunk
             \<and> (\<not>is_equal c1r c2l 
             \<or> \<not>is_equal thunk l 
             \<or> \<not>is_equal c2r r)))
       )"

  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"


  have assms: "?A \<or> ?B \<or> ?C" 
    using make_none[OF assms] by blast

  show ?thesis
    using assms
  proof
    assume "?A"
    then have "\<not> nat_of_int (I32.lift0 1) < length coupons"
      by (simp add: nat_of_int_i32.abs_eq)
    then show ?thesis
      apply (invoke_coupon_func fuel_idx_def: plus_54 func_make_think_application_coupon_idx_def)
      apply (table_get_local_set)
      done
  next
    assume "?B \<or> ?C"
    then show ?thesis
    proof
      assume "?B"
      then obtain c1 c2 xs where
        "coupons = c1 # c2 # xs"
        and "\<not> is_eval_coupon c1 \<or> (is_eval_coupon c1 \<and> \<not> is_apply_coupon c2)"
        by blast
      then show ?thesis
        using fixpoint_is_eval_coupon_impl[of ?state]
        fixpoint_is_apply_coupon_impl[of ?state]
        apply (invoke_coupon_func fuel_idx_def: plus_54 func_make_think_application_coupon_idx_def)
        apply (table_get_local_set)
        apply (call_api_func)
        apply (if_block)
        apply (call_api_func)
        apply (if_block)
        done
    next
      assume "?C"
      then obtain c1 c2 xs c1l c1r c2l c2r where
        1: "coupons = c1 # c2 # xs \<and>
         is_eval_coupon c1 \<and>
         is_apply_coupon c2 \<and>
         get_coupon_lhs c1 = Some c1l \<and>
         get_coupon_rhs c1 = Some c1r \<and>
         get_coupon_lhs c2 = Some c2l \<and>
         get_coupon_rhs c2 = Some c2r"
      and  2: "(create_application_thunk_api c1l = None \<or>
      (\<exists>thunk.
          create_application_thunk_api c1l = Some thunk \<and>
          (\<not> is_equal c1r c2l \<or> \<not> is_equal thunk l \<or> \<not> is_equal c2r r)))"
        by blast

      show ?thesis
        using 2
      proof
        assume "create_application_thunk_api c1l = None"
        then show ?thesis
          using 1
            fixpoint_is_eval_coupon_impl[of ?state]
            fixpoint_is_apply_coupon_impl[of ?state]
            fixpoint_get_coupon_lhs_impl[of ?state]
            fixpoint_get_coupon_rhs_impl[of ?state]
            fixpoint_is_equal_impl[of ?state]
            fixpoint_create_think_coupon_impl[of ?state]
            fixpoint_create_application_thunk_impl[of ?state]
          apply (invoke_coupon_func fuel_idx_def: plus_54 func_make_think_application_coupon_idx_def)
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
        assume "(\<exists>thunk.
          create_application_thunk_api c1l = Some thunk \<and>
          (\<not> is_equal c1r c2l \<or> \<not> is_equal thunk l \<or> \<not> is_equal c2r r))"
        then obtain thunk 
          where "create_application_thunk_api c1l = Some thunk" 
            and "(\<not> is_equal c1r c2l \<or> \<not> is_equal thunk l \<or> \<not> is_equal c2r r)" 
          by blast

        then show ?thesis
          using 1
            fixpoint_is_eval_coupon_impl[of ?state]
            fixpoint_is_apply_coupon_impl[of ?state]
            fixpoint_get_coupon_lhs_impl[of ?state]
            fixpoint_get_coupon_rhs_impl[of ?state]
            fixpoint_is_equal_impl[of ?state]
            fixpoint_create_think_coupon_impl[of ?state]
            fixpoint_create_application_thunk_impl[of ?state]
          apply (invoke_coupon_func fuel_idx_def: plus_54 func_make_think_application_coupon_idx_def)
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
          done
      qed
    qed
  qed
qed

end