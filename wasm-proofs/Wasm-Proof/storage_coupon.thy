theory storage_coupon
  imports Wasm_Proof_Playground
begin

fun make_blob_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_blob_coupon_raw (c # xs) l r =
   (if (is_storage_coupon_api c) 
    then (case (get_coupon_lhs c, get_coupon_rhs c) of
     (Some l', Some r') \<Rightarrow> (if ( is_equal l l' \<and> is_equal r r') then Some (create_eq_coupon l r)
                                                                else None)
    | _ \<Rightarrow> None)
    else None)"
| "make_blob_coupon_raw [] l r = None"

lemma mb_some:
  assumes "make_blob_coupon_raw coupons l r = Some res"
  shows "(\<exists>c xs l' r'. coupons = c # xs
              \<and> is_storage_coupon_api c
              \<and> get_coupon_lhs c = Some l'
              \<and> get_coupon_rhs c = Some r'
              \<and> is_equal l l'
              \<and> is_equal r r'
              \<and> res = (create_eq_coupon l r))"
proof -
  obtain c xs l' r' where 1: "coupons  = c # xs"
                      and 2: "is_storage_coupon_api c"
                      and 3: "get_coupon_lhs c = Some l'"
                      and 4: "get_coupon_rhs c = Some r'"
  by (metis assms is_coupon_lhs is_coupon_rhs is_storage_coupon_api_def make_blob_coupon_raw.elims option.simps(3))

  then have "make_blob_coupon_raw coupons l r = 
       (if (is_equal l l' \<and> is_equal r r') then Some (create_eq_coupon l r) else None)"
    by (simp add: 1 2 3 4)

  then show ?thesis
    by (metis "1" "2" "3" "4" assms handy_if_lemma)
qed

lemma plus_31:
"n + 31 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))"
  by auto

lemma make_blob_coupon_raw_run_iter:
  assumes "make_blob_coupon_raw coupons l r = Some res"
  shows  "run_iter (n + 31)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_blob_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  obtain c xs l' r' where 1: "coupons = c # xs"
                      and 2: "is_storage_coupon_api c"
                      and 3: "get_coupon_lhs c = Some l'"
                      and 4: "get_coupon_rhs c = Some r'"
                      and 5: "is_equal l l'"
                      and 6: "is_equal r r'"
                      and 7: "res = (create_eq_coupon l r)"
    using mb_some assms by blast

  let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  let ?ce = "to_externref c"

  have A: "nat_of_int (I32.lift0 0) < length coupons"
    by (metis "1" Abs_fnat_hom_0 gr_zeroI impossible_Cons le0 zero zero_i32_def)

  have B: "(coupons ! nat_of_int (I32.lift0 0)) = c"
    using "1" nat_of_int_i32.abs_eq by auto

  have C: "\<And>s. (host_func_apply_impl s type1 fixpoint_is_storage_coupon_api 
    [V_ref (ConstRefExtern (to_externref c))] = Some (s, [V_num (ConstInt32 (I32.int_of_nat 1))]))"
    using bool_to_i32_true fixpoint_is_storage_coupon_api_impl 2 by auto

  have D: "(I32.int_and 1 1) = 1"
    using I32.int_and_def by force
  have D: "(int_and (I32.int_of_nat (Suc 0)) (I32.int_of_nat (Suc 0))) = (I32.int_of_nat 1)"
    by (simp add: D I32.int_of_nat_def
        int_and_i32.abs_eq)

  show ?thesis
    using A C[of ?state] 
          fixpoint_get_coupon_lhs_impl[of ?state ?ce] 3 
          fixpoint_get_coupon_rhs_impl[of ?state ?ce] 4
          fixpoint_is_equal_correct_externref[of "to_externref l" "to_externref l'" ?state] 5
          fixpoint_is_equal_correct_externref[of "to_externref r" "to_externref r'" ?state] 6
          fixpoint_create_eq_coupon_impl[of ?state "to_externref l" "to_externref r"] 7
    by (auto split: cl.splits simp del: split_n.simps simp add:  init_def func_make_blob_coupon_idx_def n_zeros_def bitzero_def tab_coupons_idx_def app_s_f_v_s_table_get_def stab_ind_def load_tabs1_def B
    app_f_v_s_local_set_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def  se tb_tf_def typeof_ref_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def D split_n_0 split_n_1 split_n_2 app_v_s_if_def plus_31)
qed

lemma mb_some_rev:
  assumes "(\<exists>c xs l' r'. coupons = c # xs
              \<and> is_storage_coupon_api c
              \<and> get_coupon_lhs c = Some l'
              \<and> get_coupon_rhs c = Some r'
              \<and> is_equal l l'
              \<and> is_equal r r'
              \<and> res = (create_eq_coupon l r))"
  shows "make_blob_coupon_raw coupons l r = Some res"
  using assms by fastforce

lemma mb_none:
  assumes "make_blob_coupon_raw coupons l r = None"
  shows "(coupons = [] \<or>
          (\<exists> c xs. coupons = c # xs \<and> \<not> is_storage_coupon_api c) \<or>
          (\<exists> c xs l' r'. coupons = c # xs \<and> 
                         is_storage_coupon_api c \<and> 
                         get_coupon_lhs c = Some l' \<and>
                         get_coupon_rhs c = Some r' \<and>
                         \<not> is_equal l l') \<or>
          (\<exists> c xs l' r'. coupons = c # xs \<and>
                         is_storage_coupon_api c \<and>
                         get_coupon_lhs c = Some l' \<and>
                         get_coupon_rhs c = Some r' \<and>
                         is_equal l l' \<and>
                         \<not> is_equal r r'))"
  by (metis assms if_Some_None_eq_None is_coupon_lhs is_coupon_rhs is_storage_coupon_api_def make_blob_coupon_raw.elims mb_some_rev)

lemma make_blob_coupon_raw_run_invoke_none:
  assumes "make_blob_coupon_raw coupons l r = None"
  shows "\<exists>msg cfg.
          run_iter (fuel50 n)
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_blob_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
        = (cfg, RTrap msg)"
proof -
  let ?A = "coupons = []"
  let ?B = "(\<exists> c xs. coupons = c # xs \<and> \<not> is_storage_coupon_api c)"
  let ?C = "(\<exists> c xs l' r'. coupons = c # xs \<and> 
                              is_storage_coupon_api c \<and> 
                              get_coupon_lhs c = Some l' \<and>
                              get_coupon_rhs c = Some r' \<and>
                              \<not> is_equal l l')"
  let ?D = "(\<exists> c xs l' r'. coupons = c # xs \<and>
                              is_storage_coupon_api c \<and>
                              get_coupon_lhs c = Some l' \<and>
                              get_coupon_rhs c = Some r' \<and>
                              is_equal l l' \<and>
                              \<not> is_equal r r')"

  have assms: "?A \<or> ?B \<or> ?C \<or> ?D" using mb_none assms by auto

  let ?state = "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  show ?thesis
    using assms
  proof
    assume "?A"
    then have 1: "\<not> nat_of_int (I32.lift0 0) < length coupons" by auto

    show ?thesis
      using 1
      by (auto split: cl.splits simp del: split_n.simps simp add: init_def func_make_blob_coupon_idx_def app_f_call_def sfunc_ind_def n_zeros_def bitzero_def split_n_2 tab_coupons_idx_def app_s_f_v_s_table_get_def stab_ind_def load_tabs1_def)
  next
    assume "?B \<or> ?C \<or> ?D"
    then show "?thesis"
    proof
      assume ?B
      then obtain c xs where 1: "coupons = c # xs" and 2: "\<not> is_storage_coupon_api c" by auto

      then show "?thesis"        
        using fixpoint_is_storage_coupon_api_externref_neq[of "to_externref c" ?state] 2
        by (auto split: cl.splits simp del: split_n.simps simp add: init_def func_make_blob_coupon_idx_def n_zeros_def bitzero_def tab_coupons_idx_def app_s_f_v_s_table_get_def stab_ind_def load_tabs1_def app_f_v_s_local_set_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def  se tb_tf_def typeof_ref_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def 1 nat_of_int_i32.abs_eq sf split_n_0 split_n_1 split_n_2 app_v_s_if_def)
    next
      assume "?C \<or> ?D"
      then show "?thesis"
      proof
        assume ?C
        then obtain c xs l' r' where 1: "coupons = c # xs"
                                 and 2: "is_storage_coupon_api c"
                                 and 3: "get_coupon_lhs c = Some l'"
                                 and 4: "get_coupon_rhs c = Some r'"
                                 and 5: "\<not> is_equal l l'"
          by blast

        have 6: "I32.int_and 0 0 = 0"
          using I32.int_and_def by force
        have 6: "(int_and (I32.int_of_nat 0) (I32.int_of_nat 0)) = (I32.int_of_nat 0)"
          by (simp add: 6 I32.int_of_nat_def int_and_i32.abs_eq)

        have 7: "I32.int_and 0 1 = 0"
          using I32.int_and_def by force
        have 7: "(int_and (I32.int_of_nat 0) (I32.int_of_nat (Suc 0))) = (I32.int_of_nat 0)"
          by (simp add: 7 I32.int_of_nat_def int_and_i32.abs_eq)

        show "?thesis" 
          using fixpoint_is_storage_coupon_api_externref[of "to_externref c" ?state] 2
          fixpoint_get_coupon_lhs_impl[of ?state "to_externref c"] 3
          fixpoint_get_coupon_rhs_impl[of ?state "to_externref c"] 4
          fixpoint_is_equal_correct_externref_neq[of "to_externref l" "to_externref l'" ?state] 5
          fixpoint_is_equal_correct_externref[of "to_externref r" "to_externref r'" ?state]
          fixpoint_is_equal_correct_externref_neq[of "to_externref r" "to_externref r'" ?state]
      
          apply (auto split: cl.splits simp add: init_def func_make_blob_coupon_idx_def n_zeros_def bitzero_def tab_coupons_idx_def app_s_f_v_s_table_get_def stab_ind_def load_tabs1_def app_f_v_s_local_set_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def app_v_s_if_def se tb_tf_def typeof_ref_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def 1 nat_of_int_i32.abs_eq sf split_n_0 split_n_1 split_n_2)
          apply (cases "is_equal r r'")
          apply (auto split: cl.splits simp add: init_def func_make_blob_coupon_idx_def n_zeros_def bitzero_def tab_coupons_idx_def app_s_f_v_s_table_get_def stab_ind_def load_tabs1_def app_f_v_s_local_set_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def app_v_s_if_def se tb_tf_def typeof_ref_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def 1 nat_of_int_i32.abs_eq sf 6 7 split_n_0 split_n_1 split_n_2)
          done
      next
        assume ?D
        then obtain c xs l' r' where 1: "coupons = c # xs"
                                 and 2: "is_storage_coupon_api c"
                                 and 3: "get_coupon_lhs c = Some l'"
                                 and 4: "get_coupon_rhs c = Some r'"
                                 and 5: "is_equal l l'"
                                 and 6: "\<not> is_equal r r'"
          by blast
        
        have 7: "I32.int_and 1 0 = 0"
          using I32.int_and_def by force
        have 7: "(int_and (I32.int_of_nat (Suc 0)) (I32.int_of_nat 0)) = (I32.int_of_nat 0)"
          by (simp add: 7 I32.int_of_nat_def int_and_i32.abs_eq)
        
        show "?thesis"
          using fixpoint_is_storage_coupon_api_externref[of "to_externref c" ?state] 2
          fixpoint_get_coupon_lhs_impl[of ?state "to_externref c"] 3
          fixpoint_get_coupon_rhs_impl[of ?state "to_externref c"] 4
          fixpoint_is_equal_correct_externref[of "to_externref l" "to_externref l'" ?state] 5
          fixpoint_is_equal_correct_externref_neq[of "to_externref r" "to_externref r'" ?state] 6
          by (auto split: cl.splits simp add: init_def func_make_blob_coupon_idx_def n_zeros_def bitzero_def tab_coupons_idx_def app_s_f_v_s_table_get_def stab_ind_def load_tabs1_def app_f_v_s_local_set_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def app_v_s_if_def se tb_tf_def typeof_ref_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def 1 nat_of_int_i32.abs_eq sf 7 split_n_0 split_n_1 split_n_2)
      qed
    qed
  qed
qed

end