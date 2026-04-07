theory tree_coupon
  imports custom_method isabelle_coupon
begin

axiomatization where
  tree_size_i32: "(\<exists>s. get_tree_size_api l = Some s) \<longrightarrow> (\<exists>s. get_tree_size_api l = Some s \<and> s < 2^(LENGTH(i32) - 1))"

lemma make_some:
  assumes "make_tree_coupon_raw coupons l r = Some res"
  shows "(\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i))) \<and>
         get_tree_size_api l = Some (length coupons) \<and>
         get_tree_size_api r = Some (length coupons) \<and>
         (\<forall>i. (i < length coupons \<longrightarrow>
           (\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr))) \<and>
         res = create_eq_coupon l r"
proof -
  have 1: "(\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i)))"
    by (metis assms make_tree_coupon_raw.simps option.distinct(1))
  then have 5: "(\<forall>i. (i < length coupons \<longrightarrow> 
        (\<exists>cl cr. get_coupon_lhs (coupons ! i) = Some cl 
               \<and> get_coupon_rhs (coupons ! i) = Some cr)))"
    by (metis is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def)

  have 2: "get_tree_size_api l = Some (length coupons)"
    by (metis assms make_tree_coupon_raw.simps option.distinct(1))
  then have 6: "\<forall>i < length coupons. \<exists>li. get_tree_data_api l i = Some li"
    using get_tree_size_def get_tree_data_def
    by (cases l) auto

  have 3: "get_tree_size_api r = Some (length coupons)"
    by (metis assms make_tree_coupon_raw.simps option.distinct(1))
  then have 7: "\<forall>i < length coupons. \<exists>ri. get_tree_data_api r i = Some ri"
    using get_tree_size_def get_tree_data_def
    by (cases r) auto

  have 4: "(\<forall>i. (i < length coupons \<longrightarrow>
         (case (get_tree_data_api l i, get_tree_data_api r i, get_coupon_lhs (coupons ! i), get_coupon_rhs (coupons ! i)) of
             (Some li, Some ri, Some cl, Some cr) \<Rightarrow> (is_equal li cl \<and> is_equal ri cr)
           | _ \<Rightarrow> False)))"
    by (metis (no_types, lifting) assms make_tree_coupon_raw.simps option.distinct(1))

  have 5: "(\<forall>i. (i < length coupons \<longrightarrow>
           (\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)))"
  proof
    fix i
    show "(i < length coupons \<longrightarrow>
           (\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr))"
    proof (intro impI)
      assume H: "i < length coupons"
      obtain li ri cl cr where H1: "get_coupon_lhs (coupons ! i) = Some cl" 
                                and H2: "get_coupon_rhs (coupons ! i) = Some cr"
                                and H3: "get_tree_data_api l i = Some li"
                                and H4: "get_tree_data_api r i = Some ri"
        using 5 6 7 H
        by meson
      then have "is_equal li cl \<and> is_equal ri cr"
        using 4 H by auto
      then show "(\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)"
        using H1 H2 H3 H4 by auto
    qed
  qed

  show ?thesis
    using 1 2 3 5
    by (metis (no_types, lifting) assms make_tree_coupon_raw.simps option.discI option.sel)
qed

lemma make_some_rev:
  assumes "(\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i))) \<and>
         get_tree_size_api l = Some (length coupons) \<and>
         get_tree_size_api r = Some (length coupons) \<and>
         (\<forall>i. (i < length coupons \<longrightarrow>
           (\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)))"
  shows "make_tree_coupon_raw coupons l r = Some (create_eq_coupon l r)"
  using assms by fastforce

lemma make_none:
  assumes "make_tree_coupon_raw coupons l r = None"
  shows "(\<exists>i. i < length coupons \<and> \<not>is_eq_coupon_api (coupons ! i) 
                \<and> (\<forall>j < i. is_eq_coupon_api (coupons ! j))) \<or>
         ((\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i))) \<and>
          ((get_tree_size_api l = None \<or> 
            get_tree_size_api r = None \<or> 
            (\<exists>l'. get_tree_size_api l = Some l' \<and> l' \<noteq> length coupons) \<or>
            (\<exists>r'. get_tree_size_api r = Some r' \<and> r' \<noteq> length coupons)) \<or>
           (get_tree_size_api l = Some (length coupons) \<and>
            get_tree_size_api r = Some (length coupons) \<and>
            (\<exists>i. i < length coupons \<and> 
               (\<exists> li ri cl cr.
                get_tree_data_api l i = Some li \<and>
                get_tree_data_api r i = Some ri \<and>
                get_coupon_lhs (coupons ! i) = Some cl \<and>
                get_coupon_rhs (coupons ! i) = Some cr \<and>
               (\<not>is_equal li cl \<or> \<not>is_equal ri cr)) \<and>

               (\<forall>j < i. (\<exists> li ri cl cr.
                get_tree_data_api l j = Some li \<and>
                get_tree_data_api r j = Some ri \<and>
                get_coupon_lhs (coupons ! j) = Some cl \<and>
                get_coupon_rhs (coupons ! j) = Some cr \<and>
                is_equal li cl \<and>
                is_equal ri cr))))
))"
proof (cases "\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i))")
  case False 
  then have H: "\<exists>i. (i < length coupons \<and> \<not>is_eq_coupon_api (coupons ! i))" by auto
  have "(\<exists>i. i < length coupons \<and> \<not>is_eq_coupon_api (coupons ! i) 
                \<and> (\<forall>j < i. is_eq_coupon_api (coupons ! j)))"
  proof -
    let ?P = "\<lambda>i. i < length coupons \<and> \<not> is_eq_coupon_api (coupons ! i)"
    let ?i = "LEAST i. ?P i"
    have "?P ?i" using H by (rule LeastI_ex)
    moreover have "\<forall>j<?i. is_eq_coupon_api (coupons ! j)"
      using not_less_Least
      using calculation order_less_trans by blast
    ultimately show ?thesis by blast
  qed
  then show ?thesis by auto
next
  case True
  then have T1: "\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i))" .
  then have 1: "(\<forall>i. (i < length coupons \<longrightarrow> 
        (\<exists>cl cr. get_coupon_lhs (coupons ! i) = Some cl 
               \<and> get_coupon_rhs (coupons ! i) = Some cr)))"
    by (metis is_coupon_lhs is_coupon_rhs is_eq_coupon_api_def)

  show ?thesis
  proof (cases "get_tree_size_api l = Some (length coupons) \<and> get_tree_size_api r = Some (length coupons)")
    case False then show ?thesis by (metis True not_Some_eq)
  next
    case True
    then have T2: "get_tree_size_api l = Some (length coupons)" by simp
    then have 2: "\<forall>i < length coupons. \<exists>li. get_tree_data_api l i = Some li"
      using get_tree_size_def get_tree_data_def by (cases l) auto

    have T3: "get_tree_size_api r = Some (length coupons)" using True by simp
    then have 3: "\<forall>i < length coupons. \<exists>ri. get_tree_data_api r i = Some ri"
      using get_tree_size_def get_tree_data_def by (cases r) auto

    have "\<not>(\<forall>i. (i < length coupons \<longrightarrow>
           (\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)))"
      using T1 T2 T3 assms make_some_rev by force

    then have H: "\<exists>i. i < length coupons \<and> 
               (\<exists>li ri cl cr.
                get_tree_data_api l i = Some li \<and>
                get_tree_data_api r i = Some ri \<and>
                get_coupon_lhs (coupons ! i) = Some cl \<and>
                get_coupon_rhs (coupons ! i) = Some cr \<and>
                (\<not>is_equal li cl \<or> \<not>is_equal ri cr))"
      by (meson "1" "2" "3")

    have "(\<exists>i. i < length coupons \<and> 
               (\<exists> li ri cl cr.
                get_tree_data_api l i = Some li \<and>
                get_tree_data_api r i = Some ri \<and>
                get_coupon_lhs (coupons ! i) = Some cl \<and>
                get_coupon_rhs (coupons ! i) = Some cr \<and>
               (\<not>is_equal li cl \<or> \<not>is_equal ri cr)) \<and>

               (\<forall>j < i. (\<exists> li ri cl cr.
                get_tree_data_api l j = Some li \<and>
                get_tree_data_api r j = Some ri \<and>
                get_coupon_lhs (coupons ! j) = Some cl \<and>
                get_coupon_rhs (coupons ! j) = Some cr \<and>
                is_equal li cl \<and>
                is_equal ri cr)))"
    proof -
      let ?P = "\<lambda>i. i < length coupons \<and> 
               (\<exists> li ri cl cr.
                get_tree_data_api l i = Some li \<and>
                get_tree_data_api r i = Some ri \<and>
                get_coupon_lhs (coupons ! i) = Some cl \<and>
                get_coupon_rhs (coupons ! i) = Some cr \<and>
               (\<not>is_equal li cl \<or> \<not>is_equal ri cr))"
      let ?i = "LEAST i. ?P i"
      have H1: "?P ?i" using H by (rule LeastI_ex)

      have H2: "\<forall>j < ?i. (\<exists> li ri cl cr.
                get_tree_data_api l j = Some li \<and>
                get_tree_data_api r j = Some ri \<and>
                get_coupon_lhs (coupons ! j) = Some cl \<and>
                get_coupon_rhs (coupons ! j) = Some cr)"
        using 1 2 3 H1 by auto

      have H3: "\<forall>j < ?i. \<not>(\<exists> li ri cl cr.
                get_tree_data_api l j = Some li \<and>
                get_tree_data_api r j = Some ri \<and>
                get_coupon_lhs (coupons ! j) = Some cl \<and>
                get_coupon_rhs (coupons ! j) = Some cr \<and>
               (\<not>is_equal li cl \<or> \<not>is_equal ri cr))"
        using H1 not_less_Least order_less_trans by blast

      have "\<forall>j < ?i. (\<exists> li ri cl cr.
                get_tree_data_api l j = Some li \<and>
                get_tree_data_api r j = Some ri \<and>
                get_coupon_lhs (coupons ! j) = Some cl \<and>
                get_coupon_rhs (coupons ! j) = Some cr \<and>
                is_equal li cl \<and>
                is_equal ri cr)"
        using H2 H3
        by meson

      then show ?thesis using H1
        by blast
    qed
    then show ?thesis
      using T1 True by blast
  qed
qed

definition first_loop where
"first_loop = Loop (Tbv None)
             [Local_get 4,
              Local_get 3,
              Relop T_i32
               (Relop_i (Ge S)),
              Br_if (Suc 0),
              Local_get 4,
              Table_get 0, Call 3,
              b_e.If (Tbv None) [Nop]
               [Unreachable],
              Local_get 4,
              EConstNum
               (ConstInt32
                 (I32.lift0 1)),
              Binop T_i32
               (Binop_i Add),
              Local_set 4, Br 0]"

lemma first_loop_last:
" run_iter (n + 6)
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([first_loop]))
       [Label_context [] b_es 0 [], Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      fcs ) = 
  run_iter n  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] b_es)
       [Label_context [] [] (Suc 0) []]
       (Suc 0)
             \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      fcs)"
proof -
  have plus_6: "n + 6 = (Suc (Suc (Suc (Suc (Suc (Suc n))))))" by auto

  show ?thesis
  apply (simp add: init_def plus_6 tb_tf_def app_f_v_s_local_get_def app_v_s_relop_def first_loop_def)
  apply (simp add: app_relop_def app_relop_i_v_def app_relop_i_def I32.int_ge_s_def int_ge_s_i32_def app_v_s_br_if_def)
  apply (simp add: wasm_bool_def st)
  done
qed

lemma add_one_is_add_one:
  "(int_add (int_of_nat i) (I32.lift0 1)) = (int_of_nat (Suc i))"
  by (metis I32.int_add_def Rep_i32_inverse
      add.commute int_add_i32.abs_eq
      int_of_nat_i32.rep_eq semiring_1_class.of_nat_simps(2))

lemma first_loop_internal_good:
  assumes H1: "i < length coupons"
  assumes H2: "is_eq_coupon_api (coupons ! i)"
  assumes H3: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "run_iter (n + 17) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([first_loop]))
       [Label_context [] b_es 0 [], Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat i))],
          f_inst = exp_inst\<rparr>)
      fcs ) = 
  run_iter n  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
       (Frame_context
       (Redex [] []
         ([first_loop]))
       [Label_context [] b_es 0 [], Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (Suc i)))],
          f_inst = exp_inst\<rparr>)
      fcs)"
proof -
  have plus_17: "n + 17 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))" by auto

  let ?state =  "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  show ?thesis
  using fixpoint_is_eq_coupon_impl[of ?state]
    ge_than_32[OF H1 H3]
    nat_of_int_rev_trans[OF H1 H3]
    H1 H2 add_one_is_add_one
  apply (simp add: init_def tab_coupons_idx_def tb_tf_def plus_17 app_f_v_s_local_get_def app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def app_v_s_br_if_def first_loop_def)
  apply (if_block)
  apply (table_get_local_set)
  apply (call_api_func)
  apply (if_block)
  apply (simp add: app_f_v_s_local_get_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def)
  apply (table_get_local_set)
  done
qed

lemma first_loop_internal_bad:
  assumes H1: "i < length coupons"
  assumes H2: "\<not> is_eq_coupon_api (coupons ! i)"
  assumes H3: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<exists>cfg msg. run_iter (n + 17) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([first_loop]))
       [Label_context [] b_es 0 [], Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat i))],
          f_inst = exp_inst\<rparr>)
      fcs ) = (cfg, RTrap msg)"
proof -
  have plus_17: "n + 17 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))" by auto

  let ?state =  "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  show ?thesis
  using fixpoint_is_eq_coupon_impl[of ?state]
    ge_than_32[OF H1 H3]
    nat_of_int_rev_trans[OF H1 H3]
    H1 H2 add_one_is_add_one
  apply (simp add: init_def tab_coupons_idx_def tb_tf_def plus_17 app_f_v_s_local_get_def app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def app_v_s_br_if_def first_loop_def)
  apply (if_block)
  apply (table_get_local_set)
  apply (call_api_func)
  apply (if_block)
  done
qed

lemma first_loop_good_multiple:
  assumes H1: "\<forall>i. i < x \<longrightarrow> is_eq_coupon_api (coupons ! i)"
  assumes H2: "x \<le> length coupons"
  assumes H3: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<And>n. run_iter (n + 17 * x) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([first_loop]))
       [Label_context [] b_es 0 [], Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat 0))],
          f_inst = exp_inst\<rparr>)
      fcs ) =
run_iter n
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([first_loop]))
       [Label_context [] b_es 0 [], Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat x))],
          f_inst = exp_inst\<rparr>)
      fcs )"
  using H1 H2 H3
proof (induction x arbitrary: n)
  case 0
  show ?case
    using 0 by auto
next
  case (Suc y)
  then have 1: "y < length coupons" and 2: "is_eq_coupon_api  (coupons ! y)" 
    by auto
  have "n + 17 + 17 * y = n + 17 * (Suc y)" by auto 
  then show ?case using  
    first_loop_internal_good[OF 1 2 Suc.prems(3)] 
    Suc.IH[of "n + 17"] 1 2 Suc.prems
    by (metis dual_order.strict_trans le_eq_less_or_eq lessI)
qed

lemma first_loop_good:
  assumes H1: "\<forall>i. i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i)"
  assumes H2: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "run_iter (n + 6 + 17 * (length coupons)) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([first_loop]))
       [Label_context [] b_es 0 [], Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat 0))],
          f_inst = exp_inst\<rparr>)
      fcs ) =
 run_iter n  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] b_es)
       [Label_context [] [] (Suc 0) []]
       (Suc 0)
             \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      fcs)"
proof -
  have 1: "length coupons \<le> length coupons" by simp
  show ?thesis 
    using first_loop_good_multiple[OF H1 1 H2, of "n+6"]
          first_loop_last[of n n']
    by auto
qed

lemma first_loop_bad:
  assumes H1: "(\<exists>i. i < length coupons \<and> \<not>is_eq_coupon_api (coupons ! i) 
                \<and> (\<forall>j < i. is_eq_coupon_api (coupons ! j)))"
  assumes H2: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<exists>cfg msg. run_iter (n + 6 + 17 * (length coupons)) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([first_loop]))
       [Label_context [] b_es 0 [], Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat 0))],
          f_inst = exp_inst\<rparr>)
      fcs ) = (cfg, RTrap msg)"
proof -
  obtain i where 1: "i < length coupons" 
             and 2: "\<not>is_eq_coupon_api (coupons ! i)"
             and 3: "(\<forall>j < i. is_eq_coupon_api (coupons ! j))"
    using H1 by auto

  have 4: "i \<le> length coupons" using 1 by auto

  have A: "n + 6 + 17 * (length coupons - i) - 17 + 17 = n + 6 + 17 * (length coupons - i)"
    using 1
    by auto

  have B: "(n + 6 + 17 * (length coupons - i) + 17 * i) = n + 6 + 17 * (length coupons)"
    using 1
    by auto

  show ?thesis
    using first_loop_internal_bad[OF 1 2 H2, of "(n + 6 + 17 * (length coupons - i) - 17)" n'] first_loop_good_multiple[OF 3 4 H2, of "n + 6 + 17 * (length coupons - i)" n'] A B
    by metis
qed

definition second_loop where 
"second_loop = 
(Loop (Tbv None)
[(Local_get 4),
(Local_get 3),
(Relop T_i32 (Relop_i (relop_i.Ge S))),
(Br_if 1),
(Local_get 4),
(Table_get 0),
(Local_set 2),
(Local_get 0),
(Local_get 4),
(Call 10),
(Local_get 2),
(Call 6),
(Call 0),
(If (Tbv None)
[(Local_get 1),
(Local_get 4),
(Call 10),
(Local_get 2),
(Call 7),
(Call 0),
(If (Tbv None)
[Nop]
[Unreachable])]
[Unreachable]),
(Local_get 4),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Binop T_i32 (Binop_i Add)),
(Local_set 4),
(Br 0)])"

lemma second_loop_last:
" run_iter (n + 6)
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([second_loop]))
       [Label_context [] b_es 0 [], 
        Label_context [] [] (Suc 0) [], 
        Label_context [] [] (Suc 0) [], 
        Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           someloc,
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      fcs ) = 
  run_iter n  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] b_es)
       [Label_context [] [] (Suc 0) [], 
        Label_context [] [] (Suc 0) [], 
        Label_context [] [] (Suc 0) []]
       (Suc 0)
             \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           someloc,
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      fcs)"
proof -
  have plus_6: "n + 6 = (Suc (Suc (Suc (Suc (Suc (Suc n))))))" by auto

  show ?thesis
  apply (simp add: init_def plus_6 tb_tf_def app_f_v_s_local_get_def app_v_s_relop_def second_loop_def)
  apply (simp add: app_relop_def app_relop_i_v_def app_relop_i_def I32.int_ge_s_def int_ge_s_i32_def app_v_s_br_if_def)
  apply (simp add: wasm_bool_def st)
  done
qed

lemma second_loop_internal_good:
  assumes H1: "i < length coupons"
  assumes H2: "(\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)"
  assumes H3: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "run_iter (n + 37) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([second_loop]))
       [Label_context [] b_es 0 [], 
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           someloc,
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat i))],
          f_inst = exp_inst\<rparr>)
      fcs ) = 
  run_iter n  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
       (Frame_context
       (Redex [] []
         ([second_loop]))
       [Label_context [] b_es 0 [], 
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (ConstRefExtern (to_externref (coupons ! i))),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (Suc i)))],
          f_inst = exp_inst\<rparr>)
      fcs)"
proof -
  have plus_30: "n + 37 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))))))))" by auto

  let ?state =  "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  obtain li ri cl cr where 
    1: "get_tree_data_api l i = Some li \<and>
        get_tree_data_api r i = Some ri \<and>
        get_coupon_lhs (coupons ! i) = Some cl \<and>
        get_coupon_rhs (coupons ! i) = Some cr \<and>
        is_equal li cl \<and>
        is_equal ri cr"
    using H2 by auto

  show ?thesis
    using fixpoint_get_tree_data_impl[of ?state]
          ge_than_32[OF H1 H3]
          fixpoint_get_coupon_lhs_impl[of ?state]
          fixpoint_get_coupon_rhs_impl[of ?state]
          fixpoint_is_equal_impl[of ?state]
          nat_of_int_rev_trans[OF H1 H3]
          nat_of_int_rev_trans_32[OF H1 H3]
          H1 1 add_one_is_add_one
    apply (simp add: init_def tab_coupons_idx_def tb_tf_def plus_30 app_f_v_s_local_get_def app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def app_v_s_br_if_def second_loop_def)
    apply (if_block, table_get_local_set, call_api_func)
    apply (if_block)
    apply (call_api_func)
    apply (if_block)
    apply (simp add: app_f_v_s_local_get_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def)
    apply (table_get_local_set) 
    done
qed

lemma second_loop_internal_bad:
  assumes H1: "i < length coupons"
  assumes H2: "(\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            (\<not>is_equal li cl \<or> \<not>is_equal ri cr))"
  assumes H3: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<exists>cfg msg. run_iter (n + 37) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([second_loop]))
       [Label_context [] b_es 0 [], 
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           someloc,
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat i))],
          f_inst = exp_inst\<rparr>)
      fcs ) = (cfg, RTrap msg)"
proof -
  have plus_30: "n + 37 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))))))))))))))))))))))))))))" by auto

  let ?state =  "(init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)"

  obtain li ri cl cr where 
    1: "get_tree_data_api l i = Some li \<and>
        get_tree_data_api r i = Some ri \<and>
        get_coupon_lhs (coupons ! i) = Some cl \<and>
        get_coupon_rhs (coupons ! i) = Some cr \<and>
        (\<not>is_equal li cl \<or> \<not>is_equal ri cr)"
    using H2 by auto

  show ?thesis
    using fixpoint_get_tree_data_impl[of ?state]
          ge_than_32[OF H1 H3]
          fixpoint_get_coupon_lhs_impl[of ?state]
          fixpoint_get_coupon_rhs_impl[of ?state]
          fixpoint_is_equal_impl[of ?state]
          nat_of_int_rev_trans[OF H1 H3]
          nat_of_int_rev_trans_32[OF H1 H3]
          H1 1 add_one_is_add_one
    apply (simp add: init_def tab_coupons_idx_def tb_tf_def plus_30 app_f_v_s_local_get_def app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def app_v_s_br_if_def second_loop_def)
    apply (if_block, table_get_local_set, call_api_func)
    apply (if_block)
    apply (call_api_func)
    apply (if_block)
    done
qed

lemma second_loop_good_multiple:
  assumes H1: "\<forall>i. ((i < x \<longrightarrow>
           (\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)))" 
  assumes H2: "x \<le> length coupons"
  assumes H3: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<And>n. \<exists>someotherloc. run_iter (n + 37 * x) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([second_loop]))
       [Label_context [] b_es 0 [], 
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           someloc,
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat 0))],
          f_inst = exp_inst\<rparr>)
      fcs ) =
run_iter n
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([second_loop]))
       [Label_context [] b_es 0 [], 
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           someotherloc,
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat x))],
          f_inst = exp_inst\<rparr>)
      fcs )"
  using H1 H2 H3
proof (induction x arbitrary: n)
  case 0
  then show ?case by auto
next
  case (Suc y)
  then have 1: "y < length coupons" 
        and 2: "(\<exists>li ri cl cr.
            get_tree_data_api l y = Some li \<and>
            get_tree_data_api r y = Some ri \<and>
            get_coupon_lhs (coupons ! y) = Some cl \<and>
            get_coupon_rhs (coupons ! y) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)"
    by auto

  have 3: "n + 37 + 37 * y = n + 37 * (Suc y)" by auto

  obtain someotherloc where "run_iter (n + 37 + 37 * y)
        (Config n'
          (init
           \<lparr>s.tabs :=
              (s.tabs init)
              [tab_coupons_idx :=
                 (T_tab \<lparr>l_min = 0, l_max = None\<rparr> T_ext_ref,
                  map (\<lambda>c. ConstRefExtern (to_externref c))
                   coupons)]\<rparr>)
          (Frame_context (Redex [] [] [second_loop])
            [Label_context [] b_es 0 [],
             Label_context [] [] (Suc 0) [],
             Label_context [] [] (Suc 0) [],
             Label_context [] [] (Suc 0) []]
            (Suc 0)
            \<lparr>f_locs =
               [V_ref (ConstRefExtern (to_externref l)),
                V_ref (ConstRefExtern (to_externref r)),
                someloc,
                V_num
                 (ConstInt32 (int_of_nat (length coupons))),
                V_num (ConstInt32 (int_of_nat 0))],
               f_inst = exp_inst\<rparr>)
          fcs) =
       run_iter (n + 37)
        (Config n'
          (init
           \<lparr>s.tabs :=
              (s.tabs init)
              [tab_coupons_idx :=
                 (T_tab \<lparr>l_min = 0, l_max = None\<rparr> T_ext_ref,
                  map (\<lambda>c. ConstRefExtern (to_externref c))
                   coupons)]\<rparr>)
          (Frame_context (Redex [] [] [second_loop])
            [Label_context [] b_es 0 [],
             Label_context [] [] (Suc 0) [],
             Label_context [] [] (Suc 0) [],
             Label_context [] [] (Suc 0) []]
            (Suc 0)
            \<lparr>f_locs =
               [V_ref (ConstRefExtern (to_externref l)),
                V_ref (ConstRefExtern (to_externref r)),
                someotherloc,
                V_num
                 (ConstInt32 (int_of_nat (length coupons))),
                V_num (ConstInt32 (int_of_nat y))],
               f_inst = exp_inst\<rparr>)
          fcs)"
    using Suc.IH[of "n + 37"] 1 2 Suc.prems by auto

  then show ?case using
      second_loop_internal_good[OF 1 2 Suc.prems(3)]
    by (metis 3)
qed

lemma second_loop_good:
  assumes H1: "\<forall>i. i < length coupons \<longrightarrow> (\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)"
  assumes H2: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<exists>someloc. run_iter (n + 6 + 37 * (length coupons)) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([second_loop]))
       [Label_context [] b_es 0 [], 
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat 0))],
          f_inst = exp_inst\<rparr>)
      fcs ) =
 run_iter n  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] b_es)
       [Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) []]
       (Suc 0)
             \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           someloc,
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      fcs)"
proof -
  have 1: "length coupons \<le> length coupons" by simp
  show ?thesis 
    using second_loop_good_multiple[OF H1 1 H2, of "n+6"]
          second_loop_last[of n n']
    by metis
qed

lemma second_loop_bad:
  assumes H1: "(\<exists>i. i < length coupons \<and> 
               (\<exists> li ri cl cr.
                get_tree_data_api l i = Some li \<and>
                get_tree_data_api r i = Some ri \<and>
                get_coupon_lhs (coupons ! i) = Some cl \<and>
                get_coupon_rhs (coupons ! i) = Some cr \<and>
               (\<not>is_equal li cl \<or> \<not>is_equal ri cr)) \<and>

               (\<forall>j < i. (\<exists> li ri cl cr.
                get_tree_data_api l j = Some li \<and>
                get_tree_data_api r j = Some ri \<and>
                get_coupon_lhs (coupons ! j) = Some cl \<and>
                get_coupon_rhs (coupons ! j) = Some cr \<and>
                is_equal li cl \<and>
                is_equal ri cr)))"
  assumes H2: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<exists>cfg msg. run_iter (n + 6 + 37 * (length coupons)) 
     (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] []
         ([second_loop]))
       [Label_context [] b_es 0 [], 
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) [],
        Label_context [] [] (Suc 0) []]
       (Suc 0)
       \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat 0))],
          f_inst = exp_inst\<rparr>)
      fcs ) = (cfg, RTrap msg)"
proof -
  obtain i where 1: "i < length coupons"
             and 2: "(\<exists> li ri cl cr.
                get_tree_data_api l i = Some li \<and>
                get_tree_data_api r i = Some ri \<and>
                get_coupon_lhs (coupons ! i) = Some cl \<and>
                get_coupon_rhs (coupons ! i) = Some cr \<and>
               (\<not>is_equal li cl \<or> \<not>is_equal ri cr))"
             and 3: "(\<forall>j < i. (\<exists> li ri cl cr.
                get_tree_data_api l j = Some li \<and>
                get_tree_data_api r j = Some ri \<and>
                get_coupon_lhs (coupons ! j) = Some cl \<and>
                get_coupon_rhs (coupons ! j) = Some cr \<and>
                is_equal li cl \<and>
                is_equal ri cr))"
    using H1 by auto

  have 4: "i \<le> length coupons" using 1 by auto

  have A: "n + 6 + 37 * (length coupons - i) - 37 + 37 = n + 6 + 37 * (length coupons - i)"
    using 1 by auto

  have B: "(n + 6 + 37 * (length coupons - i) + 37 * i) = n + 6 + 37 * (length coupons)"
    using 1 by auto

  show ?thesis
    using second_loop_internal_bad[OF 1 2 H2, of "(n + 6 + 37 * (length coupons - i) - 37)" n']
          second_loop_good_multiple[OF 3 4 H2, of "n + 6 + 37 * (length coupons - i)" n'] A B
    by metis
qed

definition first_be where
"first_be = [Local_get 0, Call 9, Local_get 3,
            Relop T_i32 (Relop_i relop_i.Eq),
            b_e.If (Tbv (Some (T_ref T_ext_ref)))
             [Local_get (Suc 0), Call 9, Local_get 3,
              Relop T_i32 (Relop_i relop_i.Eq),
              b_e.If (Tbv (Some (T_ref T_ext_ref)))
               [EConstNum (ConstInt32 (I32.lift0 0)), Local_set 4,
                Block (Tbv None)
                 [Loop (Tbv None)
                   [Local_get 4, Local_get 3, Relop T_i32 (Relop_i (Ge S)),
                    Br_if (Suc 0), Local_get 4, Table_get 0, Local_set 2,
                    Local_get 0, Local_get 4, Call 10, Local_get 2, Call 6,
                    Call 0,
                    b_e.If (Tbv None)
                     [Local_get (Suc 0), Local_get 4, Call 10, Local_get 2,
                      Call 7, Call 0, b_e.If (Tbv None) [Nop] [Unreachable]]
                     [Unreachable],
                    Local_get 4, EConstNum (ConstInt32 (I32.lift0 1)),
                    Binop T_i32 (Binop_i Add), Local_set 4, Br 0]],
                Local_get 0, Local_get (Suc 0), Call 8]
               [Unreachable]]
             [Unreachable]]"

lemma E1: "run_iter 
          (n + 5)
         (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_tree_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs) =
        run_iter
          n
          (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] [first_loop])
              [Label_context [] first_be 0 [], Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 V_ref (bitzero_ref T_ext_ref),
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (I32.lift0 0))],
              f_inst = exp_inst\<rparr>) 
            (Frame_context (Redex rest_vs [] b_es) lc f 
                \<lparr>f_locs = locs, f_inst = exp_inst \<rparr> # fcs))"
    apply (simp)
    apply (invoke_coupon_func fuel_idx_def: func_make_tree_coupon_idx_def)

    apply (rule_tac t="5" and s="Suc 4" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: init_def tab_coupons_idx_def n_zeros_def bitzero_def stab_ind_def split_n_0 split_n_1 split_n_2)

    apply (rule_tac t="4" and s="Suc 3" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_s_f_v_s_table_size_def stab_ind_def app_f_v_s_local_set_def)

    apply (rule_tac t="3" and s="Suc 2" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_s_f_v_s_table_size_def stab_ind_def app_f_v_s_local_set_def)

    apply (simp add: tb_tf_def first_loop_def first_be_def)
    done

definition second_be where
"second_be = [Local_get 0, Local_get (Suc 0), Call 8]"

lemma E3: 
  assumes H1: "get_tree_size_api l = Some (length coupons)"
      and H2: "get_tree_size_api r = Some (length coupons)"
shows "run_iter
    (n + 16)
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] first_be)
       [Label_context [] [] (Suc 0) []]
       (Suc 0)
          \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      fcs) =
            run_iter 
            n
            (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] [second_loop])
              [Label_context [] second_be 0 [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 V_ref (bitzero_ref T_ext_ref),
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (I32.lift0 0))],
              f_inst = exp_inst\<rparr>) fcs)"
   using fixpoint_get_tree_size_impl H1 H2
    apply (simp add: first_be_def init_def)
    apply (rule_tac t="16" and s="Suc 15" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="15" and s="Suc 14" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (rule_tac t="14" and s="Suc 13" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (rule_tac t="13" and s="Suc 12" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="12" and s="Suc 11" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def)
    apply (simp add: I32.int_eq_def I32.int_of_nat_def int_eq_i32.rep_eq
    int_of_nat_i32_def)

    apply (rule_tac t="11" and s="Suc 10" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_if_def st sff tb_tf_def wasm_bool_def)

    apply (rule_tac t="10" and s="Suc 9" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: tb_tf_def)

    apply (rule_tac t="9" and s="Suc 8" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="8" and s="Suc 7" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (rule_tac t="7" and s="Suc 6" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (rule_tac t="6" and s="Suc 5" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="5" and s="Suc 4" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def)
    apply (simp add: I32.int_eq_def I32.int_of_nat_def int_eq_i32.rep_eq
    int_of_nat_i32_def)

    apply (rule_tac t="4" and s="Suc 3" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_if_def st sff tb_tf_def wasm_bool_def)

    apply (rule_tac t="3" and s="Suc 2" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_set_def tb_tf_def)

    apply (simp add: second_loop_def second_be_def)
    done

lemma E3_err:
  assumes H1: "get_tree_size_api l = None \<or> 
           get_tree_size_api r = None \<or> 
           (\<exists>l'. get_tree_size_api l = Some l' \<and> l' \<noteq> length coupons) \<or>
           (\<exists>r'. get_tree_size_api r = Some r' \<and> r' \<noteq> length coupons)"
      and H2: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<exists>cfg msg. run_iter
    (n + 16)
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] first_be)
       [Label_context [] [] (Suc 0) []]
       (Suc 0)
          \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      fcs) = (cfg, RTrap msg)"
proof -
  let ?l_bad = "(get_tree_size_api l = None \<or> (\<exists>l'. get_tree_size_api l = Some l' \<and> l' \<noteq> length coupons \<and> l' <  2^(LENGTH(i32) - 1)))"
  let ?l_good = "(\<exists>l'. get_tree_size_api l = Some l' \<and> l' = length coupons)"
  let ?r_bad = "(get_tree_size_api r = None \<or> (\<exists>r'. get_tree_size_api r = Some r' \<and> r' \<noteq> length coupons \<and> r' <  2^(LENGTH(i32) - 1)))"

  have "?l_bad \<or> ?l_good" using tree_size_i32 by auto
  moreover have "?l_good \<longrightarrow> ?r_bad" using assms tree_size_i32 by force
  ultimately have assms: "?l_bad \<or> (?l_good \<and> ?r_bad)" by auto

  from assms H2 neq_32 show ?thesis
    using fixpoint_get_tree_size_impl
    apply (simp add: first_be_def init_def)
    apply (rule_tac t="16" and s="Suc 15" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="15" and s="Suc 14" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (rule_tac t="14" and s="Suc 13" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (erule disjE, simp)

    apply (erule disjE, erule exE, erule conjE, simp add: typeof_def typeof_num_def typeof_ref_def)
    apply (rule_tac t="13" and s="Suc 12" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="12" and s="Suc 11" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def)
    apply (simp add: I32.int_eq_def I32.int_of_nat_def int_eq_i32.rep_eq
    int_of_nat_i32_def)

    apply (rule_tac t="11" and s="Suc 10" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_if_def st sff tb_tf_def wasm_bool_def)

    apply (rule_tac t="10" and s="Suc 9" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: tb_tf_def)

    apply (rule_tac t="9" and s="Suc 8" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    (* l_good  r_bad *)
    apply (erule conjE, simp add: typeof_def typeof_num_def typeof_ref_def)
    apply (rule_tac t="13" and s="Suc 12" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="12" and s="Suc 11" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def)
    apply (simp add: I32.int_eq_def I32.int_of_nat_def int_eq_i32.rep_eq
    int_of_nat_i32_def)

    apply (rule_tac t="11" and s="Suc 10" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_if_def st sff tb_tf_def wasm_bool_def)

    apply (rule_tac t="10" and s="Suc 9" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: tb_tf_def)

    apply (rule_tac t="9" and s="Suc 8" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="8" and s="Suc 7" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (rule_tac t="7" and s="Suc 6" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (erule disjE, simp)
    apply (erule exE, erule conjE, simp add: typeof_def typeof_num_def typeof_ref_def)
    apply (rule_tac t="6" and s="Suc 5" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="5" and s="Suc 4" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_relop_def app_relop_def app_relop_i_v_def app_relop_i_def)
    apply (simp add: I32.int_eq_def I32.int_of_nat_def int_eq_i32.rep_eq
    int_of_nat_i32_def)

    apply (rule_tac t="4" and s="Suc 3" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_v_s_if_def st sff tb_tf_def wasm_bool_def)

    apply (rule_tac t="3" and s="Suc 2" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_set_def tb_tf_def)
    done
qed

lemma E6:
  "run_iter (n + 8)
            (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] second_be)
               [Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 someloc,
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (int_of_nat (length coupons)))],
              f_inst = exp_inst\<rparr>)   
             (Frame_context (Redex rest_vs [] b_es) lc f 
                \<lparr>f_locs = locs, f_inst = exp_inst \<rparr> # fcs))
= run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
 using fixpoint_create_eq_coupon_impl
    apply (simp add: second_be_def)
    apply (rule_tac t="8" and s="Suc 7" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)

    apply (rule_tac t="7" and s="Suc 6" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: app_f_v_s_local_get_def)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)
    apply (simp add: tab_coupons_idx_def)

    apply (rule_tac t="6" and s="Suc 5" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq init_def)

    apply (rule_tac t="5" and s="Suc 4" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp add: typeof_ref_def typeof_def)

    apply (rule_tac t="4" and s="Suc 3" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp)

    apply (rule_tac t="3" and s="Suc 2" in subst, simp)
    apply (subst add_Suc_right, subst run_iter.simps)
    apply (simp)
    done

lemma make_tree_coupon_raw_run_iter:
  assumes H1: "make_tree_coupon_raw coupons l r = Some res"
  assumes H2: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "run_iter 
          (n + 6 + 37 * (length coupons) + 6 + 17 * (length coupons) + 29)
         (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_tree_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 =
          run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
proof -
  let ?state = " (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr> )"

  have add_Suc_left: "\<And>m1 m2. Suc m1 + m2 = Suc (m1 + m2)"
    by simp

  have 1: "(\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i)))" 
   and 2: "get_tree_size_api l = Some (length coupons)"
   and 3: "get_tree_size_api r = Some (length coupons)" 
   and 4: "(\<forall>i. (i < length coupons \<longrightarrow>
           (\<exists>li ri cl cr.
            get_tree_data_api l i = Some li \<and>
            get_tree_data_api r i = Some ri \<and>
            get_coupon_lhs (coupons ! i) = Some cl \<and>
            get_coupon_rhs (coupons ! i) = Some cr \<and>
            is_equal li cl \<and>
            is_equal ri cr)))"
   and 5: "res = create_eq_coupon l r" using make_some[OF H1] by (blast+)

  let ?newfcs = "(Frame_context (Redex rest_vs [] b_es) lc f 
                \<lparr>f_locs = locs, f_inst = exp_inst \<rparr> # fcs)"

  have E1: "run_iter 
          (n + 6 + 37 * (length coupons) + 6 + 17 * (length coupons) + 29)
         (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_tree_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs) =
        run_iter
          (36 + (54 * (length coupons) + n))
          (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] [first_loop])
              [Label_context [] first_be 0 [], Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 V_ref (bitzero_ref T_ext_ref),
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (I32.lift0 0))],
              f_inst = exp_inst\<rparr>) ?newfcs)"
    using E1[of "36 + (54 * (length coupons) + n)"] by simp

  have E2: "... = run_iter (30 + n + 37 * (length coupons))  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] first_be)
       [Label_context [] [] (Suc 0) []]
       (Suc 0)
          \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      ?newfcs)"
    using first_loop_good[OF 1 H2, of "30 + n + 37 * length coupons" n' first_be l r ?newfcs]
    by (simp, rule_tac s="54 * (length coupons) + (36 + n)" and t="36  + (54 * (length coupons) + n)" in subst, simp, simp add: int_of_nat_i32.abs_eq)

  have E3: "... =
         run_iter (14 + n + 37 * (length coupons))
            (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] [second_loop])
              [Label_context [] second_be 0 [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 V_ref (bitzero_ref T_ext_ref),
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (I32.lift0 0))],
              f_inst = exp_inst\<rparr>) ?newfcs)"
    using E3[OF 2 3, of "14 + n + 37 * (length coupons)" n' ?newfcs]
    by (rule_tac t="30 + n + 37 * (length coupons)" and s="(14 + n + 37 * (length coupons)) + 16" in subst, simp_all)

  have E4: "\<exists>someloc. ... = run_iter (8 + n)
            (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] second_be)
               [Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 someloc,
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (int_of_nat (length coupons)))],
              f_inst = exp_inst\<rparr>) ?newfcs)"
    using second_loop_good[OF 4 H2, of "8 + n" n']
    by (simp add: int_of_nat_i32.abs_eq)

  obtain someloc where E5: "run_iter 
          (n + 6 + 37 * (length coupons) + 6 + 17 * (length coupons) + 29)
         (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_tree_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs) = 
run_iter (8 + n)
            (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] second_be)
               [Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 someloc,
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (int_of_nat (length coupons)))],
              f_inst = exp_inst\<rparr>) ?newfcs)"
    using E1 E2 E3 E4
    by presburger

  have E6: "... = run_iter n
          (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context (Redex (V_ref (ConstRefExtern (to_externref (create_eq_coupon l r))) # rest_vs) [] b_es) lc f  \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)"
    using E6
    by (rule_tac t="8 + n" and s="n + 8" in subst, simp)

  then show ?thesis using E5 E6
    by presburger
qed

lemma make_tree_coupon_raw_run_invoke_none:
  assumes H1: "make_tree_coupon_raw coupons l r = None"
  assumes H2: "length coupons < 2^(LENGTH(i32) - 1)"
  shows "\<exists>cfg msg. run_iter 
          (n + 6 + 37 * (length coupons) + 6 + 17 * (length coupons) + 29)
         (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_tree_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs)
 = (cfg, RTrap msg)"
proof -
  have H1: "(\<exists>i. i < length coupons \<and> \<not>is_eq_coupon_api (coupons ! i) 
                \<and> (\<forall>j < i. is_eq_coupon_api (coupons ! j))) \<or>
         ((\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i))) \<and>
          ((get_tree_size_api l = None \<or> 
            get_tree_size_api r = None \<or> 
            (\<exists>l'. get_tree_size_api l = Some l' \<and> l' \<noteq> length coupons) \<or>
            (\<exists>r'. get_tree_size_api r = Some r' \<and> r' \<noteq> length coupons)) \<or>
           (get_tree_size_api l = Some (length coupons) \<and>
            get_tree_size_api r = Some (length coupons) \<and>
            (\<exists>i. i < length coupons \<and> 
               (\<exists> li ri cl cr.
                get_tree_data_api l i = Some li \<and>
                get_tree_data_api r i = Some ri \<and>
                get_coupon_lhs (coupons ! i) = Some cl \<and>
                get_coupon_rhs (coupons ! i) = Some cr \<and>
               (\<not>is_equal li cl \<or> \<not>is_equal ri cr)) \<and>

               (\<forall>j < i. (\<exists> li ri cl cr.
                get_tree_data_api l j = Some li \<and>
                get_tree_data_api r j = Some ri \<and>
                get_coupon_lhs (coupons ! j) = Some cl \<and>
                get_coupon_rhs (coupons ! j) = Some cr \<and>
                is_equal li cl \<and>
                is_equal ri cr))))
))"
    using make_none[OF H1] .

  have add_Suc_left: "\<And>m1 m2. Suc m1 + m2 = Suc (m1 + m2)"
    by simp

  let ?newfcs = "(Frame_context (Redex rest_vs [] b_es) lc f 
                \<lparr>f_locs = locs, f_inst = exp_inst \<rparr> # fcs)"

  have E1: "run_iter 
          (n + 6 + 37 * (length coupons) + 6 + 17 * (length coupons) + 29)
         (Config 
           (Suc n')
           (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
           (Frame_context 
              (Redex ((V_ref (ConstRefExtern (to_externref r))) #
                      (V_ref (ConstRefExtern (to_externref l))) #
                      rest_vs)
                     [Invoke func_make_tree_coupon_idx]
                     b_es)
            lc f \<lparr>f_locs = locs, f_inst = exp_inst\<rparr>) fcs) =
        run_iter
          (36 + (54 * (length coupons) + n))
          (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] [first_loop])
              [Label_context [] first_be 0 [], Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 V_ref (bitzero_ref T_ext_ref),
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (I32.lift0 0))],
              f_inst = exp_inst\<rparr>) ?newfcs)"
    using E1[of "36 + (54 * (length coupons) + n)"] by simp

  from H1 show ?thesis
  proof
    assume assm: "\<exists>i<length coupons. \<not> is_eq_coupon_api (coupons ! i) \<and>
       (\<forall>j<i. is_eq_coupon_api (coupons ! j))"

    have "\<exists>cfg msg. run_iter
          (36 + (54 * (length coupons) + n))
          (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] [first_loop])
              [Label_context [] first_be 0 [], Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 V_ref (bitzero_ref T_ext_ref),
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (I32.lift0 0))],
              f_inst = exp_inst\<rparr>) ?newfcs) = (cfg, RTrap msg)"
      using first_loop_bad[OF assm H2, of "30 + n + 37 * length coupons" n' first_be l r ?newfcs]
      by (simp, rule_tac s="54 * (length coupons) + (36 + n)" and t="36  + (54 * (length coupons) + n)" in subst, simp, simp add: int_of_nat_i32.abs_eq)

    then show ?thesis using E1 by presburger
  next
    assume assm: "(\<forall>i<length coupons. is_eq_coupon_api (coupons ! i)) \<and>
    ((get_tree_size_api l = None \<or>
      get_tree_size_api r = None \<or>
      (\<exists>l'. get_tree_size_api l = Some l' \<and> l' \<noteq> length coupons) \<or>
      (\<exists>r'. get_tree_size_api r = Some r' \<and> r' \<noteq> length coupons)) \<or>
     get_tree_size_api l = Some (length coupons) \<and>
     get_tree_size_api r = Some (length coupons) \<and>
     (\<exists>i<length coupons.
         (\<exists>li ri cl cr.
             get_tree_data_api l i = Some li \<and>
             get_tree_data_api r i = Some ri \<and>
             get_coupon_lhs (coupons ! i) = Some cl \<and>
             get_coupon_rhs (coupons ! i) = Some cr \<and>
             (\<not> is_equal li cl \<or> \<not> is_equal ri cr)) \<and>
         (\<forall>j<i. \<exists>li ri cl cr.
                   get_tree_data_api l j = Some li \<and>
                   get_tree_data_api r j = Some ri \<and>
                   get_coupon_lhs (coupons ! j) = Some cl \<and>
                   get_coupon_rhs (coupons ! j) = Some cr \<and>
                   is_equal li cl \<and> is_equal ri cr)))"
    then have 1: "(\<forall>i<length coupons. is_eq_coupon_api (coupons ! i))"
          and 2: " ((get_tree_size_api l = None \<or>
      get_tree_size_api r = None \<or>
      (\<exists>l'. get_tree_size_api l = Some l' \<and> l' \<noteq> length coupons) \<or>
      (\<exists>r'. get_tree_size_api r = Some r' \<and> r' \<noteq> length coupons)) \<or>
     get_tree_size_api l = Some (length coupons) \<and>
     get_tree_size_api r = Some (length coupons) \<and>
     (\<exists>i<length coupons.
         (\<exists>li ri cl cr.
             get_tree_data_api l i = Some li \<and>
             get_tree_data_api r i = Some ri \<and>
             get_coupon_lhs (coupons ! i) = Some cl \<and>
             get_coupon_rhs (coupons ! i) = Some cr \<and>
             (\<not> is_equal li cl \<or> \<not> is_equal ri cr)) \<and>
         (\<forall>j<i. \<exists>li ri cl cr.
                   get_tree_data_api l j = Some li \<and>
                   get_tree_data_api r j = Some ri \<and>
                   get_coupon_lhs (coupons ! j) = Some cl \<and>
                   get_coupon_rhs (coupons ! j) = Some cr \<and>
                   is_equal li cl \<and> is_equal ri cr)))"
      by blast+


  have E2: "run_iter
          (36 + (54 * (length coupons) + n))
          (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] [first_loop])
              [Label_context [] first_be 0 [], Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 V_ref (bitzero_ref T_ext_ref),
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (I32.lift0 0))],
              f_inst = exp_inst\<rparr>) ?newfcs) 
= run_iter (30 + n + 37 * (length coupons))  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] first_be)
       [Label_context [] [] (Suc 0) []]
       (Suc 0)
             \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      ?newfcs)"
         using first_loop_good[OF 1 H2, of "30 + n + 37 * length coupons" n' first_be l r ?newfcs]
         by (simp, rule_tac s="54 * (length coupons) + (36 + n)" and t="36  + (54 * (length coupons) + n)" in subst, simp, simp add: int_of_nat_i32.abs_eq)

  from 2 show ?thesis
  proof
    assume 2: "get_tree_size_api l = None \<or>
               get_tree_size_api r = None \<or>
               (\<exists>l'. get_tree_size_api l = Some l' \<and> l' \<noteq> length coupons) \<or>
               (\<exists>r'. get_tree_size_api r = Some r' \<and> r' \<noteq> length coupons)"

    have "\<exists>cfg msg. run_iter (30 + n + 37 * (length coupons))  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] first_be)
       [Label_context [] [] (Suc 0) []]
       (Suc 0)
             \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      ?newfcs) = (cfg, RTrap msg)"
      using E3_err[OF 2 H2, of "(14 + n + 37 * (length coupons))" n' ?newfcs]
      by (rule_tac t="30 + n + 37 * (length coupons)" and s="(14 + n + 37 * (length coupons)) + 16" in subst, simp_all)

    then show ?thesis using E1 E2 by presburger
  next
    assume 2: "get_tree_size_api l = Some (length coupons) \<and>
               get_tree_size_api r = Some (length coupons) \<and>
               (\<exists>i<length coupons.
                   (\<exists>li ri cl cr.
                       get_tree_data_api l i = Some li \<and>
                       get_tree_data_api r i = Some ri \<and>
                       get_coupon_lhs (coupons ! i) = Some cl \<and>
                       get_coupon_rhs (coupons ! i) = Some cr \<and>
                       (\<not> is_equal li cl \<or> \<not> is_equal ri cr)) \<and>
                   (\<forall>j<i. \<exists>li ri cl cr.
                             get_tree_data_api l j = Some li \<and>
                             get_tree_data_api r j = Some ri \<and>
                             get_coupon_lhs (coupons ! j) = Some cl \<and>
                             get_coupon_rhs (coupons ! j) = Some cr \<and>
                             is_equal li cl \<and> is_equal ri cr))"

    have lenl: "get_tree_size_api l = Some (length coupons)"
     and lenr: "get_tree_size_api r = Some (length coupons)"
     and bad_loop: "(\<exists>i<length coupons.
                   (\<exists>li ri cl cr.
                       get_tree_data_api l i = Some li \<and>
                       get_tree_data_api r i = Some ri \<and>
                       get_coupon_lhs (coupons ! i) = Some cl \<and>
                       get_coupon_rhs (coupons ! i) = Some cr \<and>
                       (\<not> is_equal li cl \<or> \<not> is_equal ri cr)) \<and>
                   (\<forall>j<i. \<exists>li ri cl cr.
                             get_tree_data_api l j = Some li \<and>
                             get_tree_data_api r j = Some ri \<and>
                             get_coupon_lhs (coupons ! j) = Some cl \<and>
                             get_coupon_rhs (coupons ! j) = Some cr \<and>
                             is_equal li cl \<and> is_equal ri cr))"
      using 2 by blast+

    have E3: "run_iter (30 + n + 37 * (length coupons))  
    (Config n'
     (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
     (Frame_context
       (Redex [] [] first_be)
       [Label_context [] [] (Suc 0) []]
       (Suc 0)
             \<lparr>f_locs =
          [V_ref (ConstRefExtern (to_externref l)),
           V_ref (ConstRefExtern (to_externref r)),
           V_ref (bitzero_ref T_ext_ref),
           V_num (ConstInt32 (int_of_nat (length coupons))),
           V_num (ConstInt32 (int_of_nat (length coupons)))],
          f_inst = exp_inst\<rparr>)
      ?newfcs) =    
   run_iter (14 + n + 37 * (length coupons))
            (Config
             n'
            (init\<lparr> tabs := (tabs init)[tab_coupons_idx := ((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), (map (\<lambda>c. (ConstRefExtern (to_externref c))) coupons))] \<rparr>)
            (Frame_context 
              (Redex [] [] [second_loop])
              [Label_context [] second_be 0 [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) [], 
               Label_context [] [] (Suc 0) []] (Suc 0)
              \<lparr>f_locs =
                [V_ref (ConstRefExtern (to_externref l)),
                 V_ref (ConstRefExtern (to_externref r)),
                 V_ref (bitzero_ref T_ext_ref),
                 V_num (ConstInt32 (int_of_nat (length coupons))),
                 V_num (ConstInt32 (I32.lift0 0))],
              f_inst = exp_inst\<rparr>) ?newfcs)"
      using E3[OF lenl lenr, of "14 + n + 37 * (length coupons)" n' ?newfcs]
      by (rule_tac t="30 + n + 37 * (length coupons)" and s="(14 + n + 37 * (length coupons)) + 16" in subst, simp_all)

    have E4: "\<exists>cfg msg. ... = (cfg, RTrap msg)"
      using second_loop_bad[OF bad_loop H2, of "8 + n" n']
      by (simp add: int_of_nat_i32.abs_eq)

    show ?thesis using E1 E2 E3 E4 by presburger
    qed
  qed
qed

end
              

