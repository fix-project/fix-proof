theory custom_method
  imports Wasm_Proof_Playground util
begin

method invoke_coupon_func uses fuel_idx_def =
(simp del: split_n.simps add: fuel_idx_def init_def tab_coupons_idx_def n_zeros_def bitzero_def stab_ind_def split_n_0 split_n_1 split_n_2)

method table_get_local_set =
 (simp del: split_n.simps add: load_tabs1_def app_s_f_v_s_table_get_def stab_ind_def app_f_v_s_local_set_def)

method call_api_func =
(simp del: split_n.simps add: n_zeros_def bitzero_def split_n_0 split_n_1 split_n_2 app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def typeof_ref_def nat_of_int_i32.abs_eq)

method and_wasm_bool =
(simp del: split_n.simps add: wasm_bool_def app_v_s_binop_def and_00 and_01 and_10 and_11)

method if_block =
(simp add: app_v_s_if_def st sff tb_tf_def wasm_bool_def)

end
