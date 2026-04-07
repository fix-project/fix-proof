theory Host
  imports WebAssembly_Dev.Wasm_Ast WebAssembly_Dev.Wasm_Interpreter WebAssembly_Dev.Wasm_Base_Defs coupon
begin

(* Establish translation between externref and handles *)
consts to_externref :: "handle \<Rightarrow> host" 
consts to_handle :: "host \<Rightarrow> handle"

axiomatization where
  to_externref_to_handle[simp]: "to_externref (to_handle x) = x"
and
  to_handle_to_externref[simp]: "to_handle (to_externref y) = y"

definition type_rr_i32 :: "tf" where [simp]:
  "type_rr_i32 = Tf [(T_ref T_ext_ref), (T_ref T_ext_ref)] [(T_num T_i32)]"
definition type_r_i32 :: "tf" where [simp]:
  "type_r_i32 = Tf [(T_ref T_ext_ref)] [(T_num T_i32)]"
definition type_r_r :: "tf" where [simp]:
  "type_r_r = Tf [(T_ref T_ext_ref)] [(T_ref T_ext_ref)]"
definition type_rr_r :: "tf" where [simp]:
  "type_rr_r = Tf [(T_ref T_ext_ref), (T_ref T_ext_ref)] [(T_ref T_ext_ref)]"
definition type_ri32_r :: "tf" where [simp]:
  "type_ri32_r = Tf [(T_ref T_ext_ref), (T_num T_i32)] [(T_ref T_ext_ref)]"

(* Fixpoint APIs exposed to Wasm modules *)
consts fixpoint_is_equal :: host_func
consts fixpoint_is_storage_coupon :: host_func
consts fixpoint_is_force_coupon :: host_func
consts fixpoint_is_eq_coupon :: host_func
consts fixpoint_create_thunk :: host_func
consts fixpoint_create_encode :: host_func
consts fixpoint_get_coupon_lhs :: host_func
consts fixpoint_get_coupon_rhs :: host_func
consts fixpoint_create_eq_coupon :: host_func
consts fixpoint_get_tree_size :: host_func
consts fixpoint_get_tree_data :: host_func

axiomatization where
  (* We are stating here that the exposed fixpoint_is_equal is the same as
     isabelle is_equal given the declared (host from/to externref) and (bool from/to i32) translations *)
  fixpoint_is_equal_impl:
  "host_func_apply_impl s type_rr_i32 fixpoint_is_equal 
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))]
  = Some (s, [V_num (ConstInt32 (wasm_bool (is_equal (to_handle r1) (to_handle r2))))])"
and
  fixpoint_is_storage_coupon_impl:
  "host_func_apply_impl s type_r_i32 fixpoint_is_storage_coupon
  [(V_ref (ConstRefExtern r))] 
  = Some (s, [V_num (ConstInt32 (wasm_bool (is_storage_coupon_api (to_handle r))))])"
and
  fixpoint_is_force_coupon_impl:
  "host_func_apply_impl s type_r_i32 fixpoint_is_force_coupon
  [(V_ref (ConstRefExtern r))] 
  = Some (s, [V_num (ConstInt32 (wasm_bool (is_force_coupon_api (to_handle r))))])"
and
  fixpoint_is_eq_coupon_impl:
  "host_func_apply_impl s type_r_i32 fixpoint_is_eq_coupon
  [(V_ref (ConstRefExtern r))] 
  = Some (s, [V_num (ConstInt32 (wasm_bool (is_eq_coupon_api (to_handle r))))])"
and
  fixpoint_create_thunk_impl:
  "host_func_apply_impl s type_r_r fixpoint_create_thunk
  [(V_ref (ConstRefExtern r))] 
  = map_option (\<lambda>h. (s, [V_ref (ConstRefExtern (to_externref h))])) (create_thunk_api (to_handle r))"
and
  fixpoint_create_encode_impl:
  "host_func_apply_impl s type_r_r fixpoint_create_encode
  [(V_ref (ConstRefExtern r))] 
  = map_option (\<lambda>h. (s, [V_ref (ConstRefExtern (to_externref h))])) (create_encode_api (to_handle r))"
and
  fixpoint_get_coupon_lhs_impl:
  "host_func_apply_impl s type_r_r fixpoint_get_coupon_lhs 
  [(V_ref (ConstRefExtern r))] 
  = map_option (\<lambda>h. (s, [V_ref (ConstRefExtern (to_externref h))])) (get_coupon_lhs (to_handle r))" 
and
  fixpoint_get_coupon_rhs_impl:
  "host_func_apply_impl s type_r_r fixpoint_get_coupon_rhs 
  [(V_ref (ConstRefExtern r))] 
  = map_option (\<lambda>h. (s, [V_ref (ConstRefExtern (to_externref h))])) (get_coupon_rhs (to_handle r))" 
and
  fixpoint_create_eq_coupon_impl:
  "host_func_apply_impl s type_rr_r fixpoint_create_eq_coupon
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] 
  = Some (s, [V_ref (ConstRefExtern (to_externref (create_eq_coupon (to_handle r1) (to_handle r2))))])"
and
  fixpoint_get_tree_size_impl:
  "host_func_apply_impl s type_r_i32 fixpoint_get_tree_size
  [(V_ref (ConstRefExtern r))]
  = map_option (\<lambda>n. (s, [V_num (ConstInt32 (I32.int_of_nat n))])) (get_tree_size_api (to_handle r))"
and
  fixpoint_get_tree_data_impl:
  "host_func_apply_impl s type_ri32_r fixpoint_get_tree_data
  [(V_ref (ConstRefExtern r)), (V_num (ConstInt32 n))]
  = map_option (\<lambda>h. (s, [V_ref (ConstRefExtern (to_externref h))])) (get_tree_data_api (to_handle r) (I32.nat_of_int n))"


(* Helper lemmas for simplifying bool_to_i32 from the axiom statement *)
lemma fixpoint_is_equal_correct_externref:
  "is_equal (to_handle r1) (to_handle r2) \<longleftrightarrow> host_func_apply_impl s type_rr_i32 fixpoint_is_equal 
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 1))])"
  by (simp only: fixpoint_is_equal_impl, cases "is_equal (to_handle r1) (to_handle r2)") (auto simp add: I32.int_of_nat_def wasm_bool.abs_eq i32.Abs_i32_inject)

lemma fixpoint_is_equal_correct_externref_neq:
  "\<not>is_equal (to_handle r1) (to_handle r2) \<longleftrightarrow> host_func_apply_impl s type_rr_i32 fixpoint_is_equal 
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 0))])"
  by (simp only: fixpoint_is_equal_impl, cases "is_equal (to_handle r1) (to_handle r2)") (auto simp add: I32.int_of_nat_def wasm_bool.abs_eq i32.Abs_i32_inject)

lemma fixpoint_is_storage_coupon_externref:
  "is_storage_coupon_api (to_handle r) \<longleftrightarrow> host_func_apply_impl s type_r_i32
   fixpoint_is_storage_coupon
   [(V_ref (ConstRefExtern r))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 1))])"
  by (simp only: fixpoint_is_storage_coupon_impl, cases "is_storage_coupon_api (to_handle r)") (auto simp add: I32.int_of_nat_def wasm_bool.abs_eq i32.Abs_i32_inject)

lemma fixpoint_is_storage_coupon_externref_neq:
  "\<not>is_storage_coupon_api (to_handle r) \<longleftrightarrow> host_func_apply_impl s type_r_i32
   fixpoint_is_storage_coupon
   [(V_ref (ConstRefExtern r))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 0))])"
  by (simp only: fixpoint_is_storage_coupon_impl, cases "is_storage_coupon_api (to_handle r)") (auto simp add: I32.int_of_nat_def wasm_bool.abs_eq i32.Abs_i32_inject)
end