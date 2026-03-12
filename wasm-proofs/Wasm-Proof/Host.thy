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

definition type0 :: "tf" where [simp]:
  "type0 = Tf [(T_ref T_ext_ref), (T_ref T_ext_ref)] [(T_num T_i32)]"
definition type1 :: "tf" where [simp]:
  "type1 = Tf [(T_ref T_ext_ref)] [(T_num T_i32)]"
definition type2 :: "tf" where [simp]:
  "type2 = Tf [(T_ref T_ext_ref)] [(T_ref T_ext_ref)]"
definition type3 :: "tf" where [simp]:
  "type3 = Tf [(T_ref T_ext_ref), (T_ref T_ext_ref)] [(T_ref T_ext_ref)]"

(* functions and lemmas for translating between isabelle bool and wasm i32*)
fun bool_to_i32 :: "bool \<Rightarrow> i32" where
  "bool_to_i32 False = (I32.int_of_nat 0)"
| "bool_to_i32 True = (I32.int_of_nat 1)"

lemma i32_one_ne_zero:
  "(I32.lift0 1) \<noteq> I32.lift0 0"
  by transfer simp

lemma bool_to_i32_true:
  "bool_to_i32 a = (I32.int_of_nat 1) \<longleftrightarrow> a"
proof
  assume assms: "bool_to_i32 a = (I32.int_of_nat 1)"
  show "a"
  proof (cases "a")
    case True
    then show ?thesis by auto
  next
    case False
    then have "bool_to_i32 a = (I32.int_of_nat 0)" by auto
    then show ?thesis
      using I32.int_of_nat_def assms i32_one_ne_zero int_of_nat_i32.abs_eq by auto
  qed
next
  assume a
  then show "bool_to_i32 a = (I32.int_of_nat 1)" by auto
qed

lemma bool_to_i32_false:
  "bool_to_i32 a = (I32.int_of_nat 0) \<longleftrightarrow> \<not>a"
  by (metis bool_to_i32.elims bool_to_i32_true)

(* Fixpoint APIs exposed to Wasm modules *)
consts fixpoint_is_equal :: host_func
consts fixpoint_is_storage_coupon_api :: host_func
consts fixpoint_get_coupon_lhs :: host_func
consts fixpoint_get_coupon_rhs :: host_func
consts fixpoint_create_eq_coupon :: host_func

axiomatization where
  (* We are stating here that the exposed fixpoint_is_equal is the same as
     isabelle is_equal given the declared (host from/to externref) and (bool from/to i32) translations *)
  fixpoint_is_equal_impl:
  "host_func_apply_impl s type0 fixpoint_is_equal 
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))]
  = Some (s, [V_num (ConstInt32 (bool_to_i32 (is_equal (to_handle r1) (to_handle r2))))])"
and
  fixpoint_is_storage_coupon_api_impl:
  "host_func_apply_impl s type1 fixpoint_is_storage_coupon_api 
  [(V_ref (ConstRefExtern r))] 
  = Some (s, [V_num (ConstInt32 (bool_to_i32 (is_storage_coupon_api (to_handle r))))])"
and
  fixpoint_get_coupon_lhs_impl:
  "host_func_apply_impl s type2 fixpoint_get_coupon_lhs 
  [(V_ref (ConstRefExtern r))] 
  = map_option (\<lambda>h. (s, [V_ref (ConstRefExtern (to_externref h))])) (get_coupon_lhs (to_handle r))" 
and
  fixpoint_get_coupon_rhs_impl:
  "host_func_apply_impl s type2 fixpoint_get_coupon_rhs 
  [(V_ref (ConstRefExtern r))] 
  = map_option (\<lambda>h. (s, [V_ref (ConstRefExtern (to_externref h))])) (get_coupon_rhs (to_handle r))" 
and
  fixpoint_create_eq_coupon_impl:
  "host_func_apply_impl s type3 fixpoint_create_eq_coupon
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] 
  = Some (s, [V_ref (ConstRefExtern (to_externref (create_eq_coupon (to_handle r1) (to_handle r2))))])"

(* Helper lemmas for simplifying bool_to_i32 from the axiom statement *)
lemma fixpoint_is_equal_correct_externref:
  "is_equal (to_handle r1) (to_handle r2) \<longleftrightarrow> host_func_apply_impl s type0 fixpoint_is_equal 
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 1))])"
  using fixpoint_is_equal_impl bool_to_i32_true by auto

lemma fixpoint_is_equal_correct_externref_neq:
  "\<not>is_equal (to_handle r1) (to_handle r2) \<longleftrightarrow> host_func_apply_impl s type0 fixpoint_is_equal 
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 0))])"
  using bool_to_i32_false fixpoint_is_equal_impl by auto

lemma fixpoint_is_storage_coupon_api_externref:
  "is_storage_coupon_api (to_handle r) \<longleftrightarrow> host_func_apply_impl s type1
   fixpoint_is_storage_coupon_api
   [(V_ref (ConstRefExtern r))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 1))])"
  using bool_to_i32_true fixpoint_is_storage_coupon_api_impl by auto

lemma fixpoint_is_storage_coupon_api_externref_neq:
  "\<not>is_storage_coupon_api (to_handle r) \<longleftrightarrow> host_func_apply_impl s type1
   fixpoint_is_storage_coupon_api
   [(V_ref (ConstRefExtern r))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 0))])"
  using bool_to_i32_false fixpoint_is_storage_coupon_api_impl by auto
end