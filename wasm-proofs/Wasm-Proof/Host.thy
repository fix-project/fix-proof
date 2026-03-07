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

definition type0 :: "tf" where 
  "type0 = Tf [(T_ref T_ext_ref), (T_ref T_ext_ref)] [(T_num T_i32)]"

consts fixpoint_is_equal :: host_func

fun bool_to_i32 :: "bool \<Rightarrow> i32" where
  "bool_to_i32 False = (I32.int_of_nat 0)"
| "bool_to_i32 True = (I32.int_of_nat 1)"

lemma i32_one_ne_zero[simp]:
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
    then have "bool_to_i32 a = (I32.int_of_nat 0)"  by auto
    then show ?thesis using assms I32.int_of_nat_def by auto
  qed
next
  assume a
  then show "bool_to_i32 a = (I32.int_of_nat 1)" by auto
qed

axiomatization where
  fixpoint_is_equal_impl:
  "host_func_apply_impl s type0 fixpoint_is_equal 
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))]
  = Some (s, [V_num (ConstInt32 (bool_to_i32 (is_equal (to_handle r1) (to_handle r2))))])"

term "ConstInt32 (I32.int_of_nat 1)"

lemma fixpoint_is_equal_correct_handle:
  "is_equal h1 h2 \<longleftrightarrow> host_func_apply_impl s type0 fixpoint_is_equal 
  [(V_ref (ConstRefExtern (to_externref h1))), (V_ref (ConstRefExtern (to_externref h2)))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 1))])"
  using fixpoint_is_equal_impl bool_to_i32_true by auto

lemma fixpoint_is_equal_correct_externref:
  "is_equal (to_handle r1) (to_handle r2) \<longleftrightarrow> host_func_apply_impl s type0 fixpoint_is_equal 
  [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] = Some(s, [V_num (ConstInt32 (I32.int_of_nat 1))])"
  using fixpoint_is_equal_impl bool_to_i32_true by auto

end