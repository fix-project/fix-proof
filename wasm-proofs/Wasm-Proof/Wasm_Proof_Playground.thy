theory Wasm_Proof_Playground 
  imports WebAssembly_Dev.Wasm_Interpreter WebAssembly_Dev.Wasm WebAssembly_Dev.Wasm_Ast WebAssembly_Dev.Wasm_Interpreter_Properties
begin

lemma sc:
"(app_binop_i Add (I32.int_of_nat 1) (I32.int_of_nat 2)) = Some (int_add (I32.int_of_nat 1) (I32.int_of_nat 2))" 
  by (simp add: app_binop_i_def)

thm "I32.rep_abs"
find_theorems name: "rep_abs" 

lemma sd:
"app_binop_i Add (I32.int_of_nat 1) (I32.int_of_nat 2) = Some (I32.int_of_nat 3)" 
proof -
  have "int_add (I32.int_of_nat 1) (I32.int_of_nat 2) = I32.int_of_nat 3"
    by (simp add: I32.int_add_def I32.int_of_nat_def int_add_i32_def I32.rep_abs)
  then show ?thesis using sc by auto
qed

lemma run_iter_with_locals:
  "run_iter (Suc (Suc (Suc n)))
             (Config d s 
             (Frame_context (Redex [] [] [(Local_get 0), (Local_get 1), (Binop T_i32 (Binop_i Add))]) lcs nf 
             (\<lparr>f_locs = [V_num (ConstInt32 (I32.int_of_nat 1)), V_num (ConstInt32 (I32.int_of_nat 2))], f_inst = inst \<rparr>)) fcs) =
   run_iter n (Config d s 
               (Frame_context (Redex [(V_num (ConstInt32 (I32.int_of_nat 3)))] [] []) lcs nf 
               (\<lparr>f_locs = [V_num (ConstInt32 (I32.int_of_nat 1)), V_num (ConstInt32 (I32.int_of_nat 2))], f_inst = inst \<rparr>)) fcs)"
  using app_f_v_s_local_get_def app_v_s_binop_def app_binop_def app_binop_i_v_def sd by auto
end