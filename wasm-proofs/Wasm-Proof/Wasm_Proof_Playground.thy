theory Wasm_Proof_Playground 
  imports WebAssembly_Dev.Wasm_Interpreter WebAssembly_Dev.Wasm WebAssembly_Dev.Wasm_Ast WebAssembly_Dev.Wasm_Interpreter_Properties Host Init
begin

lemma valid_local_get:
  assumes "k < length (f_locs f)"
  shows "run_step_b_e (Local_get k) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs) = (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) (((f_locs f)!k)#v_s) []) fcs, Step_normal)"
  using app_f_v_s_local_get_def assms by auto

lemma with_locals: 
  "run_step_b_e (Local_get 0) 
  (Config d s ((Frame_context (Redex v_s es b_es) lcs nf (\<lparr>f_locs = [V_num (ConstInt32 (I32.int_of_nat 1)) ], f_inst = inst\<rparr>))) fcs) 
  = (Config d s 
  (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf (\<lparr>f_locs = [V_num (ConstInt32 (I32.int_of_nat 1)) ], f_inst = inst\<rparr>))) ((V_num (ConstInt32 (I32.int_of_nat 1)))#v_s) []) fcs, Step_normal)" using app_f_v_s_local_get_def by auto

lemma with_locals_new: 
  "run_step_b_e (Local_get 0) 
  (Config d s ((Frame_context (Redex v_s es b_es) lcs nf (\<lparr>f_locs = [V_num (ConstInt32 (I32.int_of_nat 1)) ], f_inst = inst\<rparr>))) fcs) 
  = 
  ((Config d s ((Frame_context (Redex ((V_num (ConstInt32 (I32.int_of_nat 1)))#v_s) es b_es) lcs nf (\<lparr>f_locs = [V_num (ConstInt32 (I32.int_of_nat 1)) ], f_inst = inst\<rparr>))) fcs), Step_normal) "
  using app_f_v_s_local_get_def by auto
           
lemma sb: "int_add (I32.int_of_nat 1) (I32.int_of_nat 2)= (I32.int_of_nat 3)" by (rule  Uint8.uint8.of_class_interval_bot  Uint8.uint8.of_class_interval_top)

lemma sc:
"(app_binop_i Add (I32.int_of_nat 1) (I32.int_of_nat 2)) = Some (int_add (I32.int_of_nat 1) (I32.int_of_nat 2))" by (simp add: app_binop_i_def)

lemma sd:
"app_binop_i Add (I32.int_of_nat 1) (I32.int_of_nat 2) = Some (I32.int_of_nat 3)"
  using sb sc by auto

lemma run_iter_with_locals:
  "run_iter (Suc (Suc (Suc n)))
             (Config d s 
             (Frame_context (Redex [] [] [(Local_get 0), (Local_get 1), (Binop T_i32 (Binop_i Add))]) lcs nf 
             (\<lparr>f_locs = [V_num (ConstInt32 (I32.int_of_nat 1)), V_num (ConstInt32 (I32.int_of_nat 2))], f_inst = inst \<rparr>)) fcs) =
   run_iter n (Config d s 
               (Frame_context (Redex [(V_num (ConstInt32 (I32.int_of_nat 3)))] [] []) lcs nf 
               (\<lparr>f_locs = [V_num (ConstInt32 (I32.int_of_nat 1)), V_num (ConstInt32 (I32.int_of_nat 2))], f_inst = inst \<rparr>)) fcs)"
  using app_f_v_s_local_get_def app_v_s_binop_def app_binop_def app_binop_i_v_def app_binop_i_def sd by auto
end