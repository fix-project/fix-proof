theory Wasm_Proof_Playground 
  imports WebAssembly_Dev.Wasm_Interpreter WebAssembly_Dev.Wasm WebAssembly_Dev.Wasm_Ast
  WebAssembly_Dev.Wasm_Countable
  WebAssembly_Dev.Wasm_Base_Defs
  Init
begin

(* Helper lemmas for int_eqz *)
lemma se:
  "\<not> int_eq (I32.int_of_nat (Suc 0)) 0"
  by (simp add: I32.int_of_nat_def int_eq_i32_def Wasm_Ast.i32.Rep_i32_inject zero_i32_def I32.int_eq_def Wasm_Ast.i32.Abs_i32_inject)

lemma sf:
  "int_eq (I32.int_of_nat 0) 0"
  by (simp add: I32.int_eq_def I32.int_of_nat_def int_eq_i32.abs_eq zero_i32_def)

(* Given a fuel and depth that is enough to get to the result state, after run_iter, the result is a specific input argument *)
lemma init_run_iter:
  assumes "is_equal (to_handle r1) (to_handle r2)"
  shows "run_iter (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))) (Config (Suc n') init (Frame_context (Redex [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))] [Invoke 1] []) [] 0 empty_frame) []) = 
     (let v_s = [V_ref (ConstRefExtern r1)]
     in (Config (Suc n')
         init
         (Frame_context (Redex v_s [] []) [] 0 empty_frame) [],
         RValue v_s))"
  using fixpoint_is_equal_correct_externref[of r1 r2 init] assms
  by (auto split: cl.splits simp add: n_zeros_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def init_def app_v_s_if_def se tb_tf_def)

lemma init_run_iter_neq:
  assumes "\<not>is_equal (to_handle r1) (to_handle r2)"
  shows "run_iter (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n)))))))))))) (Config (Suc n') init (Frame_context (Redex [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))] [Invoke 1] []) [] 0 empty_frame) []) = 
     (let v_s = [V_ref (ConstRefExtern r2)]
     in (Config (Suc n')
         init
         (Frame_context (Redex v_s [] []) [] 0 empty_frame) [],
         RValue v_s))"
  using fixpoint_is_equal_correct_externref_neq[of r1 r2 init] assms
  by (auto split: cl.splits simp add: n_zeros_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def init_def app_v_s_if_def sf tb_tf_def)

(* From the run_iter lemmas, one step out to the run_invoke lemmas *)
lemma init_run_invoke:
  assumes "is_equal (to_handle r1) (to_handle r2)" 
  shows "run_invoke_v (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))
   (Suc 0) (init, [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))], 1) = (init, RValue [V_ref (ConstRefExtern r1)])"
proof -
  have X: "run_iter (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))) (Config (Suc 0) init (Frame_context (Redex [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))] [Invoke 1] []) [] 0 empty_frame) []) = 
     (let v_s = [V_ref (ConstRefExtern r1)]
     in (Config (Suc 0)
         init
         (Frame_context (Redex v_s [] []) [] 0 empty_frame) [],
         RValue v_s))"
    using init_run_iter assms by auto

  have Y: "rev [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] = [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))]"
    by auto

  show ?thesis
    apply (auto split: config.splits simp only: X run_invoke_v.simps Y case_prod_conv)
    apply (auto split: config.splits)
    apply (metis case_prod_conv config.case)
    done
qed

lemma init_run_invoke_neq:
  assumes "\<not>is_equal (to_handle r1) (to_handle r2)" 
  shows "run_invoke_v (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))
   (Suc 0) (init, [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))], 1) = (init, RValue [V_ref (ConstRefExtern r2)])"
proof -
  have X: "run_iter (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))) (Config (Suc 0) init (Frame_context (Redex [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))] [Invoke 1] []) [] 0 empty_frame) []) = 
     (let v_s = [V_ref (ConstRefExtern r2)]
     in (Config (Suc 0)
         init
         (Frame_context (Redex v_s [] []) [] 0 empty_frame) [],
         RValue v_s))"
    using init_run_iter_neq assms by auto

  have Y: "rev [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))] = [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))]"
    by auto

  show ?thesis
    apply (auto split: config.splits simp only: X run_invoke_v.simps Y case_prod_conv)
    apply (auto split: config.splits)
    apply (metis case_prod_conv config.case)
    done
qed

fun isabelle_func :: "handle \<Rightarrow> handle \<Rightarrow> handle" where
  "isabelle_func h1 h2 = (if (is_equal h1 h2) then h1 else h2)"

(* Now we show that the function at index 1 is equivalent to the isabelle function such that there exists a fuel and depth such that for any pair of input handles, translating those to externrefs and invoking the function with the fuel and depth returns a result that is the same as translating the isabelle function output to an externref.*)
lemma func_equiv:
  "\<exists>f d s.
   run_invoke_v f d 
   (init, 
   [V_ref (ConstRefExtern (to_externref h1)), 
    V_ref (ConstRefExtern (to_externref h2))], 1) 
   = (s, RValue [V_ref (ConstRefExtern (to_externref (isabelle_func h1 h2)))])"
  by (metis init_run_invoke init_run_invoke_neq isabelle_func.simps to_handle_to_externref)

end
