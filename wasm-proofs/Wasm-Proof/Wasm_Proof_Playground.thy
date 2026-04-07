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

lemma st:
  "\<not> int_eq (I32.lift0 1) 0"
  by (simp add: I32.int_eq_def I32.rep_0 I32.rep_abs
      int_eq_i32.rep_eq)

lemma sf:
  "int_eq (I32.int_of_nat 0) 0"
  by (simp add: I32.int_eq_def I32.int_of_nat_def int_eq_i32.abs_eq zero_i32_def)

lemma sff:
  "int_eq (I32.lift0 0) 0"
  by (simp add: I32.int_eq_def I32.rep_0 I32.rep_abs
      int_eq_i32.rep_eq)


definition fuel50 :: "nat \<Rightarrow> nat" where [simp]:
"fuel50 n =
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))))))))))))))))))))))))))))))))))))))))))))))"

lemma fifty_is_fifty:
"n + 50 =
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))))))))))))))))))))))))))))))))))))))))))))))"
  by auto

(* Given a fuel and depth that is enough to get to the result state, after run_iter, the result is a specific input argument *)
lemma init_run_iter:
  assumes "is_equal (to_handle r1) (to_handle r2)"
  shows "run_iter (fuel50 n) (Config (Suc n') init (Frame_context (Redex [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))] [Invoke func_ret_idx] []) [] 0 empty_frame) []) = 
     (let v_s = [V_ref (ConstRefExtern r1)]
     in (Config (Suc n')
         init
         (Frame_context (Redex v_s [] []) [] 0 empty_frame) [],
         RValue v_s))"
  using fixpoint_is_equal_correct_externref[of r1 r2 init] assms
  by (auto split: cl.splits simp add: n_zeros_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def init_def app_v_s_if_def se tb_tf_def func_ret_idx_def)

lemma init_run_iter_neq:
  assumes "\<not>is_equal (to_handle r1) (to_handle r2)"
  shows "run_iter (fuel50 n) (Config (Suc n') init (Frame_context (Redex [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))] [Invoke func_ret_idx] []) [] 0 empty_frame) []) = 
     (let v_s = [V_ref (ConstRefExtern r2)]
     in (Config (Suc n')
         init
         (Frame_context (Redex v_s [] []) [] 0 empty_frame) [],
         RValue v_s))"
  using fixpoint_is_equal_correct_externref_neq[of r1 r2 init] assms
  by (auto split: cl.splits simp add: n_zeros_def app_f_v_s_local_get_def app_f_call_def sfunc_ind_def typeof_def typeof_num_def init_def app_v_s_if_def sf tb_tf_def func_ret_idx_def fixpoint_is_equal_impl)

(* From the run_iter lemmas, one step out to the run_invoke lemmas *)
lemma init_run_invoke:
  assumes "is_equal (to_handle r1) (to_handle r2)" 
  shows "run_invoke_v (fuel50 n)
   (Suc 0) (init, [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))], func_ret_idx) = (init, RValue [V_ref (ConstRefExtern r1)])"
proof -
  have X: "run_iter (fuel50 n) (Config (Suc 0) init (Frame_context (Redex [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))] [Invoke func_ret_idx] []) [] 0 empty_frame) []) = 
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
  shows "run_invoke_v (fuel50 n)
   (Suc 0) (init, [(V_ref (ConstRefExtern r1)), (V_ref (ConstRefExtern r2))], func_ret_idx) = (init, RValue [V_ref (ConstRefExtern r2)])"
proof -
  have X: "run_iter (fuel50 n) (Config (Suc 0) init (Frame_context (Redex [(V_ref (ConstRefExtern r2)), (V_ref (ConstRefExtern r1))] [Invoke func_ret_idx] []) [] 0 empty_frame) []) = 
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
    V_ref (ConstRefExtern (to_externref h2))], func_ret_idx) 
   = (s, RValue [V_ref (ConstRefExtern (to_externref (isabelle_func h1 h2)))])"
  by (metis init_run_invoke init_run_invoke_neq isabelle_func.simps to_handle_to_externref)

definition exp_inst :: "inst" where [simp]: 
"exp_inst = \<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>"

lemma split_n_0: 
"split_n (rest_vs) 0 = ([], rest_vs)"
  by (simp add: split_n_conv_take_drop)

lemma split_n_1: 
"split_n (h1 # rest_vs) (Suc 0) = ([h1], rest_vs)"
  by (simp add: split_n_conv_take_drop)

lemma split_n_2: 
"split_n (h1 # h2 # rest_vs) (Suc (Suc 0)) = ([h1, h2], rest_vs)"
  by (simp add: split_n_conv_take_drop)

end