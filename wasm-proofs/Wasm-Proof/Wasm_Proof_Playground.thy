theory Wasm_Proof_Playground imports WebAssembly_Dev.Wasm_Interpreter WebAssembly_Dev.Wasm WebAssembly_Dev.Wasm_Ast WebAssembly_Dev.Wasm_Interpreter_Properties begin

lemma wasm_function: "run_step_b_e (Binop T_i32 (Binop_i Add)) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs) =( let (v_s', res) = (app_v_s_binop (Binop_i Add) v_s) in
        ((Config d s (update_fc_step (Frame_context (Redex v_s es b_es) lcs nf f) v_s' []) fcs), res))"
  by auto

lemma wasm_args: "run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs) = (let (v_s', res) = (app_f_v_s_local_get 0 f v_s) in
        (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) v_s' []) fcs, res))"
  by auto                                                       

lemma app_local_no_crash:
  assumes "k < length (f_locs f)"
  shows "snd(app_f_v_s_local_get k f v_s) = Step_normal"                                 
  using assms        
  unfolding app_f_v_s_local_get_def
  by auto

lemma no_crash: 
  assumes "0 < length (f_locs f)"
  shows "snd (run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs)) = Step_normal"
proof -
  have "run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs) = (let (v_s', res) = (app_f_v_s_local_get 0 f v_s) in
        (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) v_s' []) fcs, res))" using wasm_args by auto
  then have X: "snd(run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs)) = (snd(let (v_s', res) = (app_f_v_s_local_get 0 f v_s) in
        (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) v_s' []) fcs, res)))" by auto

  have " (snd(let (v_s', res) = (app_f_v_s_local_get 0 f v_s) in
        (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) v_s' []) fcs, res))) = (snd (app_f_v_s_local_get 0 f v_s))"
    using snd_def by (cases "app_f_v_s_local_get 0 f v_s") auto
                                  
  then have "snd(run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs)) = (snd (app_f_v_s_local_get 0 f v_s))" using X by auto
  then show ?thesis using app_local_no_crash assms by auto
qed     

lemma app_local_updates_stack:
  assumes "k < length (f_locs f)"
  shows "fst(app_f_v_s_local_get k f v_s) = ((f_locs f)!k)#v_s"
  using assms
  unfolding app_f_v_s_local_get_def
  by auto


lemma stack_update:
  assumes "0 < length (f_locs f)"
  shows "fst (run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs)) = (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) (((f_locs f)!0)#v_s) []) fcs)"
proof -
  have "run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs) = (let (v_s', res) = (app_f_v_s_local_get 0 f v_s) in
        (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) v_s' []) fcs, res))" using wasm_args by auto
  then have X: "fst(run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs)) = (fst(let (v_s', res) = (app_f_v_s_local_get 0 f v_s) in
        (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) v_s' []) fcs, res)))" by auto

  have " (fst(let (v_s', res) = (app_f_v_s_local_get 0 f v_s) in
        (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) v_s' []) fcs, res))) = (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) (fst (app_f_v_s_local_get 0 f v_s)) []) fcs)"
    using fst_def by (cases "app_f_v_s_local_get 0 f v_s") auto
                                  
  then have "fst(run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs)) = (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) (fst (app_f_v_s_local_get 0 f v_s)) []) fcs)" using X by auto
  then show ?thesis using app_local_updates_stack [OF assms] by auto
qed

lemma valid_local_get:
  assumes "0 < length (f_locs f)"
  shows "run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf f)) fcs) = (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf f)) (((f_locs f)!0)#v_s) []) fcs, Step_normal)"
proof
  show "fst (run_step_b_e (Local_get 0)
          (Config d s
            (Frame_context
              (Redex v_s es b_es) lcs nf
              f)
            fcs)) =
    fst (Config d s
          (update_fc_step
            (Frame_context
              (Redex v_s es b_es) lcs nf
              f)
            (f_locs f ! 0 # v_s) [])
          fcs,
         Step_normal)" using assms stack_update by auto
next
  show "snd (run_step_b_e (Local_get 0)
          (Config d s
            (Frame_context
              (Redex v_s es b_es) lcs nf
              f)
            fcs)) =
    snd (Config d s
          (update_fc_step
            (Frame_context
              (Redex v_s es b_es) lcs nf
              f)
            (f_locs f ! 0 # v_s) [])
          fcs,
         Step_normal)" using no_crash assms by auto
qed

lemma with_locals: "run_step_b_e (Local_get 0) (Config d s ((Frame_context (Redex v_s es b_es) lcs nf (\<lparr>f_locs = [V_num (ConstI32 1) ], f_inst = inst\<rparr>))) fcs) 
= (Config d s (update_fc_step ((Frame_context (Redex v_s es b_es) lcs nf (\<lparr>f_locs = [V_num (ConstI32 1) ], f_inst = inst\<rparr>))) ((V_num (ConstI32 1))#v_s) []) fcs, Step_normal)"
  using valid_local_get by auto

end