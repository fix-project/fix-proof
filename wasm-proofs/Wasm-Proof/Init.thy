theory Init
  imports Host
begin

definition func_make_eq_tree_coupon_idx :: nat where "func_make_eq_tree_coupon_idx = 21"
definition func_make_eval_tree_coupon_idx :: nat where "func_make_eval_tree_coupon_idx = 22"
definition func_make_force_result_eq_coupon_idx :: nat where "func_make_force_result_eq_coupon_idx = 23"
definition func_make_eval_eq_coupon_idx :: nat where "func_make_eval_eq_coupon_idx = 24"
definition func_make_think_application_coupon_idx :: nat where "func_make_think_application_coupon_idx = 25"
definition func_make_think_to_force_coupon_idx :: nat where "func_make_think_to_force_coupon_idx = 26"
definition func_make_force_to_encode_strict_coupon_idx :: nat where "func_make_force_to_encode_strict_coupon_idx = 27"
definition func_make_eval_blobobj_coupon_idx :: nat where "func_make_eval_blobobj_coupon_idx = 28"
definition func_make_eq_application_coupon_idx :: nat where "func_make_eq_application_coupon_idx = 29"
definition func_make_eq_encode_strict_coupon_idx :: nat where "func_make_eq_encode_strict_coupon_idx = 30"
definition func_make_sym_coupon_idx :: nat where "func_make_sym_coupon_idx = 31"
definition func_make_trans_coupon_idx :: nat where "func_make_trans_coupon_idx = 32"
definition func_make_self_coupon_idx :: nat where "func_make_self_coupon_idx = 33"
definition func_make_coupon_idx :: nat where "func_make_coupon_idx = 34"
definition tab_coupons_idx :: nat where "tab_coupons_idx = 0"
definition init :: "s" where "init = 
\<lparr> funcs = 
[(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_equal)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_storage_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_force_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_eq_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_eval_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_apply_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_think_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_application_thunk)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_strict_encode)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_shallow_encode)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_get_coupon_lhs)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_get_coupon_rhs)),
(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_eq_coupon)),
(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_eval_coupon)),
(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_think_coupon)),
(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_force_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_get_tree_size)),
(Func_host ([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_get_tree_data)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_blob_obj)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_data)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_object)),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref), (T_num T_i32), (T_num T_i32)]
[(Table_size 0),
(Local_set 3),
(EConstNum (ConstInt32 (Abs_i32 0))),
(Local_set 4),
(Block (Tbv None)
[(Loop (Tbv None)
[(Local_get 4),
(Local_get 3),
(Relop T_i32 (Relop_i (relop_i.Ge S))),
(Br_if 1),
(Local_get 4),
(Table_get 0),
(Call 3),
(If (Tbv None)
[Nop]
[Unreachable]),
(Local_get 4),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Binop T_i32 (Binop_i Add)),
(Local_set 4),
(Br 0)])]),
(Local_get 0),
(Call 16),
(Local_get 3),
(Relop T_i32 (Relop_i relop_i.Eq)),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Call 16),
(Local_get 3),
(Relop T_i32 (Relop_i relop_i.Eq)),
(If (Tbv (Some (T_ref T_ext_ref)))
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Local_set 4),
(Block (Tbv None)
[(Loop (Tbv None)
[(Local_get 4),
(Local_get 3),
(Relop T_i32 (Relop_i (relop_i.Ge S))),
(Br_if 1),
(Local_get 4),
(Table_get 0),
(Local_set 2),
(Local_get 0),
(Local_get 4),
(Call 17),
(Local_get 2),
(Call 10),
(Call 0),
(If (Tbv None)
[(Local_get 1),
(Local_get 4),
(Call 17),
(Local_get 2),
(Call 11),
(Call 0),
(If (Tbv None)
[Nop]
[Unreachable])]
[Unreachable]),
(Local_get 4),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Binop T_i32 (Binop_i Add)),
(Local_set 4),
(Br 0)])]),
(Local_get 0),
(Local_get 1),
(Call 12)]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref), (T_num T_i32), (T_num T_i32)]
[(Table_size 0),
(Local_set 3),
(EConstNum (ConstInt32 (Abs_i32 0))),
(Local_set 4),
(Block (Tbv None)
[(Loop (Tbv None)
[(Local_get 4),
(Local_get 3),
(Relop T_i32 (Relop_i (relop_i.Ge S))),
(Br_if 1),
(Local_get 4),
(Table_get 0),
(Call 4),
(If (Tbv None)
[Nop]
[Unreachable]),
(Local_get 4),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Binop T_i32 (Binop_i Add)),
(Local_set 4),
(Br 0)])]),
(Local_get 0),
(Call 16),
(Local_get 3),
(Relop T_i32 (Relop_i relop_i.Eq)),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Call 16),
(Local_get 3),
(Relop T_i32 (Relop_i relop_i.Eq)),
(If (Tbv (Some (T_ref T_ext_ref)))
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Local_set 4),
(Block (Tbv None)
[(Loop (Tbv None)
[(Local_get 4),
(Local_get 3),
(Relop T_i32 (Relop_i (relop_i.Ge S))),
(Br_if 1),
(Local_get 4),
(Table_get 0),
(Local_set 2),
(Local_get 0),
(Local_get 4),
(Call 17),
(Local_get 2),
(Call 10),
(Call 0),
(If (Tbv None)
[(Local_get 1),
(Local_get 4),
(Call 17),
(Local_get 2),
(Call 11),
(Call 0),
(If (Tbv None)
[Nop]
[Unreachable])]
[Unreachable]),
(Local_get 4),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Binop T_i32 (Binop_i Add)),
(Local_set 4),
(Br 0)])]),
(Local_get 0),
(Local_get 1),
(Call 13)]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref), (T_ref T_ext_ref), (T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Table_get 0),
(Local_set 3),
(EConstNum (ConstInt32 (Abs_i32 2))),
(Table_get 0),
(Local_set 4),
(Local_get 2),
(Call 2),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 2),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 4),
(Call 3),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Local_get 4),
(Call 10),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 11),
(Local_get 4),
(Call 11),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 10),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 10),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 12)]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref), (T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Table_get 0),
(Local_set 3),
(Local_get 2),
(Call 4),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 3),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 10),
(Local_get 3),
(Call 10),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 11),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 13)]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref), (T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Table_get 0),
(Local_set 3),
(Local_get 2),
(Call 4),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 5),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Local_get 3),
(Call 10),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 10),
(Call 7),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 11),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 14)]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(Local_get 2),
(Call 6),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Call 19),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 10),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 15)]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(Local_get 2),
(Call 2),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Call 20),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 10),
(Call 8),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 12)]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[]
[(Local_get 0),
(Call 18),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 13)]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(Local_get 2),
(Call 3),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 2),
(Call 10),
(Call 7),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Local_get 2),
(Call 11),
(Call 7),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 12)]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(Local_get 2),
(Call 3),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 10),
(Call 8),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Call 8),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 12)]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(Local_get 2),
(Call 3),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 10),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 12)]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref), (T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Table_get 0),
(Local_set 3),
(Local_get 2),
(Call 3),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 3),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 11),
(Local_get 3),
(Call 10),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 2),
(Call 10),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Local_get 3),
(Call 11),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 12)]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[]
[(Local_get 0),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 12)]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]),
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34],
tabs = [0, 1],
mems = [],
globs = [],
elems = [0],
datas = []
\<rparr>
([(T_num T_i32), (T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[]
[(Local_get 0),
(Table_size 1),
(Relop T_i32 (Relop_i (relop_i.Lt U))),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Local_get 2),
(Local_get 0),
(Call_indirect 1 0)]
[Unreachable])])],
tabs = [((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), []),
((T_tab \<lparr> l_min = 13, l_max = (Some 13)\<rparr> T_func_ref), [(ConstRefFunc 21),
(ConstRefFunc 29),
(ConstRefFunc 23),
(ConstRefFunc 30),
(ConstRefFunc 25),
(ConstRefFunc 26),
(ConstRefFunc 27),
(ConstRefFunc 24),
(ConstRefFunc 28),
(ConstRefFunc 22),
(ConstRefFunc 31),
(ConstRefFunc 32),
(ConstRefFunc 33)])],
mems = [],
globs = [],
elems = [],
datas = []
\<rparr>
"

end
