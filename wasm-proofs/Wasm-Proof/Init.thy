theory Init
  imports Host
begin

definition func_ret_idx :: nat where "func_ret_idx = 11"
definition func_make_storage_coupon_idx :: nat where "func_make_storage_coupon_idx = 12"
definition func_make_tree_coupon_idx :: nat where "func_make_tree_coupon_idx = 13"
definition func_make_thunk_coupon_idx :: nat where "func_make_thunk_coupon_idx = 14"
definition func_make_thunktree_coupon_idx :: nat where "func_make_thunktree_coupon_idx = 15"
definition func_make_thunkforce_coupon_idx :: nat where "func_make_thunkforce_coupon_idx = 16"
definition func_make_encode_coupon_idx :: nat where "func_make_encode_coupon_idx = 17"
definition func_make_sym_coupon_idx :: nat where "func_make_sym_coupon_idx = 18"
definition func_make_trans_coupon_idx :: nat where "func_make_trans_coupon_idx = 19"
definition func_make_self_coupon_idx :: nat where "func_make_self_coupon_idx = 20"
definition func_make_coupon_idx :: nat where "func_make_coupon_idx = 21"
definition tab_coupons_idx :: nat where "tab_coupons_idx = 0"
definition init :: "s" where "init = 
\<lparr> funcs = 
[(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_equal)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_storage_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_force_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_eq_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_thunk)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_encode)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_get_coupon_lhs)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_get_coupon_rhs)),
(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_eq_coupon)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_get_tree_size)),
(Func_host ([(T_ref T_ext_ref), (T_num T_i32)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_get_tree_data)),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
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
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[]
[(Local_get 0),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0)]
[(Local_get 1)])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
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
\<rparr>
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])
[(T_ref T_ext_ref)]
[(EConstNum (ConstInt32 (Abs_i32 0))),
(Table_get 0),
(Local_set 2),
(Local_get 2),
(Call 1),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 2),
(Call 6),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Local_get 2),
(Call 7),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 8)]
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
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
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
(Call 9),
(Local_get 3),
(Relop T_i32 (Relop_i relop_i.Eq)),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Call 9),
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
(Call 10),
(Local_get 2),
(Call 6),
(Call 0),
(If (Tbv None)
[(Local_get 1),
(Local_get 4),
(Call 10),
(Local_get 2),
(Call 7),
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
(Call 8)]
[Unreachable])]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
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
(Call 7),
(Local_get 4),
(Call 6),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 7),
(Local_get 4),
(Call 7),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 6),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 6),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 8)]
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
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
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
(Call 6),
(Call 4),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Local_get 2),
(Call 7),
(Call 4),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 8)]
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
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
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
(Local_set 4),
(EConstNum (ConstInt32 (Abs_i32 1))),
(Table_get 0),
(Local_set 2),
(EConstNum (ConstInt32 (Abs_i32 2))),
(Table_get 0),
(Local_set 3),
(Local_get 4),
(Call 3),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 2),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 2),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 6),
(Local_get 4),
(Call 6),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 6),
(Local_get 4),
(Call 7),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 7),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 3),
(Call 7),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 8)]
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
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
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
(Call 6),
(Call 5),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 7),
(Call 5),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 8)]
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
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
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
(Call 7),
(Local_get 0),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 2),
(Call 6),
(Local_get 1),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 8)]
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
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
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
(Call 7),
(Local_get 3),
(Call 6),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 2),
(Call 6),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 1),
(Local_get 3),
(Call 7),
(Call 0),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 8)]
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
funcs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
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
(Call 8)]
[Unreachable])]),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
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
((T_tab \<lparr> l_min = 9, l_max = (Some 9)\<rparr> T_func_ref), [(ConstRefFunc 12),
(ConstRefFunc 13),
(ConstRefFunc 14),
(ConstRefFunc 15),
(ConstRefFunc 16),
(ConstRefFunc 17),
(ConstRefFunc 18),
(ConstRefFunc 19),
(ConstRefFunc 20)])],
mems = [],
globs = [],
elems = [],
datas = []
\<rparr>
"

end
