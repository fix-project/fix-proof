theory Init
  imports Host
begin

definition func_ret_idx :: nat where "func_ret_idx = 5"
definition func_make_blob_coupon_idx :: nat where "func_make_blob_coupon_idx = 6"
definition tab_coupons_idx :: nat where "tab_coupons_idx = 0"
definition init :: "s" where "init = 
\<lparr> funcs = 
[(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_equal)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func fixpoint_is_storage_coupon_api)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_get_coupon_lhs)),
(Func_host ([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_get_coupon_rhs)),
(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]) (Host_func fixpoint_create_eq_coupon)),

(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6],
tabs = [0],
mems = [],
globs = [],
elems = [],
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
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1, 2, 3, 4, 5, 6],
tabs = [0],
mems = [],
globs = [],
elems = [],
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
(Call 2),
(Call 0),
(Local_get 1),
(Local_get 2),
(Call 3),
(Call 0),
(Binop T_i32 (Binop_i And)),
(If (Tbv (Some (T_ref T_ext_ref)))
[(Local_get 0),
(Local_get 1),
(Call 4)]
[Unreachable])]
[Unreachable])])],
tabs = [((T_tab \<lparr> l_min = 0, l_max = None\<rparr> T_ext_ref), [])],
mems = [],
globs = [],
elems = [],
datas = []
\<rparr>
"

end
