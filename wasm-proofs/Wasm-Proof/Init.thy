theory Init
  imports Host
begin

definition init :: "s" where "init = 
\<lparr> funcs = 
[(Func_host ([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]) (Host_func is_equal)),
(Func_native 
\<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_num T_i32)]),
([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)])],
funcs = [0, 1],
tabs = [],
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
[(Local_get 1)])])],
tabs = [],
mems = [],
globs = [],
elems = [],
datas = []
\<rparr>
"

end
