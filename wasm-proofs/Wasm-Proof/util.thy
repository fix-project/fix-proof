theory util
  imports Init Main WebAssembly_Dev.Wasm_Base_Defs WebAssembly_Dev.Wasm_Interpreter
begin

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

lemma list_length_2:
  assumes "\<not> length xs < 2"
  shows "\<exists>x1 x2 rest. xs = x1 # x2 # rest"
  by (metis Suc_le_length_iff assms not_le_imp_less numeral_2_eq_2)

lemma list_length_3:
  assumes "\<not> length xs < 3"
  shows "\<exists>x1 x2 x3 rest. xs = x1 # x2 # x3 # rest"
  by (metis Suc_le_length_iff assms not_le_imp_less numeral_3_eq_3)

lemma and_00:
  shows "app_binop (Binop_i And) ((ConstInt32 (I32.lift0 0))) ((ConstInt32 (I32.lift0 0))) = Some ((ConstInt32 (I32.lift0 0)))"
  by (auto simp add: app_binop_def app_binop_i_v_def app_binop_i_def int_and_i32.abs_eq I32.int_and_def I32.int_of_nat_def)

lemma and_01:
  shows "app_binop (Binop_i And) ((ConstInt32 (I32.lift0 0))) ((ConstInt32 (I32.lift0 1))) = Some ((ConstInt32 (I32.lift0 0)))"
  by (auto simp add: app_binop_def app_binop_i_v_def app_binop_i_def int_and_i32.abs_eq I32.int_and_def I32.int_of_nat_def)

lemma and_10:
  shows "app_binop (Binop_i And) ((ConstInt32 (I32.lift0 1))) ((ConstInt32 (I32.lift0 0))) = Some ((ConstInt32 (I32.lift0 0)))"
  by (auto simp add: app_binop_def app_binop_i_v_def app_binop_i_def int_and_i32.abs_eq I32.int_and_def I32.int_of_nat_def)

lemma and_11:
  shows "app_binop (Binop_i And) ((ConstInt32 (I32.lift0 1))) ((ConstInt32 (I32.lift0 1))) = Some ((ConstInt32 (I32.lift0 1)))"
  by (auto simp add: app_binop_def app_binop_i_v_def app_binop_i_def int_and_i32.abs_eq I32.int_and_def I32.int_of_nat_def)

lemma less_than:
  fixes i j :: nat
  assumes "i < j"
  assumes "j < 2^(LENGTH('a::len) - 1)"
  shows "(word_of_nat i :: 'a word) <s word_of_nat j"
  by (metis (no_types, lifting) assms(1,2) int_eq_sint
      less_imp_of_nat_less less_or_eq_imp_le
      order_le_less_trans word_sless_alt)

lemma not_ge_than:
  fixes i j :: nat
  assumes "i < j"
  assumes "j < 2^(LENGTH('a::len) - 1)"
  shows "\<not> ((word_of_nat j :: 'a word) \<le>s word_of_nat i)"
  using assms(1,2) less_than signed.not_less
  by blast

lemma another_less_than:
  fixes i j :: nat
  assumes "i < j"
  assumes "j < 2^(LENGTH(i32) - 1)"
  shows "int_lt_s (I32.int_of_nat i) (I32.int_of_nat j)"
  using assms(1,2) less_than
  by (simp add: I32.int_lt_s_def int_lt_s_i32_def I32.rep_abs I32.int_of_nat_def) force

lemma ge_than_32:
  fixes i j :: nat
  assumes "i < j"
  assumes "j < 2^(LENGTH(i32) - 1)"
  shows "\<not> int_ge_s (int_of_nat i :: i32) (int_of_nat j :: i32)"
  using I32.int_lt_s_def another_less_than assms(1,2)
    int_lt_s_i32.rep_eq 
  using I32.int_of_nat_def int_of_nat_i32_def
  unfolding I32.int_ge_s_def int_ge_s_i32_def I32.rep_abs
  by fastforce

lemma nat_of_int_rev:
  assumes "i < 2^(LENGTH(i32) - 1)"
  shows "nat_of_int (int_of_nat i :: i32) = i"
  by (metis I32.length assms int_of_nat_i32.abs_eq
      nat_of_int_i32.abs_eq nat_power_minus_less
      unat_of_nat_len)

lemma nat_of_int_rev_trans:
  assumes "i < j"
  assumes "j < 2^(LENGTH(i32) - 1)"
  shows "nat_of_int (int_of_nat i :: i32) = i"
  using assms(1,2) dual_order.strict_trans nat_of_int_rev
  by blast

lemma nat_of_int_rev_trans_32:
  assumes "i < j"
  assumes "j < 2^(LENGTH(i32) - 1)"
  shows "I32.nat_of_int (int_of_nat i :: i32) = i"
  using I32.nat_of_int_def assms(1,2) nat_of_int_i32_def nat_of_int_rev_trans by presburger

lemma neq_32:
  assumes "i \<noteq> j"
  assumes "i < 2^(LENGTH(i32) - 1)"
  assumes "j < 2^(LENGTH(i32) - 1)"
  shows "Rep_i32 (I32.lift0 (word_of_nat i)) \<noteq> Rep_i32 (I32.lift0 (word_of_nat j))"
  by (metis I32.rep_abs assms(1,2,3) int_of_nat_i32.abs_eq nat_of_int_rev)

definition exp_inst :: "inst" where [simp]: 
"exp_inst = \<lparr>types = [([(T_ref T_ext_ref), (T_ref T_ext_ref)] _> [(T_ref T_ext_ref)]),
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
