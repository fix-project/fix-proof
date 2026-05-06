theory isabelle_coupon
  imports coupon
begin

datatype coupon_type =
  Force | Storage | Apply | Slice | Think | Eval | Eq

record coupon = 
  type :: coupon_type
  lhs :: handle
  rhs :: handle

consts
  (* coupon-related ones *)
  is_coupon :: "handle \<Rightarrow> bool"
  create_coupon :: "coupon_type \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle"

  get_coupon_lhs :: "handle \<Rightarrow> handle option"
  get_coupon_rhs :: "handle \<Rightarrow> handle option"
  get_coupon_type :: "handle \<Rightarrow> coupon_type option"

  (* typeless Fix apis *)
  get_tree_size_api :: "handle \<Rightarrow>  nat option"
  get_tree_data_api :: "handle \<Rightarrow> nat \<Rightarrow> handle option"
  create_application_thunk_api :: "handle \<Rightarrow> handle option"
  create_selection_thunk_api :: "handle \<Rightarrow> handle option"
  create_identification_thunk_api :: "handle \<Rightarrow> handle option"
  create_strict_encode_api :: "handle \<Rightarrow> handle option"
  create_shallow_encode_api :: "handle \<Rightarrow> handle option"

  is_equal :: "handle \<Rightarrow>  handle \<Rightarrow> bool"

(* coupon-related ones *)
axiomatization where
  get_coupon_lhs_match[simp]:
  "get_coupon_lhs (create_coupon r x y) = Some x"
and
  get_coupon_rhs_match[simp]:
  "get_coupon_rhs (create_coupon r x y) = Some y"
and
  get_coupon_type_match[simp]:
  "get_coupon_type (create_coupon r x y) = Some r"
and
  get_coupon_type_exists[simp]:
  "get_coupon_type c = Some t \<Longrightarrow> \<exists>r x y. c = create_coupon r x y"
  
(* typeless Fix api axioms *)
axiomatization where
  get_tree_data_api_match: 
  "get_tree_data_api h i =
    (case h of
      (Data (Object (TreeObj t))) \<Rightarrow> 
        (if i < length (get_tree_raw t) then 
          Some (get_tree_data  t i) else None)
    | _ \<Rightarrow> None)" 
and
  get_tree_size_api_match: 
  "get_tree_size_api h =
    (case h of
      (Data (Object (TreeObj t))) \<Rightarrow> Some (get_tree_size t) 
     | _ \<Rightarrow> None)" 
and
  create_application_thunk_api_match:
  "create_application_thunk_api h =
     (case h of
       (Data (Object (TreeObj t))) \<Rightarrow> Some (Thunk (Application t))
     | _ \<Rightarrow> None)"
and
  create_selection_thunk_api_match:
  "create_selection_thunk_api h =
   (case h of
     (Data (Object (TreeObj t))) \<Rightarrow> Some (Thunk (Selection t))
   | (Data (Ref (TreeRef t))) \<Rightarrow> Some (Thunk (Selection t))
   | _ \<Rightarrow> None)"
and
  create_identification_thunk_api_match:
  "create_identification_thunk_api h =
   (case h of
     (Data d) \<Rightarrow> Some (Thunk (Identification d))
   | _ \<Rightarrow> None)"
and
  create_strict_encode_api_match:
  "create_strict_encode_api h = 
   (case h of
     (Thunk th) \<Rightarrow> Some (Encode (Strict th))
   | _ \<Rightarrow> None)"
and
  create_shallow_encode_api_match:
  "create_shallow_encode_api h = 
   (case h of
     (Thunk th) \<Rightarrow> Some (Encode (Shallow th))
   | _ \<Rightarrow> None)"
and
  is_equal_match[simp]:
  "is_equal h1 h2 = (h1 = h2)"

definition is_force_coupon :: "handle \<Rightarrow> bool" where
  "is_force_coupon c \<equiv> (get_coupon_type c = Some Force)"

definition is_storage_coupon :: "handle \<Rightarrow> bool" where
  "is_storage_coupon c \<equiv> (get_coupon_type c = Some Storage)"

definition is_apply_coupon :: "handle \<Rightarrow> bool" where
  "is_apply_coupon c \<equiv> (get_coupon_type c = Some Apply)"

definition is_slice_coupon :: "handle \<Rightarrow> bool" where
  "is_slice_coupon c \<equiv> (get_coupon_type c = Some Slice)"

definition is_think_coupon :: "handle \<Rightarrow> bool" where
  "is_think_coupon c \<equiv> (get_coupon_type c = Some Think)"

definition is_eq_coupon :: "handle \<Rightarrow> bool" where
  "is_eq_coupon c \<equiv> (get_coupon_type c = Some Eq)"

definition is_eval_coupon :: "handle \<Rightarrow> bool" where
  "is_eval_coupon c \<equiv> (get_coupon_type c = Some Eval)"

definition coupon_good :: "handle \<Rightarrow> bool"
  where
"coupon_good c = 
  (case (get_coupon_type c, get_coupon_lhs c, get_coupon_rhs c) of 
    (Some t, Some l, Some r) \<Rightarrow>
      (case t of
         Force \<Rightarrow> coupon_force l r
       | Storage \<Rightarrow> coupon_storage l r
       | Apply \<Rightarrow> coupon_apply l r
       | Slice \<Rightarrow> coupon_slice l r
       | Think \<Rightarrow> coupon_think l r
       | Eval \<Rightarrow> coupon_eval l r
       | Eq \<Rightarrow> coupon_eq l r)
   | _ \<Rightarrow> False)"

(* CouponTreeEq *)
fun make_eq_tree_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_eq_tree_coupon coupons l r =
   (if (\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon (coupons ! i))) then
    (if (get_tree_size_api l = Some (length coupons) \<and> get_tree_size_api r = Some (length coupons)) then
      (if (\<forall>i. (i < length coupons \<longrightarrow>
         (case (get_tree_data_api l i, get_tree_data_api r i, get_coupon_lhs (coupons ! i), get_coupon_rhs (coupons ! i)) of
             (Some li, Some ri, Some cl, Some cr) \<Rightarrow> (is_equal li cl \<and> is_equal ri cr)
           | _ \<Rightarrow> False))) 
      then Some (create_coupon Eq l r) else None)
    else None)
  else None)"

lemma eq_lhs_exist:
  assumes "is_eq_coupon c"
  shows "\<exists>l. get_coupon_lhs c = Some l"
  using assms get_coupon_lhs_match get_coupon_type_exists is_eq_coupon_def by blast

lemma eq_rhs_exist:
  assumes "is_eq_coupon c"
  shows "\<exists>r. get_coupon_rhs c = Some r"
  using assms get_coupon_rhs_match get_coupon_type_exists is_eq_coupon_def by blast

lemma eval_lhs_exist:
  assumes "is_eval_coupon c"
  shows "\<exists>l. get_coupon_lhs c = Some l"
  using assms get_coupon_lhs_match get_coupon_type_exists is_eval_coupon_def by blast

lemma eval_rhs_exist:
  assumes "is_eval_coupon c"
  shows "\<exists>r. get_coupon_rhs c = Some r"
  using assms get_coupon_rhs_match get_coupon_type_exists is_eval_coupon_def by blast

lemma think_lhs_exist:
  assumes "is_think_coupon c"
  shows "\<exists>l. get_coupon_lhs c = Some l"
  using assms get_coupon_lhs_match get_coupon_type_exists is_think_coupon_def by blast

lemma think_rhs_exist:
  assumes "is_think_coupon c"
  shows "\<exists>r. get_coupon_rhs c = Some r"
  using assms get_coupon_rhs_match get_coupon_type_exists is_think_coupon_def by blast

lemma apply_lhs_exist:
  assumes "is_apply_coupon c"
  shows "\<exists>l. get_coupon_lhs c = Some l"
  using assms get_coupon_lhs_match get_coupon_type_exists is_apply_coupon_def by blast

lemma apply_rhs_exist:
  assumes "is_apply_coupon c"
  shows "\<exists>r. get_coupon_rhs c = Some r"
  using assms get_coupon_rhs_match get_coupon_type_exists is_apply_coupon_def by blast

lemma force_lhs_exist:
  assumes "is_force_coupon c"
  shows "\<exists>l. get_coupon_lhs c = Some l"
  using assms get_coupon_lhs_match get_coupon_type_exists is_force_coupon_def by blast

lemma force_rhs_exist:
  assumes "is_force_coupon c"
  shows "\<exists>r. get_coupon_rhs c = Some r"
  using assms get_coupon_rhs_match get_coupon_type_exists is_force_coupon_def by blast

lemma good_eq:
  assumes "coupon_good c"
  and "is_eq_coupon c"
shows "coupon_eq (the (get_coupon_lhs c)) (the (get_coupon_rhs c))"
  using eq_lhs_exist eq_rhs_exist coupon_good_def
  apply simp
  using assms(1,2) is_eq_coupon_def by fastforce

lemma good_eval:
  assumes "coupon_good c"
  and "is_eval_coupon c"
shows "coupon_eval (the (get_coupon_lhs c)) (the (get_coupon_rhs c))"
  using eval_lhs_exist eval_rhs_exist coupon_good_def
  apply simp
  using assms(1,2) is_eval_coupon_def by fastforce

lemma good_apply:
  assumes "coupon_good c"
  and "is_apply_coupon c"
shows "coupon_apply (the (get_coupon_lhs c)) (the (get_coupon_rhs c))"
  using apply_lhs_exist apply_rhs_exist coupon_good_def
  apply simp
  using assms(1,2) is_apply_coupon_def by fastforce

lemma good_force:
  assumes "coupon_good c"
  and "is_force_coupon c"
shows "coupon_force (the (get_coupon_lhs c)) (the (get_coupon_rhs c))"
  using coupon_good_def is_force_coupon_def get_coupon_type_exists
  apply simp
  using assms(1,2) force_lhs_exist force_rhs_exist
  by force

lemma make_eq_tree_coupon_good:
  assumes H1: "list_all coupon_good coupons"
  and H2: "make_eq_tree_coupon coupons l r = Some c"
shows "coupon_good c"
proof - 
  have H: "(\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon (coupons ! i)))"
    using H2
    by (metis make_eq_tree_coupon.simps
        option.distinct(1))

  then have Sizel: "get_tree_size_api l = Some (length coupons)"
       and  Sizer: "get_tree_size_api r = Some (length coupons)"
    using H
    by (metis H2 make_eq_tree_coupon.simps option.distinct(1))+

  then obtain tl tr where "l = HTreeObj tl" and "r = HTreeObj tr"
    using HTreeObj_def get_tree_size_api_match
    apply (cases l; cases r; simp_all)
    by (metis Data.simps(5,6) Object.simps(5) lower_data.cases
        option.distinct(1))

  then have "(\<forall>i. (i < length coupons \<longrightarrow>
         (get_tree_data tl i = the (get_coupon_lhs (coupons ! i))) \<and> get_tree_data tr i = the (get_coupon_rhs (coupons ! i))))"
    using H H2 Sizel Sizer get_tree_size_def get_tree_data_def get_tree_data_api_match get_tree_size_api_match
    by (simp, metis (no_types, lifting) is_equal_match
        option.case_eq_if option.discI)

  then have "(\<forall>i. (i < length coupons \<longrightarrow>
         (coupon_eq (get_tree_data tl i) (get_tree_data tr i))))"
    by (metis H H1 good_eq list_all_length)
  then have "coupon_eq (HTreeObj tl) (HTreeObj tr)"
    using CouponTreeEq
get_tree_data_def get_tree_size_def Sizel Sizer
get_tree_data_api_match get_tree_size_api_match
    by (simp add: \<open>l = HTreeObj tl\<close> \<open>r = HTreeObj tr\<close>
        list_all2_all_nthI)

  have "c = create_coupon Eq l r"
    by (metis (no_types, lifting) H2
        make_eq_tree_coupon.simps option.discI
        option.inject)
  then show ?thesis
    using \<open>coupon_eq (HTreeObj tl) (HTreeObj tr)\<close>
      \<open>l = HTreeObj tl\<close> \<open>r = HTreeObj tr\<close>
      coupon_good_def by force
qed

(* CouponForceResultEq *)
fun make_force_result_eq_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_force_result_eq_coupon (f1 # f2 # e # xs) l r =
   (if ((is_force_coupon f1) \<and> (is_force_coupon f2) \<and> (is_eq_coupon e)) 
    then
     (case (get_coupon_lhs f1, get_coupon_rhs f1, get_coupon_lhs f2, get_coupon_rhs f2,  get_coupon_lhs e, get_coupon_rhs e) of
      (Some f1l, Some f1r, Some f2l, Some f2r, Some el, Some er) \<Rightarrow>
         (if (is_equal f1r el \<and> is_equal f2r er \<and> is_equal f1l l \<and> is_equal f2l r) then Some (create_coupon Eq l r) else None)
     | _ \<Rightarrow> None)
    else None)"
| "make_force_result_eq_coupon _ _ _ = None"

lemma make_force_result_eq_coupon_good:
  assumes H1: "list_all coupon_good coupons"
  and H2: "make_force_result_eq_coupon coupons l r = Some c"
shows "coupon_good c"
proof - 
  obtain f1 f2 e xs where COUPONS: "coupons = f1 # f2 # e # xs"
    using H2
    apply (cases coupons; simp_all)
    by (metis make_force_result_eq_coupon.simps(3,4) option.distinct(1)
        remdups_adj.cases)

  then have F1: "is_force_coupon f1" and F2: "is_force_coupon f2" and E: "is_eq_coupon e"
    using H2
    by (metis H2 make_force_result_eq_coupon.simps(1) option.distinct(1))+

  moreover then obtain f1l f1r f2l f2r el er 
    where f1l: "get_coupon_lhs f1 = Some f1l"
    and   f1r: "get_coupon_rhs f1 = Some f1r"
    and   f2l: "get_coupon_lhs f2 = Some f2l"
    and   f2r: "get_coupon_rhs f2 = Some f2r"
    and   el: "get_coupon_lhs e = Some el"
    and   er: "get_coupon_rhs e = Some er"
    using force_lhs_exist force_rhs_exist eq_lhs_exist eq_rhs_exist
    by presburger

  moreover have "coupon_good f1" 
           and "coupon_good f2" 
           and "coupon_good e"
    using H1
    by (simp add: \<open>coupons = f1 # f2 # e # xs\<close>)+

  ultimately have "coupon_force f1l f1r"  
             and "coupon_force f2l f2r" 
             and "coupon_eq el er"
    using H1 is_force_coupon_def coupon_good_def good_eq good_force
    using \<open>coupon_good e\<close> 
    by (simp_all, fastforce)

  moreover have "f1r = el \<and> f2r = er \<and> f1l = l \<and> f2l = r"
           and "c = create_coupon Eq l r"
    using H2 F1 F2 E COUPONS f1l f1r f2l f2r el er is_equal_match
    by (simp, metis option.distinct(1) option.sel)+

  ultimately show ?thesis
    using CouponForceResultEq coupon_good_def
    by simp
qed

(* CouponThinkApplication *)
fun make_think_application_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
"make_think_application_coupon (c1 # c2 # xs) l r =
  (if (is_eval_coupon c1 \<and> is_apply_coupon c2) then
     (case (get_coupon_lhs c1, get_coupon_rhs c1, get_coupon_lhs c2, get_coupon_rhs c2) of
       (Some evall, Some evalr, Some applyl, Some applyr) \<Rightarrow>
         (if (is_equal evalr applyl) then
           (case (create_application_thunk_api evall) of
             Some thunk \<Rightarrow>
               (if (is_equal thunk l \<and> is_equal applyr r) then Some (create_coupon Think l r) else None)
           | _ \<Rightarrow> None)
         else None)
     | _ \<Rightarrow> None)
   else None)"
| "make_think_application_coupon _ l r = None"

lemma make_think_application_coupon_good:
  assumes H1: "list_all coupon_good coupons"
  and H2: "make_think_application_coupon coupons l r = Some c"
shows "coupon_good c"
proof -
  obtain c1 c2 xs where COUPONS: "coupons = c1 # c2 # xs"
    using H2
    by (cases coupons; simp_all; case_tac list; simp_all)

  then have C1: "is_eval_coupon c1" and C2: "is_apply_coupon c2"
    using H2
    by (metis make_think_application_coupon.simps(1)
        option.distinct(1))+

  then obtain c1l c1r c2l c2r
    where c1l: "get_coupon_lhs c1 = Some c1l"
    and c1r: "get_coupon_rhs c1 = Some c1r"
    and c2l: "get_coupon_lhs c2 = Some c2l"
    and c2r: "get_coupon_rhs c2 = Some c2r"
    using eval_lhs_exist eval_rhs_exist apply_lhs_exist apply_rhs_exist
    by presburger

  then have C1C: "coupon_eval c1l c1r" and C2C: "coupon_apply c2l c2r"
    using C1 C2 COUPONS H1 good_eval good_apply
    by fastforce+

  obtain thunk where SAME: "c1r = c2l" 
                        and THUNK: "create_application_thunk_api c1l = Some thunk"
    using H2 COUPONS C1 C2 c1l c1r c2l c2r is_equal_match
    apply (simp, meson option.distinct(1))
    by (metis (lifting)
        option.distinct(1) option.exhaust_sel option.simps(4))

  then obtain c1lt where "c1l = HTreeObj c1lt"
    using create_application_thunk_api_match HTreeObj_def
    by (simp, metis (lifting) Data.simps(5,6) Object.simps(5)
        handle.exhaust handle.simps(10,11,12) lower_data.cases
        not_Some_eq)

  moreover obtain c2lt where "c2l = HTreeObj c2lt"
    using C2C coupon_sound
    by meson

  ultimately have "coupon_think thunk c2r"
    using CouponThinkApplication
    C1C C2C SAME THUNK create_application_thunk_api_match
    by (simp, blast)

  moreover have "c = create_coupon Think thunk c2r"
    using H2 C1 C2 C1C C2C COUPONS c1l c1r c2l c2r THUNK SAME create_application_thunk_api_match is_equal_match
    by (simp, metis option.distinct(1) option.inject)

  ultimately show ?thesis
    using coupon_good_def
    by simp
qed

(* CouponThinkToForce *)
fun make_think_to_force_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
"make_think_to_force_coupon (t # xs) l r =
  (if (is_think_coupon t) then
    (case (get_coupon_lhs t, get_coupon_rhs t) of
       (Some l', Some r') \<Rightarrow>
          (if (get_type r' = 0 \<or> get_type r' = 1 \<or> get_type r' = 2 \<or> get_type r' = 3) then
            (if (is_equal l' l \<and> is_equal r' r) then
              Some (create_coupon Force l r)
            else None)
          else None)
     | _ \<Rightarrow> None)
   else None)"
| "make_think_to_force_coupon [] l r = None"

lemma make_think_to_force_coupon_good:
  assumes "list_all coupon_good coupons"
  and "make_think_to_force_coupon coupons l r = Some c"
shows "coupon_good c"
proof -
  obtain t xs where step1: "coupons = t # xs"
    using assms(2)
    by (cases coupons; simp_all)

  then have step2: "is_think_coupon t"
    using assms(2)
    by (metis make_think_to_force_coupon.simps(1) option.distinct(1))

  then obtain tl tr where
        tl: "get_coupon_lhs t = Some tl"
    and tr: "get_coupon_rhs t = Some tr"
    using think_lhs_exist think_rhs_exist
    by presburger

  then have tc: "coupon_think tl tr"
    using assms(1) step1 step2 coupon_good_def is_think_coupon_def
    by simp

  have "get_type tr = 0 \<or> get_type tr = 1 \<or> get_type tr = 2 \<or> get_type tr = 3"
  and "tl = l \<and> tr = r"
  and "c = create_coupon Force l r"
    using step1 step2 assms(2) tl tr
    apply (simp, meson option.distinct(1))
    using step1 step2 assms(2) tl tr
    apply (simp, meson is_equal_match
        option.distinct(1))
    using step1 step2 assms(2) tl tr
    by (simp, metis not_Some_eq option.inject)

  then obtain d where "tr = Data d"
    by (cases tr; force)

  then have "coupon_force tl tr"
    using tc
    by (metis CouponThinktoForce
        coupon_sound)

  then show ?thesis
    using coupon_good_def
    by (simp add: \<open>c = create_coupon Force l r\<close>
        \<open>tl = l \<and> tr = r\<close>)
qed

(* CouponEqApplication *)
fun make_eq_application_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_eq_application_coupon (e # xs) l r =
   (if (is_eq_coupon e) then
      (case (get_coupon_lhs e, get_coupon_rhs e) of
       (Some l', Some r') \<Rightarrow> 
         (case (create_application_thunk_api l', create_application_thunk_api r') of
           (Some l'', Some r'') \<Rightarrow> 
           (if (is_equal l l'' \<and> is_equal r r'') then Some(create_coupon Eq l r) else None)
          | _ \<Rightarrow> None)
       | _ \<Rightarrow> None)
     else None)"
| "make_eq_application_coupon [] l r = None"

lemma make_eq_application_coupon_good:
  assumes "list_all coupon_good coupons"
  and "make_eq_application_coupon coupons l r = Some c"
shows "coupon_good c"
proof - 
  obtain e xs where step1: "coupons = e # xs"
    using assms(2)
    by (cases coupons; simp_all)

  then have step2: "is_eq_coupon e" 
    using assms(2)
    by (metis make_eq_application_coupon.simps(1)
        option.distinct(1))

  then obtain el er where el: "get_coupon_lhs e = Some el"
                    and   er: "get_coupon_rhs e = Some er"
    using eq_lhs_exist eq_rhs_exist
    by blast

  then obtain l' r' where l': "create_application_thunk_api el = Some l'"
                    and   r': "create_application_thunk_api er = Some r'"
    using step1 step2 assms(2)
    by (simp, metis (no_types, lifting) option.case_eq_if
        option.exhaust_sel)

  then obtain treel treer where treel: "el = HTreeObj treel" 
                          and treer: "er = HTreeObj treer"
    using create_application_thunk_api_match
    by (simp_all, metis (lifting) Data.exhaust Data.simps(5,6)
        Object.exhaust Object.simps(5) handle.exhaust
        handle.simps(10,11,12)
        option.distinct(1))

  have "l' = l" and "r' = r" and "c = create_coupon Eq l' r'"
    using step1 step2 assms(2) el er l' r' is_equal_match
    by (simp_all, metis option.distinct(1) option.sel)+

  have "coupon_eq el er"
    using el er step1 step2 assms(1) good_eq by force
  then have "coupon_eq l' r'"
    using l' r' create_application_thunk_api_match treel treer
    using CouponEqApplication by auto
  then show ?thesis
    by (simp add: \<open>c = create_coupon Eq l' r'\<close>
        coupon_good_def)
qed

(* CouponEvalBlobObj *)
fun make_eval_blob_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
"make_eval_blob_coupon _ l r =
   (if (get_type l = 0 \<and> is_equal l r) then
     Some (create_coupon Eval l r)
   else None)"

lemma make_eval_blob_coupon_good:
  assumes "make_eval_blob_coupon coupons l r = Some c"
  shows "coupon_good c"
proof -
  have step1: "get_type l = 0 \<and> is_equal l r"
    using assms
    by (simp, meson option.distinct(1))

  then have "c = create_coupon Eval l r"
    using assms
    by auto

  moreover obtain b where "l = HBlobObj b"
    using step1 HBlobObj_def
    apply (cases l; simp_all; case_tac x1; simp_all)
    apply (metis Object.exhaust get_type.simps(2)
        zero_neq_one)
    by (metis Ref.exhaust Suc_1 eval_nat_numeral(3)
        get_type.simps(3,4) old.nat.distinct(1))

  ultimately show ?thesis
    using coupon_good_def step1 CouponEvalBlobObj is_equal_match
    by (simp, blast)
qed

(* CouponEvalTreeObj *)
fun make_eval_tree_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_eval_tree_coupon coupons l r =
   (if (\<forall>i. (i < length coupons \<longrightarrow> is_eval_coupon (coupons ! i))) then
    (if (get_tree_size_api l = Some (length coupons) \<and> get_tree_size_api r = Some (length coupons)) then
      (if (\<forall>i. (i < length coupons \<longrightarrow>
         (case (get_tree_data_api l i, get_tree_data_api r i, get_coupon_lhs (coupons ! i), get_coupon_rhs (coupons ! i)) of
             (Some li, Some ri, Some cl, Some cr) \<Rightarrow> (is_equal li cl \<and> is_equal ri cr)
           | _ \<Rightarrow> False))) 
      then Some (create_coupon Eval l r) else None)
    else None)
  else None)"

lemma make_eval_tree_coupon_good:
  assumes H1: "list_all coupon_good coupons"
  and H2: "make_eval_tree_coupon coupons l r = Some c"
shows "coupon_good c"
proof - 
  have H: "(\<forall>i. (i < length coupons \<longrightarrow> is_eval_coupon (coupons ! i)))"
    using H2
    by (metis make_eval_tree_coupon.simps
        option.distinct(1))

  then have Sizel: "get_tree_size_api l = Some (length coupons)"
       and  Sizer: "get_tree_size_api r = Some (length coupons)"
    using H
    by (metis H2 make_eval_tree_coupon.simps option.distinct(1))+

  then obtain tl tr where "l = HTreeObj tl" and "r = HTreeObj tr"
    using HTreeObj_def get_tree_size_api_match
    apply (cases l; cases r; simp_all)
    by (metis Data.simps(5,6) Object.simps(5) lower_data.cases
        option.distinct(1))

  then have "(\<forall>i. (i < length coupons \<longrightarrow>
         (get_tree_data tl i = the (get_coupon_lhs (coupons ! i))) \<and> get_tree_data tr i = the (get_coupon_rhs (coupons ! i))))"
    using H H2 Sizel Sizer get_tree_size_def get_tree_data_def get_tree_size_api_match get_tree_data_api_match
    by (simp, metis (no_types, lifting) is_equal_match
        option.case_eq_if option.discI)

  then have "(\<forall>i. (i < length coupons \<longrightarrow>
         (coupon_eval (get_tree_data tl i) (get_tree_data tr i))))"
    by (metis H H1 good_eval list_all_length)
  then have "coupon_eval (HTreeObj tl) (HTreeObj tr)"
    using CouponEvalTreeObj get_tree_data_def get_tree_size_def Sizel Sizer get_tree_size_api_match get_tree_data_api_match
    by (simp add: \<open>l = HTreeObj tl\<close> \<open>r = HTreeObj tr\<close>
        list_all2_all_nthI)

  have "c = create_coupon Eval l r"
    by (metis (no_types, lifting) H2
        make_eval_tree_coupon.simps option.discI
        option.inject)
  then show ?thesis
    using \<open>coupon_eval (HTreeObj tl) (HTreeObj tr)\<close>
      \<open>l = HTreeObj tl\<close> \<open>r = HTreeObj tr\<close>
      coupon_good_def by force
qed

(* CouponForcetoEncodeStrict *)
fun make_force_to_encode_strict_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option"
where 
"make_force_to_encode_strict_coupon (e # xs) l r = 
  (if (is_force_coupon e) then
    (case (get_coupon_lhs e, get_coupon_rhs e) of
      (Some el, Some er) \<Rightarrow>
         (case (create_strict_encode_api el) of
           Some el' \<Rightarrow> 
            (if (is_equal el' l \<and> is_equal er r \<and> (get_type er = 0 
                                                 \<or> get_type er = 1)) 
              then Some (create_coupon Eq l r)
              else None)
         | None \<Rightarrow> None)
     | _ \<Rightarrow> None)
   else None)"
| "make_force_to_encode_strict_coupon [] l r = None"

lemma make_force_to_encode_strict_coupon_good:
  assumes "list_all coupon_good coupons"
  and "make_force_to_encode_strict_coupon coupons l r = Some c"
shows "coupon_good c"
proof -
  obtain e xs where step1: "coupons = e # xs"
    using assms(2)
    by (cases coupons; simp_all)

  then have step2: "is_force_coupon e"
    using assms(2)
    by (simp, metis option.discI)

  then obtain el er where el: "get_coupon_lhs e = Some el"
                    and   er: "get_coupon_rhs e = Some er"
    using force_lhs_exist force_rhs_exist
    by blast

  then obtain el' where el': "create_strict_encode_api el = Some el'"
    using assms(2) step1 step2 el er
    by (simp, fastforce)

  then have step3: "(is_equal el' l \<and> is_equal er r \<and> (get_type er = 0 
                                                 \<or> get_type er = 1))"
    using assms(2) step1 step2 el er
    by (simp, metis option.distinct(1))
  then have step4: "c = create_coupon Eq l r"
    using assms(2) step1 step2 el er el' is_equal_match
    by (simp, force)

  have "coupon_force el er"
    using step2 assms(2) step1 el er
    using assms(1) good_force by fastforce
  moreover have "lift er = er"
    using step3 is_equal_match
    apply (cases er; simp_all)
    apply (case_tac x1; simp_all)
    apply force
    by (case_tac x2; simp_all)
  ultimately have "coupon_eq el' er"
    using el' create_strict_encode_api_match CouponForcetoEncodeStrict is_equal_match
    apply simp
    apply (cases el; simp_all)
    by fastforce

  then show ?thesis
    using coupon_good_def step4 step3 is_equal_match
    by simp
qed

(* CouponEvalEq *)
fun make_eval_eq_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option"
  where
"make_eval_eq_coupon (c1 # c2 # xs) l r =
 (if (is_eval_coupon c1 \<and> is_eq_coupon c2) then
    (case (get_coupon_lhs c1, get_coupon_rhs c1, get_coupon_lhs c2, get_coupon_rhs c2) of
    (Some evall, Some evalr, Some eql, Some eqr) \<Rightarrow>
       (if (is_equal evall eql \<and> is_equal eqr l \<and> is_equal evalr r) then
          Some (create_coupon Eval l r)
        else None)
  | _ \<Rightarrow> None)
 else None)"
| "make_eval_eq_coupon _ l r = None"

lemma make_eval_eq_coupon_good:
  assumes "list_all coupon_good coupons"
and "make_eval_eq_coupon coupons l r = Some c"
shows "coupon_good c"
proof -
  obtain c1 c2 xs where step1: "coupons = c1 # c2 # xs"
    using assms(2)
    by (cases coupons; simp_all; case_tac list; simp_all)

  then have step2: "is_eval_coupon c1 \<and> is_eq_coupon c2"
    using assms(2)
    by (metis make_eval_eq_coupon.simps(1)
        option.distinct(1))

  then obtain c1l c1r c2l c2r 
    where c1l: "get_coupon_lhs c1 = Some c1l"
    and   c1r: "get_coupon_rhs c1 = Some c1r"
    and   c2l: "get_coupon_lhs c2 = Some c2l"
    and   c2r: "get_coupon_rhs c2 = Some c2r"
    using eval_lhs_exist eval_rhs_exist eq_lhs_exist eq_rhs_exist
    by presburger

  then have step3: "is_equal c1l c2l \<and> is_equal c2r l \<and> is_equal c1r r"
    using assms(2) step1 step2
    by (simp, metis option.distinct(1))
  then have step4: "c = create_coupon Eval l r"
    using assms(2) step1 step2 c1l c1r c2l c2r
    by simp

  have "coupon_eval c1l c1r"
    using step2 step1 coupon_good_def assms(1) c1l c1r good_eval by force
  moreover have "coupon_eq c1l c2r"
    using step2 step1 coupon_good_def assms(1) c2l c2r good_eq step3 is_equal_match by force
  ultimately have "coupon_eval c2r c1r"
    using CouponEvalEq by blast
  then show ?thesis 
    using step1 step4 step3 coupon_good_def is_equal_match
    by auto
qed

(* CouponEqEncodeStrict *)
fun make_eq_encode_strict_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
 "make_eq_encode_strict_coupon (e # xs) l r =
  (if (is_eq_coupon e) then
    (case (get_coupon_lhs e, get_coupon_rhs e) of
      (Some l', Some r') \<Rightarrow>
       (case (create_strict_encode_api l', create_strict_encode_api r') of
         (Some l'', Some r'') \<Rightarrow>
           (if (is_equal l l'' \<and> is_equal r r'') then Some (create_coupon Eq l r) else None)
        | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)
    else None)"
| "make_eq_encode_strict_coupon [] l r = None"

lemma make_eq_encode_strict_coupon_good:
  assumes "list_all coupon_good coupons"
  and "make_eq_encode_strict_coupon coupons l r = Some c"
shows "coupon_good c"
proof -
  obtain e xs where step1: "coupons = e # xs"
    using assms(2)
    by (cases coupons; simp_all)

  then have step2: "is_eq_coupon e"
    using assms(2)
    by (simp, metis option.discI)

  then obtain el er where el: "get_coupon_lhs e = Some el"
                    and   er: "get_coupon_rhs e = Some er"
    using eq_lhs_exist eq_rhs_exist
    by blast

  then obtain el' er' where el': "create_strict_encode_api el = Some el'"
                      and   er': "create_strict_encode_api er = Some er'"
    using assms(2) step1 step2
    apply simp
    by (metis (no_types, lifting) option.case_eq_if
        option.exhaust)

  then have step3: "l = el' \<and> r = er'" and step4: "c = create_coupon Eq l r"
    using assms(2) step1 step2 el er is_equal_match
    apply simp_all
    apply (metis option.distinct(1))
    by (metis option.distinct(1) option.sel)

  have "coupon_eq el er"
    using step2 assms(1) coupon_good_def step1 el er
    using good_eq by force
  have "coupon_eq el' er'"
    using el' er' create_strict_encode_api_match CouponEqEncodeStrict
    apply (cases el; cases er; simp_all)
    using \<open>coupon_eq el er\<close> by blast
  then show ?thesis
    using step4 coupon_good_def step3
    by simp
qed

(* CouponEqEncodeShallow *)
fun make_eq_encode_shallow_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
 "make_eq_encode_shallow_coupon (e # xs) l r =
  (if (is_eq_coupon e) then
    (case (get_coupon_lhs e, get_coupon_rhs e) of
      (Some l', Some r') \<Rightarrow>
       (case (create_shallow_encode_api l', create_shallow_encode_api r') of
         (Some l'', Some r'') \<Rightarrow>
           (if (is_equal l l'' \<and> is_equal r r'') then Some (create_coupon Eq l r) else None)
        | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)
    else None)"
| "make_eq_encode_shallow_coupon [] l r = None"

lemma make_eq_encode_shallow_coupon_good:
  assumes "list_all coupon_good coupons"
  and "make_eq_encode_shallow_coupon coupons l r = Some c"
shows "coupon_good c"
proof -
  obtain e xs where step1: "coupons = e # xs"
    using assms(2)
    by (cases coupons; simp_all)

  then have step2: "is_eq_coupon e"
    using assms(2)
    by (simp, metis option.discI)

  then obtain el er where el: "get_coupon_lhs e = Some el"
                    and   er: "get_coupon_rhs e = Some er"
    using eq_lhs_exist eq_rhs_exist
    by blast

  then obtain el' er' where el': "create_shallow_encode_api el = Some el'"
                      and   er': "create_shallow_encode_api er = Some er'"
    using assms(2) step1 step2
    apply simp
    by (metis (no_types, lifting) option.case_eq_if
        option.exhaust)

  then have step3: "l = el' \<and> r = er'" and step4: "c = create_coupon Eq l r"
    using assms(2) step1 step2 el er is_equal_match
    apply simp_all
    apply (metis option.distinct(1))
    by (metis option.distinct(1) option.sel)

  have "coupon_eq el er"
    using step2 assms(1) coupon_good_def step1 el er
    using good_eq by force
  have "coupon_eq el' er'"
    using el' er' create_shallow_encode_api_match CouponEqEncodeShallow
    apply (cases el; cases er; simp_all)
    using \<open>coupon_eq el er\<close> by blast
  then show ?thesis
    using step4 coupon_good_def step3
    by simp
qed

(* CouponSym *)
fun make_sym_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_sym_coupon (e # xs) l r =
   (if (is_eq_coupon e) then
     (case (get_coupon_lhs e, get_coupon_rhs e) of
      (Some l', Some r') \<Rightarrow>
        (if (is_equal r' l \<and> is_equal l' r) then Some (create_coupon Eq l r) else None)
      | _ \<Rightarrow> None)
   else None)"
| "make_sym_coupon _ l r = None"

lemma make_sym_coupon_good:
  assumes "list_all coupon_good coupons"
and "make_sym_coupon coupons l r = Some c"
shows "coupon_good c"
proof -
  obtain e xs where step1: "coupons = e # xs"
    using assms(2)
    by (cases coupons; simp_all)

  then have step2: "is_eq_coupon e"
    using assms(2)
    by (simp, metis option.discI)

  then obtain el er where el: "get_coupon_lhs e = Some el"
                    and   er: "get_coupon_rhs e = Some er"
    using eq_lhs_exist eq_rhs_exist
    by blast

  then have step3: "er = l \<and> el = r"
    using assms(2) step1 step2 is_equal_match
    by (simp, metis option.distinct(1))

  then have step4: "c = create_coupon Eq l r"
    using assms(2) step1 step2 el er is_equal_match
    by simp

  have "coupon_eq el er" 
    using step2 el er step1 assms(2)
    using assms(1) good_eq by force
  then have "coupon_eq l r"
    using step3 CouponSym
    by blast
  then show ?thesis
    using coupon_good_def step4 by simp
qed

(* CouponTrans *)
fun make_trans_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
 "make_trans_coupon (e1 # e2 # xs) l r = 
    (if (is_eq_coupon e1 \<and> is_eq_coupon e2) then
        (case (get_coupon_lhs e1, get_coupon_rhs e1, get_coupon_lhs e2, get_coupon_rhs e2) of
           (Some e1l, Some e1r, Some e2l, Some e2r) \<Rightarrow>
             (if (is_equal e1r e2l \<and> is_equal l e1l \<and> is_equal r e2r) then
               Some (create_coupon Eq l r)
              else None)
          | _ \<Rightarrow> None)
        else None)"
| "make_trans_coupon _ l r = None"

lemma make_trans_coupon_good:
  assumes "list_all coupon_good coupons"
  and "make_trans_coupon coupons l r = Some c"
shows "coupon_good c"
proof -
  obtain c1 c2 xs where step1: "coupons = c1 # c2 # xs"
    using assms(2)
    by (cases coupons; simp_all; case_tac list; simp_all)

  then have step2: "is_eq_coupon c1 \<and> is_eq_coupon c2"
    using assms(2)
    by (metis make_trans_coupon.simps(1)
        option.distinct(1))

  then obtain c1l c1r c2l c2r 
    where c1l: "get_coupon_lhs c1 = Some c1l"
    and   c1r: "get_coupon_rhs c1 = Some c1r"
    and   c2l: "get_coupon_lhs c2 = Some c2l"
    and   c2r: "get_coupon_rhs c2 = Some c2r"
    using eq_lhs_exist eq_rhs_exist
    by presburger

  then have step3: "is_equal c1r c2l \<and> is_equal l c1l \<and> is_equal r c2r"
    using assms(2) step1 step2
    by (simp, metis option.distinct(1))

  then have step4: "c = create_coupon Eq l r"
    using assms(2) step1 step2 c1l c1r c2l c2r
    by simp

  have "coupon_eq c1l c1r"
    using step2 step1 assms(1) coupon_good_def good_eq c1l c1r
    by force
  moreover have "coupon_eq c2l c2r"
    using step2 step1 assms(1) coupon_good_def good_eq c2l c2r
    by force
  ultimately have "coupon_eq c1l c2r"
    by (metis CouponTrans is_equal_match
        step3)
  then show ?thesis
    using step3 coupon_good_def step4 is_equal_match
    by simp
qed

(* CouponSelf *)
fun make_self_coupon :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
"make_self_coupon _ l r = 
 (if (is_equal l r) then 
    Some (create_coupon Eq l r) 
  else 
    None)"

lemma make_self_coupon_good:
  assumes "make_self_coupon coupons l r = Some c"
  shows "coupon_good c"
proof -
  have "is_equal l r"
    using assms
    by (metis make_self_coupon.simps
        option.distinct(1))
  then have "c = create_coupon Eq l r"
    using assms
    by simp

  moreover have "coupon_eq l r"
    using CouponSelf \<open>is_equal l r\<close> is_equal_match
    by fastforce
  ultimately show ?thesis
    using coupon_good_def
    by force
qed

datatype request =
  TreeEq | ForceResultEq | ThinkApplication | ThinkToForce | EqApplication | EvalBlobObj | EvalTreeObj | ForceToEncodeStrict | EvalEq | EqEncodeStrict | Sym | Trans | Self

fun make_coupon :: "request \<Rightarrow> handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_coupon TreeEq coupons l r = make_eq_tree_coupon coupons l r"
| "make_coupon ForceResultEq coupons l r = make_force_result_eq_coupon coupons l r"
| "make_coupon ThinkApplication coupons l r = make_think_application_coupon coupons l r"
| "make_coupon ThinkToForce coupons l r = make_think_to_force_coupon coupons l r"
| "make_coupon EqApplication coupons l r = make_eq_application_coupon coupons l r"
| "make_coupon EvalBlobObj coupons l r = make_eval_blob_coupon coupons l r"
| "make_coupon EvalTreeObj coupons l r = make_eval_tree_coupon coupons l r"
| "make_coupon ForceToEncodeStrict coupons l r = make_force_to_encode_strict_coupon coupons l r"
| "make_coupon EvalEq coupons l r = make_eval_eq_coupon coupons l r"
| "make_coupon EqEncodeStrict coupons l r = make_eq_encode_strict_coupon coupons l r"
| "make_coupon Self coupons l r = make_self_coupon coupons l r"
| "make_coupon Sym coupons l r = make_sym_coupon coupons l r"
| "make_coupon Trans coupons l r = make_trans_coupon coupons l r"

lemma make_coupon_good:
  assumes H1: "list_all coupon_good coupons"
  and H2: "make_coupon req coupons l r = Some c"
shows "coupon_good c"
  using assms(2)
proof (cases req)
  case TreeEq
  then show ?thesis
    using H1 H2 make_eq_tree_coupon_good
    by auto
next
  case ForceResultEq
  then show ?thesis
    using H1 H2 make_force_result_eq_coupon_good
    by force
next
  case ThinkApplication
  then show ?thesis
    using H1 H2 make_think_application_coupon_good
    by force
next
  case ThinkToForce
  then show ?thesis
    using H1 H2 make_think_to_force_coupon_good
    by force
next
  case EqApplication
  then show ?thesis
    using H1 H2 make_eq_application_coupon_good
    by force
next
  case EvalBlobObj
  then show ?thesis
    using H2 make_eval_blob_coupon_good
    by force
next
  case EvalTreeObj
  then show ?thesis
    using H1 H2 make_eval_tree_coupon_good
    by force
next
  case ForceToEncodeStrict
  then show ?thesis
    using H1 H2
      make_force_to_encode_strict_coupon_good
    by auto
next
  case EvalEq
  then show ?thesis
    using H1 H2 make_eval_eq_coupon_good
    by force
next
  case EqEncodeStrict
  then show ?thesis
    using H1 H2 make_eq_encode_strict_coupon_good
    by auto
next
  case Sym
  then show ?thesis
    using H1 H2 make_sym_coupon_good by force
next
  case Trans
  then show ?thesis
    using H1 H2 make_trans_coupon_good by force
next
  case Self
  then show ?thesis
    using H2 make_self_coupon_good by force
qed

end