theory isabelle_coupon
  imports coupon
begin

fun make_storage_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_storage_coupon_raw (c # xs) l r =
   (if (is_storage_coupon_api c) 
    then (case (get_coupon_lhs c, get_coupon_rhs c) of
     (Some l', Some r') \<Rightarrow> (if ( is_equal l l' \<and> is_equal r r') then Some (create_eq_coupon l r)
                                                                else None)
    | _ \<Rightarrow> None)
    else None)"
| "make_storage_coupon_raw [] l r = None"

fun make_tree_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_tree_coupon_raw coupons l r =
   (if (\<forall>i. (i < length coupons \<longrightarrow> is_eq_coupon_api (coupons ! i))) then
    (if (get_tree_size_api l = Some (length coupons) \<and> get_tree_size_api r = Some (length coupons)) then
      (if (\<forall>i. (i < length coupons \<longrightarrow>
         (case (get_tree_data_api l i, get_tree_data_api r i, get_coupon_lhs (coupons ! i), get_coupon_rhs (coupons ! i)) of
             (Some li, Some ri, Some cl, Some cr) \<Rightarrow> (is_equal li cl \<and> is_equal ri cr)
           | _ \<Rightarrow> False))) 
      then Some (create_eq_coupon l r) else None)
    else None)
  else None)"

fun make_thunk_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_thunk_coupon_raw (f1 # f2 # e # xs) l r =
   (if ((is_force_coupon_api f1) \<and> (is_force_coupon_api f2) \<and> (is_eq_coupon_api e)) 
    then
     (case (get_coupon_lhs f1, get_coupon_rhs f1, get_coupon_lhs f2, get_coupon_rhs f2,  get_coupon_lhs e, get_coupon_rhs e) of
      (Some f1l, Some f1r, Some f2l, Some f2r, Some el, Some er) \<Rightarrow>
         (if (is_equal f1r el \<and> is_equal f2r er \<and> is_equal f1l l \<and> is_equal f2l r) then Some (create_eq_coupon l r) else None)
     | _ \<Rightarrow> None)
    else None)"
| "make_thunk_coupon_raw _ _ _ = None"

fun make_thunktree_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_thunktree_coupon_raw (e # xs) l r =
   (if (is_eq_coupon_api e) then
      (case (get_coupon_lhs e, get_coupon_rhs e) of
       (Some l', Some r') \<Rightarrow> 
         (case (create_thunk_api l', create_thunk_api r') of
           (Some l'', Some r'') \<Rightarrow> 
           (if (is_equal l l'' \<and> is_equal r r'') then Some(create_eq_coupon l r) else None)
          | _ \<Rightarrow> None)
       | _ \<Rightarrow> None)
     else None)"
| "make_thunktree_coupon_raw [] l r = None"

fun make_thunkforce_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
"make_thunkforce_coupon_raw (e # f1 # f2 # xs) l r = 
   (if ((is_eq_coupon_api e) \<and> (is_force_coupon_api f1) \<and> (is_force_coupon_api f2))
    then
    (case (get_coupon_lhs e, get_coupon_rhs e, get_coupon_lhs f1, get_coupon_rhs f1, get_coupon_lhs f2, get_coupon_rhs f2) of
     (Some el, Some er, Some f1l, Some f1r, Some f2l, Some f2r) \<Rightarrow>
        (if (is_equal f1l el \<and> is_equal f2l er \<and> is_equal f1r l \<and> is_equal f2r r) then
         Some (create_eq_coupon l r)
        else None)
     | _ \<Rightarrow> None)
   else None)"
| "make_thunkforce_coupon_raw _ l r = None"

fun make_encode_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
 "make_encode_coupon_raw (e # xs) l r =
  (if (is_eq_coupon_api e) then
    (case (get_coupon_lhs e, get_coupon_rhs e) of
      (Some l', Some r') \<Rightarrow>
       (case (create_encode_api l', create_encode_api r') of
         (Some l'', Some r'') \<Rightarrow>
           (if (is_equal l l'' \<and> is_equal r r'') then Some (create_eq_coupon l r) else None)
        | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)
    else None)"
| "make_encode_coupon_raw [] l r = None"

fun make_sym_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_sym_coupon_raw (e # xs) l r =
   (if (is_eq_coupon_api e) then
     (case (get_coupon_lhs e, get_coupon_rhs e) of
      (Some l', Some r') \<Rightarrow>
        (if (is_equal r' l \<and> is_equal l' r) then Some (create_eq_coupon l r) else None)
      | _ \<Rightarrow> None)
   else None)"
| "make_sym_coupon_raw _ l r = None"

fun make_trans_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
 "make_trans_coupon_raw (e1 # e2 # xs) l r = 
    (if (is_eq_coupon_api e1 \<and> is_eq_coupon_api e2) then
        (case (get_coupon_lhs e1, get_coupon_rhs e1, get_coupon_lhs e2, get_coupon_rhs e2) of
           (Some e1l, Some e1r, Some e2l, Some e2r) \<Rightarrow>
             (if (is_equal e1r e2l \<and> is_equal l e1l \<and> is_equal r e2r) then
               Some (create_eq_coupon l r)
              else None)
          | _ \<Rightarrow> None)
        else None)"
| "make_trans_coupon_raw _ l r = None"
  

fun make_self_coupon_raw :: "handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
"make_self_coupon_raw xs l r = 
 (if (is_equal l r) then 
    Some (create_eq_coupon l r) 
  else 
    None)"

datatype request =
  Storage | Tree | Thunk | ThunkTree | ThunkForce | Encode | Sym | Trans | Self

fun make_coupon :: "request \<Rightarrow> handle list \<Rightarrow> handle \<Rightarrow> handle \<Rightarrow> handle option" where
  "make_coupon Storage coupons l r = make_storage_coupon_raw coupons l r"
| "make_coupon Tree coupons l r = make_tree_coupon_raw coupons l r"
| "make_coupon Thunk coupons l r = make_thunk_coupon_raw coupons l r"
| "make_coupon ThunkTree coupons l r = make_thunktree_coupon_raw coupons l r"
| "make_coupon ThunkForce coupons l r = make_thunkforce_coupon_raw coupons l r"
| "make_coupon Encode coupons l r = make_encode_coupon_raw coupons l r"
| "make_coupon Self coupons l r = make_self_coupon_raw coupons l r"
| "make_coupon Sym coupons l r = make_sym_coupon_raw coupons l r"
| "make_coupon Trans coupons l r = make_trans_coupon_raw coupons l r"

end