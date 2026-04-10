theory fix_handle
  imports Main
begin

typedecl BlobName
typedecl TreeName
datatype Object = BlobObj BlobName | TreeObj TreeName
datatype Ref = BlobRef BlobName | TreeRef TreeName
datatype Data = Object Object | Ref Ref
datatype Thunk = Application TreeName | Identification Data | Selection TreeName | Digestion TreeName
datatype Encode = Strict Thunk | Shallow Thunk

datatype handle = Data Data | Thunk Thunk | Encode Encode

typedecl raw
type_synonym BlobData = "raw list"
type_synonym TreeData = "handle list"

(* Fixpoint APIs *)

consts 
  get_blob_data :: "BlobName \<Rightarrow> BlobData"
  get_tree_raw :: "TreeName \<Rightarrow> handle list"
  to_nat :: "raw list \<Rightarrow> nat"

  create_blob :: "BlobData \<Rightarrow> BlobName"
  create_tree :: "TreeData \<Rightarrow> TreeName"
  from_nat :: "nat \<Rightarrow> raw list"

definition get_tree_data :: "TreeName \<Rightarrow> nat \<Rightarrow> handle" where
  "get_tree_data t i \<equiv> (get_tree_raw t) ! i"

definition get_tree_size :: "TreeName \<Rightarrow> nat" where
  "get_tree_size t \<equiv> length (get_tree_raw t)"

definition get_blob_size :: "BlobName \<Rightarrow> nat" where
  "get_blob_size b \<equiv> length (get_blob_data b)"

(* Blob/Tree creation rules *)

axiomatization where
  get_blob_data_create_blob[simp]:
  "get_blob_data (create_blob x) = x"
  and
  get_tree_raw_create_tree[simp]:
  "get_tree_raw (create_tree xs) = xs"
  and
  from_nat_to_nat[simp]:
  "from_nat (to_nat r) = r"
  and
  to_nat_from_nat[simp]:
  "to_nat (from_nat n) = n"

(* Trees are acyclic *)

definition tree_child :: "TreeName \<Rightarrow> TreeName \<Rightarrow> bool"
  where "tree_child t2 t1 \<equiv> (Data (Object (TreeObj t2))) \<in> set (get_tree_raw t1) \<or> (Data (Ref (TreeRef t2))) \<in> set (get_tree_raw t2)"

axiomatization where
  wfp_tree_child: "wfP tree_child"

(* same-type ness: all accessible handles from two trees are same-typed *)

inductive same_typed_handle :: "handle \<Rightarrow> handle \<Rightarrow> bool" 
and same_typed_tree :: "TreeName \<Rightarrow> TreeName \<Rightarrow> bool"
where 
 tree[intro]:
  "list_all2 same_typed_handle (get_tree_raw t1) (get_tree_raw t2) \<Longrightarrow> same_typed_tree t1 t2"
| blob_obj[intro]:
  "same_typed_handle (Data (Object (BlobObj b1))) (Data (Object (BlobObj b2)))"
| blob_ref[intro]:
  "same_typed_handle (Data (Ref (BlobRef b1))) (Data (Ref (BlobRef b2)))"
| tree_obj[intro]:
  "same_typed_tree t1 t2 \<Longrightarrow> same_typed_handle (Data (Object (TreeObj t1))) (Data (Object (TreeObj t2)))"
| tree_ref[intro]:
  "same_typed_handle (Data (Ref (TreeRef t1))) (Data (Ref (TreeRef t2)))"
| thunk[intro]:
  "same_typed_handle (Thunk th1) (Thunk th2)"
| encode_shallow[intro]:
  "same_typed_handle (Encode (Shallow e1)) (Encode (Shallow e2))"
| encode_strict[intro]:
  "same_typed_handle (Encode (Strict e1)) (Encode (Strict e2))"

fun rel_opt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "rel_opt X None None = True"
| "rel_opt X (Some h1) (Some h2) = X h1 h2"
| "rel_opt X _ _ = False"

definition HTreeObj :: "TreeName \<Rightarrow> handle"
  where [simp]:
"HTreeObj t = (Data (Object (TreeObj t)))"

definition HBlobObj :: "BlobName \<Rightarrow> handle"
  where [simp]:
"HBlobObj t = (Data (Object (BlobObj t)))"

definition HTreeRef :: "TreeName \<Rightarrow> handle"
  where [simp]:
"HTreeRef t = (Data (Ref (TreeRef t)))"

definition HBlobRef :: "BlobName \<Rightarrow> handle"
  where [simp]:
"HBlobRef t = (Data (Ref (BlobRef t)))"


end