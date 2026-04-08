theory fix_handle
  imports Main
begin

typedecl BlobHandle
typedecl TreeHandle
datatype ThunkHandle = HThunkHandle TreeHandle
datatype EncodeHandle = HEncodeHandle ThunkHandle

datatype handle = 
  HBlobHandle BlobHandle
  | HTreeHandle TreeHandle
  | HThunkHandle ThunkHandle
  | HEncodeHandle EncodeHandle

typedecl raw
type_synonym BlobData = "raw"
type_synonym TreeData = "handle list"

(* Fixpoint APIs *)

consts 
  get_blob_data :: "BlobHandle \<Rightarrow> BlobData"
  get_tree_raw :: "TreeHandle \<Rightarrow> handle list"
  get_thunk_tree :: "ThunkHandle \<Rightarrow> TreeHandle"
  get_encode_thunk :: "EncodeHandle \<Rightarrow> ThunkHandle"

create_blob :: "BlobData \<Rightarrow> BlobHandle"
create_tree :: "TreeData \<Rightarrow> TreeHandle"
create_thunk :: "TreeHandle \<Rightarrow> ThunkHandle"
create_encode :: "ThunkHandle \<Rightarrow> EncodeHandle"

definition get_tree_data :: "TreeHandle \<Rightarrow> nat \<Rightarrow> handle" where
  "get_tree_data t i \<equiv> (get_tree_raw t) ! i"

definition get_tree_size :: "TreeHandle \<Rightarrow> nat" where
  "get_tree_size t \<equiv> length (get_tree_raw t)"

(* Blob/Tree creation rules *)

axiomatization where
  get_blob_data_create_blob[simp]:
  "get_blob_data (create_blob x) = x"
  and
  get_tree_raw_create_tree[simp]:
  "get_tree_raw (create_tree xs) = xs"
  and
  get_thunk_tree_create_thunk[simp]:
  "get_thunk_tree (create_thunk th) = th"
  and
  create_thunk_get_thunk_tree[simp]:
  "create_thunk (get_thunk_tree t) = t"
  and
  create_encode_get_thunk_encode[simp]:
  "create_encode (get_encode_thunk e) = e"
  and
  get_thunk_encode_create_encode[simp]:
  "get_encode_thunk (create_encode thunk) = thunk"

(* Trees are acyclic *)

definition tree_child :: "TreeHandle \<Rightarrow> TreeHandle \<Rightarrow> bool"
  where "tree_child t2 t1 \<equiv> (HTreeHandle t2) \<in> set (get_tree_raw t1)"

axiomatization where
  wfp_tree_child: "wfP tree_child"

(* same-type ness *)

inductive same_typed_tree :: "TreeHandle \<Rightarrow> TreeHandle \<Rightarrow> bool"
and same_typed_handle :: "handle \<Rightarrow> handle \<Rightarrow> bool" 
where 
  tree[intro]:
  "list_all2 same_typed_handle (get_tree_raw t1) (get_tree_raw t2)
       \<Longrightarrow> same_typed_tree t1 t2"
| blob_handle[intro]:
  "same_typed_handle (HBlobHandle b1) (HBlobHandle b2)"
| tree_handle[intro]:
  "same_typed_tree t1 t2 
       \<Longrightarrow> same_typed_handle (HTreeHandle t1) (HTreeHandle t2)"
| thunk_handle[intro]:
  "same_typed_handle (HThunkHandle e1) (HThunkHandle e2)"
| encode_handle[intro]:
  "same_typed_handle (HEncodeHandle e1) (HEncodeHandle e2)"

end