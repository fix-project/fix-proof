theory identify
  imports fix_handle
begin

fun identify :: "Data \<Rightarrow> handle option" where
  "identify d = Some (Data d)"

lemma identify_X:
  fixes X :: "handle \<Rightarrow> handle \<Rightarrow> bool"
  assumes "X (Data d1) (Data d2)"
  shows "rel_opt X (identify d1) (identify d2)"
  using assms by fastforce

end