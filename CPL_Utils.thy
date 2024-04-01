theory "CPL_Utils"
  imports Main "CPL_Syntax" "CPL_Semantic"
begin

(* ================= Utility Functions ================= *)

(* Ref: https://stackoverflow.com/a/28636535 *)
fun setToList :: "'a set \<Rightarrow> 'a list" where
"setToList S = (SOME l. set l = S)"

lemma set_set_to_list [simp] : "finite S \<Longrightarrow> set (setToList S) = S"
  by (metis (mono_tags, lifting) finite_list setToList.simps someI_ex)

(* ======================== Tests ======================== *)

end