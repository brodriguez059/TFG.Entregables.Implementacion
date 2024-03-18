theory "CPL_Utils"
  imports Main "CPL_Instance"
begin

(* ================= Proof System Utility Functions ================= *)

(* Note: |` is called restrict_map operator. m |` A = (\<lambda>x. if x \<in> A then m x else None) *)
fun projectValuation :: "'a Valuation \<Rightarrow> Variable set \<Rightarrow> 'a Valuation" where
"projectValuation f V = (case (V \<subseteq> (dom f)) of
  False \<Rightarrow> Map.empty |
  True \<Rightarrow> f |` V
)"

(* Note: Explain why we use nat <the cardinality of keys> here. The function can't work with set constructors*)
fun allMaps :: "nat \<Rightarrow> Variable set \<Rightarrow> 'a set \<Rightarrow> 'a Valuation set" where
"allMaps 0 keys values = { Map.empty }" |
"allMaps n keys values = (\<Union> {
    {
      m(k \<mapsto> v) | m v. v \<in> values \<and> m \<in> (allMaps (n-1) (keys - {k}) values)
    } | k. k \<in> keys
  })"

fun buildValuation :: "Variable list \<Rightarrow> 'a list \<Rightarrow> 'a Valuation"  where
"buildValuation [] [] = Map.empty " |
"buildValuation variables values = Map.empty (variables [\<mapsto>] values)"

fun isParent :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> bool" where
"isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi> = (
  let
    formula_list = (formulaToList \<phi>);
    \<psi>\<^sub>1 = (FoI (Index \<J>\<^sub>1) formula_list);
    \<psi>\<^sub>2 = (FoI (Index \<J>\<^sub>2) formula_list)
  in ( case (\<psi>\<^sub>1) of
    (Atom r var_list) \<Rightarrow> False |
    (Forall x \<phi>\<^sub>1) \<Rightarrow> (
      ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1 ) \<and>
      (\<psi>\<^sub>2 = \<phi>\<^sub>1)
    ) |
    (Exists x \<phi>\<^sub>1) \<Rightarrow> (
      ((Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1 ) \<and>
      (\<psi>\<^sub>2 = \<phi>\<^sub>1)
    ) |
    (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<Rightarrow> (
      (
        ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1 ) \<and>
        (\<psi>\<^sub>2 = \<phi>\<^sub>1)
      ) \<or> (
        ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 2 ) \<and>
        (\<psi>\<^sub>2 = \<phi>\<^sub>2)
      )
    )
  )
)"

(* ======================== Tests ======================== *)

end