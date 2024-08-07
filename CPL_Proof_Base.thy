theory "CPL_Proof_Base"
  imports Main "CPL_Semantic"
begin

(* ==================== Proof System Base ==================== *)

(* ======================== Type Definitions ======================== *)

type_synonym 'a Valuation = "Variable \<rightharpoonup> 'a" \<comment> \<open> Represented by f \<close>
datatype 'a Judgement =  Judgement (Index: "nat") (Vars:  "Variable set") (Funcs:  "'a Valuation set") \<comment> \<open> Represented by \<J>, and internally by index \<V> \<F> \<close>

abbreviation "e \<equiv> Map.empty"
abbreviation "NullJudgement \<equiv> (Judgement 1 {} {})"
abbreviation "EmptyJudgement \<equiv> (Judgement 1 {} {e})"

(* ======================== Auxiliary Functions ======================== *)

fun isParent :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula list \<Rightarrow> nat list \<Rightarrow> bool" where
"isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi>\<^sub>L P\<^sub>L = (
  let
    \<psi>\<^sub>1 = (FoI (Index \<J>\<^sub>1) \<phi>\<^sub>L);
    \<psi>\<^sub>2 = (FoI (Index \<J>\<^sub>2) \<phi>\<^sub>L)
  in ( case (\<psi>\<^sub>1) of
    (Atom r var_list) \<Rightarrow> False |
    (Forall x \<phi>\<^sub>1) \<Rightarrow> ( ((Index \<J>\<^sub>1) = (P\<^sub>L ! (Index \<J>\<^sub>2 - 1)) ) \<and> (\<psi>\<^sub>2 = \<phi>\<^sub>1) ) |
    (Exists x \<phi>\<^sub>1) \<Rightarrow> ( ((Index \<J>\<^sub>1) = (P\<^sub>L ! (Index \<J>\<^sub>2 - 1)) ) \<and> (\<psi>\<^sub>2 = \<phi>\<^sub>1) ) |
    (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<Rightarrow> (
      ( (Index \<J>\<^sub>1) = (P\<^sub>L ! (Index \<J>\<^sub>2 - 1)) ) \<and> ( (\<psi>\<^sub>2 = \<phi>\<^sub>1) \<or> (\<psi>\<^sub>2 = \<phi>\<^sub>2) )
    )
  )
)"

(* ======================== Well-Formedness Functions ======================== *)

fun wfJudgement :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfJudgement \<J> \<phi> \<B> = (let
    (\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>;
    judgement_index = (Index \<J>);
    judgement_free_vars = (Vars \<J>);
    judgement_valuations = (Funcs \<J>);
    structure_domain = (Univ \<B>)
  in (
    ( wfCPLInstance \<phi> \<B> ) \<and>
    ( judgement_index \<in> (setOfIndex P\<^sub>L) ) \<and>
    ( judgement_free_vars \<subseteq> (freeVar (FoI judgement_index \<phi>\<^sub>L)) ) \<and>
    ( \<forall>f \<in> judgement_valuations. ((dom f) = judgement_free_vars) )  \<and>
    ( \<forall>f \<in> judgement_valuations. ((ran f) \<subseteq> structure_domain) )
  )
)"

(* ==================== Tests ==================== *)

abbreviation "myValuationSet::(BEnum Valuation set) \<equiv> {
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> A],
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> C],
  [CHR ''x'' \<mapsto> B, CHR ''y'' \<mapsto> A]
}"
abbreviation "myFreeVariableSet::(Variable set) \<equiv> {CHR ''x'', CHR ''y''}"
abbreviation "myJudgement::(BEnum Judgement) \<equiv> (Judgement 6 myFreeVariableSet myValuationSet)"

lemma [simp] : "wfJudgement myJudgement myFormula myStructure = True"
  by(auto simp add: Let_def)

end