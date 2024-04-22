theory "CPL_Semantic"
  imports Main "CPL_Syntax"
begin

(* ==================== Semantics ==================== *)

(* ======================== Type Definitions ======================== *)

type_synonym Signature =  "Relation \<rightharpoonup> nat" \<comment> \<open> Represented by \<S> \<close>
type_synonym 'a Interpretation = "Relation \<rightharpoonup> 'a list set" \<comment> \<open> Represented by \<I> \<close>
datatype 'a Structure =  Structure (Sig: "Signature") (Univ: "'a set")  (Interp: "'a Interpretation") \<comment> \<open> Represented by \<B>, and internally by \<S> universe \<I> \<close>

type_synonym 'a Valuation = "Variable \<rightharpoonup> 'a" \<comment> \<open> Represented by f \<close>
datatype 'a Judgement =  Judgement (Index: "nat") (Vars:  "Variable set") (Funcs:  "'a Valuation set") \<comment> \<open> Represented by \<J>, and internally by index \<V> \<F> \<close>

(* ======================== Auxiliary Functions ======================== *)

fun formulaToList :: "Formula \<Rightarrow> Formula list" where
"formulaToList (Atom r var_list) = [Atom r var_list]" |
"formulaToList (And \<phi>\<^sub>1 \<phi>\<^sub>2) = [And \<phi>\<^sub>1 \<phi>\<^sub>2, \<phi>\<^sub>1, \<phi>\<^sub>2] @ (tl (formulaToList \<phi>\<^sub>1)) @ (tl (formulaToList \<phi>\<^sub>2))" |
"formulaToList (Forall x \<phi>) = [Forall x \<phi>] @ (formulaToList \<phi>)" |
"formulaToList (Exists x \<phi>) = [Exists x \<phi>] @ (formulaToList \<phi>)"

fun setOfIndex :: "Formula list \<Rightarrow> nat set" where
"setOfIndex formula_list = { 1 .. (length formula_list) }"

fun FoI :: "nat \<Rightarrow> Formula list \<Rightarrow> Formula" where
"FoI formula_index formula_list = formula_list ! (formula_index - 1)"

(* ======================== Well-Formedness Functions ======================== *)

fun wfFormula :: "Formula \<Rightarrow> Signature \<Rightarrow> bool" where
"wfFormula (Atom r var_list) \<S> = (
    case (\<S> r) of
    None \<Rightarrow> False |
    (Some n) \<Rightarrow> ((length var_list) = n)
)" |
"wfFormula (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<S> = ((wfFormula \<phi>\<^sub>1 \<S>) \<and> (wfFormula \<phi>\<^sub>2 \<S>))" |
"wfFormula (Forall x \<phi>) \<S> = (wfFormula \<phi> \<S>)" |
"wfFormula (Exists x \<phi>) \<S> = (wfFormula \<phi> \<S>)"


fun wfStructure :: "'a Structure \<Rightarrow> bool" where
"wfStructure (Structure \<S> universe \<I>) = (
  ( universe \<noteq> {} )  \<and>
  ( \<forall>r. r \<in> (dom \<S>) \<longrightarrow> (
      case (\<I> r) of
      None \<Rightarrow> False |
      (Some set_of_lists) \<Rightarrow> (case (\<S> r) of
         None \<Rightarrow> False |
         (Some n) \<Rightarrow> (\<forall>l \<in> set_of_lists. ((length l) = n) \<and> ((set l) \<subseteq> universe)) \<comment> \<open> Note: Añadimos (set l \<subseteq> universe) para que se confirme que los datos pertenecen al dominio \<close>
      )
    )
  )
)"

fun wfCPLInstance :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfCPLInstance \<phi> \<B> = (
  (sentence \<phi>) \<and>  
  (wfStructure \<B>) \<and>
  (wfFormula \<phi> (Sig \<B>))
)"

fun wfJudgement :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfJudgement \<J> \<phi> \<B> = (let
    formula_list = formulaToList \<phi>;
    judgement_index = (Index \<J>);
    judgement_free_vars = (Vars \<J>);
    judgement_valuations = (Funcs \<J>);
    structure_domain = (Univ \<B>)
  in (
    ( wfCPLInstance \<phi> \<B> ) \<and>
    ( judgement_index \<in> (setOfIndex formula_list) ) \<and>
    ( judgement_free_vars \<subseteq> (freeVar (FoI judgement_index formula_list)) ) \<and>
    ( \<forall>f \<in> judgement_valuations. ((dom f) = judgement_free_vars) )  \<and>
    ( \<forall>f \<in> judgement_valuations. ((ran f) \<subseteq> structure_domain) )
  )
)"

(* ==================== Tests ==================== *)

abbreviation "myUniverse::(BEnum set) \<equiv> {A,B,C}"
abbreviation "mySignature::(Signature) \<equiv> [CHR ''E'' \<mapsto> 2]"
abbreviation "myFormula \<equiv> (
  Exists (CHR ''x'') (
    Forall (CHR ''y'') (
      And (
        (Atom (CHR ''E'') [CHR ''x'', CHR ''y'']))
        (Exists (CHR ''x'') (
          Atom (CHR ''E'') [CHR ''x'',CHR ''y'']
        )
      )
    )
  )
)"

lemma "wfFormula myFormula mySignature = True"
  by auto



abbreviation "myInterpretation::(BEnum Interpretation) \<equiv> [CHR ''E'' \<mapsto> {[A,A],[A,C],[B,A]}]"
abbreviation "myStructure::(BEnum Structure) \<equiv> (Structure mySignature myUniverse myInterpretation)"

lemma "wfStructure myStructure = True"
  by auto

abbreviation "myValuationSet::(BEnum Valuation set) \<equiv> {
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> A],
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> C],
  [CHR ''x'' \<mapsto> B, CHR ''y'' \<mapsto> A]
}"
abbreviation "myFreeVariableSet::(Variable set) \<equiv> {CHR ''x'', CHR ''y''}"
abbreviation "myJudgement::(BEnum Judgement) \<equiv> (Judgement 6 myFreeVariableSet myValuationSet)"

lemma "wfJudgement myJudgement myFormula myStructure = True"
  by(auto simp add: Let_def)

end