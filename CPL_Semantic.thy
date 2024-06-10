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

fun buildFormulaParentList :: "Formula \<Rightarrow> (Formula list) \<times> (nat list)" where
"buildFormulaParentList (Atom r var_list) = ([(Atom r var_list)], [0])" |
"buildFormulaParentList (Forall x \<phi>) = (let
    (formula_list, parent_list) = (buildFormulaParentList \<phi>);
    new_parent_list = (map ((+) 1) parent_list)
  in (
     ((Forall x \<phi>) # formula_list, 0 # new_parent_list)
  )
)" |
"buildFormulaParentList (Exists x \<phi>) = (let
    (formula_list, parent_list) = (buildFormulaParentList \<phi>);
    new_parent_list = (map ((+) 1) parent_list)
  in (
     ((Exists x \<phi>) # formula_list, 0 # new_parent_list)
  )
)" |
"buildFormulaParentList (And \<phi>\<^sub>1 \<phi>\<^sub>2) = (let
    (formula_list_\<phi>\<^sub>1, parent_list_\<phi>\<^sub>1) = (buildFormulaParentList \<phi>\<^sub>1);
    new_parent_list_\<phi>\<^sub>1 = (map ((+) 1) parent_list_\<phi>\<^sub>1);
    (formula_list_\<phi>\<^sub>2, parent_list_\<phi>\<^sub>2) = (buildFormulaParentList \<phi>\<^sub>2);
    temp_new_parent_list_\<phi>\<^sub>2 = (map ((+) (1 + (length parent_list_\<phi>\<^sub>1))) parent_list_\<phi>\<^sub>2);
    new_parent_list_\<phi>\<^sub>2 = 1 # (tl temp_new_parent_list_\<phi>\<^sub>2)
  in (
    ((And \<phi>\<^sub>1 \<phi>\<^sub>2) # formula_list_\<phi>\<^sub>1 @ formula_list_\<phi>\<^sub>2, 0 # new_parent_list_\<phi>\<^sub>1 @ new_parent_list_\<phi>\<^sub>2)
  )
)"

fun setOfIndex :: "nat list \<Rightarrow> nat set" where
"setOfIndex parent_list = { 1 .. (length parent_list) }"

fun FoI :: "nat \<Rightarrow> Formula list \<Rightarrow> Formula" where
"FoI i formula_list = formula_list ! (i - 1)"

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
    (formula_list, parent_list) = buildFormulaParentList \<phi>;
    judgement_index = (Index \<J>);
    judgement_free_vars = (Vars \<J>);
    judgement_valuations = (Funcs \<J>);
    structure_domain = (Univ \<B>)
  in (
    ( wfCPLInstance \<phi> \<B> ) \<and>
    ( judgement_index \<in> (setOfIndex parent_list) ) \<and>
    ( judgement_free_vars \<subseteq> (freeVar (FoI judgement_index formula_list)) ) \<and>
    ( \<forall>f \<in> judgement_valuations. ((dom f) = judgement_free_vars) )  \<and>
    ( \<forall>f \<in> judgement_valuations. ((ran f) \<subseteq> structure_domain) )
  )
)"

(* ==================== Tests ==================== *)

abbreviation "myUniverse::(BEnum set) \<equiv> {A,B,C}"
abbreviation "mySignature::(Signature) \<equiv> [CHR ''E'' \<mapsto> 2]"

abbreviation "myExtendedFormula \<equiv> (
  Exists (CHR ''x'') (
    Forall (CHR ''y'') (
      And (
        Exists (CHR ''z'') (
          And (
            (Atom (CHR ''E'') [CHR ''z'', CHR ''x''])
          ) (
            (Atom (CHR ''E'') [CHR ''x'', CHR ''y''])
          )
        )
      )
      (
        Forall (CHR ''w'') (
          And (
            And (
              (Atom (CHR ''E'') [CHR ''y'', CHR ''w''])
            ) (
              (Atom (CHR ''E'') [CHR ''y'', CHR ''w''])
            )
          ) (
            And (
              Forall (CHR ''b'') (
                (Atom (CHR ''E'') [CHR ''y'', CHR ''b''])
              )
            ) (
              (Atom (CHR ''E'') [CHR ''y'', CHR ''w''])
            )
          )
        )
      )
    )
  )
)"
abbreviation "myParentList \<equiv> [0,1,2,3,4,5,5,3,8,9,10,10,9,13,14,13]"

lemma "(snd (buildFormulaParentList myExtendedFormula)) = myParentList"
  by auto

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

lemma [simp] : "wfCPLInstance myFormula myStructure = True"
  by(auto)

lemma [simp] : "wfJudgement myJudgement myFormula myStructure = True"
  by(auto simp add: Let_def)

end