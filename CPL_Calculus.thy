theory "CPL_Calculus"        
  imports Main
begin

(* ======================== Syntax ======================== *)

(* ================= Type Definitions ================= *)

(* Note: Explain the caveats of using string. We will have to keep using char for now *)
type_synonym Variable =  "char"
type_synonym Relation =  "char"
datatype Formula =
  Atom (Rel: "Relation") (VarList: "Variable list")
| And (and_f1: "Formula") (and_f2: "Formula")
| Forall (forall_x: "Variable") (forall_f: "Formula")
| Exists (exists_x: "Variable") (exists_f: "Formula")

(* ================= Auxiliary Functions ================= *)

fun freeVar :: "Formula \<Rightarrow> Variable set" where
"freeVar (Atom r var_list) = set var_list" |
"freeVar (And \<phi>\<^sub>0 \<phi>\<^sub>1) = freeVar \<phi>\<^sub>0 \<union> freeVar \<phi>\<^sub>1" |
"freeVar (Forall x \<phi>) = freeVar \<phi> - {x}" |
"freeVar (Exists x \<phi>) = freeVar \<phi> - {x}"

fun sentence :: "Formula \<Rightarrow> bool" where
"sentence \<phi> = ((freeVar \<phi>) = {})"

fun isFormulaAtom :: "Formula \<Rightarrow> bool" where
"isFormulaAtom (Atom r var_list) = True" |
"isFormulaAtom (And \<phi>\<^sub>1 \<phi>\<^sub>2) = False" |
"isFormulaAtom (Forall x \<phi>) = False" |
"isFormulaAtom (Exists x \<phi>) = False"

fun isFormulaAnd :: "Formula \<Rightarrow> bool" where
"isFormulaAnd (Atom r var_list) = False" |
"isFormulaAnd (And \<phi>\<^sub>1 \<phi>\<^sub>2) = True" |
"isFormulaAnd (Forall x \<phi>) = False" |
"isFormulaAnd (Exists x \<phi>) = False"

fun isFormulaForAll :: "Formula \<Rightarrow> bool" where
"isFormulaForAll (Atom r var_list) = False" |
"isFormulaForAll (And \<phi>\<^sub>1 \<phi>\<^sub>2) = False" |
"isFormulaForAll (Forall x \<phi>) = True" |
"isFormulaForAll (Exists x \<phi>) = False"

(* ======================== Semantics ======================== *)

(* ================= Type Definitions ================= *)
type_synonym Signature =  "Relation \<rightharpoonup> nat"
type_synonym 'a Interpretation = "Relation \<rightharpoonup> 'a list set"
datatype 'a Structure =  Structure (Sig: "Signature") (Univ: "'a set")  (Interp: "'a Interpretation")

type_synonym 'a Valuation = "Variable \<rightharpoonup> 'a"
datatype 'a Judgement =  Judgement (Index: "nat") (Vars:  "Variable set") (Funcs:  "'a Valuation set")

(* ================= Auxiliary Functions ================= *)

fun formulaToList :: "Formula \<Rightarrow> Formula list" where
"formulaToList (Atom r var_list) = [Atom r var_list]" |
"formulaToList (And \<phi>\<^sub>1 \<phi>\<^sub>2) = [And \<phi>\<^sub>1 \<phi>\<^sub>2, \<phi>\<^sub>1, \<phi>\<^sub>2] @ (tl (formulaToList \<phi>\<^sub>1)) @ (tl (formulaToList \<phi>\<^sub>2))" |
"formulaToList (Forall x \<phi>) = [Forall x \<phi>] @ (formulaToList \<phi>)" |
"formulaToList (Exists x \<phi>) = [Exists x \<phi>] @ (formulaToList \<phi>)"

fun setOfIndex :: "Formula list \<Rightarrow> nat set" where
"setOfIndex formula_list = {1..(length formula_list)}"

fun FoI :: "nat \<Rightarrow> Formula list \<Rightarrow> Formula" where
"FoI formula_index formula_list = formula_list ! (formula_index - 1)"

(* ================= Well-Formedness Functions ================= *)

fun wfFormula :: "Formula \<Rightarrow> Signature \<Rightarrow> bool" where
"wfFormula (Atom r var_list) signature = (
    case (signature r) of
    None \<Rightarrow> False |
    (Some n) \<Rightarrow> length(var_list) = n
  )" |
"wfFormula (And \<phi>\<^sub>1 \<phi>\<^sub>2) signature = ((wfFormula \<phi>\<^sub>1 signature) \<and> (wfFormula \<phi>\<^sub>2 signature))" |
"wfFormula (Forall x \<phi>) signature = (wfFormula \<phi> signature)" |
"wfFormula (Exists x \<phi>) signature = (wfFormula \<phi> signature)"

(* Note: Añadimos (set l \<subseteq> universe) para que se confirme que los datos pertenecen al dominio *)
fun wfStructure :: "'a Structure \<Rightarrow> bool" where
"wfStructure (Structure signature universe interpretation) = (
  ( universe \<noteq> {} )  \<and>
  ( \<forall>r. r \<in> (dom signature) \<longrightarrow> (
      case (interpretation r) of
      None \<Rightarrow> False |
      (Some set_of_lists) \<Rightarrow> ( \<forall>l \<in> set_of_lists. (
         case (signature r) of
         None \<Rightarrow> False |
         (Some n) \<Rightarrow> (length(l) = n) \<and> (set l \<subseteq> universe)
        )
      )
    )
  )
)"

fun wfCPLInstance :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfCPLInstance \<phi> \<B> = (
  (wfStructure \<B>) \<and>
  (sentence \<phi>) \<and>
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

(* ================= Proof System Functions ================= *)

(* Note: |` is called restrict_map operator. m |` A = (\<lambda>x. if x \<in> A then m x else None) *)
fun projectValuation :: "'a Valuation \<Rightarrow> Variable set \<Rightarrow> 'a Valuation" where
"projectValuation f V = (case (V \<subseteq> (dom f)) of
  False \<Rightarrow> Map.empty |
  True \<Rightarrow> f |` V
)"

(* Note: Explain why we use nat <the cardinaility of keys> here. The function can't work with set constructors*)
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

fun isAtom :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isAtom \<J> \<phi> \<B> = (
  let
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>));
    interpretation = (Interp \<B>)
  in
    (isFormulaAtom \<psi>) \<and>
    ((Vars \<J>) = (set (VarList \<psi>))) \<and>
    (case (interpretation (Rel \<psi>)) of
      None \<Rightarrow> False |
      Some set_of_list \<Rightarrow> (
        (Funcs \<J>) = { buildValuation (VarList \<psi>) l | l. l \<in> set_of_list}
      )
    )
)"

fun isProjection :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isProjection \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) ) \<and>
  ( (Funcs \<J>\<^sub>1) = {projectValuation f (Vars \<J>\<^sub>1) | f. f \<in> (Funcs \<J>\<^sub>2)} )
)"

fun isDualProjection :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isDualProjection \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi> ) \<and>
  (
    let
      formula_list = (formulaToList \<phi>);
      \<psi>\<^sub>1 = (FoI (Index \<J>\<^sub>1) formula_list);
      \<psi>\<^sub>2 = (FoI (Index \<J>\<^sub>2) formula_list);
      y = (forall_x \<psi>\<^sub>1)
    in (
      ( isFormulaForAll \<psi>\<^sub>1 ) \<and>
      ( \<psi>\<^sub>1 = (Forall y \<psi>\<^sub>2) ) \<and>
      ( y \<in> (Vars \<J>\<^sub>2) )  \<and>
      ( (Vars \<J>\<^sub>1) = (Vars \<J>\<^sub>2) - ({y}) )  \<and>
      (
        {
          h \<in> (allMaps (card (Vars \<J>\<^sub>1)) (Vars \<J>\<^sub>1) (Univ \<B>)). (
            \<forall>b \<in> (Univ \<B>). h(y \<mapsto> b) \<in> (Funcs \<J>\<^sub>2)
          )
        } = (Funcs \<J>\<^sub>1)
      )
    )
  )
)"

fun isJoin :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isJoin \<J> \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J> \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( (Vars \<J>) = ((Vars \<J>\<^sub>1) \<union> (Vars \<J>\<^sub>2)) ) \<and>
  ( isFormulaAnd (FoI (Index \<J>) (formulaToList \<phi>)) ) \<and>
  ( (isParent \<J> \<J>\<^sub>1 \<phi>) \<and> (isParent \<J> \<J>\<^sub>2 \<phi>) ) \<and>
  (
    let
      variables = (Vars \<J>\<^sub>1) \<union> (Vars \<J>\<^sub>2)
    in (
      {
        f \<in> (allMaps (card variables) variables (Univ \<B>)). (
          ( (projectValuation f (Vars \<J>\<^sub>1)) \<in> (Funcs \<J>\<^sub>1) ) \<and>
          ( (projectValuation f (Vars \<J>\<^sub>2)) \<in> (Funcs \<J>\<^sub>2) )
        )
      } = (Funcs \<J>)
    )
  )
)"

fun isUpwardFlow :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isUpwardFlow \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
    ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
    ( (Vars \<J>\<^sub>1) = (Vars \<J>\<^sub>2) ) \<and>
    ( (Funcs \<J>\<^sub>1) = (Funcs \<J>\<^sub>2) ) \<and>
    ( isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi> )
)"

(* ================= Proof System ================= *)

inductive isDerivable :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement \<Rightarrow> bool" for \<phi> and \<B> where
(* Atom rule *)
ATR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  isAtom \<J> \<phi> \<B>
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| (* Projection rule *)
PJR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (isProjection \<J> \<J>' \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>')
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| (* Join rule *)
JNR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>\<^sub>0 \<J>\<^sub>1. (
    (isJoin \<J> \<J>\<^sub>0 \<J>\<^sub>1 \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>\<^sub>0 \<and> isDerivable \<phi> \<B> \<J>\<^sub>1)
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| (* \<forall>-elimination rule *)
FER: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
      (isDualProjection \<J> \<J>' \<phi> \<B>) \<and>
      (isDerivable \<phi> \<B> \<J>')
    )
  )
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| (* Upward-flow rule *)
UFR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (isUpwardFlow \<J> \<J>' \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>')
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"

(* ======================== Tests ======================== *)

datatype BEnum = A | B | C (* Finite datatype *)

lemma BEnum_induct: "\<lbrakk>x \<noteq> A; x \<noteq> B\<rbrakk> \<Longrightarrow> x = C"
  apply(cases x)
  by auto

lemma UNIV_BEnum: "UNIV = {A, B, C}"
  by (auto simp add: BEnum_induct)

(* Note: We must indicate that this type is an enum to use ran and dom *)
instantiation BEnum :: enum
begin
definition "Enum.enum = [A,B,C]"
definition "Enum.enum_all P \<longleftrightarrow> (Ball {A,B,C} P)"
definition "Enum.enum_ex P \<longleftrightarrow> (Bex {A,B,C} P)"

instance proof
qed (auto simp add: enum_BEnum_def enum_all_BEnum_def enum_ex_BEnum_def UNIV_BEnum)
end

abbreviation "myUniverse::(BEnum set) \<equiv> {A,B,C}"
abbreviation "mySignature::(Signature) \<equiv> [CHR ''E'' \<mapsto> 2]"
abbreviation "myInterpretation::(BEnum Interpretation) \<equiv> [CHR ''E'' \<mapsto> {[A,A],[A,C],[B,A]}]"
abbreviation "myStructure::(BEnum Structure) \<equiv> (Structure mySignature myUniverse myInterpretation)"

value "wfStructure myStructure"

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

value "formulaToList myFormula"

value "wfFormula myFormula mySignature"

abbreviation "myValuationSet::(BEnum Valuation set) \<equiv> {
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> A],
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> C],
  [CHR ''x'' \<mapsto> B, CHR ''y'' \<mapsto> A]
}"
abbreviation "myFreeVariableSet::(Variable set) \<equiv> {CHR ''x'', CHR ''y''}"
abbreviation "myJudgement::(BEnum Judgement) \<equiv> (Judgement 6 myFreeVariableSet myValuationSet)"


abbreviation "atomJudgement \<equiv> myJudgement"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement atomJudgement myFormula myStructure"
value "isAtom atomJudgement myFormula myStructure"



abbreviation "projectionBaseJudgement \<equiv> myJudgement"
abbreviation "projectionProjectedJudgement::(BEnum Judgement) \<equiv> (Judgement 6 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement projectionBaseJudgement myFormula myStructure"
value "wfJudgement projectionProjectedJudgement myFormula myStructure"
value "isProjection projectionProjectedJudgement projectionBaseJudgement myFormula myStructure"



abbreviation "joinFirstChildJudgement::(BEnum Judgement) \<equiv> (Judgement 4 myFreeVariableSet myValuationSet)"
abbreviation "joinSecondChildJudgement::(BEnum Judgement) \<equiv> (Judgement 5 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
abbreviation "joinParentJudgement::(BEnum Judgement) \<equiv> (Judgement 3 myFreeVariableSet {
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> A],
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> C],
  [CHR ''x'' \<mapsto> B, CHR ''y'' \<mapsto> A]
})"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement joinFirstChildJudgement myFormula myStructure"
value "wfJudgement joinSecondChildJudgement myFormula myStructure"
value "wfJudgement joinParentJudgement myFormula myStructure"
value "isJoin joinParentJudgement joinFirstChildJudgement joinSecondChildJudgement myFormula myStructure"



abbreviation "forAllBaseJudgement::(BEnum Judgement) \<equiv> (Judgement 3 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
abbreviation "forAllDualProjectedJudgement::(BEnum Judgement) \<equiv> (Judgement 2 {} {})"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement forAllBaseJudgement myFormula myStructure"
value "wfJudgement forAllDualProjectedJudgement myFormula myStructure"
value "isDualProjection forAllDualProjectedJudgement forAllBaseJudgement myFormula myStructure"



abbreviation "upwardBaseJudgement \<equiv> projectionProjectedJudgement"
abbreviation "upwardFlowedJudgement::(BEnum Judgement) \<equiv> (Judgement 5 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement upwardBaseJudgement myFormula myStructure"
value "wfJudgement upwardFlowedJudgement myFormula myStructure"
value "isUpwardFlow upwardFlowedJudgement upwardBaseJudgement myFormula myStructure"

end