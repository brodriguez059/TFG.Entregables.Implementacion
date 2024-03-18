theory "CPL_Instance"
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

value "wfJudgement myJudgement myFormula myStructure"

end