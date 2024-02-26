theory "CPL_Calculus"
  imports Main
begin

(* ======================== Syntax ======================== *)

(* ================= Type Definitions ================= *)

(*TODO: Explain the caveats of using string. We will have to keep using char for now *)
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

fun isAtom :: "Formula \<Rightarrow> bool" where
"isAtom (Atom r var_list) = True" |
"isAtom (And \<phi>\<^sub>1 \<phi>\<^sub>2) = False" |
"isAtom (Forall x \<phi>) = False" |
"isAtom (Exists x \<phi>) = False"

fun isAnd :: "Formula \<Rightarrow> bool" where
"isAnd (Atom r var_list) = False" |
"isAnd (And \<phi>\<^sub>1 \<phi>\<^sub>2) = True" |
"isAnd (Forall x \<phi>) = False" |
"isAnd (Exists x \<phi>) = False"

fun isForall :: "Formula \<Rightarrow> bool" where
"isForall (Atom r var_list) = False" |
"isForall (And \<phi>\<^sub>1 \<phi>\<^sub>2) = False" |
"isForall (Forall x \<phi>) = True" |
"isForall (Exists x \<phi>) = False"

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
"formulaToList (And \<phi>\<^sub>1 \<phi>\<^sub>2) = [And \<phi>\<^sub>1 \<phi>\<^sub>2] @ (formulaToList \<phi>\<^sub>1) @ (formulaToList \<phi>\<^sub>2)" |
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

(* TODO: Explicar por qué añadimos (set l \<subseteq> universe) *)
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

(* TODO: Check if we can make this function work with Map functions *)
fun projectValuation :: "'a Valuation \<Rightarrow> Variable set \<Rightarrow> 'a Valuation" where
"projectValuation f V = (
  \<lambda>x. if V \<subseteq> (dom f) \<and> x \<in> V then f x else None
)"

fun buildValuation :: "Variable list \<Rightarrow> 'a list \<Rightarrow> 'a Valuation"  where
"buildValuation [] [] = Map.empty " |
"buildValuation variables values = Map.empty (variables [\<mapsto>] values)"

fun isProjection :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isProjection \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) ) \<and>
  ( (Funcs \<J>\<^sub>1) = {projectValuation f (Vars \<J>\<^sub>1) | f. f \<in> (Funcs \<J>\<^sub>2)} )
)"

fun isDualProjection :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isDualProjection \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) )
)" (* TODO: Finish this function *)

fun isJoin :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isJoin \<J> \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  (  (wfJudgement \<J> \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( ((Index \<J>) = (Index \<J>\<^sub>1)) \<and> ((Index \<J>\<^sub>1) = (Index \<J>\<^sub>2)) ) \<and>
  ( ((Vars \<J>) = (Vars \<J>\<^sub>1)) \<and> ((Vars \<J>\<^sub>1) = (Vars \<J>\<^sub>2)) )
)" (* TODO: Finish this function *)

fun isUpwardFlow :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isUpwardFlow \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( (Vars \<J>\<^sub>1) = (Vars \<J>\<^sub>2) ) \<and>
  ( (Funcs \<J>\<^sub>1) = (Funcs \<J>\<^sub>2) ) \<and>
  ( (Index \<J>\<^sub>1 + 1) = (Index \<J>\<^sub>2) )
)" (* TODO: Fix this function, we cannot use Index J_1 + 1 to indicate the parent *)

(* ================= Proof System ================= *)

inductive isDerivable :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
(* Atom rule *)
ATR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (let
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>));
    interpretation = (Interp \<B>);
    V = (Vars \<J>)
  in
    (isAtom \<psi>) \<and>
    (V = (set (VarList \<psi>))) \<and>
    (\<exists>set_of_list. (
        ((interpretation (Rel \<psi>)) = Some set_of_list) \<and>
        ((Funcs \<J>) = { buildValuation (VarList \<psi>) l | l. l \<in> set_of_list})
      )
    )
  )
  \<rbrakk> \<Longrightarrow> isDerivable \<J> \<phi> \<B>"
| (* Projection rule *)
PJR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (wfJudgement \<J>' \<phi> \<B>) \<and>
    (isProjection \<J> \<J>' \<phi> \<B>) \<and>
    (isDerivable \<J>' \<phi> \<B>)
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<J> \<phi> \<B>"
| (* Join rule *)
JNR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (let
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>))
  in
    (isAnd \<psi>)
  );
  (\<exists>\<J>\<^sub>0 \<J>\<^sub>1. (
    (wfJudgement \<J>\<^sub>0 \<phi> \<B> \<and> wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and>
    ((Index \<J>\<^sub>1) = (Index \<J>\<^sub>0)) \<and>
    (isDerivable \<J>\<^sub>0 \<phi> \<B> \<and> isDerivable \<J>\<^sub>1 \<phi> \<B>) \<and>
    (isJoin \<J> \<J>\<^sub>0 \<J>\<^sub>1 \<phi> \<B>)
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<J> \<phi> \<B>"
(*| (* \<forall>-elimination rule *)
FER: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (let
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>))
  in
    (isForall \<psi>) \<and>
    (\<exists>\<J>'. (
      (wfJudgement \<J>' \<phi> \<B>) \<and>
      (\<psi> = (Forall (forall_x \<psi>) (FoI (Index \<J>') (formulaToList \<phi>)))) \<and>
      (isDerivable \<J>' \<phi> \<B>) \<and>
      (isDualProjection \<J> \<J>' \<phi> \<B>)
    ))
  )
  \<rbrakk> \<Longrightarrow> isDerivable \<J> \<phi> \<B>" *)
| (* Upward-flow rule *)
UFR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (wfJudgement \<J>' \<phi> \<B>) \<and>
    (isDerivable \<J>' \<phi> \<B>) \<and>
    (isUpwardFlow \<J> \<J>' \<phi> \<B>)
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<J> \<phi> \<B>"

(* ======================== Tests ======================== *)

datatype BEnum = A | B | C (* Finite datatype *)

lemma BEnum_induct: "\<lbrakk>x \<noteq> A; x \<noteq> B\<rbrakk> \<Longrightarrow> x = C"
  apply(cases x)
  by auto

lemma UNIV_BEnum: "UNIV = {A, B, C}"
  by (auto simp add: BEnum_induct)

instantiation BEnum :: enum (* We must indicate that this type is an enum to use ran and dom *)
begin
definition "Enum.enum = [A,B,C]"
definition "Enum.enum_all P \<longleftrightarrow> P A \<and> P B \<and> P C"
definition "Enum.enum_ex P \<longleftrightarrow> P A \<or> P B \<or> P C"

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