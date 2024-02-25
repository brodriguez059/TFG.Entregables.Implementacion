theory "CPL_Calculus"
  imports Main
begin

(* ======================== Syntax ======================== *)

(* ================= Type Definitions ================= *)

(*TODO: Look for a way of defining string with compatible dom operation for partial mappings (instead of using char)*)
type_synonym Variable =  "char"
type_synonym Relation =  "char"
datatype Formula =
  Atom Relation "Variable list"
| And Formula Formula
| Forall Variable Formula
| Exists Variable Formula

(* ================= Auxiliary Formulas ================= *)

fun freeVar :: "Formula \<Rightarrow> Variable set" where
"freeVar(Atom r var_list) = set var_list" |
"freeVar(And \<phi>\<^sub>0 \<phi>\<^sub>1) = freeVar \<phi>\<^sub>0 \<union> freeVar \<phi>\<^sub>1" |
"freeVar(Forall x \<phi>) = freeVar \<phi> - {x}" |
"freeVar(Exists x \<phi>) = freeVar \<phi> - {x}"

fun sentence :: "Formula \<Rightarrow> bool" where
"sentence \<phi> = ((freeVar \<phi>) = {})"

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
"formulaToList (And \<phi>\<^sub>0 \<phi>\<^sub>1) = [And \<phi>\<^sub>0 \<phi>\<^sub>1] @ (formulaToList \<phi>\<^sub>0) @ (formulaToList \<phi>\<^sub>1)" |
"formulaToList (Forall x \<phi>) = [Forall x \<phi>] @ (formulaToList \<phi>)" |
"formulaToList (Exists x \<phi>) = [Exists x \<phi>] @ (formulaToList \<phi>)"

fun setOfIndex :: "Formula list \<Rightarrow> nat set" where
"setOfIndex formula_list = {1..((length formula_list) + 1)}"

(* Operator `!` is the get by index operator. TODO: Add signature here to maintain well formedness *)
fun FoI :: "nat \<Rightarrow> Formula list \<Rightarrow> Formula" where
"FoI formula_index formula_list = formula_list ! formula_index"

(* ================= Well-Formedness Functions ================= *)

fun wfFormula :: "Formula \<Rightarrow> Signature \<Rightarrow> bool" where
"wfFormula (Atom r var_list) signature = (
    case (signature r) of
    None \<Rightarrow> False |
    (Some n) \<Rightarrow> length(var_list) = n
  )" |
"wfFormula (And \<phi>\<^sub>0 \<phi>\<^sub>1) signature = ((wfFormula \<phi>\<^sub>0 signature) \<and> (wfFormula \<phi>\<^sub>1 signature))" |
"wfFormula (Forall x \<phi>) signature = (wfFormula \<phi> signature)" |
"wfFormula (Exists x \<phi>) signature = (wfFormula \<phi> signature)"

(* TODO: Explicar el porqué añadimos (set l \<subseteq> universe) *)
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

fun wfCPL_Instance :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfCPL_Instance \<phi> \<B> = (let
  structure_signature = (Sig \<B>)
  in (
  (wfStructure \<B>) \<and>
  (sentence \<phi>) \<and>
  (wfFormula \<phi> structure_signature)
  )
)"

fun wfJudgement :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfJudgement \<J> \<phi> \<B> = (let
  formula_list = formulaToList \<phi>;
  judgement_index = (Index \<J>);
  judgement_free_vars = (Vars \<J>);
  judgement_valuations = (Funcs \<J>);
  structure_domain = (Univ \<B>)
  in (
    ( wfCPL_Instance \<phi> \<B> ) \<and>
    ( judgement_index \<in> (setOfIndex formula_list) ) \<and>
    ( judgement_free_vars \<subseteq> (freeVar (FoI judgement_index formula_list)) ) \<and>
    ( \<forall>f \<in> judgement_valuations. ((dom f) = judgement_free_vars) )  \<and>
    ( \<forall>f \<in> judgement_valuations. ((ran f) \<subseteq> structure_domain) )
  )
)"

(* ================= Proof System Functions ================= *)

(* ======================== Tests ======================== *)

datatype BEnum = A | B | C (* Finite datatype *)

lemma BEnum_induct: "x \<noteq> A \<Longrightarrow> x \<noteq> B \<Longrightarrow> x = C"
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
abbreviation "myJudgement::(BEnum Judgement) \<equiv> (Judgement 6 {CHR ''x'', CHR ''y''} myValuationSet)"

value "wfJudgement myJudgement myFormula myStructure"
