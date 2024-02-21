theory CPL
  imports Main "HOL-Library.Char_ord"
begin

(* Types *)

type_synonym Variable =  "char"

type_synonym Relation =  "char"

type_synonym Signature =  "Relation \<rightharpoonup> nat"

type_synonym 'a Interpretation = "Relation \<rightharpoonup> 'a list set"

datatype 'a Structure =  Structure (Sig: "Signature") (Universe: "'a set")  (I: "'a Interpretation")

fun wfStructure :: "'a Structure \<Rightarrow> bool" where 
"wfStructure (Structure sig b interpret) = (
  (b \<noteq> {})  \<and>
  ( \<forall>r \<in> dom(sig). (
      case (interpret r) of
      None \<Rightarrow> False |
      (Some setl) \<Rightarrow> ( \<forall>l \<in> setl. (
         case (sig r) of
         None \<Rightarrow> False |
         (Some n) \<Rightarrow> length(l) = n
        )
      )
    )
  )
)"

definition "s::(Signature) \<equiv> [CHR ''E'' \<mapsto> 2]"
definition "m::(int Interpretation) \<equiv> [CHR ''E'' \<mapsto> {[1,1],[2,2]}]"
definition "myStructure::(int Structure) \<equiv> (Structure (s) ({1,2}) (m))"
(* definition "myFormula \<equiv> (Exists ''x'' (Forall ''y'' (And (Atom ''E'' [''x'',''y'']) (Exists ''x'' (Atom ''E'' [''x'',''y''])))))" *)

value "wfStructure myStructure"

(* Syntax *)

datatype Formula =
  Atom Relation "Variable list"
| And Formula Formula
| Forall Variable Formula
| Exists Variable Formula

fun wfFormula :: "Formula \<Rightarrow> Signature \<Rightarrow> bool" where (*Redefine using difference to optimize it*)
"wfFormula (Atom r varlist) sig = (
    case (sig r) of
    None \<Rightarrow> False |
    (Some n) \<Rightarrow> length(varlist) = n
  )" |
"wfFormula (And phi0 phi1) sig = ((wfFormula phi0 sig) \<and> (wfFormula phi1 sig))" |
"wfFormula (Forall x phi) sig = (wfFormula phi sig)" |
"wfFormula (Exists x phi) sig = (wfFormula phi sig)"

fun ListToSet :: "'a list  \<Rightarrow> 'a set" where
"ListToSet([]) = {}" |
"ListToSet(x#xs) = {x} \<union> ListToSet(xs)"

fun freeVar :: "Formula \<Rightarrow> Variable set" where
"freeVar(Atom r varlist) = ListToSet varlist" |
"freeVar(And phi1 phi2) = freeVar phi1 \<union> freeVar phi2" |
"freeVar(Forall x phi) = freeVar phi - {x}" |
"freeVar(Exists x phi) = freeVar phi - {x}"

fun sentence :: "Formula \<Rightarrow> bool" where
"sentence(phi) = (freeVar(phi) = {})"

(* Some tests
(*This works a mapping:*)
definition "s \<equiv> (\<lambda>_. None)
  (''E'' := Some 2)
"
value "wfFormula (Exists ''x'' (Forall ''y'' (And (Atom ''E'' [''x'',''y'']) (Exists ''x'' (Atom ''E'' [''x'',''y'']))))) (s::Signature)"
value "sentence (Exists ''x'' (Forall ''y'' (And (Atom ''E'' [''x'',''y'']) (Exists ''x'' (Atom ''E'' [''x'',''y''])))))"
*)

(* Semantics *)

type_synonym 'a Valuation = "Variable \<Rightarrow> 'a"

datatype 'a Judgement =  Judgement (index: "nat") (V:  "Variable set") (F:  "'a Valuation set")

fun wfQCSP_Instance :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfQCSP_Instance phi B = (
  (wfStructure B) \<and>
  (wfFormula phi (Sig B)) \<and>
  (sentence phi)
)"

(*definition "s::(Signature) \<equiv> [CHR ''E'' \<mapsto> 2]"
definition "m::(int Interpretation) \<equiv> [CHR ''E'' \<mapsto> {[1,1],[2,2]}]"
definition "myStructure::(int Structure) \<equiv> (Structure (s) ({1,2}) (m))"*)
definition "myFormula \<equiv> (
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

value "wfFormula myFormula s"

fun wfJudgement :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfJudgement J phi B = (wfQCSP_Instance phi B)"


