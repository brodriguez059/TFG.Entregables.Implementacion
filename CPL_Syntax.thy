theory "CPL_Syntax"
  imports Main HOL.Enum
begin

(* ==================== Syntax ==================== *)

(* ======================== Type Definitions ======================== *)

(* Note: Explain the caveats of using string. We will have to keep using char for now *)
type_synonym 'a Enumerable =  "'a::enum" (* It is possible to define types that must implement a class using this syntax *)
type_synonym Variable =  "char Enumerable"
type_synonym Relation =  "char Enumerable"
datatype Formula =
Atom (atom_rel: "Relation") (atom_vars: "Variable list") |
And (and_f1: "Formula") (and_f2: "Formula") |
Forall (forall_x: "Variable") (forall_f: "Formula") |
Exists (exists_x: "Variable") (exists_f: "Formula")

(* ======================== Auxiliary Functions ======================== *)

fun freeVar :: "Formula \<Rightarrow> Variable set" where
"freeVar (Atom r var_list) = set var_list" |
"freeVar (And \<phi>\<^sub>0 \<phi>\<^sub>1) = (freeVar \<phi>\<^sub>0) \<union> (freeVar \<phi>\<^sub>1)" |
"freeVar (Forall x \<phi>) = (freeVar \<phi>) - {x}" |
"freeVar (Exists x \<phi>) = (freeVar \<phi>) - {x}"

fun sentence :: "Formula \<Rightarrow> bool" where
"sentence \<phi> = ((freeVar \<phi>) = {})"

(* ======================== Extra Functions ======================== *)

fun isFormulaAtom :: "Formula \<Rightarrow> bool" where
"isFormulaAtom (Atom r var_list) = True" |
"isFormulaAtom _ = False"

fun isFormulaAnd :: "Formula \<Rightarrow> bool" where
"isFormulaAnd (And \<phi>\<^sub>1 \<phi>\<^sub>2) = True" |
"isFormulaAnd _ = False"

fun isFormulaForAll :: "Formula \<Rightarrow> bool" where
"isFormulaForAll (Forall x \<phi>) = True" |
"isFormulaForAll _ = False"

fun isFormulaExists :: "Formula \<Rightarrow> bool" where
"isFormulaExists (Exists x \<phi>) = True" |
"isFormulaExists _ = False"

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



abbreviation "atomFormula::Formula \<equiv> (Atom (CHR ''E'') [CHR ''x'', CHR ''y''])"

lemma "freeVar atomFormula = {CHR ''x'', CHR ''y''}"
  by auto

lemma "sentence atomFormula = False"
  by auto

lemma "isFormulaAtom atomFormula = True"
  by auto

lemma "isFormulaForAll atomFormula = False"
  by auto

lemma "isFormulaExists atomFormula = False"
  by auto

lemma "isFormulaAnd atomFormula = False"
  by auto



abbreviation "forAllFormula::Formula \<equiv> (Forall (CHR ''x'') atomFormula)"

lemma "freeVar forAllFormula = {CHR ''y''}"
  by auto

lemma "sentence forAllFormula = False"
  by auto

lemma "isFormulaAtom forAllFormula = False"
  by auto

lemma "isFormulaForAll forAllFormula = True"
  by auto

lemma "isFormulaExists forAllFormula = False"
  by auto

lemma "isFormulaAnd forAllFormula = False"
  by auto



abbreviation "existsFormula::Formula \<equiv> (Exists (CHR ''y'') atomFormula)"

lemma "freeVar existsFormula = {CHR ''x''}"
  by auto

lemma "sentence existsFormula = False"
  by auto

lemma "isFormulaAtom existsFormula = False"
  by auto

lemma "isFormulaForAll existsFormula = False"
  by auto

lemma "isFormulaExists existsFormula = True"
  by auto

lemma "isFormulaAnd existsFormula = False"
  by auto



abbreviation "andFormula::Formula \<equiv> (And forAllFormula existsFormula)"

lemma "freeVar andFormula = {CHR ''x'', CHR ''y''}"
  by auto

lemma "sentence andFormula = False"
  by auto

lemma "isFormulaAtom andFormula = False"
  by auto

lemma "isFormulaForAll andFormula = False"
  by auto

lemma "isFormulaExists andFormula = False"
  by auto

lemma "isFormulaAnd andFormula = True"
  by auto



abbreviation "sentenceFormula::Formula \<equiv> (Forall (CHR ''x'') existsFormula)"

lemma "freeVar sentenceFormula = {}"
  by auto

lemma "sentence sentenceFormula = True"
  by auto

end