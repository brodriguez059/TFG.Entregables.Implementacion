theory "CPL_Syntax"
  imports Main HOL.Enum
begin

(* ==================== Syntax ==================== *)

(* ======================== Type Definitions ======================== *)

type_synonym Variable =  "char" \<comment> \<open> Note: Explain the caveats of using string. We will have to keep using char for now \<close>
type_synonym Relation =  "char"
datatype Formula =
Atom (atom_rel: "Relation") (atom_vars: "Variable list") |
And (and_f1: "Formula") (and_f2: "Formula") |
Forall (forall_x: "Variable") (forall_f: "Formula") |
Exists (exists_x: "Variable") (exists_f: "Formula")

value "(exists_f (Exists (CHR ''x'') (Atom (CHR ''E'') [CHR ''x''])))"

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

fun containsSubformula :: "Formula \<Rightarrow> Formula \<Rightarrow> bool" where
"containsSubformula (Atom r var_list) \<phi>\<^sub>2 = False" |
"containsSubformula (Forall x \<phi>) \<phi>\<^sub>2 = (\<phi> = \<phi>\<^sub>2)" |
"containsSubformula (Exists x \<phi>) \<phi>\<^sub>2 = (\<phi> = \<phi>\<^sub>2)" |
"containsSubformula (And \<phi>\<^sub>0 \<phi>\<^sub>1) \<phi>\<^sub>2 = ((\<phi>\<^sub>0 = \<phi>\<^sub>2) \<or> (\<phi>\<^sub>1 = \<phi>\<^sub>2))"

fun containsSubformulaInTree :: "Formula \<Rightarrow> Formula \<Rightarrow> bool" where
"containsSubformulaInTree (Atom r var_list) \<phi>\<^sub>2 = ((Atom r var_list) = \<phi>\<^sub>2)" |
"containsSubformulaInTree (Forall x \<phi>) \<phi>\<^sub>2 = (
  ((Forall x \<phi>) = \<phi>\<^sub>2) \<or>
  (containsSubformulaInTree \<phi> \<phi>\<^sub>2)
)" |
"containsSubformulaInTree (Exists x \<phi>) \<phi>\<^sub>2 = (
  ((Exists x \<phi>) = \<phi>\<^sub>2) \<or>
  (containsSubformulaInTree \<phi> \<phi>\<^sub>2)
)" |
"containsSubformulaInTree (And \<phi>\<^sub>0 \<phi>\<^sub>1) \<phi>\<^sub>2 = (
  ((And \<phi>\<^sub>0 \<phi>\<^sub>1) = \<phi>\<^sub>2) \<or>
  ((containsSubformulaInTree \<phi>\<^sub>0 \<phi>\<^sub>2) \<or> (containsSubformulaInTree \<phi>\<^sub>1 \<phi>\<^sub>2))
)"

fun formulaDepth :: "Formula \<Rightarrow> nat" where
"formulaDepth (Atom r var_list) = 0" |
"formulaDepth (Forall x \<phi>) = 1 + (formulaDepth \<phi>)" |
"formulaDepth (Exists x \<phi>) = 1 + (formulaDepth \<phi>)" |
"formulaDepth (And \<phi>\<^sub>0 \<phi>\<^sub>1) = 1 + (max (formulaDepth \<phi>\<^sub>0) (formulaDepth \<phi>\<^sub>1))"

(* ======================== Extra Lemmas ======================== *)

lemma finite_definition_of_formulas [simp] :
  fixes \<phi>\<^sub>1 :: Formula
  fixes \<phi>\<^sub>2 :: Formula
  assumes "(containsSubformula \<phi>\<^sub>1 \<phi>\<^sub>2)"
  shows "(formulaDepth \<phi>\<^sub>2) < (formulaDepth \<phi>\<^sub>1)"
proof (cases \<phi>\<^sub>1)
  case (Atom r var_list)
  show ?thesis using Atom assms by fastforce
next
  case (Forall x \<phi>)
  have "\<phi> = \<phi>\<^sub>2" using Forall assms by fastforce
  then show ?thesis by (simp add: Forall)
next
  case (Exists x \<phi>)
  have "\<phi> = \<phi>\<^sub>2" using Exists assms by fastforce
  then show ?thesis by (simp add: Exists)
next
  case (And \<phi>\<^sub>3 \<phi>\<^sub>4)
  let ?fD1 = "(formulaDepth \<phi>\<^sub>1)"
  let ?fD2 = "(formulaDepth \<phi>\<^sub>2)"
  let ?fD3 = "(formulaDepth \<phi>\<^sub>3)"
  let ?fD4 = "(formulaDepth \<phi>\<^sub>4)"
  let ?maxFD = "(max ?fD3 ?fD4)"
  have and_subformula_equality : "((\<phi>\<^sub>3 = \<phi>\<^sub>2) \<or> (\<phi>\<^sub>4 = \<phi>\<^sub>2))" using And assms by fastforce
  have max_depth_is_lesser : "?maxFD < ?fD1" using And by simp
  show ?thesis using and_subformula_equality max_depth_is_lesser by auto
qed

lemma element_is_inside_its_own_tree [simp] :
  fixes \<phi>:: Formula
  shows "containsSubformulaInTree \<phi> \<phi>"
proof (cases \<phi>)
  case (Atom r var_list)
  thus ?thesis by (simp add: Atom)
next
  case (Forall x \<psi>)
  thus ?thesis by (simp add: Forall)
next
  case (Exists x \<psi>)
  thus ?thesis by (simp add: Exists)
next
  case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
  thus ?thesis by (simp add: And)
qed

lemma non_empty_atom_cannot_be_sentence [simp] : "\<lbrakk>
  (isFormulaAtom \<phi>);
  (length (atom_vars \<phi>) > 0)
\<rbrakk> \<Longrightarrow> (\<not> (sentence \<phi>))"
  apply (auto)
  by (metis Formula.collapse(1) Formula.discI(1) freeVar.simps(1) isFormulaAtom.elims(2) set_empty2)

(* ======================== Tests ======================== *)

datatype BEnum = A | B | C (* Finite datatype *)

lemma BEnum_induct: "\<lbrakk>x \<noteq> A; x \<noteq> B\<rbrakk> \<Longrightarrow> x = C"
  apply(cases x)
  by auto

lemma UNIV_BEnum: "UNIV = {A, B, C}"
  by (auto simp add: BEnum_induct)

instantiation BEnum :: enum \<comment> \<open> Note: We must indicate that this type is an enum to use ran and dom \<close>
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