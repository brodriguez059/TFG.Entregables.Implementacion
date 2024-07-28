theory "CPL_Semantic"
  imports Main "CPL_Syntax"
begin

(* ==================== Semantics ==================== *)

(* ======================== Type Definitions ======================== *)

type_synonym Signature =  "Relation \<rightharpoonup> nat" \<comment> \<open> Represented by \<S> \<close>
type_synonym 'a Interpretation = "Relation \<rightharpoonup> 'a list set" \<comment> \<open> Represented by \<I> \<close>
type_synonym ParentIndex = "nat"
type_synonym ChildIndexes = "nat list"
datatype 'a Structure =  Structure (Sig: "Signature") (Univ: "'a set")  (Interp: "'a Interpretation") \<comment> \<open> Represented by \<B>, and internally by \<S> D \<I> \<close>

(* ======================== Auxiliary Functions ======================== *)

fun buildFormulaParentList :: "Formula \<Rightarrow> (Formula list) \<times> (ParentIndex list)" where
"buildFormulaParentList (Atom r var_list) = ([(Atom r var_list)], [0])" |
"buildFormulaParentList (Forall x \<phi>) = (let
    (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
    new_P\<^sub>L = (map ((+) 1) P\<^sub>L)
  in (
     ((Forall x \<phi>) # \<phi>\<^sub>L, 0 # new_P\<^sub>L)
  )
)" |
"buildFormulaParentList (Exists x \<phi>) = (let
    (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
    new_P\<^sub>L = (map ((+) 1) P\<^sub>L)
  in (
     ((Exists x \<phi>) # \<phi>\<^sub>L, 0 # new_P\<^sub>L)
  )
)" |
"buildFormulaParentList (And \<phi>\<^sub>1 \<phi>\<^sub>2) = (let
    (\<phi>\<^sub>L_\<phi>\<^sub>1, P\<^sub>L_\<phi>\<^sub>1) = (buildFormulaParentList \<phi>\<^sub>1);
    new_P\<^sub>L_\<phi>\<^sub>1 = (map ((+) 1) P\<^sub>L_\<phi>\<^sub>1);
    (\<phi>\<^sub>L_\<phi>\<^sub>2, P\<^sub>L_\<phi>\<^sub>2) = (buildFormulaParentList \<phi>\<^sub>2);
    temp_new_P\<^sub>L_\<phi>\<^sub>2 = (map ((+) (1 + (length P\<^sub>L_\<phi>\<^sub>1))) P\<^sub>L_\<phi>\<^sub>2);
    new_P\<^sub>L_\<phi>\<^sub>2 = 1 # (tl temp_new_P\<^sub>L_\<phi>\<^sub>2)
  in (
    ((And \<phi>\<^sub>1 \<phi>\<^sub>2) # \<phi>\<^sub>L_\<phi>\<^sub>1 @ \<phi>\<^sub>L_\<phi>\<^sub>2, 0 # new_P\<^sub>L_\<phi>\<^sub>1 @ new_P\<^sub>L_\<phi>\<^sub>2)
  )
)"

lemma formula_list_is_never_empty [simp] :
  fixes \<phi> :: Formula
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "ParentIndex list"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  shows "(length \<phi>\<^sub>L) > 0"
proof (cases \<phi>)
  case (Atom r var_list)
  let ?len = "length \<phi>\<^sub>L"
  have "?len = 1" using Atom assms by fastforce
  then show ?thesis by simp
next
  case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
  let ?len = "length \<phi>\<^sub>L"
  have "?len > 0" by (metis (no_types, lifting) And Pair_inject assms buildFormulaParentList.simps(4) length_greater_0_conv list.discI split_def) 
  then show ?thesis by auto
next
  case (Forall x \<psi>)
  let ?len = "length \<phi>\<^sub>L"
  have "?len > 0" by (metis (no_types, lifting) Forall Pair_inject assms buildFormulaParentList.simps(2) length_greater_0_conv list.discI split_def)
  then show ?thesis by simp
next
  case (Exists x \<psi>)
  let ?len = "length \<phi>\<^sub>L"
  have "?len > 0" by (smt (verit) Exists assms buildFormulaParentList.simps(3) length_greater_0_conv list.distinct(1) prod.inject split_def) 
  then show ?thesis by simp
qed

fun setOfIndex :: "nat list \<Rightarrow> nat set" where
"setOfIndex P\<^sub>L = { 1 .. (length P\<^sub>L) }"

fun FoI :: "nat \<Rightarrow> Formula list \<Rightarrow> Formula" where
"FoI i \<phi>\<^sub>L = \<phi>\<^sub>L ! (i - 1)"

fun CoIIndexed :: "nat \<Rightarrow> ParentIndex list \<Rightarrow> nat \<Rightarrow> ChildIndexes" where
"CoIIndexed i [] k = []" |
"CoIIndexed i (p#ps) k = (if (i = p)
  then ((k+1) # (CoIIndexed i ps (k+1)))
  else (CoIIndexed i ps (k+1))
)"

fun CoI :: "nat \<Rightarrow> ParentIndex list \<Rightarrow> ChildIndexes" where
"CoI i [] = []" |
"CoI i P\<^sub>L = (CoIIndexed i P\<^sub>L 0)"

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

lemma [simp] : "wfCPLInstance myFormula myStructure = True"
  by(auto)

end