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
    new_P\<^sub>L_\<phi>\<^sub>2 = 1 # (tl (map ((+) (1 + (length P\<^sub>L_\<phi>\<^sub>1))) P\<^sub>L_\<phi>\<^sub>2))
  in (
    ((And \<phi>\<^sub>1 \<phi>\<^sub>2) # \<phi>\<^sub>L_\<phi>\<^sub>1 @ \<phi>\<^sub>L_\<phi>\<^sub>2, 0 # new_P\<^sub>L_\<phi>\<^sub>1 @ new_P\<^sub>L_\<phi>\<^sub>2)
  )
)"

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

(* ======================== Auxiliary Lemmas ======================== *)

lemma [simp] : "\<lbrakk>(length xs) > 0\<rbrakk> \<Longrightarrow> (length (x # (tl xs))) = (length xs)"
  by (auto)

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

lemma parent_list_is_never_empty [simp] :
  fixes \<phi> :: Formula
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "ParentIndex list"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  shows "(length P\<^sub>L) > 0"
proof (cases \<phi>)
  case (Atom r var_list)
  let ?len = "length P\<^sub>L"
  have "?len = 1" using Atom assms by fastforce
  then show ?thesis by simp
next
  case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
  let ?len = "length P\<^sub>L"
  have "?len > 0" by (metis (no_types, lifting) And Pair_inject assms buildFormulaParentList.simps(4) length_greater_0_conv list.discI split_def) 
  then show ?thesis by auto
next
  case (Forall x \<psi>)
  let ?len = "length P\<^sub>L"
  have "?len > 0" by (metis (no_types, lifting) Forall Pair_inject assms buildFormulaParentList.simps(2) length_greater_0_conv list.discI split_def)
  then show ?thesis by simp
next
  case (Exists x \<psi>)
  let ?len = "length P\<^sub>L"
  have "?len > 0" by (smt (verit) Exists assms buildFormulaParentList.simps(3) length_greater_0_conv list.distinct(1) prod.inject split_def) 
  then show ?thesis by simp
qed

lemma formula_and_parent_list_are_always_the_same_length [simp] :
  fixes \<phi> :: Formula
  shows "(length (fst (buildFormulaParentList \<phi>))) = (length (snd (buildFormulaParentList \<phi>)))" (is "?P \<phi>")
proof (induction \<phi>)
  case (Atom r var_list)
  show ?case by simp
next
  case (Forall x \<psi>)
  assume IH: "?P \<psi>"
  thus ?case by (smt (verit, ccfv_threshold) IH buildFormulaParentList.simps(2) case_prod_unfold fst_conv length_Cons length_map snd_conv)
next
  case (Exists x \<psi>)
  assume IH: "?P \<psi>"
  thus ?case by (smt (verit, ccfv_threshold) IH buildFormulaParentList.simps(3) case_prod_unfold fst_conv length_Cons length_map snd_conv)
next
  case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
  assume IH1: "?P \<psi>\<^sub>1"
  assume IH2: "?P \<psi>\<^sub>2"
  obtain \<phi>\<^sub>L P\<^sub>L where "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList (And \<psi>\<^sub>1 \<psi>\<^sub>2))" by (metis old.prod.exhaust)
  obtain \<phi>\<^sub>L_\<psi>\<^sub>1 P\<^sub>L_\<psi>\<^sub>1 where "(\<phi>\<^sub>L_\<psi>\<^sub>1, P\<^sub>L_\<psi>\<^sub>1) = (buildFormulaParentList \<psi>\<^sub>1)" by (metis old.prod.exhaust)
  have "(length \<phi>\<^sub>L_\<psi>\<^sub>1) = (length P\<^sub>L_\<psi>\<^sub>1)" by (metis IH1 \<open>(\<phi>\<^sub>L_\<psi>\<^sub>1, P\<^sub>L_\<psi>\<^sub>1) = buildFormulaParentList \<psi>\<^sub>1\<close> fst_conv snd_conv)
  obtain \<phi>\<^sub>L_\<psi>\<^sub>2 P\<^sub>L_\<psi>\<^sub>2 where "(\<phi>\<^sub>L_\<psi>\<^sub>2, P\<^sub>L_\<psi>\<^sub>2) = (buildFormulaParentList \<psi>\<^sub>2)" by (metis old.prod.exhaust)
  have "(length \<phi>\<^sub>L_\<psi>\<^sub>2) = (length P\<^sub>L_\<psi>\<^sub>2)" by (metis IH2 \<open>(\<phi>\<^sub>L_\<psi>\<^sub>2, P\<^sub>L_\<psi>\<^sub>2) = buildFormulaParentList \<psi>\<^sub>2\<close> fst_conv snd_conv)
  have "\<phi>\<^sub>L = ((And \<psi>\<^sub>1 \<psi>\<^sub>2) # \<phi>\<^sub>L_\<psi>\<^sub>1 @ \<phi>\<^sub>L_\<psi>\<^sub>2)" by (metis (mono_tags, lifting) \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList (And \<psi>\<^sub>1 \<psi>\<^sub>2)\<close> \<open>(\<phi>\<^sub>L_\<psi>\<^sub>1, P\<^sub>L_\<psi>\<^sub>1) = buildFormulaParentList \<psi>\<^sub>1\<close> \<open>(\<phi>\<^sub>L_\<psi>\<^sub>2, P\<^sub>L_\<psi>\<^sub>2) = buildFormulaParentList \<psi>\<^sub>2\<close> buildFormulaParentList.simps(4) fst_conv split_def)
  have "(length \<phi>\<^sub>L) = (1 + (length \<phi>\<^sub>L_\<psi>\<^sub>1) + (length \<phi>\<^sub>L_\<psi>\<^sub>2))" by (simp add: \<open>\<phi>\<^sub>L = And \<psi>\<^sub>1 \<psi>\<^sub>2 # \<phi>\<^sub>L_\<psi>\<^sub>1 @ \<phi>\<^sub>L_\<psi>\<^sub>2\<close>)
  fix new_P\<^sub>L_\<psi>\<^sub>1 temp_new_P\<^sub>L_\<psi>\<^sub>2 new_P\<^sub>L_\<psi>\<^sub>2
  obtain new_P\<^sub>L_\<psi>\<^sub>1 where "new_P\<^sub>L_\<psi>\<^sub>1 = (map ((+) 1) P\<^sub>L_\<psi>\<^sub>1)" by auto
  have "(length new_P\<^sub>L_\<psi>\<^sub>1) = (length P\<^sub>L_\<psi>\<^sub>1)" by (simp add: \<open>new_P\<^sub>L_\<psi>\<^sub>1 = map ((+) 1) P\<^sub>L_\<psi>\<^sub>1\<close>) 
  obtain new_P\<^sub>L_\<psi>\<^sub>2 where "new_P\<^sub>L_\<psi>\<^sub>2 = 1 # (tl (map ((+) (1 + (length P\<^sub>L_\<psi>\<^sub>1))) P\<^sub>L_\<psi>\<^sub>2))" by auto
  have "(length new_P\<^sub>L_\<psi>\<^sub>2) = (length P\<^sub>L_\<psi>\<^sub>2)" using \<open>(\<phi>\<^sub>L_\<psi>\<^sub>2, P\<^sub>L_\<psi>\<^sub>2) = buildFormulaParentList \<psi>\<^sub>2\<close> \<open>new_P\<^sub>L_\<psi>\<^sub>2 = 1 # tl (map ((+) (1 + length P\<^sub>L_\<psi>\<^sub>1)) P\<^sub>L_\<psi>\<^sub>2)\<close> parent_list_is_never_empty by auto 
  have "P\<^sub>L = (0 # new_P\<^sub>L_\<psi>\<^sub>1 @ new_P\<^sub>L_\<psi>\<^sub>2)" by (metis (mono_tags, lifting) \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList (And \<psi>\<^sub>1 \<psi>\<^sub>2)\<close> \<open>(\<phi>\<^sub>L_\<psi>\<^sub>1, P\<^sub>L_\<psi>\<^sub>1) = buildFormulaParentList \<psi>\<^sub>1\<close> \<open>(\<phi>\<^sub>L_\<psi>\<^sub>2, P\<^sub>L_\<psi>\<^sub>2) = buildFormulaParentList \<psi>\<^sub>2\<close> \<open>new_P\<^sub>L_\<psi>\<^sub>1 = map ((+) 1) P\<^sub>L_\<psi>\<^sub>1\<close> \<open>new_P\<^sub>L_\<psi>\<^sub>2 = 1 # tl (map ((+) (1 + length P\<^sub>L_\<psi>\<^sub>1)) P\<^sub>L_\<psi>\<^sub>2)\<close> buildFormulaParentList.simps(4) prod.sel(2) split_def)
  have "(length P\<^sub>L) = (1 + (length new_P\<^sub>L_\<psi>\<^sub>1) + (length new_P\<^sub>L_\<psi>\<^sub>2))" using \<open>P\<^sub>L = 0 # new_P\<^sub>L_\<psi>\<^sub>1 @ new_P\<^sub>L_\<psi>\<^sub>2\<close> by auto
  have "(length \<phi>\<^sub>L) = (length P\<^sub>L)" by (simp add: \<open>length P\<^sub>L = 1 + length new_P\<^sub>L_\<psi>\<^sub>1 + length new_P\<^sub>L_\<psi>\<^sub>2\<close> \<open>length \<phi>\<^sub>L = 1 + length \<phi>\<^sub>L_\<psi>\<^sub>1 + length \<phi>\<^sub>L_\<psi>\<^sub>2\<close> \<open>length \<phi>\<^sub>L_\<psi>\<^sub>1 = length P\<^sub>L_\<psi>\<^sub>1\<close> \<open>length \<phi>\<^sub>L_\<psi>\<^sub>2 = length P\<^sub>L_\<psi>\<^sub>2\<close> \<open>length new_P\<^sub>L_\<psi>\<^sub>1 = length P\<^sub>L_\<psi>\<^sub>1\<close> \<open>length new_P\<^sub>L_\<psi>\<^sub>2 = length P\<^sub>L_\<psi>\<^sub>2\<close>)
  show ?case by (metis \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList (And \<psi>\<^sub>1 \<psi>\<^sub>2)\<close> \<open>length \<phi>\<^sub>L = length P\<^sub>L\<close> fst_conv snd_conv)
qed

lemma set_of_index_never_contains_zero [simp] : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)
\<rbrakk> \<Longrightarrow> (0 \<notin> (setOfIndex P\<^sub>L))"
  by (auto)

lemma every_index_is_in_inside_range : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
  (i \<in> (setOfIndex P\<^sub>L))
\<rbrakk> \<Longrightarrow> (1 \<le> i) \<and> (i \<le> (length P\<^sub>L))"
  by (auto)

lemma one_is_always_in_set_of_index : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)
\<rbrakk> \<Longrightarrow> (1 \<in> (setOfIndex P\<^sub>L))"
  apply (auto)
  by (meson Suc_leI parent_list_is_never_empty)

lemma formula_list_element_is_always_the_root_formula [simp] : 
  fixes \<phi> :: Formula
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "nat list"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  shows "\<phi> = (hd \<phi>\<^sub>L)"
proof (cases \<phi>)
  case (Atom r var_list)
  have "(length \<phi>\<^sub>L) = 1" using Atom assms by auto
  thus ?thesis using Atom assms by auto
next
  case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
  obtain \<phi>\<^sub>L_\<psi>\<^sub>1 where "\<phi>\<^sub>L_\<psi>\<^sub>1 = (fst (buildFormulaParentList \<psi>\<^sub>1))" by auto
  obtain \<phi>\<^sub>L_\<psi>\<^sub>2 where "\<phi>\<^sub>L_\<psi>\<^sub>2 = (fst (buildFormulaParentList \<psi>\<^sub>2))" by auto
  then have "\<phi>\<^sub>L = ((And \<psi>\<^sub>1 \<psi>\<^sub>2) # \<phi>\<^sub>L_\<psi>\<^sub>1 @ \<phi>\<^sub>L_\<psi>\<^sub>2)" by (metis (no_types, lifting) And Pair_inject \<open>\<phi>\<^sub>L_\<psi>\<^sub>1 = fst (buildFormulaParentList \<psi>\<^sub>1)\<close> assms buildFormulaParentList.simps(4) split_def)
  thus ?thesis by (simp add: And) 
next
  case (Forall x \<psi>)
  obtain \<psi>\<^sub>L where "\<psi>\<^sub>L = (fst (buildFormulaParentList \<psi>))" by auto
  then have "\<phi>\<^sub>L = ((Forall x \<psi>) # \<psi>\<^sub>L)" by (metis (mono_tags, lifting) Forall assms buildFormulaParentList.simps(2) case_prod_unfold fst_conv)
  thus ?thesis by (simp add: Forall) 
next
  case (Exists x \<psi>)
  obtain \<psi>\<^sub>L where "\<psi>\<^sub>L = (fst (buildFormulaParentList \<psi>))" by auto
  then have "\<phi>\<^sub>L = ((Exists x \<psi>) # \<psi>\<^sub>L)" by (metis (mono_tags, lifting) Exists assms buildFormulaParentList.simps(3) case_prod_unfold fst_conv)
  thus ?thesis by (simp add: Exists)
qed

lemma foi_first_index_is_always_the_root_formula [simp] : "\<phi> = (FoI 1 (fst (buildFormulaParentList \<phi>)))"
  apply (auto)
  by (metis formula_and_parent_list_are_always_the_same_length formula_list_element_is_always_the_root_formula hd_conv_nth length_greater_0_conv parent_list_is_never_empty prod.collapse)


(* ======================== Well-Formedness Functions ======================== *)

fun wfFormula :: "Formula \<Rightarrow> Signature \<Rightarrow> bool" where
"wfFormula (Atom r var_list) \<S> = (
    case (\<S> r) of
    None \<Rightarrow> False |
    (Some n) \<Rightarrow> ((length var_list) = n) \<comment> \<open> Note: I have made the assumption that we accept relationship symbols with arity=0 \<close>
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

fun wfCPLFormula :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfCPLFormula \<phi> \<B> = (
  (wfStructure \<B>) \<and>
  (wfFormula \<phi> (Sig \<B>))
)"

fun wfCPLInstance :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfCPLInstance \<phi> \<B> = (
  (sentence \<phi>) \<and>  
  (wfCPLFormula \<phi> \<B>)
)"

(* ======================== Well-Formedness Lemmas ======================== *)

lemma wf_atom_in_wf_structure_always_has_an_interpretation_for_its_relation [simp] : "\<lbrakk>
  (wfCPLFormula (Atom r var_list) \<B>)
\<rbrakk> \<Longrightarrow> (((Interp \<B>) r) \<noteq> None)"
  apply (auto)
  by (smt (z3) Structure.sel(1) Structure.sel(3) case_optionE domIff option.simps(3) wfStructure.elims(2))

lemma well_formedness_breaks_with_atom [simp] : "\<lbrakk>
  (\<not> (wfCPLFormula (Atom r var_list) \<B>));
  (containsSubformulaInTree (Atom r var_list) \<phi>)
\<rbrakk> \<Longrightarrow> (\<not> (wfCPLFormula \<phi> \<B>))"
  by (auto)

lemma well_formedness_carries_to_atom [simp] : "\<lbrakk>
  ((wfCPLFormula \<phi> \<B>));
  (containsSubformulaInTree (Atom r var_list) \<phi>)
\<rbrakk> \<Longrightarrow> ((wfCPLFormula (Atom r var_list) \<B>))"
  by (auto)

lemma formula_list_maintains_well_formedness [simp] :
  fixes \<phi> :: Formula
  assumes "wfCPLFormula \<phi> \<B>"
  shows "( \<forall>\<psi>. \<psi> \<in> (set (fst (buildFormulaParentList \<phi>))) \<longrightarrow> (wfCPLFormula \<psi> \<B>) )" (is "?P \<phi>")
proof (induct \<phi>) \<comment> \<open> TODO: Terminar y fixear, puede que HI no sea lo más adecuado aquí \<close>
  case (Atom r var_list)
  have "[(Atom r var_list)] = (fst (buildFormulaParentList (Atom r var_list)))" using Atom by auto
  have "(wfStructure \<B>)" using assms by auto
  obtain \<S> where "\<S> = (Sig \<B>)" by auto
  thus ?case
  proof (cases "(\<S> r)")
    case None
    thus ?thesis sorry
  next
    case (Some n)
    thus ?thesis
    proof (cases "(length var_list) = n")
      case True
      have "(wfFormula (Atom r var_list) \<S>)" by (simp add: Some \<open>length var_list = n\<close>)
      have "wfCPLFormula (Atom r var_list) \<B>" using \<open>\<S> = Sig \<B>\<close> \<open>wfFormula (Atom r var_list) \<S>\<close> \<open>wfStructure \<B>\<close> by auto
      have "?P (Atom r var_list)" using \<open>wfCPLFormula (Atom r var_list) \<B>\<close> by auto
      thus ?thesis by blast
    next
      case False
      thus ?thesis sorry
    qed
  qed
next
  case (Forall x \<psi>)
  assume IH: "?P \<psi>"
  obtain \<phi>\<^sub>L where "\<phi>\<^sub>L = (fst (buildFormulaParentList (Forall x \<psi>)))" by simp 
  have "(Forall x \<psi>) = (hd \<phi>\<^sub>L)" by (metis FoI.simps One_nat_def \<open>\<phi>\<^sub>L = fst (buildFormulaParentList (Forall x \<psi>))\<close> add_diff_cancel_left' foi_first_index_is_always_the_root_formula formula_and_parent_list_are_always_the_same_length hd_conv_nth less_numeral_extra(3) list.size(3) parent_list_is_never_empty plus_1_eq_Suc prod.collapse)
  have "wfCPLFormula (Forall x \<psi>) \<B>" by (metis FoI.simps IH cancel_comm_monoid_add_class.diff_cancel foi_first_index_is_always_the_root_formula formula_list_is_never_empty hd_conv_nth insert_iff list.exhaust_sel list.simps(15) list.size(3) nat_less_le surjective_pairing wfCPLFormula.elims(1) wfFormula.simps(3))
  show ?case by (metis (mono_tags, lifting) IH \<open>wfCPLFormula (Forall x \<psi>) \<B>\<close> buildFormulaParentList.simps(2) case_prod_unfold fst_conv insert_iff list.simps(15))
next
  case (Exists x \<psi>)
  assume IH: "?P \<psi>"
  obtain \<phi>\<^sub>L where "\<phi>\<^sub>L = (fst (buildFormulaParentList (Exists x \<psi>)))" by simp
  have "(Exists x \<psi>) = hd \<phi>\<^sub>L" by (metis FoI.simps One_nat_def \<open>\<phi>\<^sub>L = fst (buildFormulaParentList (Exists x \<psi>))\<close> add_diff_cancel_left' foi_first_index_is_always_the_root_formula formula_and_parent_list_are_always_the_same_length hd_conv_nth less_numeral_extra(3) list.size(3) parent_list_is_never_empty plus_1_eq_Suc prod.collapse)
  have "wfCPLFormula (Exists x \<psi>) \<B>" by (metis FoI.simps IH cancel_comm_monoid_add_class.diff_cancel foi_first_index_is_always_the_root_formula formula_list_is_never_empty hd_conv_nth in_set_member less_numeral_extra(3) list.exhaust_sel list.size(3) member_rec(1) prod.collapse wfCPLFormula.elims(1) wfFormula.simps(4))
  thus ?case by (metis (mono_tags, lifting) IH buildFormulaParentList.simps(3) case_prod_unfold fst_conv in_set_member member_rec(1))
next
  case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
  assume IH1: "?P \<psi>\<^sub>1"
  assume IH2: "?P \<psi>\<^sub>2"
  obtain \<phi>\<^sub>L where "\<phi>\<^sub>L = (fst (buildFormulaParentList (And \<psi>\<^sub>1 \<psi>\<^sub>2)))" by blast
  obtain \<phi>\<^sub>L_\<phi>\<^sub>1 where "\<phi>\<^sub>L_\<phi>\<^sub>1 = (fst (buildFormulaParentList \<psi>\<^sub>1))" by blast
  obtain \<phi>\<^sub>L_\<phi>\<^sub>2 where "\<phi>\<^sub>L_\<phi>\<^sub>2 = (fst (buildFormulaParentList \<psi>\<^sub>2))" by blast
  have "\<phi>\<^sub>L = ((And \<psi>\<^sub>1 \<psi>\<^sub>2) # \<phi>\<^sub>L_\<phi>\<^sub>1 @ \<phi>\<^sub>L_\<phi>\<^sub>2)" by (metis (mono_tags, lifting) \<open>\<phi>\<^sub>L = fst (buildFormulaParentList (And \<psi>\<^sub>1 \<psi>\<^sub>2))\<close> \<open>\<phi>\<^sub>L_\<phi>\<^sub>1 = fst (buildFormulaParentList \<psi>\<^sub>1)\<close> \<open>\<phi>\<^sub>L_\<phi>\<^sub>2 = fst (buildFormulaParentList \<psi>\<^sub>2)\<close> buildFormulaParentList.simps(4) case_prod_unfold fst_conv) 
  have "(And \<psi>\<^sub>1 \<psi>\<^sub>2) = hd \<phi>\<^sub>L" by (metis FoI.simps One_nat_def \<open>\<phi>\<^sub>L = fst (buildFormulaParentList (And \<psi>\<^sub>1 \<psi>\<^sub>2))\<close> add_diff_cancel_left' foi_first_index_is_always_the_root_formula formula_and_parent_list_are_always_the_same_length hd_conv_nth less_numeral_extra(3) list.size(3) parent_list_is_never_empty plus_1_eq_Suc prod.collapse)
  have "wfCPLFormula (And \<psi>\<^sub>1 \<psi>\<^sub>2) \<B>" by (metis FoI.simps IH1 IH2 cancel_comm_monoid_add_class.diff_cancel foi_first_index_is_always_the_root_formula formula_list_is_never_empty hd_Cons_tl hd_conv_nth in_set_member less_numeral_extra(3) list.size(3) member_rec(1) prod.collapse wfCPLFormula.elims(2) wfCPLFormula.elims(3) wfFormula.simps(2))
  show ?case using IH1 IH2 \<open>\<phi>\<^sub>L = And \<psi>\<^sub>1 \<psi>\<^sub>2 # \<phi>\<^sub>L_\<phi>\<^sub>1 @ \<phi>\<^sub>L_\<phi>\<^sub>2\<close> \<open>\<phi>\<^sub>L = fst (buildFormulaParentList (And \<psi>\<^sub>1 \<psi>\<^sub>2))\<close> \<open>\<phi>\<^sub>L_\<phi>\<^sub>1 = fst (buildFormulaParentList \<psi>\<^sub>1)\<close> \<open>\<phi>\<^sub>L_\<phi>\<^sub>2 = fst (buildFormulaParentList \<psi>\<^sub>2)\<close> \<open>wfCPLFormula (And \<psi>\<^sub>1 \<psi>\<^sub>2) \<B>\<close> by auto
qed

lemma foi_index_is_well_formed_if_root_formula_is_well_formed [simp] : 
  fixes \<phi> :: Formula
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "nat list"
  fixes \<B> :: "'a Structure"
  assumes "wfCPLFormula \<phi> \<B>"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  assumes "(i \<in> (setOfIndex P\<^sub>L))"
  shows "(wfCPLFormula (FoI i (fst (buildFormulaParentList \<phi>))) \<B>)"
proof (cases \<phi>)
  case (Atom r var_list)
  thus ?thesis using Atom assms by auto
next
  case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
  thus ?thesis by (metis FoI.simps One_nat_def Suc_le_eq Suc_pred assms(1) assms(2) assms(3) every_index_is_in_inside_range formula_and_parent_list_are_always_the_same_length formula_list_maintains_well_formedness nth_mem snd_conv) 
next
  case (Forall x \<psi>)
  thus ?thesis by (metis FoI.simps One_nat_def Suc_le_eq Suc_pred assms(1) assms(2) assms(3) every_index_is_in_inside_range formula_and_parent_list_are_always_the_same_length formula_list_maintains_well_formedness nth_mem snd_conv)  
next
  case (Exists x \<psi>)
  thus ?thesis by (metis FoI.simps One_nat_def Suc_le_eq Suc_pred assms(1) assms(2) assms(3) every_index_is_in_inside_range formula_and_parent_list_are_always_the_same_length formula_list_maintains_well_formedness nth_mem snd_conv)
qed

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