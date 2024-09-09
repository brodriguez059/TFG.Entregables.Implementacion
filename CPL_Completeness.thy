theory "CPL_Completeness"
  imports Main "CPL_Syntax" "CPL_Semantic" "CPL_Proof_System"
begin

(* ==================== Completeness ==================== *)

(* ======================== Auxiliary Functions ======================== *)

fun buildJudgementAtom :: "nat \<Rightarrow> Variable list \<Rightarrow> Relation \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement" where
"buildJudgementAtom i var_list r \<B> = (if (wfCPLFormula (Atom r var_list) \<B>)
    then (case ((Interp \<B>) r) of
      None \<Rightarrow> (Judgement 0 {} {}) |
      (Some f) \<Rightarrow> Judgement i (set var_list) (buildAtomValuations var_list f)
    )
    else (Judgement 0 {} {})
)"

fun join :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> 'a Judgement" where
"join \<J>\<^sub>0 \<J>\<^sub>1 = Judgement (Index \<J>\<^sub>0) ((Vars \<J>\<^sub>0) \<union> (Vars \<J>\<^sub>1)) (joinJudgementValuations \<J>\<^sub>0 \<J>\<^sub>1)"

fun dualProject :: "Variable \<Rightarrow> 'a Judgement \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement" where
"dualProject y \<J> \<B> = (let
    variables = ((Vars \<J>) - {y});
    \<J>\<^sub>0 = (Judgement (Index \<J>) variables (projectJudgementValuations \<J> variables))
  in (
    Judgement (Index \<J>) variables (dualProjectJudgementValuations \<J>\<^sub>0 \<J> y \<B>)
  )
)"

fun project :: "'a Judgement \<Rightarrow> Variable set \<Rightarrow> 'a Judgement" where
"project \<J> V = (Judgement (Index \<J>) V (projectJudgementValuations \<J> V))"

(* ======================== Auxiliary Lemmas ======================== *)

lemma build_judgement_atom_can_be_null_when_interpretation_does_not_have_relation [simp] : "\<lbrakk>
  ((Interp \<B>) r) = None
\<rbrakk> \<Longrightarrow> (buildJudgementAtom i var_list r \<B>) = (Judgement 0 {} {})"
  by (auto)

lemma build_judgement_atom_cannot_be_null_when_interpretation_has_relation [simp] : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
  (i \<in> (setOfIndex P\<^sub>L));
  (wfCPLFormula (Atom r var_list) \<B>);
  ((Interp \<B>) r) = (Some f)
\<rbrakk> \<Longrightarrow> (buildJudgementAtom i var_list r \<B>) \<noteq> (Judgement 0 {} {})"
  by (auto)

lemma build_judgement_atom_index_is_maintained [simp] : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
  (i \<in> (setOfIndex P\<^sub>L));
  (wfCPLFormula (Atom r var_list) \<B>);
  ((Interp \<B>) r) = (Some f)
\<rbrakk> \<Longrightarrow> (Index (buildJudgementAtom i var_list r \<B>)) = i"
  by (auto)

lemma build_judgement_atom_var_set_is_defined [simp] : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
  (i \<in> (setOfIndex P\<^sub>L));
  (wfCPLFormula (Atom r var_list) \<B>);
  ((Interp \<B>) r) = (Some f)
\<rbrakk> \<Longrightarrow> (Vars (buildJudgementAtom i var_list r \<B>)) = (set var_list)"
  by (auto)

lemma build_judgement_atom_var_set_is_its_free_vars [simp] : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
  (i \<in> (setOfIndex P\<^sub>L));
  (wfCPLFormula (Atom r var_list) \<B>);
  ((Interp \<B>) r) = (Some f)
\<rbrakk> \<Longrightarrow> (Vars (buildJudgementAtom i var_list r \<B>)) = (freeVar (Atom r var_list))"
  by (auto)

lemma build_judgement_atom_funcs_is_defined [simp] : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
  (i \<in> (setOfIndex P\<^sub>L));
  (wfCPLFormula (Atom r var_list) \<B>);
  ((Interp \<B>) r) = (Some f)
\<rbrakk> \<Longrightarrow> (Funcs (buildJudgementAtom i var_list r \<B>)) = (buildAtomValuations var_list f)"
  by (auto)

lemma join_index_is_maintained [simp] : "(Index (join \<J>\<^sub>0 \<J>\<^sub>1)) = (Index \<J>\<^sub>0)"
  by (auto)

lemma join_var_set_is_increased [simp] : "(Vars (join \<J>\<^sub>0 \<J>\<^sub>1)) = ((Vars \<J>\<^sub>0) \<union> (Vars \<J>\<^sub>1))"
  by (auto)

lemma join_funcs_is_updated [simp] : "(Funcs (join \<J>\<^sub>0 \<J>\<^sub>1)) = (joinJudgementValuations \<J>\<^sub>0 \<J>\<^sub>1)"
  by (auto)

lemma dual_project_index_is_maintained [simp] : "(Index (dualProject y \<J> \<B>)) = (Index \<J>)"
  apply (auto)
  by (meson Judgement.sel(1))

lemma dual_project_var_set_is_reduced [simp] : "(Vars (dualProject y \<J> \<B>)) = ((Vars \<J>) - {y})"
  apply (auto)
  apply (metis Diff_iff Judgement.sel(2))
  apply (metis DiffE Judgement.sel(2) insertCI)
  by (metis DiffI Judgement.sel(2) singletonD)

lemma dual_project_funcs_is_updated [simp] : "\<lbrakk>
  variables = ((Vars \<J>) - {y});
  \<J>\<^sub>0 = (Judgement (Index \<J>) variables (projectJudgementValuations \<J> variables))
\<rbrakk> \<Longrightarrow>(Funcs (dualProject y \<J> \<B>)) = (dualProjectJudgementValuations \<J>\<^sub>0 \<J> y \<B>)"
  sorry

lemma project_var_set_is_maintained [simp] : "(Vars (project \<J> V)) = V"
  by (auto)

lemma project_funcs_is_updated [simp] : "(Funcs (project \<J> V)) = (projectJudgementValuations \<J> V)"
  by (auto)

(* ======================== Canonical Judgement Functions ======================== *)

function canonicalJudgementRec :: "Formula \<Rightarrow> nat \<Rightarrow> Formula list \<Rightarrow> ParentIndex list \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement" where
"((\<not> (wfCPLFormula \<psi> \<B>)) \<or> ((length P\<^sub>L) = 0) \<or> (i = 0)) \<Longrightarrow> canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B> = (Judgement 0 {} {})" |
"(wfCPLFormula \<psi> \<B>) \<and> ((length P\<^sub>L) > 0) \<and> (i > (length P\<^sub>L)) \<Longrightarrow> canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B> = (Judgement 0 {} {})" |
"(wfCPLFormula \<psi> \<B>) \<and> ((length P\<^sub>L) > 0) \<and> (i > 0) \<and> (i \<le> (length P\<^sub>L)) \<Longrightarrow> canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B> = (
  case \<psi> of
  (Atom r var_list) \<Rightarrow> (
    buildJudgementAtom i var_list r \<B>
  ) |
  (Forall x \<psi>\<^sub>1) \<Rightarrow> (let
    \<J>\<^sub>0 = (canonicalJudgementRec \<psi>\<^sub>1 (i+1) \<phi>\<^sub>L P\<^sub>L \<B>)
  in (
      (if (x \<in> (Vars \<J>\<^sub>0))
        then (dualProject x \<J>\<^sub>0 \<B>)
        else (Judgement i (Vars \<J>\<^sub>0) (Funcs \<J>\<^sub>0))
      )
    )
  ) |
  (Exists x \<psi>\<^sub>1) \<Rightarrow> (let
    \<J>\<^sub>0 = (canonicalJudgementRec \<psi>\<^sub>1 (i+1) \<phi>\<^sub>L P\<^sub>L \<B>);
    \<J>\<^sub>p = (project \<J>\<^sub>0 ((Vars \<J>\<^sub>0) - {x}))
  in (
      (if (x \<in> (Vars \<J>\<^sub>0))
        then (Judgement i (Vars \<J>\<^sub>p) (Funcs \<J>\<^sub>p))
        else (Judgement i (Vars \<J>\<^sub>0) (Funcs \<J>\<^sub>0))
      )
    )
  ) |
  (And \<psi>\<^sub>1 \<psi>\<^sub>2) \<Rightarrow> (let
    childIndexes = (CoI i P\<^sub>L); \<comment> \<open> This always returns two elements \<close>
    j = hd childIndexes;
    k = last childIndexes;
    \<J>\<^sub>0' = (canonicalJudgementRec \<psi>\<^sub>1 j \<phi>\<^sub>L P\<^sub>L \<B>);
    \<J>\<^sub>1' = (canonicalJudgementRec \<psi>\<^sub>2 k \<phi>\<^sub>L P\<^sub>L \<B>)
  in (
      join (Judgement i (Vars \<J>\<^sub>0') (Funcs \<J>\<^sub>0')) (Judgement i (Vars \<J>\<^sub>1') (Funcs \<J>\<^sub>1'))
    )
  )
)
"
  apply (auto)
  using linorder_not_less by blast
termination canonicalJudgementRec
  apply (relation "measures [\<lambda>(\<psi>, _, _, _, _). formulaDepth \<psi>]")
  by (auto)

fun canonicalJudgement :: "nat \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement" where
"canonicalJudgement 0 \<phi> \<B> = (Judgement 0 {} {})" |
"canonicalJudgement i \<phi> \<B> = (let
    (\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>
  in (
    (if ((\<not> (wfCPLFormula \<phi> \<B>)) \<or> (i = 0) \<or> (i > (length P\<^sub>L)) \<or> ((length P\<^sub>L) = 0))
      then (Judgement 0 {} {})
      else (canonicalJudgementRec (FoI i \<phi>\<^sub>L) i \<phi>\<^sub>L P\<^sub>L \<B>)
    )
  )
)"

(* ======================== Canonical Judgement Lemmas ======================== *)

(*
lemma canonical_judgement_rec_cannot_be_null_judgement_if_valid [simp] : "\<lbrakk>
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
  (i \<in> (setOfIndex P\<^sub>L));
  ((length P\<^sub>L) > 0);
  (i > 0);
  (i \<le> (length P\<^sub>L));
  \<psi> = (FoI i \<phi>\<^sub>L)
\<rbrakk> \<Longrightarrow> (canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B>) \<noteq> (Judgement 0 {} {})"
  apply (auto)
*)

(*
lemma canonical_judgement_is_canonical_judgement_rec_if_valid [simp] : "\<lbrakk>
  (wfCPLFormula \<phi> \<B>);
  (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
  (i \<in> (setOfIndex P\<^sub>L));
  (i > 0);
  (i \<le> (length P\<^sub>L))
\<rbrakk> \<Longrightarrow> ((canonicalJudgement i \<phi> \<B>) = (canonicalJudgementRec (FoI i \<phi>\<^sub>L) i \<phi>\<^sub>L P\<^sub>L \<B>))"
  apply (auto)
  apply (rule canonicalJudgement.cases)
*)


lemma canonical_judgement_is_canonical_judgement_rec_if_valid [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "nat list"
  assumes "(wfCPLFormula \<phi> \<B>)"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  assumes "(i \<in> (setOfIndex P\<^sub>L))"
  shows "(canonicalJudgement i \<phi> \<B>) = (canonicalJudgementRec (FoI i \<phi>\<^sub>L) i \<phi>\<^sub>L P\<^sub>L \<B>)"
proof -
  obtain \<psi> where "\<psi> = (FoI i \<phi>\<^sub>L)" by auto
  have "((length P\<^sub>L) > 0)" using assms(2) parent_list_is_never_empty by auto
  have "(length \<phi>\<^sub>L) = (length P\<^sub>L)" by (metis assms(2) formula_and_parent_list_are_always_the_same_length fst_conv snd_conv)
  have "(i > 0) \<and> (i \<le> (length P\<^sub>L))" using Suc_le_eq assms(3) by auto
  have "(wfCPLFormula \<phi> \<B>)" using assms(1) by auto 
  have "(wfCPLFormula \<psi> \<B>)" by (metis \<open>\<psi> = FoI i \<phi>\<^sub>L\<close> assms(1) assms(2) assms(3) foi_index_is_well_formed_if_root_formula_is_well_formed fst_conv)
  obtain \<J>\<^sub>c where "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)" by auto
  obtain \<J>\<^sub>r where "\<J>\<^sub>r = (canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B>)" by auto
  have "\<J>\<^sub>c \<noteq> (Judgement 0 {} {})" sorry
  have "\<J>\<^sub>r \<noteq> (Judgement 0 {} {})" sorry
  thus ?thesis sorry
qed

lemma canonical_judgement_rec_index_is_maintained_for_atom [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "nat list"
  fixes r :: Relation
  fixes var_list :: "Variable list"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  assumes "(i \<in> (setOfIndex P\<^sub>L))"
  assumes "(Atom r var_list) = (FoI i \<phi>\<^sub>L)"
  shows "(Index (canonicalJudgementRec (Atom r var_list) i \<phi>\<^sub>L P\<^sub>L \<B>)) = i"
proof -
  obtain \<psi> where "\<psi> = (FoI i \<phi>\<^sub>L)" by auto
  have "isFormulaAtom \<psi>" by (metis \<open>\<psi> = FoI i \<phi>\<^sub>L\<close> assms(4) isFormulaAtom.simps(1)) 
  have "((length P\<^sub>L) > 0)" using assms(2) parent_list_is_never_empty by auto
  have "(length \<phi>\<^sub>L) = (length P\<^sub>L)" by (metis assms(2) formula_and_parent_list_are_always_the_same_length fst_conv snd_conv)
  have "(i > 0) \<and> (i \<le> (length P\<^sub>L))" using Suc_le_eq assms(3) by auto
  have "(wfCPLFormula \<phi> \<B>)" using assms(1) by auto
  have "(wfFormula \<phi> (Sig \<B>))" using assms(1) by auto
  have "(wfFormula \<psi> (Sig \<B>))" by (metis \<open>\<psi> = FoI i \<phi>\<^sub>L\<close> \<open>wfCPLFormula \<phi> \<B>\<close> assms(2) assms(3) foi_index_is_well_formed_if_root_formula_is_well_formed fst_conv wfCPLFormula.elims(1)) 
  have "((Interp \<B>) r) \<noteq> None" by (metis \<open>\<psi> = FoI i \<phi>\<^sub>L\<close> \<open>wfCPLFormula \<phi> \<B>\<close> \<open>wfFormula \<psi> (Sig \<B>)\<close> assms(4) wfCPLFormula.elims(2) wfCPLFormula.elims(3) wf_atom_in_wf_structure_always_has_an_interpretation_for_its_relation) 
  obtain \<J> where "\<J> = (canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B>)" by simp
  have "(Index \<J>) \<noteq> 0" sorry
  thus ?thesis sorry
qed


lemma canonical_judgement_is_always_well_formed [simp] : 
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "nat list"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  assumes "(i \<in> (setOfIndex P\<^sub>L))"
  assumes "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)"
  shows "(wfJudgement \<J>\<^sub>c \<phi> \<B>)"
proof -
  obtain \<psi> where "\<psi> = (FoI i \<phi>\<^sub>L)" by simp
  thus ?thesis sorry
  (*proof (cases \<psi>)
    case (Atom r var_list)
    thus ?thesis sorry
  next
    case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
    then show ?thesis sorry
  next
    case (Forall x \<psi>\<^sub>1)
    then show ?thesis sorry
  next
    case (Exists x \<psi>\<^sub>1)
    then show ?thesis sorry
  qed*)
qed

lemma canonical_judgement_lemma_index [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "nat list"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  assumes "(i \<in> (setOfIndex P\<^sub>L))"
  assumes "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)"
  shows "(Index \<J>\<^sub>c) = i"
proof -
  obtain \<psi> where "\<psi> = (FoI i \<phi>\<^sub>L)" by simp
  thus ?thesis
  proof (cases \<psi>)
    case (Atom r var_list)
    have "i > 0 \<and> i \<le> (length P\<^sub>L)" using Suc_le_eq assms(3) by auto
    have "(length \<phi>\<^sub>L) > 0" using assms(2) formula_list_is_never_empty by auto
    obtain \<J> where "\<J> = canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B>" by simp
    thus ?thesis sorry
  next
    case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
    thus ?thesis sorry
  next
    case (Forall x \<psi>\<^sub>1)
    thus ?thesis sorry
  next
    case (Exists x \<psi>\<^sub>1)
    thus ?thesis sorry
  qed
qed

lemma canonical_judgement_lemma_var_set [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "nat list"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  assumes "(i \<in> (setOfIndex P\<^sub>L))"
  assumes "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)"
  shows "(Vars \<J>\<^sub>c) = (freeVar (FoI i \<phi>\<^sub>L))"
proof -  
  obtain \<psi> where "\<psi> = (FoI i \<phi>\<^sub>L)" by simp
  thus ?thesis
  proof (cases \<psi>)
    case (Atom r var_list)
    have "isFormulaAtom \<psi>" by (simp add: Atom)
    have "(wfCPLFormula \<psi> \<B>)" by (metis \<open>\<psi> = FoI i \<phi>\<^sub>L\<close> assms(1) assms(2) assms(3) foi_index_is_well_formed_if_root_formula_is_well_formed fst_conv wfCPLInstance.elims(2))
    obtain f where "(Some f) = ((Interp \<B>) r)" by (metis Atom \<open>wfCPLFormula \<psi> \<B>\<close> not_Some_eq wf_atom_in_wf_structure_always_has_an_interpretation_for_its_relation)
    thus ?thesis sorry
  next
    case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
    then show ?thesis sorry
  next
    case (Forall x \<psi>\<^sub>1)
    then show ?thesis sorry
  next
    case (Exists x \<psi>\<^sub>1)
    then show ?thesis sorry
  qed
qed

lemma canonical_judgement_lemma_is_derivable [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  fixes \<phi>\<^sub>L :: "Formula list"
  fixes P\<^sub>L :: "nat list"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)"
  assumes "(i \<in> (setOfIndex P\<^sub>L))"
  assumes "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)"
  shows "isDerivable \<phi> \<B> \<J>\<^sub>c"
proof -        
  obtain \<psi> where "\<psi> = (FoI i \<phi>\<^sub>L)" by simp
  thus ?thesis
  proof (cases \<psi>)
    case (Atom r var_list)
    thus ?thesis sorry
  next
    case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
    thus ?thesis sorry
  next
    case (Forall x \<psi>\<^sub>1)
    thus ?thesis sorry
  next
    case (Exists x \<psi>\<^sub>1)
    thus ?thesis sorry
  qed
qed

lemma completeness_canonical_judgement_funcs_set_is_empty [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "\<not>(isModel \<B> e \<phi>)"
  shows "(Funcs (canonicalJudgement 1 \<phi> \<B>)) = {}"
proof -
  show ?thesis sorry
qed

(* ================= Completeness Proof ================= *)

theorem CPL_Completeness_Theorem [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "\<not>(isModel \<B> e \<phi>)"
  shows "isDerivable \<phi> \<B> (Judgement 1 {} {})"
proof -
  have "(wfStructure \<B>)" using assms(1) by auto 
  have "(wfFormula \<phi> (Sig \<B>))" using assms(1) by auto
  have "((ran e) \<subseteq> (Univ \<B>))" by simp
  have "sentence \<phi>" using assms(1) by auto
  obtain \<phi>\<^sub>L P\<^sub>L where "(\<phi>\<^sub>L, P\<^sub>L)= (buildFormulaParentList \<phi>)" by (metis old.prod.exhaust)
  have "\<phi> = (FoI 1 \<phi>\<^sub>L)" by (metis \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> foi_first_index_is_always_the_root_formula fst_conv)
  have "(1 \<in> (setOfIndex P\<^sub>L))" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> one_is_always_in_set_of_index by blast
  thus ?thesis
  proof (cases \<phi>)
    case (Atom r var_list)
    have "(set var_list) = (freeVar \<phi>)" by (simp add: Atom)
    have "((freeVar \<phi>) \<subseteq> (dom e))" using \<open>sentence \<phi>\<close> by auto
    thus ?thesis
    proof (cases "((Sig \<B>) r)")
      case None
      show ?thesis
      proof (rule ccontr)
        show "False" using Atom None \<open>wfFormula \<phi> (Sig \<B>)\<close> by auto
      qed
    next
      case (Some arity)
      show ?thesis
      proof (cases "arity = 0")
        case False
        have "arity > 0" using False by auto
        have "(isFormulaAtom \<phi>)" by (simp add: Atom) 
        have "((length var_list) = arity)" using Atom Some \<open>wfFormula \<phi> (Sig \<B>)\<close> by force
        show ?thesis
        proof (rule ccontr)
          have "\<not> (sentence \<phi>)" using Atom \<open>0 < arity\<close> \<open>length var_list = arity\<close> by auto
          thus "False" using \<open>sentence \<phi>\<close> by blast 
        qed
      next
        case True \<comment> \<open> Note: I have made the assumption that we accept relationship symbols with arity=0 \<close>
        have "(length var_list) = 0" using \<open>sentence \<phi>\<close> \<open>set var_list = freeVar \<phi>\<close> by auto
        obtain \<J>\<^sub>c where "\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>" by auto
        then have "isDerivable \<phi> \<B> \<J>\<^sub>c" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> assms(1) canonical_judgement_lemma_is_derivable by blast
        have "(Index \<J>\<^sub>c) = 1" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) canonical_judgement_lemma_index by blast
        have "(Vars \<J>\<^sub>c) = {}" by (metis \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> \<open>\<phi> = FoI 1 \<phi>\<^sub>L\<close> \<open>sentence \<phi>\<close> assms(1) canonical_judgement_lemma_var_set sentence.elims(2))
        have "(Funcs \<J>\<^sub>c) = {}" using \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) assms(2) completeness_canonical_judgement_funcs_set_is_empty by blast
        have "\<J>\<^sub>c = (Judgement 1 {} {})" by (metis Judgement.collapse \<open>Funcs \<J>\<^sub>c = {}\<close> \<open>Index \<J>\<^sub>c = 1\<close> \<open>Vars \<J>\<^sub>c = {}\<close>) 
        thus ?thesis using \<open>isDerivable \<phi> \<B> \<J>\<^sub>c\<close> by blast
      qed
    qed
  next
    case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
    obtain \<J>\<^sub>c where "\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>" by auto
    then have "isDerivable \<phi> \<B> \<J>\<^sub>c" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> assms(1) canonical_judgement_lemma_is_derivable by blast
    have "(Index \<J>\<^sub>c) = 1" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) canonical_judgement_lemma_index by blast
    have "(Vars \<J>\<^sub>c) = {}" by (metis \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> \<open>\<phi> = FoI 1 \<phi>\<^sub>L\<close> \<open>sentence \<phi>\<close> assms(1) canonical_judgement_lemma_var_set sentence.elims(2)) 
    have "(Funcs \<J>\<^sub>c) = {}" using \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) assms(2) completeness_canonical_judgement_funcs_set_is_empty by blast 
    have "\<J>\<^sub>c = (Judgement 1 {} {})" by (metis Judgement.collapse \<open>Funcs \<J>\<^sub>c = {}\<close> \<open>Index \<J>\<^sub>c = 1\<close> \<open>Vars \<J>\<^sub>c = {}\<close>) 
    thus ?thesis using \<open>isDerivable \<phi> \<B> \<J>\<^sub>c\<close> by auto
  next
    case (Forall x \<psi>)
    obtain \<J>\<^sub>c where "\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>" by auto
    then have "isDerivable \<phi> \<B> \<J>\<^sub>c" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> assms(1) canonical_judgement_lemma_is_derivable by blast 
    have "(Index \<J>\<^sub>c) = 1" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) canonical_judgement_lemma_index by blast 
    have "(Vars \<J>\<^sub>c) = {}" by (metis \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> \<open>\<phi> = FoI 1 \<phi>\<^sub>L\<close> \<open>sentence \<phi>\<close> assms(1) canonical_judgement_lemma_var_set sentence.elims(2))
    have "(Funcs \<J>\<^sub>c) = {}" using \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) assms(2) completeness_canonical_judgement_funcs_set_is_empty by blast 
    have "\<J>\<^sub>c = (Judgement 1 {} {})" by (metis Judgement.collapse \<open>Funcs \<J>\<^sub>c = {}\<close> \<open>Index \<J>\<^sub>c = 1\<close> \<open>Vars \<J>\<^sub>c = {}\<close>) 
    thus ?thesis using \<open>isDerivable \<phi> \<B> \<J>\<^sub>c\<close> by auto  
  next
    case (Exists x \<psi>)
    obtain \<J>\<^sub>c where "\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>" by auto
    then have "isDerivable \<phi> \<B> \<J>\<^sub>c" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> assms(1) canonical_judgement_lemma_is_derivable by blast 
    have "(Index \<J>\<^sub>c) = 1" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) canonical_judgement_lemma_index by blast 
    have "(Vars \<J>\<^sub>c) = {}" using \<open>(\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>\<close> \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> \<open>\<phi> = FoI 1 \<phi>\<^sub>L\<close> \<open>sentence \<phi>\<close> assms(1) canonical_judgement_lemma_var_set sentence.simps by blast 
    have "(Funcs \<J>\<^sub>c) = {}" using \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) assms(2) completeness_canonical_judgement_funcs_set_is_empty by blast 
    have "\<J>\<^sub>c = (Judgement 1 {} {})" by (metis Judgement.collapse \<open>Funcs \<J>\<^sub>c = {}\<close> \<open>Index \<J>\<^sub>c = 1\<close> \<open>Vars \<J>\<^sub>c = {}\<close>) 
    thus ?thesis using \<open>isDerivable \<phi> \<B> \<J>\<^sub>c\<close> by auto
  qed
qed


(* ==================== Tests ==================== *)

lemma "(canonicalJudgement 10 myFormula myStructure) = (Judgement 0 {} {})"
  apply (simp add: numeral_nat(2) numeral_Bit1)
  done

abbreviation "myOtherAtomFormula \<equiv> (Atom (CHR ''E'') [CHR ''x'', CHR ''y''])"

lemma "(canonicalJudgement 1 myOtherAtomFormula myStructure) = (
    Judgement 1 {CHR ''x'', CHR ''y''} {
      [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> A],
      [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> C],
      [CHR ''x'' \<mapsto> B, CHR ''y'' \<mapsto> A]
    }
  )"
  apply (auto)
  apply (metis map_upds_Cons map_upds_Nil1)
  apply (metis map_upds_Cons map_upds_Nil1)
  apply (metis map_upds_Cons map_upds_Nil1)
  done



lemma example_formula_incomplete_is_wf_cpl_instance [simp] : "(wfCPLInstance exampleFormulaIncomplete exampleStructureIncomplete)"
  by auto

lemma e_is_not_model_of_example_formula_incomplete [simp] : "\<not>(isModel exampleStructureIncomplete e exampleFormulaIncomplete)"
  by auto

lemma "isDerivable exampleFormulaIncomplete exampleStructureIncomplete (Judgement 1 {} {})"
  using CPL_Completeness_Theorem e_is_not_model_of_example_formula_incomplete example_formula_incomplete_is_wf_cpl_instance by blast

end