theory "CPL_Completeness"
  imports Main "CPL_Syntax" "CPL_Semantic" "CPL_Proof_Base" "CPL_Proof_System"
begin

(* ==================== Completeness ==================== *)

(* ======================== Auxiliary Functions ======================== *)

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

(* ======================== Canonical Judgement ======================== *)


function canonicalJudgementF :: "nat \<Rightarrow> Formula list \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement" where
"((length formula_list) = 0) \<Longrightarrow> canonicalJudgementF i formula_list \<B> = (Judgement 0 {} {})" |
"(i = 0) \<Longrightarrow> canonicalJudgementF i formula_list \<B> = (Judgement 0 {} {})" |
"((length formula_list) > 0) \<and> (i > (length formula_list)) \<Longrightarrow> canonicalJudgementF i formula_list \<B> = (Judgement 0 {} {})" |
"((length formula_list) > 0) \<and> (i > 0) \<and> (i \<le> (length formula_list)) \<Longrightarrow> canonicalJudgementF i formula_list \<B> = (
    let
      \<psi> = (FoI i formula_list);
      \<I> = (Interp \<B>)
    in (
      case \<psi> of
      (Atom r var_list) \<Rightarrow> (
        Judgement i (set var_list) (buildAtomValuations var_list (the (\<I> r)))
      ) |
      (Forall x \<psi>\<^sub>1) \<Rightarrow> (let
        \<J>\<^sub>0 = (canonicalJudgementF (i+1) formula_list \<B>)
      in (
          (if (x \<in> (Vars \<J>\<^sub>0))
            then (dualProject x \<J>\<^sub>0 \<B>)
            else (Judgement i (Vars \<J>\<^sub>0) (Funcs \<J>\<^sub>0))
          )
        )
      ) |
      (Exists x \<psi>\<^sub>1) \<Rightarrow> (let
        \<J>\<^sub>0 = (canonicalJudgementF (i+1) formula_list \<B>);
        \<J>\<^sub>p = (project \<J>\<^sub>0 ((Vars \<J>\<^sub>0) - {x}))
      in (
          (if (x \<in> (Vars \<J>\<^sub>0))
            then (Judgement i (Vars \<J>\<^sub>p) (Funcs \<J>\<^sub>p))
            else (Judgement i (Vars \<J>\<^sub>0) (Funcs \<J>\<^sub>0))
          )
        )
      ) |
      (And \<psi>\<^sub>1 \<psi>\<^sub>2) \<Rightarrow> (let
        \<J>\<^sub>0' = (canonicalJudgementF (i+1) formula_list \<B>);
        \<J>\<^sub>1' = (canonicalJudgementF (i+2) formula_list \<B>)
      in (
          join (Judgement i (Vars \<J>\<^sub>0') (Funcs \<J>\<^sub>0')) (Judgement i (Vars \<J>\<^sub>1') (Funcs \<J>\<^sub>1'))
        )
      )
    )
  )
"
  apply (auto)
  using linorder_not_less by blast
termination
  apply (relation "measures [\<lambda>(i, formula_list, _). formulaDepth(FoI i formula_list)]")
  apply (auto)
  


inductive canonicalJudgementInductive :: "'a Structure \<Rightarrow> Formula list \<Rightarrow> Formula \<Rightarrow> nat \<Rightarrow> 'a Judgement \<Rightarrow> bool"
  for \<B>::"'a Structure" and \<phi>\<^sub>L :: "Formula list"
  where
    atomJ [simp] : "\<lbrakk>
      (isFormulaAtom \<psi>)
    \<rbrakk> \<Longrightarrow> canonicalJudgementInductive \<B> \<phi>\<^sub>L \<psi> i (
        Judgement i (set (atom_vars \<psi>)) (buildAtomValuations var_list (the ((Interp \<B>) (atom_rel \<psi>))))
    )" |
    forAllJInVars [simp] : "\<lbrakk>
      (length \<phi>\<^sub>L) > 0;
      i \<le> (length \<phi>\<^sub>L);
      (isFormulaForAll \<psi>);
      (canonicalJudgementInductive \<B> \<phi>\<^sub>L (FoI (i+1) \<phi>\<^sub>L) (i+1) \<J>\<^sub>0);
      ((forall_x \<psi>) \<in> (Vars \<J>\<^sub>0))
    \<rbrakk> \<Longrightarrow> canonicalJudgementInductive \<B> \<phi>\<^sub>L \<psi> i (dualProject (forall_x \<psi>) \<J>\<^sub>0 \<B>)" |
    forAllJNotInVars [simp] : "\<lbrakk>
      (length \<phi>\<^sub>L) > 0;
      i \<le> (length \<phi>\<^sub>L);
      (isFormulaForAll \<psi>);
      (canonicalJudgementInductive \<B> \<phi>\<^sub>L (FoI (i+1) \<phi>\<^sub>L) (i+1) \<J>\<^sub>0);
      ((forall_x \<psi>) \<notin> (Vars \<J>\<^sub>0))
    \<rbrakk> \<Longrightarrow> canonicalJudgementInductive \<B> \<phi>\<^sub>L \<psi> i (Judgement i (Vars \<J>\<^sub>0) (Funcs \<J>\<^sub>0))" |
    existsJInVars [simp] : "\<lbrakk>
      (length \<phi>\<^sub>L) > 0;
      i \<le> (length \<phi>\<^sub>L);
      (isFormulaExists \<psi>);
      (canonicalJudgementInductive \<B> \<phi>\<^sub>L (FoI (i+1) \<phi>\<^sub>L) (i+1) \<J>\<^sub>0);
      ((exists_x \<psi>) \<in> (Vars \<J>\<^sub>0))
    \<rbrakk> \<Longrightarrow> canonicalJudgementInductive \<B> \<phi>\<^sub>L \<psi> i (let
        \<J>\<^sub>p = (project \<J>\<^sub>0 ((Vars \<J>\<^sub>0) - {x}))
      in (
        Judgement i (Vars \<J>\<^sub>p) (Funcs \<J>\<^sub>p)
      )
    )" |
    existsJNotInVars [simp] : "\<lbrakk>
      (length \<phi>\<^sub>L) > 0;
      i \<le> (length \<phi>\<^sub>L);
      (isFormulaExists \<psi>);
      (canonicalJudgementInductive \<B> \<phi>\<^sub>L (FoI (i+1) \<phi>\<^sub>L) (i+1) \<J>\<^sub>0);
      ((exists_x \<psi>) \<notin> (Vars \<J>\<^sub>0))
    \<rbrakk> \<Longrightarrow> canonicalJudgementInductive \<B> \<phi>\<^sub>L \<psi> i (Judgement i (Vars \<J>\<^sub>0) (Funcs \<J>\<^sub>0))"

fun canonicalJudgement :: "'a Structure \<Rightarrow> Formula list \<Rightarrow> nat \<Rightarrow> 'a Judgement" where
"canonicalJudgement \<B> [] i = (Judgement 0 {} {})" |
"canonicalJudgement \<B> \<phi>\<^sub>L i = (if (i > (length \<phi>\<^sub>L))
  then (Judgement 0 {} {})
  else (
    THE \<J>. (canonicalJudgementInductive \<B> \<phi>\<^sub>L (FoI i \<phi>\<^sub>L) i \<J>))
  )"

(*
fun setOfValModels :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Valuation set" where
"setOfValModels \<phi> \<B> = {}"

lemma canonical_judgement_lemma_set_of_val_models [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(i \<in> (setOfIndex (formulaToList \<phi>)))"
  assumes "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)"
  shows "(Funcs \<J>\<^sub>c) = (setOfValModels (FoI i (formulaToList \<phi>)) \<B>)"
proof -
  sorry
qed
*)

(*
lemma canonical_judgement_lemma_is_derivable [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(i \<in> (setOfIndex (formulaToList \<phi>)))"
  assumes "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)"
  shows "isDerivable \<phi> \<B> \<J>\<^sub>c"
proof -
  show ?thesis by sorry
qed
*)

(* ================= Completeness Proof ================= *)

theorem CPL_Completeness_Theorem [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "\<not>(isModel \<B> e \<phi>)"
  shows "isDerivable \<phi> \<B> (Judgement 1 {} {})"
proof -
  show ?thesis by sorry
qed

(* ==================== Tests ==================== *)

abbreviation "myFormulaList \<equiv> (fst (buildFormulaParentList myFormula))"

lemma "(canonicalJudgement myStructure myFormulaList 10) = (Judgement 0 {} {})"
  by (auto)

lemma "(
  canonicalJudgement
    myStructure
    (fst (buildFormulaParentList (Atom (CHR ''E'') [CHR ''x'', CHR ''y''])))
    1
  ) = (Judgement 1 {CHR ''x'', CHR ''y''} {
      [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> A],
      [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> C],
      [CHR ''x'' \<mapsto> B, CHR ''y'' \<mapsto> A]
    })"
  apply (auto)
  apply (rule the_equality)
  apply (rule canonicalJudgementInductive.induct)
  apply (auto)
  
  

end