theory "CPL_Completeness"
  imports Main "CPL_Syntax" "CPL_Semantic" "CPL_Proof_System"
begin

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

function canonicalJudgement :: "nat \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement" where
"(i \<notin> (setOfIndex (formulaToList \<phi>))) \<Longrightarrow> canonicalJudgement i \<phi> \<B> = (Judgement 0 {} {})" |
"(i \<in> (setOfIndex (formulaToList \<phi>))) \<Longrightarrow> canonicalJudgement i \<phi> \<B> = (
    let
      formula_list = (formulaToList \<phi>);
      \<psi> = (FoI i formula_list);
      \<I> = (Interp \<B>)
    in (
      case \<psi> of
      (Atom r var_list) \<Rightarrow> (
        Judgement i (set var_list) (buildAtomValuations var_list (the (\<I> r)))
      ) |
      (And \<psi>\<^sub>1 \<psi>\<^sub>2) \<Rightarrow> (let
        \<J>\<^sub>0' = (canonicalJudgement (i+1) \<phi> \<B>);
        \<J>\<^sub>1' = (canonicalJudgement (i+2) \<phi> \<B>)
      in (
          join (Judgement i (Vars \<J>\<^sub>0') (Funcs \<J>\<^sub>0')) (Judgement i (Vars \<J>\<^sub>1') (Funcs \<J>\<^sub>1'))
        )
      ) |
      (Forall x \<psi>\<^sub>1) \<Rightarrow> (let
        \<J>\<^sub>0 = (canonicalJudgement (i+1) \<phi> \<B>)
      in (
          (if (x \<in> (Vars \<J>\<^sub>0))
            then (dualProject x \<J>\<^sub>0 \<B>)
            else (Judgement i (Vars \<J>\<^sub>0) (Funcs \<J>\<^sub>0))
          )
        )
      ) |
      (Exists x \<psi>\<^sub>1) \<Rightarrow> (let
        \<J>\<^sub>0 = (canonicalJudgement (i+1) \<phi> \<B>);
        \<J>\<^sub>p = (project \<J>\<^sub>0 ((Vars \<J>\<^sub>0) - {x}))
      in (
          (if (x \<in> (Vars \<J>\<^sub>0))
            then (Judgement i (Vars \<J>\<^sub>p) (Funcs \<J>\<^sub>p))
            else (Judgement i (Vars \<J>\<^sub>0) (Funcs \<J>\<^sub>0))
          )
        )
      )
    )
  )
"
  apply (auto)
  by blast


fun setOfValModels :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Valuation set" where
"setOfValModels \<phi> \<B> = {}"

(*
lemma canonical_judgement_lemma_set_of_val_models [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(i \<in> (setOfIndex (formulaToList \<phi>)))"
  assumes "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)"
  shows "(Funcs \<J>\<^sub>c) = (setOfValModel (FoI i (formulaToList \<phi>)) \<B>)"
proof -
  sorry
qed

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
  sorry
qed

theorem CPL_Completeness_Theorem [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes \<J>\<^sub>n :: "'a Judgement"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "\<J>\<^sub>n = (Judgement 0 {} {})"
  assumes "\<not>(isModel (Map.empty) \<phi> \<B>)"
  shows "isDerivable \<phi> \<B> \<J>\<^sub>n"
proof -
  sorry
qed
*)

end