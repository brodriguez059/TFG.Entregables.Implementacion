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


function canonicalJudgementRec :: "Formula \<Rightarrow> nat \<Rightarrow> Formula list \<Rightarrow> ParentIndex list \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement" where
"(((length \<phi>\<^sub>L) = 0) \<or> (i = 0)) \<Longrightarrow> canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B> = (Judgement 0 {} {})" |
"((length \<phi>\<^sub>L) > 0) \<and> (i > (length \<phi>\<^sub>L)) \<Longrightarrow> canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B> = (Judgement 0 {} {})" |
"((length \<phi>\<^sub>L) > 0) \<and> (i > 0) \<and> (i \<le> (length \<phi>\<^sub>L)) \<Longrightarrow> canonicalJudgementRec \<psi> i \<phi>\<^sub>L P\<^sub>L \<B> = (
  case \<psi> of
  (Atom r var_list) \<Rightarrow> (let
      \<I> = (Interp \<B>)
    in (
      Judgement i (set var_list) (buildAtomValuations var_list (the (\<I> r)))
    )
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
    childIndexes = (CoI i P\<^sub>L);
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
  apply (auto)
  done


fun canonicalJudgement :: "nat \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement" where
"canonicalJudgement 0 \<phi> \<B> = (Judgement 0 {} {})" |
"canonicalJudgement i \<phi> \<B> = (let
    (\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>
  in (
    (if ((i = 0) \<or> (i > (length \<phi>\<^sub>L)) \<or> ((length \<phi>\<^sub>L) = 0))
      then (Judgement 0 {} {})
      else (canonicalJudgementRec (FoI i \<phi>\<^sub>L) i \<phi>\<^sub>L P\<^sub>L \<B>)
    )
  )
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

lemma canonical_judgement_lemma_index [simp] :
  fixes \<phi> :: Formula
  fixes \<B> :: "'a Structure"
  fixes i :: nat
  fixes \<J>\<^sub>c :: "'a Judgement"
  assumes "(wfCPLInstance \<phi> \<B>)"
  assumes "(i \<in> (setOfIndex (formulaToList \<phi>)))"
  shows "(Index (canonicalJudgement i \<phi> \<B>)) = i"
proof -
  let ?formulaParentList = "buildFormulaParentList \<phi>"
  obtain \<J>\<^sub>c where "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)" by simp
  obtain \<phi>\<^sub>L where "\<phi>\<^sub>L = fst ?formulaParentList" by simp
  obtain P\<^sub>L where "P\<^sub>L = snd ?formulaParentList" by simp
  obtain \<psi> where "\<psi> = (FoI i \<phi>\<^sub>L)" by simp
  have "(Index \<J>\<^sub>c) = i"
  show ?thesis 
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
  let ?formulaParentList = "buildFormulaParentList \<phi>"
  obtain \<phi>\<^sub>L where "\<phi>\<^sub>L = fst ?formulaParentList" by simp
  obtain P\<^sub>L where "P\<^sub>L = snd ?formulaParentList" by simp
  obtain \<psi> where "\<psi> = (FoI i \<phi>\<^sub>L)" by simp
  show ?thesis
  proof (cases \<psi>)
  case (Atom r var_list)
    then show ?thesis
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

lemma "(canonicalJudgement 10 myFormula myStructure) = (Judgement 0 {} {})"
  apply (auto)
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

end