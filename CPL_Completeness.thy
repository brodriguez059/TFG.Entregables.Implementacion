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

(* ======================== Canonical Judgement Functions ======================== *)

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
*)

(* ======================== Canonical Judgement Lemmas ======================== *)

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

(*
lemma canonical_judgement_lemma_set_of_val_models [simp] :
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
  shows "(Funcs \<J>\<^sub>c) = (setOfValModels (FoI i (formulaToList \<phi>)) \<B>)"
proof -
  obtain \<J>\<^sub>c where canonical_judgement: "\<J>\<^sub>c = (canonicalJudgement i \<phi> \<B>)" by simp
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
*)

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
  let ?formulaParentList = "buildFormulaParentList \<phi>"
  obtain \<phi>\<^sub>L where "\<phi>\<^sub>L = fst ?formulaParentList" by simp
  have "\<phi> = (FoI 1 \<phi>\<^sub>L)" by (metis \<open>\<phi>\<^sub>L = fst (buildFormulaParentList \<phi>)\<close> eq_fst_iff foi_first_index_is_always_the_root_formula) 
  obtain P\<^sub>L where "P\<^sub>L = snd ?formulaParentList" by simp
  have "(1 \<in> (setOfIndex P\<^sub>L))" using \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> one_is_always_in_set_of_index prod.collapse by blast
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
        then have "isDerivable \<phi> \<B> \<J>\<^sub>c" using \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> assms(1) canonical_judgement_lemma_is_derivable prod.collapse by blast
        have "(Index \<J>\<^sub>c) = 1" using \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) canonical_judgement_lemma_index by blast 
        have "(Vars \<J>\<^sub>c) = {}" by (metis \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> \<open>\<phi> = FoI 1 \<phi>\<^sub>L\<close> \<open>\<phi>\<^sub>L = fst (buildFormulaParentList \<phi>)\<close> \<open>freeVar \<phi> \<subseteq> dom (\<lambda>x. None)\<close> assms(1) bot.extremum_uniqueI canonical_judgement_lemma_var_set dom_empty prod.exhaust_sel) 
        have "(Funcs \<J>\<^sub>c) = {}" sorry
        have "\<J>\<^sub>c = (Judgement 1 {} {})" by (metis Judgement.collapse \<open>Funcs \<J>\<^sub>c = {}\<close> \<open>Index \<J>\<^sub>c = 1\<close> \<open>Vars \<J>\<^sub>c = {}\<close>) 
        thus ?thesis using \<open>isDerivable \<phi> \<B> \<J>\<^sub>c\<close> by blast
      qed
    qed
  next
    case (And \<psi>\<^sub>1 \<psi>\<^sub>2)
    obtain \<J>\<^sub>c where "\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>" by auto
    then have "isDerivable \<phi> \<B> \<J>\<^sub>c" using \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> assms(1) canonical_judgement_lemma_is_derivable prod.collapse by blast
    have "(Index \<J>\<^sub>c) = 1" using \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) canonical_judgement_lemma_index by blast 
    have "(Vars \<J>\<^sub>c) = {}" by (metis \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> \<open>\<phi> = FoI 1 \<phi>\<^sub>L\<close> \<open>\<phi>\<^sub>L = fst (buildFormulaParentList \<phi>)\<close> \<open>sentence \<phi>\<close> assms(1) canonical_judgement_lemma_var_set prod.collapse sentence.elims(2)) 
    have "(Funcs \<J>\<^sub>c) = {}" sorry
    have "\<J>\<^sub>c = (Judgement 1 {} {})" by (metis Judgement.collapse \<open>Funcs \<J>\<^sub>c = {}\<close> \<open>Index \<J>\<^sub>c = 1\<close> \<open>Vars \<J>\<^sub>c = {}\<close>) 
    thus ?thesis using \<open>isDerivable \<phi> \<B> \<J>\<^sub>c\<close> by auto
  next
    case (Forall x \<psi>)
    obtain \<J>\<^sub>c where "\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>" by auto
    then have "isDerivable \<phi> \<B> \<J>\<^sub>c" using \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> assms(1) canonical_judgement_lemma_is_derivable prod.collapse by blast 
    have "(Index \<J>\<^sub>c) = 1" using \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) canonical_judgement_lemma_index by blast 
    have "(Vars \<J>\<^sub>c) = {}" by (metis \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> \<open>\<phi> = FoI 1 \<phi>\<^sub>L\<close> \<open>\<phi>\<^sub>L = fst (buildFormulaParentList \<phi>)\<close> \<open>sentence \<phi>\<close> assms(1) canonical_judgement_lemma_var_set prod.collapse sentence.elims(2)) 
    have "(Funcs \<J>\<^sub>c) = {}" sorry
    have "\<J>\<^sub>c = (Judgement 1 {} {})" by (metis Judgement.collapse \<open>Funcs \<J>\<^sub>c = {}\<close> \<open>Index \<J>\<^sub>c = 1\<close> \<open>Vars \<J>\<^sub>c = {}\<close>) 
    thus ?thesis using \<open>isDerivable \<phi> \<B> \<J>\<^sub>c\<close> by auto  
  next
    case (Exists x \<psi>)
    obtain \<J>\<^sub>c where "\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>" by auto
    then have "isDerivable \<phi> \<B> \<J>\<^sub>c" using \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> assms(1) canonical_judgement_lemma_is_derivable prod.collapse by blast 
    have "(Index \<J>\<^sub>c) = 1" using \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> assms(1) canonical_judgement_lemma_index by blast
    have "(Vars \<J>\<^sub>c) = {}" by (metis \<open>1 \<in> setOfIndex P\<^sub>L\<close> \<open>P\<^sub>L = snd (buildFormulaParentList \<phi>)\<close> \<open>\<J>\<^sub>c = canonicalJudgement 1 \<phi> \<B>\<close> \<open>\<phi> = FoI 1 \<phi>\<^sub>L\<close> \<open>\<phi>\<^sub>L = fst (buildFormulaParentList \<phi>)\<close> \<open>sentence \<phi>\<close> assms(1) canonical_judgement_lemma_var_set prod.collapse sentence.elims(2)) 
    have "(Funcs \<J>\<^sub>c) = {}" sorry
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

end