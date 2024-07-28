theory "CPL_Proof_System"
  imports Main "CPL_Syntax" "CPL_Semantic" "CPL_Proof_Base"
begin

(* ================= Auxiliary Functions ================= *)

fun buildValuation :: "Variable list \<Rightarrow> 'a list \<Rightarrow> 'a Valuation"  where
"buildValuation [] [] = e " |
"buildValuation variables values = [variables [\<mapsto>] values]"

fun buildAtomValuations :: "Variable list \<Rightarrow> 'a list set \<Rightarrow> 'a Valuation set" where
"buildAtomValuations kl vs_set = { buildValuation kl vl | vl. vl \<in> vs_set }"

fun projectValuation :: "'a Valuation \<Rightarrow> Variable set \<Rightarrow> 'a Valuation" where \<comment> \<open>  Note: |` is called restrict_map operator. m |` A = (\<lambda>x. if x \<in> A then m x else None)  \<close>
"projectValuation f V = (if (V \<subseteq> (dom f))
  then f |` V
  else e
)"

fun projectJudgementValuations :: "'a Judgement \<Rightarrow> Variable set \<Rightarrow> 'a Valuation set" where
"projectJudgementValuations \<J> V = {projectValuation f V | f. f \<in> (Funcs \<J>)}"

fun valuationsProduct :: "'a Valuation set \<Rightarrow> 'a Valuation set \<Rightarrow> 'a Valuation set" where
"valuationsProduct F\<^sub>1 F\<^sub>2 = {(fst p) ++ (snd p) | p. p\<in>(F\<^sub>1\<times>F\<^sub>2)}"

fun valuationInProjectionValuations :: "'a Valuation \<Rightarrow> Variable set \<Rightarrow> 'a Valuation set \<Rightarrow> bool" where
"valuationInProjectionValuations f U F = ((projectValuation f U) \<in> F)"

fun joinJudgementValuations :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> 'a Valuation set" where
"joinJudgementValuations \<J>\<^sub>1 \<J>\<^sub>2 = (let
    F\<^sub>1 = (Funcs \<J>\<^sub>1);
    U\<^sub>1 = (Vars \<J>\<^sub>1);
    F\<^sub>2 = (Funcs \<J>\<^sub>2);
    U\<^sub>2 = (Vars \<J>\<^sub>2)
  in (
    {
       f \<in> (valuationsProduct F\<^sub>1 F\<^sub>2). (
        (valuationInProjectionValuations f U\<^sub>1 F\<^sub>1) \<and>
        (valuationInProjectionValuations f U\<^sub>2 F\<^sub>2)
      )
    }
  )
)"

fun dualProjectJudgementValuations :: "'a Judgement \<Rightarrow> 'a Judgement  \<Rightarrow> Variable \<Rightarrow> 'a Structure \<Rightarrow> 'a Valuation set" where
"dualProjectJudgementValuations \<J>\<^sub>1 \<J>\<^sub>2 y \<B> = {
    f \<in> (Funcs \<J>\<^sub>1). ( \<forall>b \<in> (Univ \<B>). f(y \<mapsto> b) \<in> (Funcs \<J>\<^sub>2))
}"

fun mapValuation :: "'a Valuation \<Rightarrow> Variable list \<Rightarrow> 'a list" where \<comment> \<open> TODO: Explain this and change in more detail \<close>
"mapValuation f vs = (if ((set vs) \<subseteq> (dom f))
  then [the (f v). v \<leftarrow> vs]
  else []
)"

(* ================= Proof System Functions ================= *)

fun isAtom :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isAtom \<J> \<phi> \<B> = (
  let
    (\<phi>\<^sub>L, _) = (buildFormulaParentList \<phi>);
    \<psi> = (FoI (Index \<J>) \<phi>\<^sub>L);
    \<I> = (Interp \<B>)
  in
    (isFormulaAtom \<psi>) \<and>
    ((Vars \<J>) = (set (atom_vars \<psi>))) \<and>
    (case (\<I> (atom_rel \<psi>)) of
      None \<Rightarrow> False |
      Some set_of_list \<Rightarrow> ( (Funcs \<J>) = (buildAtomValuations (atom_vars \<psi>) set_of_list) )
    )
)"

fun isProjection :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isProjection \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) ) \<and>
  ( (Funcs \<J>\<^sub>1) = (projectJudgementValuations \<J>\<^sub>2 (Vars \<J>\<^sub>1)) )
)"

fun isJoin :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isJoin \<J> \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J> \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( (Vars \<J>) = ((Vars \<J>\<^sub>1) \<union> (Vars \<J>\<^sub>2)) ) \<and>
  (let
    (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)
  in (
      isFormulaAnd (FoI (Index \<J>) \<phi>\<^sub>L) \<and>
      ( (isParent \<J> \<J>\<^sub>1 \<phi>\<^sub>L P\<^sub>L) \<and> (isParent \<J> \<J>\<^sub>2 \<phi>\<^sub>L P\<^sub>L) )
    )
  ) \<and>
  ( (Funcs \<J>) = (joinJudgementValuations \<J>\<^sub>1 \<J>\<^sub>2) )
)"

fun isDualProjection :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isDualProjection \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  (
    let
      (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>);
      \<psi>\<^sub>1 = (FoI (Index \<J>\<^sub>1) \<phi>\<^sub>L);
      \<psi>\<^sub>2 = (FoI (Index \<J>\<^sub>2) \<phi>\<^sub>L);
      y = (forall_x \<psi>\<^sub>1)
    in (
      ( isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi>\<^sub>L P\<^sub>L ) \<and>
      (isFormulaForAll \<psi>\<^sub>1) \<and>
      ( \<psi>\<^sub>1 = (Forall y \<psi>\<^sub>2) ) \<and>
      ( y \<in> (Vars \<J>\<^sub>2) )  \<and>
      ( (Vars \<J>\<^sub>1) = ((Vars \<J>\<^sub>2) - {y}) )  \<and>
      ( (Funcs \<J>\<^sub>1) = (dualProjectJudgementValuations \<J>\<^sub>1 \<J>\<^sub>2 y \<B>) )
    )
  )
)"

fun isUpwardFlow :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isUpwardFlow \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
    ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
    ( (Vars \<J>\<^sub>1) = (Vars \<J>\<^sub>2) ) \<and>
    ( (Funcs \<J>\<^sub>1) = (Funcs \<J>\<^sub>2) ) \<and>
    (
    let
      (\<phi>\<^sub>L, P\<^sub>L) = (buildFormulaParentList \<phi>)
    in (
        isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi>\<^sub>L P\<^sub>L
      )
    )
)"

(* ================= Proof System ================= *)

inductive isDerivable :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement \<Rightarrow> bool" for \<phi> and \<B> where
ATR: "\<lbrakk> \<comment> \<open>  Atom rule  \<close>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  isAtom \<J> \<phi> \<B>
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| \<comment> \<open>  Projection rule  \<close>
PJR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (isDerivable \<phi> \<B> \<J>') \<and>
    (isProjection \<J> \<J>' \<phi> \<B>) 
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| \<comment> \<open>  Join rule  \<close>
JNR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>\<^sub>0 \<J>\<^sub>1. (
    (isJoin \<J> \<J>\<^sub>0 \<J>\<^sub>1 \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>\<^sub>0 \<and> isDerivable \<phi> \<B> \<J>\<^sub>1)
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| \<comment> \<open>  \<forall>-elimination rule  \<close>
FER: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
      (isDualProjection \<J> \<J>' \<phi> \<B>) \<and>
      (isDerivable \<phi> \<B> \<J>')
    )
  )
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| \<comment> \<open>  Upward-flow rule  \<close>
UFR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (isUpwardFlow \<J> \<J>' \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>')
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"

\<comment> \<open>The predicate isModel decides if the (\<B>,f) is a model of \<phi> ( (\<B>,f) \<Turnstile> \<phi> )\<close>
fun isModel :: "'a Structure \<Rightarrow> 'a Valuation \<Rightarrow> Formula \<Rightarrow> bool" where
"isModel \<B> f \<phi> = (
  (wfStructure \<B>) \<and>
  (wfFormula \<phi> (Sig \<B>)) \<and>
  ((ran f) \<subseteq> (Univ \<B>)) \<and>
  ((freeVar \<phi>) \<subseteq> (dom f)) \<and>
  (case \<phi> of
    (Atom r var_list) \<Rightarrow> (case (((Interp \<B>) r)) of 
      None \<Rightarrow> False |
      (Some set_of_list) \<Rightarrow> (
        ((set var_list) \<subseteq> (dom f)) \<and>
        ((mapValuation f var_list) \<in> set_of_list)
      )
    ) |
    (And \<psi>\<^sub>1 \<psi>\<^sub>2) \<Rightarrow> ((isModel \<B> f \<psi>\<^sub>1) \<and> (isModel \<B> f \<psi>\<^sub>2)) |
    (Forall x \<psi>) \<Rightarrow> (\<forall>v\<in>(Univ \<B>). (isModel \<B> (f(x \<mapsto> v)) \<psi>))|
    (Exists x \<psi>) \<Rightarrow> (\<exists>v\<in>(Univ \<B>). (isModel \<B> (f(x \<mapsto> v)) \<psi>))
  )
)"


(* ======================== Tests ======================== *)

abbreviation "atomJudgement \<equiv> myJudgement"

lemma "wfJudgement atomJudgement myFormula myStructure = True"
  apply(simp add: Let_def)
  by auto
                                           
lemma "(isAtom atomJudgement myFormula myStructure) = True"
  apply(simp add: Let_def)
  apply(auto)
  apply(force)
  apply(force)
  by(force)



abbreviation "projectionBaseJudgement \<equiv> myJudgement"
abbreviation "projectionProjectedJudgement::(BEnum Judgement) \<equiv> (Judgement 6 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"

lemma "wfJudgement projectionBaseJudgement myFormula myStructure = True"
  by (auto simp add: Let_def)

lemma "wfJudgement projectionProjectedJudgement myFormula myStructure = True"
  by (auto simp add: Let_def)

lemma "isProjection projectionProjectedJudgement projectionBaseJudgement myFormula myStructure = True"
  apply(auto simp add: Let_def)
  apply (smt (verit, ccfv_threshold) domIff dom_eq_empty_conv dom_restrict fun_upd_same inf_bot_right option.simps(3) restrict_map_insert)
  apply (smt (verit, ccfv_threshold) domIff dom_eq_empty_conv dom_restrict fun_upd_same inf_bot_right option.simps(3) restrict_map_insert)
  done



abbreviation "joinFirstChildJudgement::(BEnum Judgement) \<equiv> (Judgement 4 myFreeVariableSet myValuationSet)"
abbreviation "joinSecondChildJudgement::(BEnum Judgement) \<equiv> (Judgement 5 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
abbreviation "joinParentJudgement::(BEnum Judgement) \<equiv> (Judgement 3 myFreeVariableSet {
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> A],
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> C],
  [CHR ''x'' \<mapsto> B, CHR ''y'' \<mapsto> A]
})"

lemma [simp] : "myFreeVariableSet - {CHR ''y''} \<subseteq> {CHR ''x''}"
  by auto

lemma [simp] : "{CHR ''y'', CHR ''x''} = myFreeVariableSet"
  by(auto)

lemma [simp] : "insert (CHR ''y'') myFreeVariableSet = myFreeVariableSet"
  by auto

lemma [simp] : "x\<in>S \<Longrightarrow> S = insert x S"
  by auto

lemma [simp] : "mapping \<noteq> Map.empty \<Longrightarrow> (\<lambda>x. None) \<noteq> mapping" \<comment> \<open>  Note: This needs to be explicit because Map.empty \<equiv> (\<lambda>x. None) is an abbreviation  \<close>
  by auto

lemma [simp] : "wfJudgement joinParentJudgement myFormula myStructure = True"
  by (simp add: Let_def)

lemma [simp] : "wfJudgement joinFirstChildJudgement myFormula myStructure = True"
  by (simp add: Let_def)

lemma [simp] : "wfJudgement joinSecondChildJudgement myFormula myStructure = True"
  by (simp add: Let_def)

lemma "isJoin joinParentJudgement joinFirstChildJudgement joinSecondChildJudgement myFormula myStructure = True"
  apply (simp_all add: Let_def)
  apply (auto)
  apply (force)
  apply (force)
  by (force)



abbreviation "forAllBaseJudgement::(BEnum Judgement) \<equiv> (Judgement 3 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
abbreviation "forAllDualProjectedJudgement::(BEnum Judgement) \<equiv> (Judgement 2 {} {})"
lemma "wfCPLInstance myFormula myStructure = True"
  by(auto)

lemma "wfJudgement forAllBaseJudgement myFormula myStructure = True"
  by(simp add: Let_def)

lemma "wfJudgement forAllDualProjectedJudgement myFormula myStructure = True"
  by(auto)

lemma "isDualProjection forAllDualProjectedJudgement forAllBaseJudgement myFormula myStructure = True"
  by (simp_all add: Let_def)



abbreviation "upwardBaseJudgement \<equiv> projectionProjectedJudgement"
abbreviation "upwardFlowedJudgement::(BEnum Judgement) \<equiv> (Judgement 5 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
lemma "wfCPLInstance myFormula myStructure = True"
  by auto

lemma "wfJudgement upwardBaseJudgement myFormula myStructure = True"
  by (simp add: Let_def)

lemma "wfJudgement upwardFlowedJudgement myFormula myStructure = True"
  by (simp add: Let_def)

lemma "isUpwardFlow upwardFlowedJudgement upwardBaseJudgement myFormula myStructure = True"
  by (simp add: Let_def)

end