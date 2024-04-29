theory "CPL_Proof_System"
  imports Main "CPL_Syntax" "CPL_Semantic"
begin

(* ================= Auxiliary Functions ================= *)

fun buildValuation :: "Variable list \<Rightarrow> 'a list \<Rightarrow> 'a Valuation"  where
"buildValuation [] [] = Map.empty " |
"buildValuation variables values = (if (length(variables) = length(values))
  then Map.empty (variables [\<mapsto>] values)
  else Map.empty
)"

fun buildAtomValuations :: "Variable list \<Rightarrow> 'a list set \<Rightarrow> 'a Valuation set" where
"buildAtomValuations ks vs_set = { buildValuation ks l | l. l \<in> vs_set }"

fun projectValuation :: "'a Valuation \<Rightarrow> Variable set \<Rightarrow> 'a Valuation" where \<comment> \<open>  Note: |` is called restrict_map operator. m |` A = (\<lambda>x. if x \<in> A then m x else None)  \<close>
"projectValuation f V = (if (V \<subseteq> (dom f))
  then f |` V
  else Map.empty
)"

lemma projected_valuation_does_not_include_excluded_variables [simp] :
  fixes f :: "'a Valuation"
  fixes U :: "char set"
  fixes V :: "char set"
  assumes "U\<inter>V={}"
  assumes "U\<union>V=(dom f)"
  shows "\<forall>x\<in>V. x\<notin>(dom (projectValuation f U))"
proof (induct "card (dom f)")
  case 0 \<comment> \<open>Case 0: keys is empty set\<close>
  have "(dom f) = {}" using "0" by auto
  hence empty_union: "U\<union>V={}" using assms(2) by auto
  hence "U\<inter>V={}" using assms(1) by auto
  hence "U={} \<and> V={}" using empty_union by auto
  thus ?case by auto
next
  case (Suc n) \<comment> \<open>Case N: keys is not the empty set\<close>
  let ?projected_domain = "(projectValuation f U)"
  have not_empty_domain: "(dom f) \<noteq> {}" using Suc.hyps(2) assms(2) by auto
  show ?case
  proof (induct "(card U)")
    case 0
    have empty_u: "U={}" using "0" by auto
    hence "V\<noteq>{}" using not_empty_domain and assms(2) by auto
    have "(dom ?projected_domain) = {}" using empty_u by auto
    thus ?case by auto
  next
    case (Suc m)
    have non_empty_u: "U\<noteq>{}" using Suc.hyps(2) by auto
    hence "(dom ?projected_domain) \<noteq> {}" by (metis UnCI Un_Int_eq(1) assms(2) dom_restrict projectValuation.simps subsetI)
    show ?case
    proof (induct "(card V)")
      case 0
      have empty_v: "V={}" using "0" by auto
      hence "U = (dom f)" using assms(2) by auto
      thus ?case using empty_v by auto
    next
      case (Suc o)
      have non_empty_v: "V\<noteq>{}" using Suc.hyps(2) by auto
      have "U = (dom ?projected_domain)" using assms(2) by auto
      thus ?case using assms(1) by auto
    qed
  qed
qed

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

fun dualProjectJudgementValuations :: "'a Judgement \<Rightarrow> 'a Judgement  \<Rightarrow> Variable \<Rightarrow> 'a Structure \<Rightarrow> 'a Valuation set" where \<comment> \<open>  Note: |` is called restrict_map operator. m |` A = (\<lambda>x. if x \<in> A then m x else None)  \<close>
"dualProjectJudgementValuations \<J>\<^sub>1 \<J>\<^sub>2 y \<B> = {
    f \<in> (Funcs \<J>\<^sub>1). ( \<forall>b \<in> (Univ \<B>). f(y \<mapsto> b) \<in> (Funcs \<J>\<^sub>2))
}"

fun HOmap :: "'a Valuation \<Rightarrow> Variable list \<Rightarrow> 'a list" where \<comment> \<open> TODO: Explain this and change in more detail \<close>
"HOmap f vs = (if ((set vs) \<subseteq> (dom f))
  then [the (f v). v \<leftarrow> vs]
  else []
)"

fun isParent :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> bool" where
"isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi> = (
  let
    formula_list = (formulaToList \<phi>);
    \<psi>\<^sub>1 = (FoI (Index \<J>\<^sub>1) formula_list);
    \<psi>\<^sub>2 = (FoI (Index \<J>\<^sub>2) formula_list)
  in ( case (\<psi>\<^sub>1) of
    (Atom r var_list) \<Rightarrow> False |
    (Forall x \<phi>\<^sub>1) \<Rightarrow> ( ((Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1) \<and> (\<psi>\<^sub>2 = \<phi>\<^sub>1) ) |
    (Exists x \<phi>\<^sub>1) \<Rightarrow> ( ((Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1) \<and> (\<psi>\<^sub>2 = \<phi>\<^sub>1) ) |
    (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<Rightarrow> (
      ( ((Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1) \<and> (\<psi>\<^sub>2 = \<phi>\<^sub>1) ) \<or>
      ( ((Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 2) \<and> (\<psi>\<^sub>2 = \<phi>\<^sub>2) )
    )
  )
)"

(* ================= Proof System Functions ================= *)

fun isAtom :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isAtom \<J> \<phi> \<B> = (
  let
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>));
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
  ( isFormulaAnd (FoI (Index \<J>) (formulaToList \<phi>)) ) \<and>
  ( (isParent \<J> \<J>\<^sub>1 \<phi>) \<and> (isParent \<J> \<J>\<^sub>2 \<phi>) ) \<and>
  ( (Funcs \<J>) = (joinJudgementValuations \<J>\<^sub>1 \<J>\<^sub>2) )
)"

fun isDualProjection :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isDualProjection \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi> ) \<and>
  (
    let
      formula_list = (formulaToList \<phi>);
      \<psi>\<^sub>1 = (FoI (Index \<J>\<^sub>1) formula_list);
      \<psi>\<^sub>2 = (FoI (Index \<J>\<^sub>2) formula_list);
      y = (forall_x \<psi>\<^sub>1)
    in (
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
    ( isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi> )
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

fun isModel :: "'a Valuation \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isModel f \<phi> \<B> = (
  (wfStructure \<B>) \<and>
  (wfFormula \<phi> (Sig \<B>)) \<and>
  ((ran f) \<subseteq> (Univ \<B>)) \<and>
  ((freeVar \<phi>) \<subseteq> (dom f)) \<and>
  (case \<phi> of
    (Atom r var_list) \<Rightarrow> (case (((Interp \<B>) r)) of 
      None \<Rightarrow> False |
      (Some set_of_list) \<Rightarrow> (
        ((set var_list) \<subseteq> (dom f)) \<and>
        ((HOmap f var_list) \<in> set_of_list)
      )
    ) |
    (And \<psi>\<^sub>1 \<psi>\<^sub>2) \<Rightarrow> ((isModel f \<psi>\<^sub>1 \<B>) \<and> (isModel f \<psi>\<^sub>2 \<B>)) |
    (Forall x \<psi>) \<Rightarrow> (\<forall>v\<in>(Univ \<B>). (isModel (f(x \<mapsto> v)) \<psi> \<B>))|
    (Exists x \<psi>) \<Rightarrow> (\<exists>v\<in>(Univ \<B>). (isModel (f(x \<mapsto> v)) \<psi> \<B>))
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