theory "CPL_Proof_System"
  imports Main "CPL_Instance" "CPL_Utils"
begin

(* ================= Proof System Functions ================= *)

fun isAtom :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isAtom \<J> \<phi> \<B> = (
  let
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>));
    interpretation = (Interp \<B>)
  in
    (isFormulaAtom \<psi>) \<and>
    ((Vars \<J>) = (set (VarList \<psi>))) \<and>
    (case (interpretation (Rel \<psi>)) of
      None \<Rightarrow> False |
      Some set_of_list \<Rightarrow> (
        (Funcs \<J>) = { buildValuation (VarList \<psi>) l | l. l \<in> set_of_list }
      )
    )
)"

fun isProjection :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isProjection \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) ) \<and>
  ( (Funcs \<J>\<^sub>1) = {projectValuation f (Vars \<J>\<^sub>1) | f. f \<in> (Funcs \<J>\<^sub>2)} )
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
      ( isFormulaForAll \<psi>\<^sub>1 ) \<and>
      ( \<psi>\<^sub>1 = (Forall y \<psi>\<^sub>2) ) \<and>
      ( y \<in> (Vars \<J>\<^sub>2) )  \<and>
      ( (Vars \<J>\<^sub>1) = (Vars \<J>\<^sub>2) - ({y}) )  \<and>
      (
        {
          h \<in> (allMaps (card (Vars \<J>\<^sub>1)) (Vars \<J>\<^sub>1) (Univ \<B>)). (
            \<forall>b \<in> (Univ \<B>). h(y \<mapsto> b) \<in> (Funcs \<J>\<^sub>2)
          )
        } = (Funcs \<J>\<^sub>1)
      )
    )
  )
)"

fun isJoin :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isJoin \<J> \<J>\<^sub>1 \<J>\<^sub>2 \<phi> \<B> = (
  ( (wfJudgement \<J> \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>1 \<phi> \<B>) \<and> (wfJudgement \<J>\<^sub>2 \<phi> \<B>) ) \<and>
  ( (Vars \<J>) = ((Vars \<J>\<^sub>1) \<union> (Vars \<J>\<^sub>2)) ) \<and>
  ( isFormulaAnd (FoI (Index \<J>) (formulaToList \<phi>)) ) \<and>
  ( (isParent \<J> \<J>\<^sub>1 \<phi>) \<and> (isParent \<J> \<J>\<^sub>2 \<phi>) ) \<and>
  (
    let
      variables = (Vars \<J>\<^sub>1) \<union> (Vars \<J>\<^sub>2)
    in (
      {
        f \<in> (allMaps (card variables) variables (Univ \<B>)). (
          ( (projectValuation f (Vars \<J>\<^sub>1)) \<in> (Funcs \<J>\<^sub>1) ) \<and>
          ( (projectValuation f (Vars \<J>\<^sub>2)) \<in> (Funcs \<J>\<^sub>2) )
        )
      } = (Funcs \<J>)
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
(* Atom rule *)
ATR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  isAtom \<J> \<phi> \<B>
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| (* Projection rule *)
PJR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (isProjection \<J> \<J>' \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>')
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| (* Join rule *)
JNR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>\<^sub>0 \<J>\<^sub>1. (
    (isJoin \<J> \<J>\<^sub>0 \<J>\<^sub>1 \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>\<^sub>0 \<and> isDerivable \<phi> \<B> \<J>\<^sub>1)
  ))
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| (* \<forall>-elimination rule *)
FER: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
      (isDualProjection \<J> \<J>' \<phi> \<B>) \<and>
      (isDerivable \<phi> \<B> \<J>')
    )
  )
  \<rbrakk> \<Longrightarrow> isDerivable \<phi> \<B> \<J>"
| (* Upward-flow rule *)
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
  (ran f \<subseteq> (Univ \<B>)) \<and>
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
    (Forall x \<psi>) \<Rightarrow> True \<or> (\<forall>v. v\<in>(Univ \<B>) \<longrightarrow> (isModel (f(x \<mapsto> v)) \<psi> \<B>))|
    (Exists x \<psi>) \<Rightarrow> True \<or> (\<exists>v. v\<in>(Univ \<B>) \<and> (isModel (f(x \<mapsto> v)) \<psi> \<B>))
  )
)"

fun isValuationModel :: "'a Valuation \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isValuationModel f \<J> \<phi> \<B> = (
  let
    var_list = (Vars \<J>);
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>))
  in (
    (f \<in> (allMaps (card var_list) var_list (Univ \<B>))) \<and>
    (wfStructure \<B>) \<and>
    (wfFormula \<phi> (Sig \<B>)) \<and>
    (wfJudgement \<J> \<phi> \<B>) \<and>
    (isModel f (existSq (setToList ((freeVar \<psi>) - (Vars \<J>))) \<psi>) \<B>)
  )
)"

(* ======================== Tests ======================== *)

abbreviation "atomJudgement \<equiv> myJudgement"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement atomJudgement myFormula myStructure"
value "isAtom atomJudgement myFormula myStructure"



abbreviation "projectionBaseJudgement \<equiv> myJudgement"
abbreviation "projectionProjectedJudgement::(BEnum Judgement) \<equiv> (Judgement 6 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement projectionBaseJudgement myFormula myStructure"
value "wfJudgement projectionProjectedJudgement myFormula myStructure"
value "isProjection projectionProjectedJudgement projectionBaseJudgement myFormula myStructure"



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
value "wfCPLInstance myFormula myStructure"
value "wfJudgement joinFirstChildJudgement myFormula myStructure"
value "wfJudgement joinSecondChildJudgement myFormula myStructure"
value "wfJudgement joinParentJudgement myFormula myStructure"
value "isJoin joinParentJudgement joinFirstChildJudgement joinSecondChildJudgement myFormula myStructure"



abbreviation "forAllBaseJudgement::(BEnum Judgement) \<equiv> (Judgement 3 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
abbreviation "forAllDualProjectedJudgement::(BEnum Judgement) \<equiv> (Judgement 2 {} {})"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement forAllBaseJudgement myFormula myStructure"
value "wfJudgement forAllDualProjectedJudgement myFormula myStructure"
value "isDualProjection forAllDualProjectedJudgement forAllBaseJudgement myFormula myStructure"



abbreviation "upwardBaseJudgement \<equiv> projectionProjectedJudgement"
abbreviation "upwardFlowedJudgement::(BEnum Judgement) \<equiv> (Judgement 5 {CHR ''y''} {
  [CHR ''y'' \<mapsto> A],
  [CHR ''y'' \<mapsto> C]
})"
value "wfCPLInstance myFormula myStructure"
value "wfJudgement upwardBaseJudgement myFormula myStructure"
value "wfJudgement upwardFlowedJudgement myFormula myStructure"
value "isUpwardFlow upwardFlowedJudgement upwardBaseJudgement myFormula myStructure"

end