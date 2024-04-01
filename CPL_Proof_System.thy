theory "CPL_Proof_System"
  imports Main "CPL_Syntax" "CPL_Semantic"
begin

(* ================= Auxiliary Functions ================= *)

(* Note: Explain why we use nat <the cardinality of keys> here. The function can't work with set constructors*)
function allMaps :: "Variable set \<Rightarrow> 'a set \<Rightarrow> 'a Valuation set" where
"allMaps keys values = (if ((card keys) > 0)
  then (
    let
      k = (SOME x. x \<in> keys);
      reduced_keys = (keys - {k})
    in (
      {
        m(k \<mapsto> v) | m v. v \<in> values \<and> m \<in> (allMaps reduced_keys values)
      }
    )
  )
  else { Map.empty }
)"
  by auto

fun HOmap :: "'a Valuation \<Rightarrow> Variable list \<Rightarrow> 'a list" where
"HOmap f var_list = (if ((set var_list) \<subseteq> (dom f))
  then [the (f v). v \<leftarrow> var_list]
  else []
)"

(* Note: |` is called restrict_map operator. m |` A = (\<lambda>x. if x \<in> A then m x else None) *)
fun projectValuation :: "'a Valuation \<Rightarrow> Variable set \<Rightarrow> 'a Valuation" where
"projectValuation f V = (if (V \<subseteq> (dom f))
  then f |` V
  else Map.empty
)"

fun buildValuation :: "Variable list \<Rightarrow> 'a list \<Rightarrow> 'a Valuation"  where
"buildValuation [] [] = Map.empty " |
"buildValuation variables values = (if (length(variables) = length(values))
  then Map.empty (variables [\<mapsto>] values)
  else Map.empty
)"

fun isParent :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> bool" where
"isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi> = (
  let
    formula_list = (formulaToList \<phi>);
    \<psi>\<^sub>1 = (FoI (Index \<J>\<^sub>1) formula_list);
    \<psi>\<^sub>2 = (FoI (Index \<J>\<^sub>2) formula_list)
  in ( case (\<psi>\<^sub>1) of
    (Atom r var_list) \<Rightarrow> False |
    (Forall x \<phi>\<^sub>1) \<Rightarrow> (
      ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1 ) \<and>
      (\<psi>\<^sub>2 = \<phi>\<^sub>1)
    ) |
    (Exists x \<phi>\<^sub>1) \<Rightarrow> (
      ((Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1 ) \<and>
      (\<psi>\<^sub>2 = \<phi>\<^sub>1)
    ) |
    (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<Rightarrow> (
      (
        ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 1 ) \<and>
        (\<psi>\<^sub>2 = \<phi>\<^sub>1)
      ) \<or> (
        ( (Index \<J>\<^sub>1) = (Index \<J>\<^sub>2) - 2 ) \<and>
        (\<psi>\<^sub>2 = \<phi>\<^sub>2)
      )
    )
  )
)"

function existSq :: "Variable set \<Rightarrow> Formula \<Rightarrow> Formula" where
"existSq vars \<phi> = (if ((card vars) > 0)
  then (
    let
      v = (SOME x. x\<in> vars);
      reduced_vars = (vars - {v})
    in (
      Exists v (existSq reduced_vars \<phi>)
    )
  )
  else \<phi>
)"
  by auto

termination existSq
  apply (relation "measures [\<lambda>(vars, \<phi>). card vars]")
  apply(auto)
  by (simp add: card_gt_0_iff some_in_eq)

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
      Some set_of_list \<Rightarrow> (
        (Funcs \<J>) = { buildValuation (atom_vars \<psi>) l | l. l \<in> set_of_list }
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
        (Funcs \<J>\<^sub>1) = {
          h \<in> (allMaps (Vars \<J>\<^sub>1) (Univ \<B>)). ( \<forall>b \<in> (Univ \<B>). h(y \<mapsto> b) \<in> (Funcs \<J>\<^sub>2))
        }
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
      variables = (Vars \<J>\<^sub>1) \<union> (Vars \<J>\<^sub>2);
      valuations = (allMaps variables (Univ \<B>))
    in (
      (Funcs \<J>) = {
        f \<in> valuations. (
          ( (projectValuation f (Vars \<J>\<^sub>1)) \<in> (Funcs \<J>\<^sub>1) ) \<and>
          ( (projectValuation f (Vars \<J>\<^sub>2)) \<in> (Funcs \<J>\<^sub>2) )
        )
      }
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
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>));
    free_var_list = ((freeVar \<psi>) - var_list)
  in (
    (f \<in> (allMaps var_list (Univ \<B>))) \<and>
    (wfStructure \<B>) \<and>
    (wfFormula \<phi> (Sig \<B>)) \<and>
    (wfJudgement \<J> \<phi> \<B>) \<and>
    (isModel f (existSq free_var_list \<psi>) \<B>)
  )
)"

inductive models :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement \<Rightarrow> bool" for \<phi> and \<B> where
(* Atom rule *)
ATR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  isAtom \<J> \<phi> \<B>;
  isDerivable \<phi> \<B> \<J>
  \<rbrakk> \<Longrightarrow> models \<phi> \<B> \<J>" (* TODO: Cambiar esta regla para que sea correcta *)
| (* Projection rule *)
PJR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (isProjection \<J> \<J>' \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>')
  ));
  isDerivable \<phi> \<B> \<J>
  \<rbrakk> \<Longrightarrow> models \<phi> \<B> \<J>" (* TODO: Cambiar esta regla para que sea correcta *)


(* ======================== Tests ======================== *)

lemma "existSq {CHR ''x''} atomFormula = (Exists (CHR ''x'') atomFormula)"
  apply (auto)
  by (simp add: Let_def)



abbreviation "atomJudgement \<equiv> myJudgement"

lemma "wfCPLInstance myFormula myStructure = True"
  by auto

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

lemma "wfCPLInstance myFormula myStructure = True"
  by auto

lemma "wfJudgement projectionBaseJudgement myFormula myStructure = True"
  apply(simp add: Let_def)
  by auto

lemma "wfJudgement projectionProjectedJudgement myFormula myStructure = True"
  apply(simp add: Let_def)
  by auto

lemma "isProjection projectionProjectedJudgement projectionBaseJudgement myFormula myStructure = True"
  apply(simp_all add: Let_def)
  apply(auto)
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
lemma "wfCPLInstance myFormula myStructure = True"
  by auto

lemma "wfJudgement joinFirstChildJudgement myFormula myStructure = True"
  apply(simp add: Let_def)
  by auto

lemma "wfJudgement joinSecondChildJudgement myFormula myStructure = True"
  apply(simp add: Let_def)
  by auto

lemma "wfJudgement joinParentJudgement myFormula myStructure = True"
  apply(simp add: Let_def)
  by auto

lemma [simp] : "myFreeVariableSet - {CHR ''y''} \<subseteq> {CHR ''x''}"
  by auto
lemma [simp] : "{CHR ''y'', CHR ''x''} = myFreeVariableSet"
  by(auto)
lemma [simp] : "x\<in>S \<Longrightarrow> S = insert x S"
  by auto
lemma [simp] : "insert (CHR ''y'') myFreeVariableSet = myFreeVariableSet"
  by auto
lemma [simp] : "mapping \<noteq> Map.empty \<Longrightarrow> (\<lambda>x. None) \<noteq> mapping" (* Note: This needs to be explicit because Map.empty \<equiv> (\<lambda>x. None) is an abbreviation *)
  by auto
(*
lemma "isJoin joinParentJudgement joinFirstChildJudgement joinSecondChildJudgement myFormula myStructure = True"
  apply(simp_all add: Let_def)
  apply(auto)
  done
*)



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
  apply(simp_all add: Let_def)
  apply(auto)
  apply(meson BEnum.simps map_upd_eqD1)
  apply(meson BEnum.simps map_upd_eqD1)
  apply(meson BEnum.simps map_upd_eqD1)
  apply(meson BEnum.simps map_upd_eqD1)
  apply(meson BEnum.simps map_upd_eqD1)
  apply(meson BEnum.simps map_upd_eqD1)
  apply(meson BEnum.simps map_upd_eqD1)
  by(meson BEnum.simps map_upd_eqD1)



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