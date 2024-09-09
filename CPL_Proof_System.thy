theory "CPL_Proof_System"
  imports Main "CPL_Syntax" "CPL_Semantic"
begin

(* ==================== Proof System ==================== *)

(* ======================== Type Definitions ======================== *)

type_synonym 'a Valuation = "Variable \<rightharpoonup> 'a" \<comment> \<open> Represented by f \<close>
datatype 'a Judgement =  Judgement (Index: "nat") (Vars:  "Variable set") (Funcs:  "'a Valuation set") \<comment> \<open> Represented by \<J>, and internally by index \<V> \<F> \<close>

abbreviation "e \<equiv> Map.empty"
abbreviation "NullJudgement \<equiv> (Judgement 1 {} {})"
abbreviation "EmptyJudgement \<equiv> (Judgement 1 {} {e})"

(* ================= Auxiliary Functions ================= *)

fun isParent :: "'a Judgement \<Rightarrow> 'a Judgement \<Rightarrow> Formula list \<Rightarrow> ParentIndex list \<Rightarrow> bool" where
"isParent \<J>\<^sub>1 \<J>\<^sub>2 \<phi>\<^sub>L P\<^sub>L = (
  let
    \<psi>\<^sub>1 = (FoI (Index \<J>\<^sub>1) \<phi>\<^sub>L);
    \<psi>\<^sub>2 = (FoI (Index \<J>\<^sub>2) \<phi>\<^sub>L)
  in ( case (\<psi>\<^sub>1) of
    (Atom r var_list) \<Rightarrow> False |
    (Forall x \<phi>\<^sub>1) \<Rightarrow> ( ((Index \<J>\<^sub>1) = (P\<^sub>L ! (Index \<J>\<^sub>2 - 1)) ) \<and> (\<psi>\<^sub>2 = \<phi>\<^sub>1) ) |
    (Exists x \<phi>\<^sub>1) \<Rightarrow> ( ((Index \<J>\<^sub>1) = (P\<^sub>L ! (Index \<J>\<^sub>2 - 1)) ) \<and> (\<psi>\<^sub>2 = \<phi>\<^sub>1) ) |
    (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<Rightarrow> (
      ( (Index \<J>\<^sub>1) = (P\<^sub>L ! (Index \<J>\<^sub>2 - 1)) ) \<and> ( (\<psi>\<^sub>2 = \<phi>\<^sub>1) \<or> (\<psi>\<^sub>2 = \<phi>\<^sub>2) )
    )
  )
)"

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

fun mapValuation :: "'a Valuation \<Rightarrow> Variable list \<Rightarrow> 'a list" where \<comment> \<open> TODO: Explain this with more detail \<close>
"mapValuation f vs = (if ((set vs) \<subseteq> (dom f))
  then [the (f v). v \<leftarrow> vs]
  else []
)"

(* ======================== Well-Formedness Functions ======================== *)

fun wfJudgement :: "'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"wfJudgement \<J> \<phi> \<B> = (let
    (\<phi>\<^sub>L, P\<^sub>L) = buildFormulaParentList \<phi>;
    judgement_index = (Index \<J>);
    judgement_free_vars = (Vars \<J>);
    judgement_valuations = (Funcs \<J>);
    structure_domain = (Univ \<B>)
  in (
    ( wfCPLInstance \<phi> \<B> ) \<and>
    ( judgement_index \<in> (setOfIndex P\<^sub>L) ) \<and>
    ( judgement_free_vars \<subseteq> (freeVar (FoI judgement_index \<phi>\<^sub>L)) ) \<and>
    ( \<forall>f \<in> judgement_valuations. ((dom f) = judgement_free_vars) )  \<and>
    ( \<forall>f \<in> judgement_valuations. ((ran f) \<subseteq> structure_domain) )
  )
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

\<comment> \<open>The inductive predicate isDerivable decides if a Judgement \<J> is derivable using the proof system rules \<close>
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

print_theorems

(* ======================== Tests ======================== *)

abbreviation "myValuationSet::(BEnum Valuation set) \<equiv> {
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> A],
  [CHR ''x'' \<mapsto> A, CHR ''y'' \<mapsto> C],
  [CHR ''x'' \<mapsto> B, CHR ''y'' \<mapsto> A]
}"
abbreviation "myFreeVariableSet::(Variable set) \<equiv> {CHR ''x'', CHR ''y''}"
abbreviation "myJudgement::(BEnum Judgement) \<equiv> (Judgement 6 myFreeVariableSet myValuationSet)"

lemma [simp] : "wfJudgement myJudgement myFormula myStructure = True"
  by(auto simp add: Let_def)



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



abbreviation "exampleFormula::Formula \<equiv> (Forall (CHR ''x'') (Exists (CHR ''y'') (And (Exists (CHR ''z'') (Atom (CHR ''E'') [CHR ''z'', CHR ''y''])) (Atom (CHR ''R'') [CHR ''y'', CHR ''x'']))))"
abbreviation "exampleUniverse::(BEnum set) \<equiv> {A,B,C}"
abbreviation "exampleSignature::(Signature) \<equiv> [CHR ''E'' \<mapsto> 2, CHR ''R'' \<mapsto> 2]"
abbreviation "exampleInterpretation::(BEnum Interpretation) \<equiv> [CHR ''E'' \<mapsto> {[A,B],[C,A]}, CHR ''R'' \<mapsto> {[A,A],[A,B],[B,C]}]"
abbreviation "exampleStructure::(BEnum Structure) \<equiv> (Structure exampleSignature exampleUniverse exampleInterpretation)"

lemma [simp] : "(wfStructure exampleStructure) = True"
  by (auto)

lemma [simp] : "((ran e) \<subseteq> (Univ exampleStructure)) = True"
  by (auto)

lemma [simp] : "(wfFormula exampleFormula (Sig exampleStructure)) = True"
  by (auto)

lemma [simp] : "((freeVar exampleFormula) \<subseteq> (dom e)) = True"
  by (auto)

lemma "(isModel exampleStructure e exampleFormula) = True"
  by (auto)



abbreviation "exampleFormulaIncomplete::Formula \<equiv> (And (Forall (CHR ''x'') (Atom (CHR ''Q'') [CHR ''x''])) (Exists (CHR ''y'') (Atom (CHR ''R'') [CHR ''y''])))"
abbreviation "exampleUniverseIncomplete::(BEnum set) \<equiv> {A,B}"
abbreviation "exampleSignatureIncomplete::(Signature) \<equiv> [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1]"
abbreviation "exampleInterpretationIncomplete::(BEnum Interpretation) \<equiv> [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}]"
abbreviation "exampleStructureIncomplete::(BEnum Structure) \<equiv> (Structure exampleSignatureIncomplete exampleUniverseIncomplete exampleInterpretationIncomplete)"

lemma [simp] : "(wfStructure exampleStructureIncomplete) = True"
  by (auto)

lemma [simp] : "((ran e) \<subseteq> (Univ exampleStructureIncomplete)) = True"
  by (auto)

lemma [simp] : "(wfFormula exampleFormulaIncomplete (Sig exampleStructureIncomplete)) = True"
  by (auto)

lemma [simp] : "((freeVar exampleFormulaIncomplete) \<subseteq> (dom e)) = True"
  by (auto)

lemma "(isModel exampleStructureIncomplete e exampleFormulaIncomplete) = False"
  by (auto)



abbreviation "exampleAtomJudgementIncomplete::(BEnum Judgement) \<equiv> (Judgement 3 {CHR ''x''} {[CHR ''x'' \<mapsto> B]})"
abbreviation "exampleAtomJudgementIncomplete2::(BEnum Judgement) \<equiv> (Judgement 5 {CHR ''y''} {[CHR ''y'' \<mapsto> A]})"
abbreviation "exampleProjectionJudgementIncomplete::(BEnum Judgement) \<equiv> (Judgement 5 {} {e})"
abbreviation "exampleUpwardJudgementIncomplete::(BEnum Judgement) \<equiv> (Judgement 4 {} {e})"
abbreviation "exampleForallElimJudgementIncomplete::(BEnum Judgement) \<equiv> (Judgement 2 {} {})"
abbreviation "exampleUpwardJudgementIncomplete2::(BEnum Judgement) \<equiv> (Judgement 1 {} {})"

lemma [simp] : "(wfCPLInstance exampleFormulaIncomplete exampleStructureIncomplete) = True"
  by auto

lemma example_atom_judgement_incomplete_is_derivable [simp] : "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete exampleAtomJudgementIncomplete) = True"
  by (simp_all add: isDerivable.ATR)

lemma example_atom_judgement_incomplete_2_is_derivable [simp] : "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete exampleAtomJudgementIncomplete2) = True"
  by (simp_all add: isDerivable.ATR)

lemma example_atom_judgement_incomplete_2_is_projection [simp] : "(isProjection exampleProjectionJudgementIncomplete exampleAtomJudgementIncomplete2 exampleFormulaIncomplete exampleStructureIncomplete) = True"
  by auto
lemma example_projection_judgement_incomplete_is_derivable [simp] : shows "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete exampleProjectionJudgementIncomplete) = True"
proof -
  have "(wfCPLInstance exampleFormulaIncomplete exampleStructureIncomplete)" by auto
  have "(wfJudgement exampleProjectionJudgementIncomplete exampleFormulaIncomplete exampleStructureIncomplete)" by auto
  obtain \<J> where "\<J> = exampleAtomJudgementIncomplete2" by auto
  have "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete \<J>)" using \<open>\<J> = Judgement 5 {CHR ''y''} {[CHR ''y'' \<mapsto> A]}\<close> example_atom_judgement_incomplete_2_is_derivable by blast
  have "(isProjection exampleProjectionJudgementIncomplete \<J> exampleFormulaIncomplete exampleStructureIncomplete)" using \<open>\<J> = Judgement 5 {CHR ''y''} {[CHR ''y'' \<mapsto> A]}\<close> example_atom_judgement_incomplete_2_is_projection by blast
  have "(\<exists>\<J>'. (
    (isDerivable exampleFormulaIncomplete exampleStructureIncomplete \<J>') \<and>
    (isProjection exampleProjectionJudgementIncomplete \<J>' exampleFormulaIncomplete exampleStructureIncomplete) 
  ))" using example_atom_judgement_incomplete_2_is_derivable example_atom_judgement_incomplete_2_is_projection by blast
  thus ?thesis using PJR \<open>wfCPLInstance exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}])\<close> example_atom_judgement_incomplete_2_is_derivable example_atom_judgement_incomplete_2_is_projection by blast
qed

lemma example_projection_judgement_incomplete_is_upward_flow [simp] : "(isUpwardFlow exampleUpwardJudgementIncomplete exampleProjectionJudgementIncomplete exampleFormulaIncomplete exampleStructureIncomplete) = True"
  by (auto)
lemma [simp] : shows "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete exampleUpwardJudgementIncomplete) = True"
proof -
  have "(wfCPLInstance exampleFormulaIncomplete exampleStructureIncomplete)" by auto
  have "(wfJudgement exampleUpwardJudgementIncomplete exampleFormulaIncomplete exampleStructureIncomplete)" by auto
  obtain \<J> where "\<J> = exampleProjectionJudgementIncomplete" by auto
  have "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete \<J>)" using \<open>\<J> = Judgement 5 {} {\<lambda>x. None}\<close> example_projection_judgement_incomplete_is_derivable by fastforce
  have "(isUpwardFlow exampleUpwardJudgementIncomplete \<J> exampleFormulaIncomplete exampleStructureIncomplete)" using \<open>\<J> = Judgement 5 {} {\<lambda>x. None}\<close> example_projection_judgement_incomplete_is_upward_flow by blast
  have "(\<exists>\<J>'. (
    (isDerivable exampleFormulaIncomplete exampleStructureIncomplete \<J>') \<and>
    (isUpwardFlow exampleUpwardJudgementIncomplete \<J>' exampleFormulaIncomplete exampleStructureIncomplete) 
  ))" using example_projection_judgement_incomplete_is_derivable example_projection_judgement_incomplete_is_upward_flow by blast
  thus ?thesis using UFR \<open>wfCPLInstance exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}])\<close> \<open>wfJudgement (Judgement 4 {} {\<lambda>x. None}) exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}])\<close> by blast
qed

lemma example_atom_judgement_incomplete_is_dual_projection [simp] : "(isDualProjection exampleForallElimJudgementIncomplete exampleAtomJudgementIncomplete exampleFormulaIncomplete exampleStructureIncomplete) = True"
  by (auto)
lemma example_for_all_elim_judgemente_incomplete_is_derivable [simp] : shows "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete exampleForallElimJudgementIncomplete) = True"
proof -
  have "(wfCPLInstance exampleFormulaIncomplete exampleStructureIncomplete)" by auto
  have "(wfJudgement exampleForallElimJudgementIncomplete exampleFormulaIncomplete exampleStructureIncomplete)" by auto
  obtain \<J> where "\<J> = exampleAtomJudgementIncomplete" by auto
  have "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete \<J>)" using \<open>\<J> = Judgement 3 {CHR ''x''} {[CHR ''x'' \<mapsto> B]}\<close> example_atom_judgement_incomplete_is_derivable by blast
  have "(isDualProjection exampleForallElimJudgementIncomplete \<J> exampleFormulaIncomplete exampleStructureIncomplete)" using \<open>\<J> = Judgement 3 {CHR ''x''} {[CHR ''x'' \<mapsto> B]}\<close> example_atom_judgement_incomplete_is_dual_projection by blast
  have "(\<exists>\<J>'. (
    (isDerivable exampleFormulaIncomplete exampleStructureIncomplete \<J>') \<and>
    (isDualProjection exampleForallElimJudgementIncomplete \<J>' exampleFormulaIncomplete exampleStructureIncomplete) 
  ))" using example_atom_judgement_incomplete_is_derivable example_atom_judgement_incomplete_is_dual_projection by blast
  thus ?thesis using FER \<open>wfCPLInstance exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}])\<close> \<open>wfJudgement exampleForallElimJudgementIncomplete exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}])\<close> by blast
qed

lemma example_for_all_elim_judgemente_incomplete_is_upward_flow [simp] : "(isUpwardFlow exampleUpwardJudgementIncomplete2 exampleForallElimJudgementIncomplete exampleFormulaIncomplete exampleStructureIncomplete) = True"
  by (auto)
lemma [simp] : shows "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete exampleUpwardJudgementIncomplete2) = True"
proof -
  have "(wfCPLInstance exampleFormulaIncomplete exampleStructureIncomplete)" by auto
  have "(wfJudgement exampleUpwardJudgementIncomplete2 exampleFormulaIncomplete exampleStructureIncomplete)" by auto
  obtain \<J> where "\<J> = exampleForallElimJudgementIncomplete" by auto
  have "(isDerivable exampleFormulaIncomplete exampleStructureIncomplete \<J>)" using \<open>\<J> = exampleForallElimJudgementIncomplete\<close> example_for_all_elim_judgemente_incomplete_is_derivable by blast
  have "(isUpwardFlow exampleUpwardJudgementIncomplete2 \<J> exampleFormulaIncomplete exampleStructureIncomplete)" using \<open>\<J> = exampleForallElimJudgementIncomplete\<close> example_for_all_elim_judgemente_incomplete_is_upward_flow by blast
  have "(\<exists>\<J>'. (
    (isDerivable exampleFormulaIncomplete exampleStructureIncomplete \<J>') \<and>
    (isUpwardFlow exampleUpwardJudgementIncomplete2 \<J>' exampleFormulaIncomplete exampleStructureIncomplete) 
  ))" using \<open>isDerivable exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}]) \<J>\<close> \<open>isUpwardFlow exampleUpwardJudgementIncomplete2 \<J> exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}])\<close> by blast
  thus ?thesis using UFR \<open>wfCPLInstance exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}])\<close> \<open>wfJudgement exampleUpwardJudgementIncomplete2 exampleFormulaIncomplete (Structure [CHR ''R'' \<mapsto> 1, CHR ''Q'' \<mapsto> 1] exampleUniverseIncomplete [CHR ''R'' \<mapsto> {[A]}, CHR ''Q'' \<mapsto> {[B]}])\<close> by blast
qed

end