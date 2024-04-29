theory "CPL_Soundness"
  imports Main "CPL_Syntax" "CPL_Semantic" "CPL_Proof_System"
begin

function allMaps :: "Variable set \<Rightarrow> 'a set \<Rightarrow> 'a Valuation set" where \<comment> \<open> TODO: Find a way to remove allMaps \<close>
"((card keys) = 0) \<and> ((card values) = 0) \<Longrightarrow> allMaps keys values = {}" |
"((card keys) > 0) \<and> ((card values) = 0) \<Longrightarrow> allMaps keys values = {}" |
"((card keys) = 0) \<and> ((card values) > 0) \<Longrightarrow> allMaps keys values = { Map.empty }" |
"((card keys) > 0) \<and> ((card values) > 0) \<Longrightarrow> allMaps keys values = (let
      k = (SOME x. x \<in> keys)
    in (
      {
        m(k \<mapsto> v) | m v. v \<in> values \<and> m \<in> (allMaps (keys - {k}) values)
      }
    )
)"
  apply auto
  by (metis bot_nat_0.not_eq_extremum card_eq_0_iff finite)
termination allMaps
  apply (relation "measures [\<lambda>(keys, _). card keys]")
  apply(auto)
  by (simp add: card_gt_0_iff some_in_eq)


function existSq :: "Variable set \<Rightarrow> Formula \<Rightarrow> Formula" where
"(card vars) = 0 \<Longrightarrow> existSq vars \<phi> = \<phi>" |
"(card vars) > 0 \<Longrightarrow> existSq vars \<phi> = (
    let
      v = (SOME x. x\<in> vars);
      reduced_vars = (vars - {v})
    in (
      Exists v (existSq reduced_vars \<phi>)
    )
  )"
  apply auto
  by (metis card_gt_0_iff finite)
termination existSq
  apply (relation "measures [\<lambda>(vars, _). card vars]")
  by (auto simp add: card_gt_0_iff some_in_eq)


fun isValuationModel :: "'a Valuation \<Rightarrow> 'a Judgement \<Rightarrow> Formula \<Rightarrow> 'a Structure \<Rightarrow> bool" where
"isValuationModel f \<J> \<phi> \<B> = (
  let
    var_list = (Vars \<J>);
    \<psi> = (FoI (Index \<J>) (formulaToList \<phi>));
    free_var_list = ((freeVar \<psi>) - var_list)
  in (
    (f \<in> (allMaps var_list (Univ \<B>))) \<and> \<comment> \<open> TODO: Find a way to remove allMaps \<close>
    (wfStructure \<B>) \<and>
    (wfFormula \<phi> (Sig \<B>)) \<and>
    (wfJudgement \<J> \<phi> \<B>) \<and>
    (isModel f (existSq free_var_list \<psi>) \<B>)
  )
)"

(*
inductive models :: "Formula \<Rightarrow> 'a Structure \<Rightarrow> 'a Judgement \<Rightarrow> bool" for \<phi> and \<B> where
ATR: "\<lbrakk> \<comment> \<open>  Atom rule  \<close>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  isAtom \<J> \<phi> \<B>;
  isDerivable \<phi> \<B> \<J>
  \<rbrakk> \<Longrightarrow> models \<phi> \<B> \<J>" \<comment> \<open>  TODO: Cambiar esta regla para que sea correcta  \<close>
| \<comment> \<open>  Projection rule  \<close>
PJR: "\<lbrakk>
  wfCPLInstance \<phi> \<B>;
  wfJudgement \<J> \<phi> \<B>;
  (\<exists>\<J>'. (
    (isProjection \<J> \<J>' \<phi> \<B>) \<and>
    (isDerivable \<phi> \<B> \<J>')
  ));
  isDerivable \<phi> \<B> \<J>
  \<rbrakk> \<Longrightarrow> models \<phi> \<B> \<J>" \<comment> \<open>  TODO: Cambiar esta regla para que sea correcta  \<close>
*)

(* ======================== Tests ======================== *)

lemma "existSq {CHR ''x''} atomFormula = (Exists (CHR ''x'') atomFormula)"
  by (auto simp add: Let_def)


end