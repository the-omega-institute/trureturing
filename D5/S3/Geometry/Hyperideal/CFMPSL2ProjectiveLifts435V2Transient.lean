import D5.S3.Geometry.Hyperideal.SL2F5Involution
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
import Lean.Util.CollectAxioms

set_option autoImplicit false

open scoped MatrixGroups

namespace CFMPSL2F5ProjectiveInvolutionLiftsExactCheck

local notation "G" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)
local notation "P" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)
local notation "q" => (QuotientGroup.mk' (Subgroup.center G) : G →* P)

example (Y : G) (hprojective_square : (q Y) ^ 2 = 1)
    (hprojective_nontrivial : q Y ≠ 1) :
    Y ^ 2 = -1 ∧ Y ^ 4 = 1 ∧ orderOf Y = 4 := by
  let hwhole : Y ^ 2 = -1 ∧ Y ^ 4 = 1 ∧ orderOf Y = 4 := by
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hcenter : Y ^ 2 ∈ Subgroup.center G := by
      apply (QuotientGroup.eq_one_iff (Y ^ 2)).mp
      change q (Y ^ 2) = 1
      rw [map_pow, hprojective_square]
    obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
    have hr_two : r ^ 2 = 1 := by simpa using hr
    have hsquare_sign : Y ^ 2 = 1 ∨ Y ^ 2 = -1 := by
      rcases sq_eq_one_iff.mp hr_two with hr_one | hr_negative
      · left
        apply Subtype.ext
        simpa only [hr_one, map_one, Matrix.SpecialLinearGroup.coe_one]
          using hscalar.symm
      · right
        apply Subtype.ext
        simpa only [hr_negative, map_neg, map_one,
          Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
          using hscalar.symm
    have hnegative_center : (-1 : G) ∈ Subgroup.center G := by
      apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
      refine ⟨(-1 : ZMod 5), ?_, ?_⟩
      · norm_num
      · simp only [map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_one]
    have hnegative_projective : q (-1 : G) = 1 :=
      (QuotientGroup.eq_one_iff (-1 : G)).mpr hnegative_center
    have hsquare_not_one : Y ^ 2 ≠ 1 := by
      intro hsquare
      rcases D5.S3.Geometry.Hyperideal.SL2F5Involution.sl2_zmod5_square_one_eq_one_or_neg_one
        Y hsquare with hY | hY
      · apply hprojective_nontrivial
        rw [hY, map_one]
      · apply hprojective_nontrivial
        rw [hY]
        exact hnegative_projective
    have hsquare_negative : Y ^ 2 = -1 := hsquare_sign.resolve_left hsquare_not_one
    have hfour : Y ^ 4 = 1 := by
      calc
        Y ^ 4 = (Y ^ 2) ^ 2 := by rw [← pow_mul]
        _ = (-1 : G) ^ 2 := by rw [hsquare_negative]
        _ = 1 := by simp [pow_two]
    have horder : orderOf Y = 4 :=
      orderOf_eq_prime_pow (p := 2) (n := 1) hsquare_not_one hfour
    exact ⟨hsquare_negative, hfour, horder⟩
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "AXIOMS49: hwhole must have a visible let value"
      let raw ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let wholeType ← Lean.instantiateMVars whole.type
      if raw.hasMVar || target.hasMVar || wholeType.hasMVar then
        Lean.throwError "AXIOMS49: unresolved expression or universe metavariables"
      unless ← Lean.Meta.isDefEq wholeType target do
        Lean.throwError "AXIOMS49: hwhole type differs from the original conclusion"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType raw) target do
        Lean.throwError "AXIOMS49: whole proof has the wrong conclusion"
      let y ← Lean.Meta.getFVarFromUserName `Y
      let hsquare ← Lean.Meta.getFVarFromUserName `hprojective_square
      let hnontrivial ← Lean.Meta.getFVarFromUserName `hprojective_nontrivial
      let params := #[y, hsquare, hnontrivial]
      for param in params do
        let decl ← Lean.Meta.getFVarLocalDecl param
        if (decl.value? (allowNondep := true)).isSome then
          Lean.throwError "AXIOMS49: original parameters must remain assumptions"
      let proof ← Lean.instantiateMVars (← Lean.Meta.mkLambdaFVars params raw)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let expectedType ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars params target)
      if proof.hasMVar || proofType.hasMVar || expectedType.hasMVar then
        Lean.throwError "AXIOMS49: closed proof or type still has metavariables"
      if proof.hasFVar || proofType.hasFVar || expectedType.hasFVar then
        Lean.throwError "AXIOMS49: proof has assumptions beyond the original parameters"
      if proof.hasLooseBVars || proofType.hasLooseBVars || expectedType.hasLooseBVars then
        Lean.throwError "AXIOMS49: closed proof or type has loose bound variables"
      unless ← Lean.Meta.isDefEq proofType expectedType do
        Lean.throwError "AXIOMS49: closed proof does not have the original full telescope"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do
        constants := constants.insert constant
      for constant in proofType.getUsedConstants do
        constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"AXIOMS49: constant absent from checked environment: {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"AXIOMS49: disallowed axiom dependency: {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_SL2_PROJECTIVE_LIFTS435_AXIOMS49 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count=3"
  exact hwhole

end CFMPSL2F5ProjectiveInvolutionLiftsExactCheck
