import D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (VertexModule transition stationaryTransition)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction
noncomputable section

abbrev signature : Signature where
  Params := Nat
  State q := VertexModule Sign q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := VertexModule Sign q
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature (fun _ _ v => v) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (i : Fin q),
    (r.readout () q (resetOddVector q) i).coeff 1 = (-1 : ℤ) ^ i.val

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hz := h 1 0
  change (0 : ℤ) = (-1 : ℤ) ^ 0 at hz
  norm_num at hz

def coefficientRegistration : Registration arena
    (∀ (q : ℕ) (i : Fin q), (resetOddVector q i).coeff 1 = (-1 : ℤ) ^ i.val) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨resetOddVector_coeff_one, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, resetOddVector 1, 0, ?_⟩
    intro h
    have hz := congrArg (fun v : VertexModule Sign 1 => (v 0).coeff 1) h
    change (resetOddVector 1 0).coeff 1 = (0 : MonoidAlgebra ℤ Sign).coeff 1 at hz
    rw [resetOddVector_coeff_one] at hz
    simp at hz

noncomputable def registration_coefficient : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.resetOddVector_coeff_one)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction.coefficient_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction.coefficientRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨coefficientRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "fn"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev thetaStageSignature : Signature where
  Params := ℕ × ℕ
  State p := VertexModule Sign p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := VertexModule Sign p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev thetaStageActual : Realization thetaStageSignature :=
  realize thetaStageSignature (fun _ _ v => v) (fun e => nomatch e)
abbrev thetaStageBad : Realization thetaStageSignature :=
  realize thetaStageSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev thetaStageArena : Arena where
  signature := thetaStageSignature
  Law r := ∀ (q n : ℕ) (v : VertexModule Sign q),
    resetTheta q
      (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
        (stationaryTransition (transition (resetMatrix q))) n (r.readout () (q, n) v)) =
    Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) n
      (transition (resetMatrix q) v)

private theorem theta_stage_bad_law : ¬ thetaStageArena.Law thetaStageBad := by
  intro h
  have hz := h 1 0 (resetOddVector 1)
  change resetTheta 1
      (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign 1)
        (stationaryTransition (transition (resetMatrix 1))) 0 0) =
    Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign 1)
      (stationaryTransition (transition (resetMatrix 1))) 0
      (transition (resetMatrix 1) (resetOddVector 1)) at hz
  rw [reset_odd_transition 1 (by decide) (by decide), map_zero, map_zero, map_neg] at hz
  change 0 = -resetOddClass 1 at hz
  exact resetOddClass_ne_zero 1 (by decide) (by decide) (neg_eq_zero.mp hz.symm)

def thetaStageRegistration : Registration thetaStageArena
    (∀ (q n : ℕ) (v : VertexModule Sign q),
      resetTheta q
        (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
          (stationaryTransition (transition (resetMatrix q))) n v) =
      Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
        (stationaryTransition (transition (resetMatrix q))) n
        (transition (resetMatrix q) v)) where
  actual := thetaStageActual
  bridge := Iff.rfl
  variation := ⟨resetTheta_apply_of, thetaStageBad, theta_stage_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨thetaStageBad, ?_, rfl, theta_stage_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨q, v, w, h⟩ := coefficientRegistration.dependence ()
    exact ⟨(q, 0), v, w, h⟩

noncomputable def registration_resetTheta_apply_of : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.resetTheta_apply_of)
    (Realization thetaStageSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction.theta_stage_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction.thetaStageRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨thetaStageArena⟩
  objectArena := .source ⟨thetaStageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source thetaStageArena ⟨thetaStageRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thetaStageSignature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction
