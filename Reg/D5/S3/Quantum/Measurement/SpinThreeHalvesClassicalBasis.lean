import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis
import Reg.Support.DependentFamily

/-! Source-bound audit of the attained spin-3/2 basis anticoherence bound. -/

namespace Reg.D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis

open _root_.D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe basis anticoherence as the basis matrix varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 4) (Fin 4) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => basisAnticoherence U) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the universal bound, the explicit unitary basis, and its attained equality. -/
abbrev arena : Arena where
  signature := signature
  Law r := (∀ U ∈ Matrix.unitaryGroup (Fin 4) ℂ, 1 / 9 ≤ r.readout () () U) ∧
    classicalBasis ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    basisAnticoherence classicalBasis = 1 / 9

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.1 1 (one_mem (Matrix.unitaryGroup (Fin 4) ℂ))
  change (1 : ℝ) / 9 ≤ 0 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, classicalBasis, ?_⟩
  have hz : basisAnticoherence 0 = 2 := by
    have hr : reducedState (fun _ : Fin 4 => (0 : ℂ)) = 0 := by
      ext c d
      simp [reducedState, dicke]
    norm_num [basisAnticoherence, anticoherence, hr]
  change basisAnticoherence 0 ≠ basisAnticoherence classicalBasis
  rw [hz, result.2.2]
  norm_num

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ U => basisAnticoherence U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis
    definition := some {
      owner := `D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis
      name := `D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis
