import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
import Reg.Support.DependentFamily

/-! Source-bound audit of the deferred instrument uniqueness settlement. -/

namespace Reg.D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
open _root_.D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Σ d : ℕ, Matrix.unitaryGroup (Fin d) ℂ × ℝ
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p state => if state then sMax p.1 p.2.2 else 0)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (d : ℕ), 2 ≤ d →
      ∀ (U : Matrix.unitaryGroup (Fin d) ℂ),
      ∀ (t : ℝ), -1 / ((d : ℝ) ^ 2 - 1) ≤ t → t ≤ 1 →
      ∀ (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ),
        ((∀ x, (J x).IsCompletelyPositive) ∧
          (∑ x, J x = It t) ∧
          (∀ x ρ, Matrix.trace (J x ρ) =
            Matrix.trace (ρ * Qs U (R.readout () ⟨d, (U, t)⟩ true) x))) ↔
        (∀ x, J x = Itilde U t x)) ∧
    (∀ (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (t : ℝ),
      R.readout () ⟨d, (U, t)⟩ true = sMax d t)

theorem actual_law : arena.Law actual := by
  constructor
  · intro d hd U t htl htu J
    simpa [actual, realize] using
      (show ((∀ x, (J x).IsCompletelyPositive) ∧
          (∑ x, J x = It t) ∧
          (∀ x ρ, Matrix.trace (J x ρ) =
            Matrix.trace (ρ * Qs U (sMax d t) x))) ↔
        (∀ x, J x = Itilde U t x) from result d hd U t htl htu J)
  · intro d U t
    rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.2 2 (1 : Matrix.unitaryGroup (Fin 2) ℂ) 0
  change (0 : ℝ) = sMax 2 0 at hbad
  norm_num [sMax] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let U : Matrix.unitaryGroup (Fin 2) ℂ := 1
  refine ⟨⟨2, (U, 0)⟩, true, false, ?_⟩
  change sMax 2 0 ≠ 0
  norm_num [sMax]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro d hd U t htl htu J
        simpa [actual, realize] using h d hd U t htl htu J
      · intro d U t
        rfl
    · intro h
      intro d hd U t htl htu J
      simpa [actual, realize] using (h.1 d hd U t htl htu J)
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness.source_registration
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
    (realize signature (fun _ p state => if state then sMax p.1 p.2.2 else 0)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
    definition := some {
      owner := `D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
      name := `D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness.claim
      path := #[] }
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #[]
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
end Reg.D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
