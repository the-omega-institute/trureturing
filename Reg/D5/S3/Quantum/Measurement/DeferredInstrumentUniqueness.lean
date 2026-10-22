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
  Params := Σ d : ℕ, Matrix.unitaryGroup (Fin d) ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p state => sMax p.1 state)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (d : ℕ) (hd : 2 ≤ d),
      ∀ (U : Matrix.unitaryGroup (Fin d) ℂ),
      ∀ (t : ℝ), -1 / ((d : ℝ) ^ 2 - 1) ≤ t → t ≤ 1 →
      ∀ (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ),
        ((∀ x, (J x).IsCompletelyPositive) ∧
          (∑ x, J x = It t) ∧
          (∀ x ρ, Matrix.trace (J x ρ) =
            Matrix.trace (ρ * Qs U
              (R.readout () ⟨d, U⟩ t) x))) ↔
        (∀ x, J x = Itilde U t x))

theorem actual_law : arena.Law actual := by
  intro d hd U t htl htu J
  simpa [actual, realize] using
    (show ((∀ x, (J x).IsCompletelyPositive) ∧
        (∑ x, J x = It t) ∧
        (∀ x ρ, Matrix.trace (J x ρ) =
          Matrix.trace (ρ * Qs U (sMax d t) x))) ↔
      (∀ x, J x = Itilde U t x) from result d hd U t htl htu J)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hiff := h 2 (by norm_num) (1 : Matrix.unitaryGroup (Fin 2) ℂ) 0
    (by norm_num) (by norm_num) (Itilde (1 : Matrix.unitaryGroup (Fin 2) ℂ) 0)
  have htrace := (hiff.mpr (by intro x; rfl)).2.2 0
    (Q (1 : Matrix.unitaryGroup (Fin 2) ℂ) 0)
  norm_num [rejected, realize, Q, Qs, Itilde, a2, b, sMax, Matrix.trace,
    Matrix.one_apply] at htrace

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let U : Matrix.unitaryGroup (Fin 2) ℂ := 1
  refine ⟨⟨2, U⟩, 0, 1, ?_⟩
  change sMax 2 0 ≠ sMax 2 1
  norm_num [sMax]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    constructor
    · intro h
      intro d hd U t htl htu J
      simpa [actual, realize] using h d hd U t htl htu J
    · intro h
      intro d hd U t htl htu J
      simpa [actual, realize] using h d hd U t htl htu J
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
    (realize signature (fun _ p state => sMax p.1 state)
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
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg", "body", "body", "arg", "arg", "arg",
        "fn", "arg"]
      stateBinder := 3
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
