import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum
import D5.S3.Quantum.Recovery.PetzWeightedHessianOptimum
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the attained diagonal BKM Hessian maximum. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzProjectedHessian
open _root_.D5.S3.Quantum.Recovery.PetzWeightedHessianOptimum
open _root_.D5.S3.Divergence.LogDerivTrace (logDeriv)
open _root_.D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)

namespace Reg.D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), {0}, ∅, ?_⟩
  intro h
  have he : IsGreatest ({0} : Set ℝ) 0 = IsGreatest (∅ : Set ℝ) 0 := congrFun h 0
  exact (Eq.mp he (by simp [IsGreatest, upperBounds])).1

abbrev arena : Arena where
  signature := signature
  Law A := ∀ (β : Slot → ℝ) (C f g : ℝ)
    (_hβ : ∀ i, 0 < β i) (_hC : 0 < C) (_hf : 0 < f) (_hg : 0 < g)
    (_h₀ : 0 ≤ margin β (reducedWeight (diagonalWeights β) 0 1) C f g 0)
    (_h₁ : 0 ≤ margin β (reducedWeight (diagonalWeights β) 0 1) C f g 1)
    (_hstrict : 0 < margin β (reducedWeight (diagonalWeights β) 0 1) C f g 0 +
      margin β (reducedWeight (diagonalWeights β) 0 1) C f g 1),
    let m := reducedWeight (diagonalWeights β) 0 1
    let ρ := Matrix.diagonal fun i => (β i : ℂ)
    let ratio (Z : Joint) := traceNorm (Z + offset f g) ^ 2 /
      (C + (Z * logDeriv ρ Z).trace.re / 2)
    let opt := 16 * m + (f + g) ^ 2 / C
    A.readout () () (ratio '' fibre) opt ∧
      ∀ Z ∈ fibre, ratio Z = opt ↔ Z = optimizer m C f g

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (fun _ => 1) 1 1 1 (fun _ => zero_lt_one) zero_lt_one zero_lt_one zero_lt_one
    (by norm_num [margin, reducedWeight, diagonalWeights])
    (by norm_num [margin, reducedWeight, diagonalWeights])
    (by norm_num [margin, reducedWeight, diagonalWeights])).1

def sourceRegistration : Registration arena (type_of% @diagonal_bkm_maximum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_bkm_maximum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonal_bkm_maximum) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum.diagonal_bkm_maximum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum
