import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability
open _root_.D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix

namespace Reg.D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ lam c => 2 * c - lam ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=  ∀ (lam c : ℝ) (_hc : lam ^ 2 ≤ c),
    let d := c - lam ^ 2
    let S := R.readout () lam c
    (S < 1 ↔ ∀ K δ, bounded K δ → stable c d K δ) ∧
    (S < 1 ↔ stable c d 2 fixedDelay) ∧
    (∀ K, 2 ≤ K →
      (S < 1 ↔ ∀ δ, bounded K δ → stable c d K δ) ∧
      (S < 1 ↔ ∀ δ, remotePositive K δ → stable c d K δ)) ∧
    (S = 1 → ∀ K, 2 ≤ K → ∃ y : History K → ℝ,
      (∀ t : ℕ, (asyncMatrix (family c d) fixedDelay K ^ (t + 4)).mulVec y =
        (asyncMatrix (family c d) fixedDelay K ^ t).mulVec y) ∧
      (∀ m : ℕ, ((asyncMatrix (family c d) fixedDelay K ^ (4 * m)).mulVec y)
        (0, ⟨0, 0⟩) = 1)) ∧
    (1 < S → ∀ K, 2 ≤ K → ∃ r : ℝ, 1 < r ∧ ∃ y : History K → ℝ,
      ∀ m : ℕ, ((asyncMatrix (family c d) fixedDelay K ^ (4 * m)).mulVec y)
        (0, ⟨0, 0⟩) = r ^ (4 * m))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have htrue := whole_theorem_three_one (1/2) (1/4)
    (by norm_num)
  have hs := htrue.1.mp (by norm_num)
  have hbad := (law (1/2) (1/4) (by norm_num)).1.mpr hs
  change (1 : ℝ) < 1 at hbad
  exact (lt_irrefl 1) hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1/2 : ℝ), (1/2 : ℝ)^2, (1/2 : ℝ)^2 + 1, ?_⟩
  change 2 * (1/2 : ℝ)^2 - (1/2 : ℝ)^2 ≠
    2 * ((1/2 : ℝ)^2 + 1) - (1/2 : ℝ)^2
  norm_num

def realization : Registration arena (type_of% (@whole_theorem_three_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_theorem_three_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@whole_theorem_three_one) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability.whole_theorem_three_one.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ lam c => 2 * c - lam ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability
