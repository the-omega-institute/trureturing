import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuParityCoherence

/-! Source-bound readouts for the directed interference, projection defect and attained maximum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Kronecker LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuPhysicalHighHigh (Mat F)
open _root_.D5.S3.Quantum.Semigroups.WuParityCoherence

namespace Reg.D5.S3.Quantum.Semigroups.WuParityCoherence

private abbrev equalitySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def equalityActual : Realization equalitySignature :=
  realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

private def equalityRejected : Realization equalitySignature :=
  realize equalitySignature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private theorem equalityDependence : ObservationalDependence equalitySignature equalityActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : ℝ) ≠ 0) (Eq.mp (congrFun h 0) rfl)

namespace Interference

private abbrev arena : Arena where
  signature := equalitySignature
  Law R := ∀ (r : ℝ) (M : Mat) (_hM : M.IsHermitian),
    let γ : ℝ := 9 / (4 * (1 + r ^ 3))
    phiInterference M = 2 * (rowDet (B (M ^ 2) 0) (B M 1)).re ∧
    psiInterference M = 2 * (rowDet (B M 0) (B (M ^ 2) 1)).re ∧
    R.readout () ()
      (-γ * r ^ 2 * phiInterference M - γ * r * psiInterference M)
      (-2 * γ * r *
        ((r : ℂ) * rowDet (B (M ^ 2) 0) (B M 1) + rowDet (B M 0) (B (M ^ 2) 1)).re)

private theorem rejected_law : ¬ arena.Law equalityRejected := by
  intro h
  have hzero : (0 : Mat).IsHermitian := Matrix.isHermitian_zero
  exact (h 1 0 hzero).2.2 (signed_interference 1 0 hzero).2.2

def family : Registration arena (type_of% @signed_interference) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@signed_interference, equalityRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equalityActual equalityRejected rejected_law
  dependence := equalityDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signed_interference) (Realization equalitySignature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuParityCoherence.signed_interference.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuParityCoherence.Interference.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuParityCoherence
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Three binders and the coefficient let precede the two right conjuncts.
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Interference

namespace ProjectionDefect

private abbrev arena : Arena where
  signature := equalitySignature
  Law R := ∀ (Q : Mat) (_hQ : Q.IsHermitian) (_hidem : Q * Q = Q) (_htrace : Q.trace = 2),
    R.readout () ()
      (3 - occupationDifference Q ^ 2 - carTrace Q Q)
      (3 * ((A Q).trace.re - 1) ^ 2 + 4 * Complex.normSq (A Q 0 1) +
        2 * Complex.normSq (B Q 0 0 - star (B Q 1 1)) +
        2 * Complex.normSq (B Q 0 1 + star (B Q 1 0)))

private theorem rejected_law : ¬ arena.Law equalityRejected := by
  intro h
  have hlo : -1 ≤ (0 : ℝ) := by norm_num
  obtain ⟨Q, hQ, hidem, htrace, _, _, _⟩ := (rankTwo_projection_isGreatest 0 hlo zero_le_one).2
  exact h Q hQ hidem htrace (rankTwo_projection_defect Q hQ hidem htrace)

def family : Registration arena (type_of% @rankTwo_projection_defect) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@rankTwo_projection_defect, equalityRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equalityActual equalityRejected rejected_law
  dependence := equalityDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rankTwo_projection_defect) (Realization equalitySignature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuParityCoherence.rankTwo_projection_defect.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuParityCoherence.ProjectionDefect.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuParityCoherence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ProjectionDefect

namespace ProjectionMaximum

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ L => 3 - L ^ 2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L : ℝ) (_hlo : -1 ≤ L) (_hhi : L ≤ 1),
    IsGreatest {g : ℝ | ∃ Q : Mat, Q.IsHermitian ∧ Q * Q = Q ∧ Q.trace = 2 ∧
      (((1 : Mat) - F) * Q).trace.re = 2 + L ∧
      carTrace Q Q = g} (R.readout () () L) ∧
    ∃ Q : Mat, Q.IsHermitian ∧ Q * Q = Q ∧ Q.trace = 2 ∧
      Commute Q (diagonal (![0, 1] : Fin 2 → ℂ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      (((1 : Mat) - F) * Q).trace.re = 2 + L ∧
      carTrace Q Q = 3 - L ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlo : -1 ≤ (0 : ℝ) := by norm_num
  have heq := (h 0 hlo zero_le_one).1.unique (rankTwo_projection_isGreatest 0 hlo zero_le_one).1
  change (0 : ℝ) = 3 - (0 : ℝ) ^ 2 at heq
  norm_num at heq

def family : Registration arena (type_of% @rankTwo_projection_isGreatest) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rankTwo_projection_isGreatest, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change (3 - (0 : ℝ) ^ 2) ≠ 3 - (1 : ℝ) ^ 2
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rankTwo_projection_isGreatest) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuParityCoherence.rankTwo_projection_isGreatest.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuParityCoherence.ProjectionMaximum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => 3 - L ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuParityCoherence
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Select the value argument of IsGreatest in the left conjunct.
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ProjectionMaximum

end Reg.D5.S3.Quantum.Semigroups.WuParityCoherence
