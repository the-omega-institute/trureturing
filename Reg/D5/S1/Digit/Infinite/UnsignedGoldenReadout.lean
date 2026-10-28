import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.UnsignedGoldenReadout
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Digit.Infinite.UnsignedGoldenReadout

open _root_.D5.S1.Digit.Infinite.UnsignedGoldenReadout
open _root_.D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open _root_.D5.S1.Digit.Infinite.SignedSeriesRange (u v)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => LegalDigits) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => U x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

/-- The full source proposition is retained. One readout in the prefix estimate
is varied, while all other clauses retain their original observations. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ x : LegalDigits, Summable (fun k : ℕ =>
      (if x.val k then (1 : ℝ) else 0) * Real.goldenRatio⁻¹ ^ (k + 1))) ∧
    Set.range U = Set.Icc (0 : ℝ) 1 ∧
    Continuous U ∧
    (∀ (n : ℕ) (x y : LegalDigits),
      (∀ k < n, x.val k = y.val k) →
        |R.readout () () x - U y| ≤ Real.goldenRatio⁻¹ ^ n) ∧
    U zeroName = 0 ∧ U u = 1 ∧
    singleName ≠ v ∧ U singleName = Real.goldenRatio⁻¹ ∧ U v = Real.goldenRatio⁻¹

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := h.2.2.2.1 0 zeroName zeroName (by intro k hk; omega)
  have hz := unsigned_golden_readout.2.2.2.2.1
  change |(2 : ℝ) - U zeroName| ≤ Real.goldenRatio⁻¹ ^ 0 at hp
  rw [hz] at hp
  norm_num at hp

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), zeroName, u, ?_⟩
  change U zeroName ≠ U u
  rw [unsigned_golden_readout.2.2.2.2.1, unsigned_golden_readout.2.2.2.2.2.1]
  norm_num

def registration : Registration arena (type_of% unsigned_golden_readout) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unsigned_golden_readout, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.UnsignedGoldenReadout.unsigned_golden_readout)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => U x) (fun e => nomatch e)))
    (type_of% LegalDigits) Unit := {
  unitName := `D5.S1.Digit.Infinite.UnsignedGoldenReadout.unsigned_golden_readout.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.UnsignedGoldenReadout.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => U x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some LegalDigits,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.UnsignedGoldenReadout, definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg", "arg", "arg", "fn", "arg", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration

end
end Reg.D5.S1.Digit.Infinite.UnsignedGoldenReadout
