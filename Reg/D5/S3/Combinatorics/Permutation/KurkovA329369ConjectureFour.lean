import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the padded permutation count in A329369 Conjecture 4. -/

namespace Reg.D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour

open _root_.D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour
open _root_.D5.S1.Digit.DyadicRowPolynomialRecurrence (wt wt_zero)
open _root_.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock (T T_one)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ w n => paddedCount w n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m k w : ℕ, 2 ^ m * (2 * k + 1) < 2 ^ w →
    (R.readout () w (2 ^ m * (2 * k + 1)) : ℚ) =
      ∑ i ∈ Finset.Icc 1 (wt k + 2),
        (i.factorial : ℚ) * (i : ℚ) ^ m * T k i * (-1 : ℚ) ^ ((wt k : ℤ) - (i : ℤ))

private theorem initial_rhs (m : ℕ) :
    (∑ i ∈ Finset.Icc 1 (wt 0 + 2),
      (i.factorial : ℚ) * (i : ℚ) ^ m * T 0 i * (-1 : ℚ) ^ ((wt 0 : ℤ) - (i : ℤ))) =
      2 * (2 : ℚ) ^ m - 1 := by
  have ht : T 0 2 = 1 := by rw [T]; norm_num
  rw [wt_zero, show Finset.Icc 1 (0 + 2) = ({1, 2} : Finset ℕ) by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [ht, T_one]
  ring

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law 0 0 1 (by decide)
  change (0 : ℚ) = _ at h
  rw [initial_rhs] at h
  norm_num at h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 1, 2, ?_⟩
  change paddedCount 2 1 ≠ paddedCount 2 2
  have h₁ := conjecture4 0 0 2 (by decide)
  have h₂ := conjecture4 1 0 2 (by decide)
  rw [initial_rhs] at h₁ h₂
  norm_num at h₁ h₂
  intro he
  have h := congrArg (fun n : ℕ => (n : ℚ)) he
  rw [h₁, h₂] at h
  norm_num at h

def sourceRegistration : Registration arena (type_of% (@conjecture4)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conjecture4, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@conjecture4) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour.conjecture4.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w n => paddedCount w n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour
