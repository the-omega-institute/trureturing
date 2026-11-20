import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity
import Reg.Support.SingleDependentReadout

/-! The integer-level capacity observes the reduced denominator in its upper bound. -/

namespace Reg.D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity

open _root_.D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ denominator => denominator) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r k n b A : ℕ}, 0 < b → A.Coprime b → ∀ w : Fin (r + 1) → ℝ,
    (∑ j, w j) = (A : ℝ) / b → ∀ level : Fin n → ℤ, Function.Injective level →
    (∀ x : Fin n, ∃ d : Fin (r + 1) → Fin (k + 1),
      (∑ j, ((d j).val : ℝ) * w j) = (level x : ℝ)) →
    b * n ≤ (R.readout () () b + k) * (k + 1)^r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let w : Fin 1 → ℝ := fun _ => 1
  let level (x : Fin 2) : ℤ := x.val
  have distinct : Function.Injective level := by
    intro x y eq
    change (x.val : ℤ) = (y.val : ℤ) at eq
    exact Fin.ext (by exact_mod_cast eq)
  have total : (∑ j, w j) = ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num [w]
  have cover (x : Fin 2) : ∃ d : Fin 1 → Fin 2,
      (∑ j, ((d j).val : ℝ) * w j) = (level x : ℝ) := by
    exact ⟨fun _ => x, by simp [w, level]⟩
  have impossible := h (r := 0) (k := 1) (n := 2) (b := 1) (A := 1)
    (by decide) (by decide) w total level distinct cover
  exact (by decide : ¬ (2 : ℕ) ≤ 1) impossible

def family : Registration arena (type_of% (@integral_levels_capacity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_levels_capacity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    exact ⟨(), 1, 2, (by decide : (1 : ℕ) ≠ 2)⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@integral_levels_capacity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ denominator => denominator) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity
