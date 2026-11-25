import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity
import Reg.Support.SingleDependentReadout

/-! The integer coverage bound depends on the short-period threshold. -/

namespace Reg.D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity

open _root_.D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ threshold => threshold) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r k n B M : ℕ}, 0 < B → ∀ w : Fin (r + 1) → ℝ,
    (∀ d : ℕ, 0 < d → d < B → d ∣ M) →
    (¬ ∃ z : ℤ, (M : ℝ) * (∑ j, w j) = z) →
    ∀ (level : Fin n → ℤ), Function.Injective level →
    (∀ x : Fin n, ∃ d : Fin (r + 1) → Fin (k + 1),
      (∑ j, ((d j).val : ℝ) * w j) = (level x : ℝ)) →
    n ≤ (k / R.readout () () B + 1) * (k + 1) ^ r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have short : ∀ d : ℕ, 0 < d → d < 1 → d ∣ 1 := by
    intro d positive bound
    omega
  let w : Fin 1 → ℝ := fun _ => 1 / 2
  have nonintegral : ¬ ∃ z : ℤ, (1 : ℝ) * (∑ j, w j) = z := by
    rintro ⟨z, hz⟩
    simp only [Fin.sum_univ_one, w, one_mul] at hz
    have eq : (2 : ℝ) * z = 1 := by linarith
    have intEq : (2 : ℤ) * z = 1 := by exact_mod_cast eq
    omega
  let level (x : Fin 2) : ℤ := x.val
  have distinct : Function.Injective level := by
    intro x y eq
    change (x.val : ℤ) = (y.val : ℤ) at eq
    apply Fin.ext
    exact_mod_cast eq
  have covers (x : Fin 2) : ∃ d : Fin 1 → Fin 3,
      (∑ j, ((d j).val : ℝ) * w j) = (level x : ℝ) := by
    fin_cases x
    · exact ⟨fun _ => 0, by norm_num [w, level]⟩
    · exact ⟨fun _ => 2, by norm_num [w, level]⟩
  have impossible := h (r := 0) (k := 2) (n := 2) (B := 1) (M := 1)
    (by decide) w short (by simpa only [Nat.cast_one] using nonintegral) level distinct covers
  exact (by decide : ¬ (2 : ℕ) ≤ 1) impossible

def family : Registration arena (type_of% (@integral_range_le_period_blocks)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_range_le_period_blocks, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    exact ⟨(), 1, 2, (by decide : (1 : ℕ) ≠ 2)⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@integral_range_le_period_blocks) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ threshold => threshold) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity
