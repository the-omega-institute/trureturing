import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity
import Reg.Support.SingleDependentReadout

/-! The number of diagonal codes bounds the full integer coverage law. -/

namespace Reg.D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity

open _root_.D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ k b => (Finset.univ.image (code (k := k) b)).card)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n b c : ℕ}, 0 < b → Nat.Coprime c b →
    ∀ a z : ℝ, a + z = (c : ℝ) / b →
      (∀ t : Fin n, ∃ d : Fin (k + 1) × Fin (k + 1),
        (d.1.val : ℝ) * a + (d.2.val : ℝ) * z = t.val) →
      n ≤ R.readout () k b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have result := h (k := 0) (n := 1) (b := 1) (c := 1)
    (by decide) (by decide) 0 1 (by norm_num) (fun t => ⟨(0, 0), by
      have ht : t.val = 0 := by omega
      simp [ht]⟩)
  exact (by decide : ¬ (1 : ℕ) ≤ 0) result

def family : Registration arena (type_of% (@integral_range_le_diagonal_codes)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_range_le_diagonal_codes, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    exact (by decide : (4 : ℕ) ≠ 3)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@integral_range_le_diagonal_codes) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k b => (Finset.univ.image (code (k := k) b)).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity
