import D5.S3.Combinatorics.BinomialBases.MatharA001722
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Whole-sequence evidence for the full recurrence and formal-series assertion. -/

namespace Reg.D5.S3.Combinatorics.BinomialBases.MatharA001722
open _root_.D5.S3.Combinatorics.BinomialBases.MatharA001722
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => if n = 3 then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 3 ≤ n →
      R.readout () () n + 3 * (-(n : ℤ) - 5) * R.readout () () (n - 1) +
      (3 * (n : ℤ)^2 + 27 * (n : ℤ) + 61) * R.readout () () (n - 2) -
      ((n : ℤ) + 4)^3 * R.readout () () (n - 3) = 0) ∧
    (∃ (r : ℕ) (p : ℕ → Polynomial ℚ),
      (∃ j : ℕ, j ≤ r ∧ p j ≠ 0) ∧
      (∑ j ∈ Finset.range (r + 1), (p j : PowerSeries ℚ) *
        ((PowerSeries.derivative : PowerSeries ℚ → PowerSeries ℚ)^[j])
          (PowerSeries.mk (fun n => (R.readout () () n : ℚ)))) = 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h.1 3 (by decide)
  norm_num [rejected, realize] at bad

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    change
      (∑ k ∈ Finset.range (0 + 1), (-1 : ℤ) ^ (0 + k) *
        ((k + 2).choose 2 : ℤ) * (5 : ℤ)^k *
        (∏ i ∈ Finset.range (0 + 2), (Polynomial.X - Polynomial.C (i : ℤ))).coeff (k + 2)) ≠
      (∑ k ∈ Finset.range (1 + 1), (-1 : ℤ) ^ (1 + k) *
        ((k + 2).choose 2 : ℤ) * (5 : ℤ)^k *
        (∏ i ∈ Finset.range (1 + 2), (Polynomial.X - Polynomial.C (i : ℤ))).coeff (k + 2))
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ,
      Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one, Nat.choose]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.BinomialBases.MatharA001722.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MatharA001722.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Combinatorics.BinomialBases.MatharA001722
