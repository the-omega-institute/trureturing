/- GID: D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation
   generality: I
   mirror-B: D5/B/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation
   mirror-E: none(waiver:finite-certificate-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.claim; result=D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.result; claim=D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.claim
   digest: The values 628 and 673 between consecutive zero values 625 and 676 refute the distinctness conjecture for OEIS A229140. -/

import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.StephanLeastCoordinateDistinctnessRefutation

/-!
OEIS A229140 assigns to each sum of two squares the least first coordinate
among its representations by two nonnegative squares.  Its 2013 comment
conjectures that the values strictly between two consecutive zero values are
pairwise distinct.

The representable values `628` and `673` lie strictly between the consecutive
zero values `625` and `676`, but both have least first coordinate `12`.
-/

/-- `x` is the least first coordinate in a representation of `m` as two
nonnegative squares. -/
def IsLeastCoord (m x : ℕ) : Prop :=
  (∃ y : ℕ, x ^ 2 + y ^ 2 = m) ∧
    ∀ x' : ℕ, x' < x → ∀ y' : ℕ, x' ^ 2 + y' ^ 2 ≠ m

/-- The OEIS A229140 conjecture, expressed directly on representable values:
least coordinates are injective inside every interval bounded by consecutive
zero values. -/
def claim : Prop :=
  ∀ L R : ℕ,
    IsLeastCoord L 0 →
    IsLeastCoord R 0 →
    L < R →
    (∀ m : ℕ, L < m → m < R → ¬ IsLeastCoord m 0) →
    ∀ m₁ m₂ k : ℕ,
      L < m₁ →
      m₁ < R →
      L < m₂ →
      m₂ < R →
      m₁ ≠ m₂ →
      IsLeastCoord m₁ k →
      IsLeastCoord m₂ k →
      False

/-- The interval from `25^2` to `26^2` contains two distinct representable
values whose least first coordinate is `12`. -/
theorem result : ¬ claim := by
  have h625 : IsLeastCoord 625 0 := by
    constructor
    · exact ⟨25, by norm_num⟩
    · intro x hx y
      omega
  have h676 : IsLeastCoord 676 0 := by
    constructor
    · exact ⟨26, by norm_num⟩
    · intro x hx y
      omega
  have hNoZero : ∀ m : ℕ, 625 < m → m < 676 → ¬ IsLeastCoord m 0 := by
    intro m hmLower hmUpper hmZero
    rcases hmZero.1 with ⟨y, hy⟩
    norm_num at hy
    have hyUpper : y < 26 := by
      by_contra hnot
      have h26 : 26 ≤ y := by omega
      have hsq : 26 ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left h26 2
      norm_num at hsq
      omega
    have hyLower : 25 < y := by
      by_contra hnot
      have hy25 : y ≤ 25 := by omega
      have hsq : y ^ 2 ≤ 25 ^ 2 := Nat.pow_le_pow_left hy25 2
      norm_num at hsq
      omega
    omega
  have h628 : IsLeastCoord 628 12 := by
    constructor
    · exact ⟨22, by norm_num⟩
    · intro x hx y hxy
      have hySq : y ^ 2 ≤ 628 := by omega
      have hyUpper : y < 26 := by
        by_contra hnot
        have h26 : 26 ≤ y := by omega
        have hsq : 26 ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left h26 2
        norm_num at hsq
        omega
      have hy25 : y ≤ 25 := by omega
      interval_cases x <;> interval_cases y <;> norm_num at hxy
  have h673 : IsLeastCoord 673 12 := by
    constructor
    · exact ⟨23, by norm_num⟩
    · intro x hx y hxy
      have hySq : y ^ 2 ≤ 673 := by omega
      have hyUpper : y < 26 := by
        by_contra hnot
        have h26 : 26 ≤ y := by omega
        have hsq : 26 ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left h26 2
        norm_num at hsq
        omega
      have hy25 : y ≤ 25 := by omega
      interval_cases x <;> interval_cases y <;> norm_num at hxy
  intro hclaim
  exact hclaim 625 676 h625 h676 (by norm_num) hNoZero
    628 673 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h628 h673

#print axioms IsLeastCoord
#print axioms claim
#print axioms result

end D5.S3.PrimeForms.StephanLeastCoordinateDistinctnessRefutation
