/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportRepeatedQuadratic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportRepeatedQuadratic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full nonsquare repeated-exponent obstruction and all two-unit exponents. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportRepeatedBlocks
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-! Both exact antisymmetric roots, their actual graph eigenvalues, and the
unbounded two-unit family. Square-discriminant cases remain separate. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedQuadratic

open SixSupportClassificationAlgebra SixSupportRepeatedBlocks
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

/-- The original exact nonnegative integer antisymmetric discriminant. -/
def discriminant (a b : ℕ) : ℕ := (a+1)^2*b^2+2*a*(3*a+1)*b+a^2

/-- Either of the full complementary antisymmetric roots. -/
def root (a b : ℕ) (positive : Bool) : ℝ :=
  (((a*b+3*a+b : ℕ) : ℝ)+
    (if positive then Real.sqrt (discriminant a b) else -Real.sqrt (discriminant a b)))/2

/-- Both displayed roots satisfy the exact complementary quadratic. -/
theorem roots (a b : ℕ) (positive : Bool) : quadratic (a : ℝ) (b : ℝ) (root a b positive) = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (discriminant a b : ℝ) from Nat.cast_nonneg _)
  have hd : ((discriminant a b : ℕ) : ℝ) =
      ((a*b+3*a+b : ℕ) : ℝ)^2-4*((a : ℝ)*(b : ℝ)+2*(a : ℝ)^2) := by
    dsimp [discriminant]
    push_cast
    ring
  have hs' := hs.trans hd
  cases positive <;> simp only [root, Bool.false_eq_true, ↓reduceIte, quadratic]
  all_goals
    push_cast at hs' ⊢
    nlinarith only [hs']

/-- Every nonsquare discriminant gives two irrational roots, with no bound
on either positive exponent. -/
theorem roots_irrational (a b : ℕ) (hD : ¬IsSquare (discriminant a b)) (positive : Bool) :
    Irrational (root a b positive) := by
  have hs : Irrational (Real.sqrt (discriminant a b)) := irrational_sqrt_natCast_iff.mpr hD
  cases positive
  · simpa [root] using (hs.neg.natCast_add (a*b+3*a+b)).div_natCast (by decide : (2 : ℕ) ≠ 0)
  · simpa [root] using (hs.natCast_add (a*b+3*a+b)).div_natCast (by decide : (2 : ℕ) ≠ 0)

/-- Every nonzero complementary quadratic root has a genuine actual ideal-graph consumer. -/
theorem actual_quadratic_eigenvalue (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (e : ℝ) (he0 : e ≠ 0) (he : quadratic (a : ℝ) (b : ℝ) e = 0) :
    HasActualEigenvalue (modulus p (exponents a a b))
      (((((a+1)*(a+1)*(b+1))-2 : ℕ) : ℝ)-e) := by
  apply actual_of_root p hp hinj a a b ha ha hb e he0
  rw [factorization,he,neg_zero,zero_mul]

/-- The full original nonsquare branch, including both irrational actual eigenvalues. -/
theorem result (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hD : ¬IsSquare (discriminant a b)) :
    (∀ positive : Bool,
      HasActualEigenvalue (modulus p (exponents a a b))
        (((((a+1)*(a+1)*(b+1))-2 : ℕ) : ℝ)-root a b positive) ∧
      Irrational (((((a+1)*(a+1)*(b+1))-2 : ℕ) : ℝ)-root a b positive)) ∧
      ¬ActualLaplacianIntegral (modulus p (exponents a a b)) := by
  have hh (positive : Bool) := roots_irrational a b hD positive
  have hActual (positive : Bool) := actual_quadratic_eigenvalue p hp hinj a b ha hb
    (root a b positive) (hh positive).ne_zero (roots a b positive)
  constructor
  · intro positive
    exact ⟨hActual positive,(hh positive).natCast_sub _⟩
  · intro hint
    obtain ⟨z,hz⟩ := hint _ (hActual true)
    exact ((hh true).natCast_sub _).ne_int z hz

/-- The exact source discriminant lies strictly between consecutive squares
for every positive third exponent when a=1. -/
theorem two_unit_nonsquare (b : ℕ) (hb : 0 < b) : ¬IsSquare (discriminant 1 b) := by
  rintro ⟨k,hk⟩
  have hsq : k^2 = discriminant 1 b := by simpa [pow_two] using hk.symm
  have hl : (2*b+1)^2 < discriminant 1 b := by dsimp [discriminant]; nlinarith
  have hu : discriminant 1 b < (2*b+2)^2 := by dsimp [discriminant]; nlinarith
  have hkl : 2*b+1 < k := (sq_lt_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp
    (by nlinarith only [hl,hsq])
  have hku : k < 2*b+2 := (sq_lt_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp
    (by nlinarith only [hu,hsq])
  omega

/-- Every positive two-unit-exponent actual ideal graph is nonintegral. -/
theorem two_unit_actual (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b : ℕ) (hb : 0 < b) :
    ¬ActualLaplacianIntegral (modulus p (exponents 1 1 b)) :=
  (result p hp hinj 1 b (by decide) hb (two_unit_nonsquare b hb)).2

#print axioms roots
#print axioms result
#print axioms two_unit_nonsquare
#print axioms two_unit_actual

end D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedQuadratic
