/- GID: D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite family closed under inversion in the unit circle lies on the circle exactly when its power-sum Toeplitz matrix is positive semidefinite. -/

import D5.S3.Weil.TestFunctions.LiCurvatureCriterion
import Mathlib.LinearAlgebra.Lagrange

/-! # Toeplitz positivity of power sums and the unit circle

Let `u : Fin m → ℂ` be a family of nonzero complex numbers, closed with
multiplicities under `z ↦ (conj z)⁻¹`: some permutation `σ` satisfies
`u (σ j) = (conj (u j))⁻¹`. Put `p k = ∑ j, u j ^ k` for integers `k`.
When every `u j` has modulus one, the power sums are the circle moments of a finite
sum of Dirac measures, so the Toeplitz matrix `[p (j - k)]` of every size is
positive semidefinite. Conversely, for every size at least the number `d`
of distinct values of `u`, positive semidefiniteness forces every `u j` onto the circle.

The quadratic form of the Toeplitz matrix on a coefficient vector `x` equals
`∑ j, conj (P (conj (u j))) * P (conj (u (σ j)))`, where `P` is the polynomial
with coefficients `x`. Off the circle, the distinct points `conj z` and `z⁻¹` of an
off-circle value `z` are interpolated by a polynomial of degree below `d` with
values `1` and `-1` that vanishes at the other values `conj (u j)`; each term is then
`0` or `-1`, and the term at `z` is `-1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Polynomial
open scoped BigOperators ComplexConjugate ComplexOrder
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
  (toeplitzMatrix circleMoment circle_moment_toeplitz_posSemidef)

namespace D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Integer power sums `p k = ∑ j, u j ^ k` of a finite complex family. -/
def powerSum {m : ℕ} (u : Fin m → ℂ) (k : ℤ) : ℂ :=
  ∑ j, u j ^ k

/-- The value at `w` of the polynomial with coefficient vector `x`. -/
private def coefficientValue {n : ℕ} (x : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∑ a, x a * w ^ (a : ℕ)

private theorem conj_partner {m : ℕ} {u : Fin m → ℂ} {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ j, u (σ j) = (conj (u j))⁻¹) (j : Fin m) :
    conj (u (σ j)) = (u j)⁻¹ := by
  rw [hσ, map_inv₀, Complex.conj_conj]

private theorem quadratic_form_eq {m N : ℕ} (u : Fin m → ℂ) (hu : ∀ j, u j ≠ 0)
    (σ : Equiv.Perm (Fin m)) (hσ : ∀ j, u (σ j) = (conj (u j))⁻¹)
    (x : Fin (N + 1) → ℂ) :
    star x ⬝ᵥ (toeplitzMatrix (powerSum u) N *ᵥ x) =
      ∑ j, star (coefficientValue x (conj (u j))) *
        coefficientValue x (conj (u (σ j))) := by
  have key : ∀ (j : Fin m) (a b : ℕ),
      u j ^ ((a : ℤ) - (b : ℤ)) = u j ^ a * conj (u (σ j)) ^ b := by
    intro j a b
    rw [conj_partner hσ, inv_pow, zpow_sub₀ (hu j), zpow_natCast, zpow_natCast,
      div_eq_mul_inv]
  have lhs : star x ⬝ᵥ (toeplitzMatrix (powerSum u) N *ᵥ x) =
      ∑ a : Fin (N + 1), ∑ b : Fin (N + 1), ∑ j,
        star (x a) * (u j ^ (a : ℕ) * conj (u (σ j)) ^ (b : ℕ)) * x b := by
    simp only [dotProduct, mulVec, toeplitzMatrix, powerSum, Pi.star_apply, key]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have rhs : ∑ j, star (coefficientValue x (conj (u j))) *
        coefficientValue x (conj (u (σ j))) =
      ∑ j, ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        star (x a) * (u j ^ (a : ℕ) * conj (u (σ j)) ^ (b : ℕ)) * x b := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [coefficientValue, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [star_mul', Complex.star_def, map_pow, Complex.conj_conj]
    ring
  rw [lhs, rhs]
  calc ∑ a : Fin (N + 1), ∑ b : Fin (N + 1), ∑ j,
        star (x a) * (u j ^ (a : ℕ) * conj (u (σ j)) ^ (b : ℕ)) * x b
      = ∑ a : Fin (N + 1), ∑ j, ∑ b : Fin (N + 1),
        star (x a) * (u j ^ (a : ℕ) * conj (u (σ j)) ^ (b : ℕ)) * x b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem coefficientValue_eq_eval {N : ℕ} (f : ℂ[X])
    (hf : f.natDegree < N + 1) (w : ℂ) :
    coefficientValue (fun a : Fin (N + 1) => f.coeff a) w = f.eval w := by
  rw [coefficientValue, Polynomial.eval_eq_sum_range' hf]
  exact Fin.sum_univ_eq_sum_range (fun a : ℕ => f.coeff a * w ^ a) (N + 1)

/-- On the unit circle every power-sum Toeplitz matrix is positive semidefinite:
if every `u j` has modulus one, then `toeplitzMatrix (powerSum u) N` is positive
semidefinite for every `N`. This is the finite-Dirac-measure case of
`LiCurvatureCriterion.circle_moment_toeplitz_posSemidef`: the power sums are the
circle moments of `∑ j, δ (u j)⁻¹`. -/
theorem powerSum_toeplitz_posSemidef_of_norm_eq_one {m N : ℕ} (u : Fin m → ℂ)
    (hunit : ∀ j, ‖u j‖ = 1) :
    (toeplitzMatrix (powerSum u) N).PosSemidef := by
  let z : Fin m → Circle := fun j =>
    ⟨u j, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hunit j⟩
  let mu : MeasureTheory.Measure Circle := ∑ j, MeasureTheory.Measure.dirac (z j)⁻¹
  have hmoment : circleMoment mu = powerSum u := by
    funext n
    rw [circleMoment, MeasureTheory.integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [MeasureTheory.integral_dirac, Circle.coe_inv, _root_.inv_zpow', neg_neg]
    · intro j _
      exact MeasureTheory.integrable_dirac (by simp)
  rw [← hmoment]
  exact circle_moment_toeplitz_posSemidef mu N

/-- Hermite-type criterion on the unit circle. Let `u : Fin m → ℂ` be nonzero
and closed with multiplicities under `z ↦ (conj z)⁻¹`, witnessed by a
permutation `σ`. For every `N` such that `N + 1` is at least the number `d` of
distinct values of `u`, the `(N + 1) × (N + 1)` Toeplitz matrix `[p (j - k)]` of the
power sums `p k = ∑ j, u j ^ k` is positive semidefinite if and only if every `u j`
lies on the unit circle. -/
theorem toeplitz_posSemidef_iff_norm_eq_one {m N : ℕ} (u : Fin m → ℂ)
    (hN : (Finset.univ.image u).card ≤ N + 1) (hu : ∀ j, u j ≠ 0) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ j, u (σ j) = (conj (u j))⁻¹) :
    (toeplitzMatrix (powerSum u) N).PosSemidef ↔ ∀ j, ‖u j‖ = 1 := by
  classical
  constructor
  · intro hpsd
    by_contra hnot
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    set z := u i with hz
    set a : ℂ := conj z with ha
    set b : ℂ := z⁻¹ with hb
    have hab : a ≠ b := by
      intro h
      apply hi
      have hz0 : z ≠ 0 := hu i
      have hmul : z * conj z = 1 := by
        rw [← ha, h, hb, mul_inv_cancel₀ hz0]
      have hnorm : (Complex.normSq z : ℂ) = 1 := by
        rw [← Complex.mul_conj, hmul]
      have hnorm' : Complex.normSq z = 1 := by exact_mod_cast hnorm
      rw [Complex.normSq_eq_norm_sq] at hnorm'
      have h0 : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith [sq_nonneg (‖z‖ - 1), sq_nonneg (‖z‖ + 1)]
    let s : Finset ℂ := Finset.univ.image (fun j => conj (u j))
    let g : ℂ → ℂ := fun w => if w = a then 1 else if w = b then -1 else 0
    let f : ℂ[X] := Lagrange.interpolate s id g
    have hinj : Set.InjOn id (↑s : Set ℂ) := Set.injOn_id _
    have hmem : ∀ j, conj (u j) ∈ s := fun j =>
      Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have hmemσ : ∀ j, (u j)⁻¹ ∈ s := by
      intro j
      rw [← conj_partner hσ j]
      exact hmem (σ j)
    have hf_eval : ∀ w ∈ s, f.eval w = g w := fun w hw =>
      Lagrange.eval_interpolate_at_node _ hinj hw
    have hcard : s.card ≤ N + 1 := by
      have hs : s = (Finset.univ.image u).image (starRingEnd ℂ) := by
        rw [Finset.image_image]
        rfl
      rw [hs]
      exact Finset.card_image_le.trans hN
    have hf_degree : f.degree < (N + 1 : ℕ) :=
      (Lagrange.degree_interpolate_lt _ hinj).trans_le (by exact_mod_cast hcard)
    have hfne : f ≠ 0 := by
      intro hf0
      have h := hf_eval a (hmem i)
      simp [hf0, g] at h
    have hnat : f.natDegree < N + 1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hfne).mpr hf_degree
    let x : Fin (N + 1) → ℂ := fun k => f.coeff k
    have hvalue : ∀ w ∈ s, coefficientValue x w = g w := by
      intro w hw
      rw [coefficientValue_eq_eval f hnat, hf_eval w hw]
    have hterm : ∀ j, (star (coefficientValue x (conj (u j))) *
        coefficientValue x (conj (u (σ j)))).re ≤ if j = i then -1 else 0 := by
      intro j
      rw [hvalue _ (hmem j), conj_partner hσ j, hvalue _ (hmemσ j)]
      have hga : g a = 1 := by simp [g]
      have hgb : g b = -1 := by simp [g, Ne.symm hab]
      by_cases hja : conj (u j) = a
      · have huj : u j = z := by
          have := congrArg conj hja
          simpa [ha] using this
        have hinv : (u j)⁻¹ = b := by rw [huj]
        rw [hja, hinv, hga, hgb]
        split_ifs <;> norm_num
      · have hji : j ≠ i := by
          intro hji
          apply hja
          rw [hji]
        by_cases hjb : conj (u j) = b
        · have hinv : (u j)⁻¹ = a := by
            have h1 : u j = conj b := by
              have := congrArg conj hjb
              simpa using this
            rw [h1, hb, ha, map_inv₀, inv_inv]
          rw [hjb, hinv, hgb, hga]
          simp [hji]
        · have hg0 : g (conj (u j)) = 0 := by simp [g, hja, hjb]
          rw [hg0]
          simp [hji]
    have hsum : (star x ⬝ᵥ (toeplitzMatrix (powerSum u) N *ᵥ x)).re ≤ -1 := by
      rw [quadratic_form_eq u hu σ hσ x, Complex.re_sum]
      calc ∑ j, (star (coefficientValue x (conj (u j))) *
            coefficientValue x (conj (u (σ j)))).re
          ≤ ∑ j, (if j = i then (-1 : ℝ) else 0) := Finset.sum_le_sum fun j _ => hterm j
        _ = -1 := by simp
    have hnonneg := hpsd.dotProduct_mulVec_nonneg x
    have hre := (Complex.le_def.mp hnonneg).1
    simp only [Complex.zero_re] at hre
    linarith
  · exact powerSum_toeplitz_posSemidef_of_norm_eq_one u

end D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion
