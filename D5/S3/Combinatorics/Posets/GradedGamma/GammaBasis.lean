/- GID: D5/S3/Combinatorics/Posets/GradedGamma/GammaBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/GammaBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff]
   utility: none
   digest: Unitriangular gamma coefficients of an integer polynomial remain integers. -/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open scoped BigOperators
open Polynomial
noncomputable section

/-- A homogeneous gamma-basis term at declared degree `d`. -/
def gammaTerm (R : Type*) [Semiring R] (d j : ℕ) : Polynomial R :=
  X ^ j * (1 + X) ^ (d - 2 * j)

/-- A real gamma expansion of an integer polynomial has integer coordinates.
Positivity transfers to those recovered integer coordinates. -/
theorem integer_gamma_recovery (d : ℕ) (p : Polynomial ℤ) (c : ℕ → ℝ)
    (h : p.map (Int.castRingHom ℝ) =
      ∑ j ∈ Finset.range (d / 2 + 1), C (c j) * gammaTerm ℝ d j)
    (hc : ∀ j < d / 2 + 1, 0 ≤ c j) :
    ∃ z : ℕ → ℤ, (∀ j < d / 2 + 1, 0 ≤ z j) ∧
      p = ∑ j ∈ Finset.range (d / 2 + 1), C (z j) * gammaTerm ℤ d j := by
  let n := d / 2 + 1
  have hcoeff (i j : ℕ) : (gammaTerm ℝ d i).coeff j =
      if i ≤ j then ((d - 2 * i).choose (j - i) : ℝ) else 0 := by
    simp only [gammaTerm, coeff_X_pow_mul']
    split_ifs with hij
    · exact coeff_one_add_X_pow ℝ _ _
    · rfl
  have heq (j : ℕ) : (p.coeff j : ℝ) =
      ∑ i ∈ Finset.range n, c i *
        (if i ≤ j then ((d - 2 * i).choose (j - i) : ℝ) else 0) := by
    have hj := congrArg (fun f : Polynomial ℝ => f.coeff j) h
    simpa [n, coeff_sum, coeff_C_mul, hcoeff] using hj
  have hint : ∀ j < n, ∃ z : ℤ, (z : ℝ) = c j := by
    intro j hj
    induction j using Nat.strong_induction_on with
    | h j ih =>
      have hsubset : Finset.range (j + 1) ⊆ Finset.range n := by
        intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega
      have hsum :
          (∑ i ∈ Finset.range (j + 1), c i *
            (if i ≤ j then ((d - 2 * i).choose (j - i) : ℝ) else 0)) =
          ∑ i ∈ Finset.range n, c i *
            (if i ≤ j then ((d - 2 * i).choose (j - i) : ℝ) else 0) := by
        apply Finset.sum_subset hsubset
        intro i hi hni
        have hji : j < i := by
          simp only [Finset.mem_range] at hni
          omega
        simp [not_le.mpr hji]
      have htail : ∃ z : ℤ, (z : ℝ) =
          ∑ i ∈ Finset.range j, c i *
            ((d - 2 * i).choose (j - i) : ℝ) := by
        let prior : ℕ → ℤ := fun i =>
          if hi : i < j then Classical.choose (ih i hi (by omega)) else 0
        refine ⟨∑ i ∈ Finset.range j,
          prior i * ((d - 2 * i).choose (j - i) : ℤ), ?_⟩
        push_cast
        apply Finset.sum_congr rfl
        intro i hi
        have hij := Finset.mem_range.mp hi
        simp only [prior, dif_pos hij]
        rw [Classical.choose_spec (ih i hij (by omega))]
      obtain ⟨z, hz⟩ := htail
      have hmain := (heq j).trans hsum.symm
      rw [Finset.sum_range_succ] at hmain
      have hprefix : (∑ i ∈ Finset.range j, c i *
          (if i ≤ j then ((d - 2 * i).choose (j - i) : ℝ) else 0)) = (z : ℝ) := by
        rw [hz]
        apply Finset.sum_congr rfl
        intro i hi
        simp [(Finset.mem_range.mp hi).le]
      rw [hprefix] at hmain
      simp at hmain
      refine ⟨p.coeff j - z, ?_⟩
      push_cast
      linarith
  let z : ℕ → ℤ := fun j => if hj : j < n then Classical.choose (hint j hj) else 0
  have hz (j : ℕ) (hj : j < n) : (z j : ℝ) = c j := by
    simp only [z, dif_pos hj]
    exact Classical.choose_spec (hint j hj)
  refine ⟨z, ?_, ?_⟩
  · intro j hj
    have hnonneg := hc j hj
    rw [← hz j hj] at hnonneg
    exact_mod_cast hnonneg
  · apply Polynomial.map_injective (Int.castRingHom ℝ)
      (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
    rw [h]
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [show (Int.castRingHom ℝ) (z j) = c j from hz j hjn]
    simp [gammaTerm]

end
end D5.S3.Combinatorics.Posets.GradedGamma
