/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ParityHalfUniqueness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ParityHalfUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: One parity in one coordinate half determines a ternary Huang eigenvector on Q9. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-! A signed eigenvector row across the coordinate cut determines the remaining
values of its parity by divisibility by three. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ParityHalfUniqueness

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip flip_adj flip_apply_same flip_flip)
open ComponentBoundary.Q9IsotropicHuang (weightedAction flipSign parity)
open private flipSign_eq_intCoeff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private intCoeff_sign_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

/-- A ternary integer eigenvector of the unweighted Huang operator with eigenvalue `3`
is uniquely determined by its signed values at one parity in a coordinate half. -/
theorem eigenvector_eq_of_agree_on_parity_half (i : Fin 9) (b t : Bool)
    {f g : Q 9 → ℤ}
    (hfBound : ∀ x, -1 ≤ f x ∧ f x ≤ 1) (hgBound : ∀ x, -1 ≤ g x ∧ g x ≤ 1)
    (hfEigen : weightedAction (fun _ => 1) f = (3 : ℤ) • f)
    (hgEigen : weightedAction (fun _ => 1) g = (3 : ℤ) • g)
    (hagree : ∀ x, parity x = b → x i = t → f x = g x) : f = g := by
  have flipParity (x : Q 9) (j : Fin 9) : parity (flip x j) = !parity x :=
    (Bool.not_eq_iff.mpr (cubeParity_ne_of_adj (flip_adj x j))).symm
  have rowDifference (x : Q 9) :
      (∑ j : Fin 9, flipSign j x * (f (flip x j) - g (flip x j))) = 3 * (f x - g x) := by
    have hfRow := congrFun hfEigen x
    have hgRow := congrFun hgEigen x
    simp only [weightedAction, Int.cast_id, one_mul, Pi.smul_apply, smul_eq_mul] at hfRow hgRow
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hfRow, hgRow]
  -- Across the coordinate cut, only the `i` term can still differ in the row at `y`.
  have agreeOnParity (x : Q 9) (hx : parity x = b) : f x = g x := by
    by_cases hbit : x i = t
    · exact hagree x hx hbit
    let y := flip x i
    have hyt : y i = t := (flip_apply_same x i).trans (Bool.not_eq_iff.mpr hbit)
    have hyj (j : Fin 9) : parity (flip y j) = b := by
      simp [y, flipParity, hx]
    have hrow := rowDifference y
    rw [Finset.sum_eq_single i] at hrow
    · rw [show flip y i = x from flip_flip x i] at hrow
      have hsign := intCoeff_sign_of_adj y (flip y i) (flip_adj y i)
      rw [← flipSign_eq_intCoeff] at hsign
      obtain ⟨hfLower, hfUpper⟩ := hfBound x
      obtain ⟨hgLower, hgUpper⟩ := hgBound x
      rcases hsign with hsign | hsign <;> rw [hsign] at hrow <;> omega
    · intro j _ hji
      have hbit' : flip y j i = t := by
        simpa [BalancedCriticalSpectrum.flip, Ne.symm hji] using hyt
      rw [hagree _ (hyj j) hbit', sub_self, mul_zero]
    · simp
  funext x
  by_cases hx : parity x = b
  · exact agreeOnParity x hx
  · have hsum : (∑ j : Fin 9, flipSign j x * (f (flip x j) - g (flip x j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hj : parity (flip x j) = b := (flipParity x j).trans (Bool.not_eq_iff.mpr hx)
      rw [agreeOnParity _ hj, sub_self, mul_zero]
    have hrow := rowDifference x
    rw [hsum] at hrow
    omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ParityHalfUniqueness
