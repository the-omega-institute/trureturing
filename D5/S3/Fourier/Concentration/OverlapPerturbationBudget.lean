/- GID: D5/S3/Fourier/Concentration/OverlapPerturbationBudget
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/OverlapPerturbationBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A lower-degree diagonal controls the inverse Euclidean scales of weighted pairs. -/

import D5.S3.Fourier.Concentration.FiniteMultinomialOverlap

/-! An aggregate bound on the inverse scales of distinct multinomial pairs. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight diagonal)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (monomialWeight_nonneg)

namespace D5.S3.Fourier.Concentration.OverlapPerturbationBudget

private theorem overlap_lt_degree_of_ne {J : Type*} [Fintype J]
    (m n : J → ℕ) (p : ℕ) (hm : (∑ j, m j) = p) (hn : (∑ j, n j) = p)
    (hne : m ≠ n) : (∑ j, min (m j) (n j)) < p := by
  have hleM : (∑ j, min (m j) (n j)) ≤ p := by
    rw [← hm]
    exact sum_le_sum (fun j _ => min_le_left _ _)
  refine lt_of_le_of_ne hleM ?_
  intro h
  have hpointM := (sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ (univ : Finset J)) => min_le_left (m j) (n j))).mp (h.trans hm.symm)
  have hpointN := (sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ (univ : Finset J)) => min_le_right (m j) (n j))).mp (h.trans hn.symm)
  exact hne (funext fun j => (hpointM j (mem_univ j)).symm.trans (hpointN j (mem_univ j)))

private theorem sqrt_scale_ge {J : Type*} [Fintype J] (radius : J → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hr : ∀ j, ρ ≤ radius j)
    {m n : J → ℕ} {p : ℕ} (hm : (∑ j, m j) = p) (hn : (∑ j, n j) = p)
    {d : ℕ} (hd : d + (∑ j, min (m j) (n j)) ≤ p) :
    ρ * Real.sqrt (2 * (d : ℝ)) ≤ Real.sqrt (∑ j, (((m j : ℝ) - n j) * radius j) ^ 2) := by
  have hreal : (d : ℝ) + ∑ j, (min (m j) (n j) : ℝ) ≤ p := by exact_mod_cast hd
  have hscale := weighted_count_difference_sq_ge radius hρ.le hr m n p hm hn
  rw [← Real.sqrt_sq hρ.le, ← Real.sqrt_mul (sq_nonneg ρ)]
  apply Real.sqrt_le_sqrt
  refine le_trans ?_ hscale
  calc
    _ = (2 * ρ ^ 2) * d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Bound the weighted inverse scales using a common-count threshold. -/
theorem weighted_inverse_scale_le_of_overlap {J : Type*} [Fintype J] [DecidableEq J]
    (w radius : J → ℝ) (hw : ∀ j, 0 ≤ w j) {ρ : ℝ} (hρ : 0 < ρ)
    (hr : ∀ j, ρ ≤ radius j) (p k : ℕ) (hk : k ≤ p) :
    (∑ m ∈ piAntidiag univ p, ∑ n ∈ (piAntidiag univ p).erase m,
      monomialWeight w m * monomialWeight w n /
        Real.sqrt (∑ j, (((m j : ℝ) - n j) * radius j) ^ 2)) ≤
      (∑ j, w j) ^ (2 * p) / (ρ * Real.sqrt (2 * ((p - k + 1 : ℕ) : ℝ))) +
        ((Nat.choose p k : ℝ) ^ 2 * (∑ j, w j) ^ (2 * (p - k)) * diagonal w k) /
          (ρ * Real.sqrt 2) := by
  let s := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let H (m n : J → ℕ) := ∑ j, min (m j) (n j)
  let S (m n : J → ℕ) := ∑ j, (((m j : ℝ) - n j) * radius j) ^ 2
  let smallDen := ρ * Real.sqrt (2 * ((p - k + 1 : ℕ) : ℝ))
  let largeDen := ρ * Real.sqrt 2
  have hsmall : 0 < smallDen := by dsimp [smallDen]; positivity
  have hlarge : 0 < largeDen := by dsimp [largeDen]; positivity
  have hweight (m n : J → ℕ) : 0 ≤ c m * c n :=
    mul_nonneg (monomialWeight_nonneg w hw m) (monomialWeight_nonneg w hw n)
  let high (m n : J → ℕ) := if k ≤ H m n then c m * c n else 0
  have hhigh (m n : J → ℕ) : 0 ≤ high m n := by
    dsimp [high]
    split_ifs
    · exact hweight m n
    · exact le_rfl
  have hterm (m n : J → ℕ) (hm : m ∈ s) (hn : n ∈ s.erase m) :
      c m * c n / Real.sqrt (S m n) ≤ c m * c n / smallDen + high m n / largeDen := by
    have hmp := (mem_piAntidiag.mp hm).1
    have hnp := (mem_piAntidiag.mp (mem_of_mem_erase hn)).1
    have hless : H m n < p := overlap_lt_degree_of_ne m n p hmp hnp (ne_of_mem_erase hn).symm
    by_cases h : k ≤ H m n
    · have hden : largeDen ≤ Real.sqrt (S m n) := by
        simpa [largeDen, S] using sqrt_scale_ge radius hρ hr hmp hnp
          (d := 1) (by change 1 + H m n ≤ p; omega)
      rw [show high m n = c m * c n from ite_eq_left h]
      exact (div_le_div_of_nonneg_left (hweight m n) hlarge hden).trans
        (le_add_of_nonneg_left (div_nonneg (hweight m n) hsmall.le))
    · have hden : smallDen ≤ Real.sqrt (S m n) :=
        sqrt_scale_ge radius hρ hr hmp hnp
          (d := p - k + 1) (by change p - k + 1 + H m n ≤ p; omega)
      rw [show high m n = 0 from ite_eq_right h, zero_div, add_zero]
      exact div_le_div_of_nonneg_left (hweight m n) hsmall hden
  have htotal : (∑ m ∈ s, ∑ n ∈ s, c m * c n) = (∑ j, w j) ^ (2 * p) := by
    simp_rw [← mul_sum, ← sum_mul]
    have hsum : (∑ m ∈ s, c m) = (∑ j, w j) ^ p :=
      (sum_pow_eq_sum_piAntidiag univ w p).symm
    rw [hsum, pow_mul, pow_two]
    ring
  calc
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m, (c m * c n / smallDen + high m n / largeDen) :=
      sum_le_sum fun m hm => sum_le_sum fun n hn => hterm m n hm hn
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, (c m * c n / smallDen + high m n / largeDen) := by
      refine sum_le_sum fun m _ => sum_le_sum_of_subset_of_nonneg (erase_subset _ _) ?_
      intro n _ _
      exact add_nonneg (div_nonneg (hweight m n) hsmall.le) (div_nonneg (hhigh m n) hlarge.le)
    _ = (∑ j, w j) ^ (2 * p) / smallDen + (∑ m ∈ s, ∑ n ∈ s, high m n) / largeDen := by
      simp only [sum_add_distrib, ← sum_div, htotal]
    _ ≤ _ := add_le_add_right
      (div_le_div_of_nonneg_right (weighted_overlap_le_diagonal w hw p k hk) hlarge.le) _

#print axioms weighted_inverse_scale_le_of_overlap

end D5.S3.Fourier.Concentration.OverlapPerturbationBudget
