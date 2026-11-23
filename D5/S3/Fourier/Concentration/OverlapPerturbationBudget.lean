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

private theorem sum_erase_of_diagonal {A : Type*} [DecidableEq A] (s : Finset A)
    (f : A → A → ℝ) :
    (∑ m ∈ s, ∑ n ∈ s.erase m, f m n) =
      (∑ m ∈ s, ∑ n ∈ s, f m n) - ∑ m ∈ s, f m m := by
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun m hm => eq_sub_of_add_eq (sum_erase_add _ _ hm)

/-- Sum the increases of the reciprocal scale against upper bounds on the nested
high-overlap masses, excluding the diagonal in every tail. -/
theorem weighted_inverse_scale_le_of_overlap {J : Type*} [Fintype J] [DecidableEq J]
    (w radius : J → ℝ) (hw : ∀ j, 0 ≤ w j) {ρ : ℝ} (hρ : 0 < ρ)
    (hr : ∀ j, ρ ≤ radius j) (p : ℕ) :
    let T := (∑ j, w j) ^ (2 * p)
    let Q (h : ℕ) := (ρ * Real.sqrt (2 * ((p - h : ℕ) : ℝ)))⁻¹
    let B (h : ℕ) := (range (h + 1)).inf' ⟨0, mem_range.mpr (Nat.succ_pos h)⟩
      (fun i => min ((Nat.choose p i : ℝ) ^ 2 * (∑ j, w j) ^ (2 * (p - i)) * diagonal w i) T) -
        diagonal w p
    (∑ m ∈ piAntidiag univ p, ∑ n ∈ (piAntidiag univ p).erase m,
      monomialWeight w m * monomialWeight w n /
        Real.sqrt (∑ j, (((m j : ℝ) - n j) * radius j) ^ 2)) ≤
      (T - diagonal w p) * Q 0 +
        ∑ h ∈ range (p - 1), B (h + 1) * (Q (h + 1) - Q h) := by
  intro T Q B
  let s := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let H (m n : J → ℕ) := ∑ j, min (m j) (n j)
  let high (h : ℕ) (m n : J → ℕ) := if h ≤ H m n then c m * c n else 0
  have hweight (m n : J → ℕ) : 0 ≤ c m * c n :=
    mul_nonneg (monomialWeight_nonneg w hw m) (monomialWeight_nonneg w hw n)
  have htotal : (∑ m ∈ s, ∑ n ∈ s, c m * c n) = T := by
    simp_rw [← mul_sum, ← sum_mul]
    have hsum : (∑ m ∈ s, c m) = (∑ j, w j) ^ p :=
      (sum_pow_eq_sum_piAntidiag univ w p).symm
    rw [hsum]
    dsimp [T]
    rw [pow_mul, pow_two]
    ring
  have hmass :
      (∑ m ∈ s, ∑ n ∈ s.erase m, c m * c n) = T - diagonal w p := by
    rw [sum_erase_of_diagonal, htotal]
    congr 1
    simp only [diagonal, s, c, pow_two]
  have htail (h : ℕ) (hh : h ≤ p) :
      (∑ m ∈ s, ∑ n ∈ s.erase m, high h m n) ≤ B h := by
    rw [sum_erase_of_diagonal]
    have hdiag : (∑ m ∈ s, high h m m) = diagonal w p := by
      refine sum_congr rfl fun m hm => ?_
      have hm' : h ≤ H m m := by simpa [H, (mem_piAntidiag.mp hm).1] using hh
      simp [high, hm', pow_two, c]
    rw [hdiag]
    apply sub_le_sub_right
    apply (Finset.le_inf'_iff _ _).mpr
    intro i hi
    have hih : i ≤ h := Nat.le_of_lt_succ (mem_range.mp hi)
    apply le_min
    · refine le_trans ?_ (weighted_overlap_le_diagonal w hw p i (hih.trans hh))
      refine sum_le_sum fun m _ => sum_le_sum fun n _ => ?_
      change (if h ≤ H m n then c m * c n else 0) ≤ (if i ≤ H m n then c m * c n else 0)
      by_cases hreach : h ≤ H m n
      · rw [ite_eq_left hreach, ite_eq_left (hih.trans hreach)]
      · rw [ite_eq_right hreach]
        split_ifs
        · exact hweight m n
        · exact le_rfl
    · rw [← htotal]
      refine sum_le_sum fun m _ => sum_le_sum fun n _ => ?_
      change (if h ≤ H m n then c m * c n else 0) ≤ c m * c n
      split_ifs
      · exact le_rfl
      · exact hweight m n
  have hQ (h : ℕ) (hh : h < p - 1) : 0 ≤ Q (h + 1) - Q h := by
    apply sub_nonneg.mpr
    have hrem : (0 : ℝ) < ((p - (h + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < p - (h + 1) by omega)
    have hsub : ((p - (h + 1) : ℕ) : ℝ) ≤ ((p - h : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_left (Nat.le_succ h) p
    exact inv_anti₀ (mul_pos hρ (Real.sqrt_pos.2 (by positivity)))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hρ.le)
  have hweighted (m n : J → ℕ) (hm : m ∈ s) (hn : n ∈ s.erase m) :
      c m * c n / Real.sqrt (∑ j, (((m j : ℝ) - n j) * radius j) ^ 2) ≤
        c m * c n * Q 0 + ∑ h ∈ range (p - 1), high (h + 1) m n * (Q (h + 1) - Q h) := by
    have hmp := (mem_piAntidiag.mp hm).1
    have hnp := (mem_piAntidiag.mp (mem_of_mem_erase hn)).1
    have hlt : H m n < p := overlap_lt_degree_of_ne m n p hmp hnp (ne_of_mem_erase hn).symm
    have hden : 0 < ρ * Real.sqrt (2 * ((p - H m n : ℕ) : ℝ)) := by
      have : (0 : ℝ) < ((p - H m n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
      positivity
    have hscale := sqrt_scale_ge radius hρ hr hmp hnp (d := p - H m n)
      (by change p - H m n + H m n ≤ p; omega)
    have hdecomp :
        (∑ h ∈ range (p - 1), high (h + 1) m n * (Q (h + 1) - Q h)) =
          c m * c n * (Q (H m n) - Q 0) := by
      rw [← sum_range_sub Q, mul_sum]
      have hsubset : range (H m n) ⊆ range (p - 1) :=
        range_subset_range.mpr (by omega)
      refine (sum_subset hsubset ?_).symm.trans (sum_congr rfl ?_)
      · intro h _ hn'
        have hlt' : ¬ h + 1 ≤ H m n := by rw [mem_range] at hn'; omega
        rw [show high (h + 1) m n = 0 from ite_eq_right hlt', zero_mul]
      · intro h hh
        rw [show high (h + 1) m n = c m * c n from ite_eq_left (mem_range.mp hh)]
    calc
      _ ≤ c m * c n / (ρ * Real.sqrt (2 * ((p - H m n : ℕ) : ℝ))) :=
        div_le_div_of_nonneg_left (hweight m n) hden hscale
      _ = _ := by rw [hdecomp, div_eq_mul_inv]; change c m * c n * Q (H m n) = _; ring
  calc
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
        (c m * c n * Q 0 + ∑ h ∈ range (p - 1), high (h + 1) m n * (Q (h + 1) - Q h)) :=
      sum_le_sum fun m hm => sum_le_sum fun n hn => hweighted m n hm hn
    _ = (T - diagonal w p) * Q 0 +
          ∑ h ∈ range (p - 1), (∑ m ∈ s, ∑ n ∈ s.erase m, high (h + 1) m n) *
            (Q (h + 1) - Q h) := by
      simp only [sum_add_distrib, ← sum_mul, hmass]
      congr 1
      simp_rw [sum_comm (t := range (p - 1)), ← sum_mul]
    _ ≤ _ := by
      apply add_le_add_right
      apply sum_le_sum
      intro h hh
      have hp := mem_range.mp hh
      exact mul_le_mul_of_nonneg_right (htail (h + 1) (by omega)) (hQ h hp)

#print axioms weighted_inverse_scale_le_of_overlap

end D5.S3.Fourier.Concentration.OverlapPerturbationBudget
