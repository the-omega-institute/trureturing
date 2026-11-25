/- GID: D5/S3/Arith/Divisors/ErdosNicolas/GapMajorant
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Adjacent-gap Cauchy majorants for finite ordered point sets. -/

import D5.S3.Arith.Divisors.ErdosNicolas.PairChecker
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The ordered-index form keeps the geometric and arithmetic bounds separate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

private theorem pairSum_mono {S T : Finset ℕ} (hST : S ⊆ T) : pairSum S ≤ pairSum T := by
  unfold pairSum
  calc
    _ ≤ ∑ d ∈ S, ∑ e ∈ T,
        if d < e then ((e - d : ℕ) : ℚ)⁻¹ else 0 := by
      apply sum_le_sum
      intro d _
      exact sum_le_sum_of_subset_of_nonneg hST (by
        intro e _ _
        split_ifs <;> positivity)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hST (by
      intro d _ _
      exact sum_nonneg fun e _ => by split_ifs <;> positivity)

theorem hHat_mono {n N : ℕ} (hnN : n ∣ N) (hN : 0 < N) : hHat n ≤ hHat N :=
  pairSum_mono (Nat.divisors_subset_of_dvd hN.ne' hnN)

/-- Reciprocal gaps of an ordered sequence, with one term for each index pair. -/
def indexPairSum (t : ℕ) (d : ℕ → ℚ) : ℚ :=
  ∑ i ∈ range t, ∑ j ∈ Ico (i + 1) t, (d j - d i)⁻¹

/-- The weight of an adjacent gap in the sum of the Cauchy majorants. -/
def gapCoefficient (t r : ℕ) : ℚ :=
  ∑ i ∈ range t, ∑ j ∈ Ico (i + 1) t,
    if i ≤ r ∧ r < j then (((j - i : ℕ) : ℚ) ^ 2)⁻¹ else 0

/-- The finite harmonic-mean inequality, without square roots. -/
private theorem reciprocal_sum_bound {ι : Type*} (s : Finset ι) (g : ι → ℚ)
    (hs : s.Nonempty) (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, g i)⁻¹ ≤ (∑ i ∈ s, (g i)⁻¹) / (s.card : ℚ) ^ 2 := by
  have hc : (0 : ℚ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : 0 < ∑ i ∈ s, g i := sum_pos hg hs
  have h := sq_sum_div_le_sum_sq_div s (fun _ => (1 : ℚ)) hg
  simp only [sum_const, nsmul_eq_mul, mul_one, one_pow, one_div] at h
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  apply (div_le_iff₀ hsum).mp at h
  rw [inv_mul_eq_div, div_le_iff₀ hsum]
  nlinarith

/-- Equation (23): a pair gap is bounded by the reciprocal adjacent gaps it spans. -/
private theorem adjacent_gap_bound (d : ℕ → ℚ) {i j : ℕ} (hij : i < j)
    (hd : ∀ r ∈ Ico i j, d r < d (r + 1)) :
    (d j - d i)⁻¹ ≤
      (∑ r ∈ Ico i j, (d (r + 1) - d r)⁻¹) / ((j - i : ℕ) : ℚ) ^ 2 := by
  have hs : (Ico i j).Nonempty := ⟨i, by simp [hij]⟩
  have h := reciprocal_sum_bound (Ico i j) (fun r => d (r + 1) - d r) hs
    (fun r hr => sub_pos.mpr (hd r hr))
  simpa only [sum_Ico_sub d hij.le, Nat.card_Ico] using h

/-- Summing equation (23) and collecting the coefficient of each adjacent gap. -/
private theorem indexPairSum_le_gapCoefficients (t : ℕ) (d : ℕ → ℚ)
    (hd : ∀ r, r + 1 < t → d r < d (r + 1)) :
    indexPairSum t d ≤
      ∑ r ∈ range t, gapCoefficient t r * (d (r + 1) - d r)⁻¹ := by
  let F : ℕ → ℕ → ℕ → ℚ := fun i j r =>
    (if i ≤ r ∧ r < j then (((j - i : ℕ) : ℚ) ^ 2)⁻¹ else 0) *
      (d (r + 1) - d r)⁻¹
  have hpair (i : ℕ) (hi : i ∈ range t) (j : ℕ) (hj : j ∈ Ico (i + 1) t) :
      (d j - d i)⁻¹ ≤ ∑ r ∈ range t, F i j r := by
    have hij : i < j := by have := (mem_Ico.mp hj).1; omega
    have hjt : j < t := (mem_Ico.mp hj).2
    have hb := adjacent_gap_bound d hij (fun r hr => hd r (by
      have := mem_Ico.mp hr
      omega))
    have heq : (∑ r ∈ Ico i j, (d (r + 1) - d r)⁻¹) /
        ((j - i : ℕ) : ℚ) ^ 2 = ∑ r ∈ range t, F i j r := by
      rw [div_eq_mul_inv, sum_mul]
      calc
        _ = ∑ r ∈ Ico i j, F i j r := by
          apply sum_congr rfl
          intro r hr
          simp only [F, (mem_Ico.mp hr).1, (mem_Ico.mp hr).2, and_self, ↓reduceIte]
          ring
        _ = _ := by
          apply sum_subset
          · intro r hr
            exact mem_range.mpr (lt_trans (mem_Ico.mp hr).2 hjt)
          · intro r _ hr
            have hn : ¬(i ≤ r ∧ r < j) := by simpa only [mem_Ico] using hr
            simp [F, hn]
    exact heq ▸ hb
  unfold indexPairSum
  calc
    _ ≤ ∑ i ∈ range t, ∑ j ∈ Ico (i + 1) t, ∑ r ∈ range t, F i j r := by
      exact sum_le_sum fun i hi => sum_le_sum fun j hj => hpair i hi j hj
    _ = ∑ i ∈ range t, ∑ r ∈ range t, ∑ j ∈ Ico (i + 1) t, F i j r := by
      exact sum_congr rfl fun _ _ => sum_comm
    _ = ∑ r ∈ range t, ∑ i ∈ range t, ∑ j ∈ Ico (i + 1) t, F i j r := sum_comm
    _ = _ := by
      simp only [gapCoefficient, sum_mul, F]

/-- Count of intervals of length `k` crossing adjacent-gap position `r`. -/
def gapMultiplicity (t r k : ℕ) : ℕ :=
  min k (min (r + 1) (min (t - 1 - r) (t - k)))

private theorem gapMultiplicity_eq (t r k : ℕ) (hr : r < t)
    (hk : 1 ≤ k) (hkt : k < t) :
    gapMultiplicity t r k = min (t - k) (r + 1) - (r + 1 - k) := by
  unfold gapMultiplicity
  omega

/-- Reindex all increasing index pairs by their length and starting position. -/
private theorem sum_indexPairs_by_length {M : Type*} [AddCommMonoid M] (t : ℕ)
    (F : ℕ → ℕ → M) :
    (∑ i ∈ range t, ∑ j ∈ Ico (i + 1) t, F i j) =
      ∑ k ∈ Ico 1 t, ∑ i ∈ range (t - k), F i (i + k) := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2 - x.1, x.1⟩)
    (fun x => ⟨x.2, x.2 + x.1⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [mem_sigma, mem_range, mem_Ico, Sigma.forall]
    omega
  · simp only [mem_sigma, mem_range, mem_Ico, Sigma.forall]
    omega
  · intro x hx
    have hx' := mem_sigma.mp hx
    have hlt := mem_Ico.mp hx'.2
    refine Sigma.ext rfl ?_
    exact heq_of_eq (by dsimp; omega)
  · intro x hx
    apply Sigma.ext (by dsimp; omega)
    rfl
  · intro x hx
    have hx' := mem_sigma.mp hx
    have hlt := mem_Ico.mp hx'.2
    dsimp
    congr 1
    omega

/-- The number of possible starting positions is exactly the four-way minimum. -/
private theorem interval_crossing_count (t r k : ℕ) (hr : r < t)
    (hk : 1 ≤ k) (hkt : k < t) :
    ((range (t - k)).filter fun i => i ≤ r ∧ r < i + k).card =
      gapMultiplicity t r k := by
  have heq : (range (t - k)).filter (fun i => i ≤ r ∧ r < i + k) =
      Ico (r + 1 - k) (min (t - k) (r + 1)) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [heq, Nat.card_Ico, gapMultiplicity_eq t r k hr hk hkt]

/-- Closed multiplicities in the collected adjacent-gap coefficient. -/
private theorem gapCoefficient_eq (t r : ℕ) (hr : r < t) :
    gapCoefficient t r = ∑ k ∈ Ico 1 t,
      (gapMultiplicity t r k : ℚ) * (((k : ℚ) ^ 2)⁻¹) := by
  unfold gapCoefficient
  rw [sum_indexPairs_by_length]
  apply sum_congr rfl
  intro k hk
  have hcross := interval_crossing_count t r k hr (mem_Ico.mp hk).1 (mem_Ico.mp hk).2
  simp only [Nat.add_sub_cancel_left]
  rw [← sum_filter, sum_const, nsmul_eq_mul, hcross]

/-- Integer numerator of an adjacent-gap coefficient, rounded before summation. -/
def gapWeight (Q t r : ℕ) : ℕ :=
  ∑ k ∈ Ico 1 t, gapMultiplicity t r k * ceilDiv Q (k ^ 2)

/-- Rounding the length coefficients upward preserves the full adjacent-gap bound. -/
private theorem gapCoefficient_rounding (Q t r : ℕ) (hr : r < t) :
    (Q : ℚ) * gapCoefficient t r ≤ gapWeight Q t r := by
  rw [gapCoefficient_eq t r hr, mul_sum]
  unfold gapWeight
  push_cast
  apply sum_le_sum
  intro k hk
  have hkp : 0 < k ^ 2 := pow_pos (by have := (mem_Ico.mp hk).1; omega) _
  have hb := reciprocal_le_ceil Q (k ^ 2)
  push_cast at hb
  have hm : (0 : ℚ) ≤ gapMultiplicity t r k := Nat.cast_nonneg _
  nlinarith

/-- The integer adjacent-gap upper numerator in equation (24). -/
def gapIndexUpper (Q t : ℕ) (d : ℕ → ℕ) : ℕ :=
  ∑ r ∈ range (t - 1), ceilDiv (gapWeight Q t r) (d (r + 1) - d r)

/-- Equation (24), with every integer rounding direction checked. -/
private theorem gapIndexUpper_sound (Q t : ℕ) (d : ℕ → ℕ)
    (hd : ∀ r, r + 1 < t → d r < d (r + 1)) :
    (Q : ℚ) * indexPairSum t (fun i => (d i : ℚ)) ≤ gapIndexUpper Q t d := by
  have hm := indexPairSum_le_gapCoefficients t (fun i => (d i : ℚ))
    (fun r hr => by exact_mod_cast hd r hr)
  have hq : (0 : ℚ) ≤ Q := Nat.cast_nonneg _
  have hb := mul_le_mul_of_nonneg_left hm hq
  have hcoeff (r : ℕ) (hr : r ∈ range t) :
      (Q : ℚ) * (gapCoefficient t r * ((d (r + 1) : ℚ) - d r)⁻¹) ≤
        if r + 1 < t then
          (ceilDiv (gapWeight Q t r) (d (r + 1) - d r) : ℚ) else 0 := by
    by_cases hrt : r + 1 < t
    · rw [if_pos hrt]
      have hd' := hd r hrt
      have hw := gapCoefficient_rounding Q t r (mem_range.mp hr)
      have hg : (0 : ℚ) < (d (r + 1) : ℚ) - d r :=
        sub_pos.mpr (by exact_mod_cast hd')
      have hh := mul_le_mul_of_nonneg_right hw (inv_nonneg.mpr hg.le)
      have hc := reciprocal_le_ceil (gapWeight Q t r) (d (r + 1) - d r)
      rw [Nat.cast_sub hd'.le] at hc
      nlinarith
    · rw [if_neg hrt]
      have he : gapCoefficient t r = 0 := by
        unfold gapCoefficient
        apply sum_eq_zero
        intro i hi
        apply sum_eq_zero
        intro j hj
        have hjt := (mem_Ico.mp hj).2
        have hn : ¬(i ≤ r ∧ r < j) := by omega
        simp [hn]
      simp [he]
  calc
    _ ≤ (Q : ℚ) *
        ∑ r ∈ range t, gapCoefficient t r * ((d (r + 1) : ℚ) - d r)⁻¹ := hb
    _ ≤ ∑ r ∈ range t, if r + 1 < t then
        (ceilDiv (gapWeight Q t r) (d (r + 1) - d r) : ℚ) else 0 := by
      rw [mul_sum]
      exact sum_le_sum hcoeff
    _ = _ := by
      unfold gapIndexUpper
      push_cast
      rw [← sum_filter]
      congr 1
      ext r
      simp only [mem_filter, mem_range]
      omega

/-- An increasing enumeration identifies the geometric index sum with `pairSum`. -/
theorem pairSum_image_eq_indexPairSum (t : ℕ) (d : ℕ → ℕ)
    (hd : ∀ i j, i < j → j < t → d i < d j) :
    pairSum ((range t).image d) = indexPairSum t (fun i => (d i : ℚ)) := by
  have hinj : Set.InjOn d (range t) := by
    intro i hi j hj he
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim ((hd i j h (mem_range.mp hj)).ne he)
    · exact h
    · exact False.elim ((hd j i h (mem_range.mp hi)).ne he.symm)
  have hiff (i j : ℕ) (hi : i ∈ range t) (hj : j ∈ range t) :
      d i < d j ↔ i < j := by
    rcases lt_trichotomy i j with h | rfl | h
    · exact iff_of_true (hd i j h (mem_range.mp hj)) h
    · simp
    · exact iff_of_false (not_lt_of_ge (hd j i h (mem_range.mp hi)).le)
        (not_lt_of_ge h.le)
  unfold pairSum indexPairSum
  simp only [sum_image hinj]
  apply sum_congr rfl
  intro i hi
  calc
    _ = ∑ j ∈ range t, if i < j then ((d j : ℚ) - d i)⁻¹ else 0 := by
      apply sum_congr rfl
      intro j hj
      simp only [hiff i j hi hj]
      split_ifs with hij
      · rw [Nat.cast_sub (hd i j hij (mem_range.mp hj)).le]
      · rfl
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      omega

/-- A complete ordered divisor enumeration gives the adjacent-gap upper bound. -/
theorem hHat_le_gapIndexUpper {n Q t : ℕ} {d : ℕ → ℕ}
    (hd : ∀ i j, i < j → j < t → d i < d j)
    (he : (range t).image d = n.divisors) :
    (Q : ℚ) * hHat n ≤ gapIndexUpper Q t d := by
  have hb := gapIndexUpper_sound Q t d (fun r hr => hd r (r + 1) (by omega) hr)
  rw [← pairSum_image_eq_indexPairSum t d hd, he] at hb
  exact hb

/-- One certified upper corner and a lower divisor count certify the entire box. -/
theorem hHat_lt_of_upper_corner {n N Q U lower : ℕ}
    (hQ : 0 < Q) (hN : 0 < N) (hnN : n ∣ N)
    (hupper : (Q : ℚ) * hHat N ≤ U) (hlower : lower ≤ n.divisors.card)
    (hstrict : U < Q * lower) : hHat n < (n.divisors.card : ℚ) := by
  have hmono := hHat_mono hnN hN
  have hq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hs : (U : ℚ) < (Q : ℚ) * lower := by exact_mod_cast hstrict
  have hl : (lower : ℚ) ≤ n.divisors.card := by exact_mod_cast hlower
  nlinarith

#print axioms adjacent_gap_bound

#print axioms pairSum_mono
#print axioms hHat_mono

end D5.S3.Arith.ErdosNicolas
