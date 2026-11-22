/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactPositiveMoments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational degree-six moment bound for the compact mixed derivative. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterShortGapNormalization

/-! # Degree-six positive-moment bound for the refined BMV kernel -/

open scoped BigOperators

namespace RefinedBMV.PositiveCenter

noncomputable section

/-- The marginal expectation of `(2 + h - X)^j * exp (t * X)` for `h = 3 / p`. -/
def compactPositiveMoment (p j : ℕ) (t : ℝ) : ℝ :=
  let h := 3 / (p : ℝ)
  (∑ i ∈ Finset.range (p + 1),
    (↑(p + 1 - i) : ℝ) * Real.exp ((h * i - 1) * t) * (2 + h - (h * i - 1)) ^ j) /
    ((DimThree.gaps p).length : ℝ)

/-- The degree-six lower bound for the joint exponential moment. -/
def compositionMomentSixth (p : ℕ) (u v : ℝ) : ℝ :=
  let h := 3 / (p : ℝ)
  let a := u / 2
  let t := v - a
  (h * a / Real.sinh (h * a)) *
    (compactPositiveMoment p 0 t + a ^ 2 / 6 * compactPositiveMoment p 2 t +
      a ^ 4 / 120 * compactPositiveMoment p 4 t +
      (287 / 1458000) * a ^ 6 * compactPositiveMoment p 6 t)

private theorem sixthPolynomial_lt_sinh_div {z : ℝ} (hz : 0 < z) :
    1 + z ^ 2 / 6 + z ^ 4 / 120 + (287 / 1458000) * z ^ 6 < Real.sinh z / z := by
  have hpartial := sum_le_hasSum (Finset.range 4)
    (fun n _ ↦ by positivity : ∀ n ∉ Finset.range 4,
      0 ≤ z ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) (Real.hasSum_sinh z)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hpartial
  apply (lt_div_iff₀ hz).2
  have hstrict := mul_lt_mul_of_pos_right
    (show (287 / 1458000 : ℝ) < 1 / 5040 by norm_num) (pow_pos hz 7)
  nlinarith only [hpartial, hstrict]

/-- Strict degree-six lower bound for the actual joint exponential moment. -/
theorem compositionMomentSixth_lt {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) (v : ℝ) :
    compositionMomentSixth p u v < 1 + compositionMoment p u v := by
  let h := 3 / (p : ℝ)
  let a := u / 2
  let q := h * a / Real.sinh (h * a)
  let t := v - a
  let n (i : ℕ) := p + 1 - i
  let X (i : ℕ) := h * i - 1
  let w (i : ℕ) := (n i : ℝ) * Real.exp (X i * t)
  let z (i : ℕ) := (n i : ℝ) * (h * a)
  let S := Finset.range (p + 1)
  let N := ((DimThree.gaps p).length : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := div_pos (by norm_num) hpR
  have ha : 0 < a := half_pos hu
  have hq : 0 < q := div_pos (mul_pos hh ha) (Real.sinh_pos_iff.mpr (mul_pos hh ha))
  have htotal : h * (p : ℝ) = 3 := div_mul_cancel₀ _ hpR.ne'
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast (DimThree.word_counts_all p).2.1
  have hfinite : compositionMomentSixth p u v =
      (∑ i ∈ S, q * w i * (1 + (a * (2 + h - X i)) ^ 2 / 6 +
        (a * (2 + h - X i)) ^ 4 / 120 + (287 / 1458000) * (a * (2 + h - X i)) ^ 6)) /
        N := by
    change q * ((∑ i ∈ S, w i * (2 + h - X i) ^ 0) / N +
      a ^ 2 / 6 * ((∑ i ∈ S, w i * (2 + h - X i) ^ 2) / N) +
      a ^ 4 / 120 * ((∑ i ∈ S, w i * (2 + h - X i) ^ 4) / N) +
      (287 / 1458000) * a ^ 6 * ((∑ i ∈ S, w i * (2 + h - X i) ^ 6) / N)) = _
    simp only [← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfinite, compositionMoment_eq_conditioned]
  apply div_lt_div_of_pos_right _ hN
  apply Finset.sum_lt_sum_of_nonempty (by simp [S])
  intro i hi
  have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hnpos : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by dsimp [n]; omega)
  have hncast : (n i : ℝ) = (p : ℝ) + 1 - i := by
    dsimp only [n]
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hz : z i = a * (2 + h - X i) := by
    dsimp only [z, X]
    rw [hncast]
    linear_combination a * htotal
  have hexp : Real.exp (X i * v) * Real.exp (-a * X i) = Real.exp (X i * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [t]
    ring
  rw [← hz, show u = 2 * a by dsimp only [a]; ring,
    compositionGap_conditional_sum hip hh ha htotal]
  change _ < Real.exp (X i * v) *
    ((n i : ℝ) * Real.exp (-a * X i) * q * (Real.sinh (z i) / z i))
  calc
    _ < q * w i * (Real.sinh (z i) / z i) :=
      mul_lt_mul_of_pos_left (sixthPolynomial_lt_sinh_div (mul_pos hnpos (mul_pos hh ha)))
        (mul_pos hq (mul_pos hnpos (Real.exp_pos _)))
    _ = _ := by
      dsimp only [w]
      rw [← hexp]
      ring

/-- A nonnegative degree-six comparison forces the actual mixed derivative to be negative. -/
theorem logKernel_mixed_neg_of_sixth {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hv : 1 ≤ v)
    (hcompare : 0 ≤ compactMixedQ p u v - compactMixedT p u v (compositionMomentSixth p u v)) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hT := compactMixedT_strictAnti hp hu hv (compositionMomentSixth_lt hp hu v)
  have hneg : compactMixedT p u v (1 + compositionMoment p u v) - compactMixedQ p u v < 0 :=
    sub_neg.mpr (hT.trans_le (sub_nonneg.mp hcompare))
  have hnorm : 0 < Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) :=
    Real.sqrt_pos.mpr (mul_pos (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
      (compositionMoment_marginal_pos hp (neg_ne_zero.mpr (hu.trans huv).ne')))
  rw [← logKernel_mixed_eq_compactMixed hp hu huv] at hneg
  exact neg_of_mul_neg_right hneg hnorm.le

#print axioms compositionMomentSixth_lt
#print axioms logKernel_mixed_neg_of_sixth

end

end RefinedBMV.PositiveCenter
