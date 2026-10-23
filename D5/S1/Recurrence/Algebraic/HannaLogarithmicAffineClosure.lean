/- GID: D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Hanna's logarithmic integer-series closure under every positive affine extraction. -/

import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

open PowerSeries Finset
open D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod (T)
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

namespace D5.S1.Recurrence.Algebraic.HannaLogarithmicAffineClosure

private noncomputable def affineColumn (k m b : ℕ) : PowerSeries ℤ :=
  ∑ j ∈ range (k + 1),
    C ((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * (j : ℤ) ^ b) *
      ((1 : PowerSeries ℤ) + X) ^ (j ^ m)

private theorem egf_affine_column (k m b : ℕ) :
    egf (fun n => (q k (m * n + b) : ℚ)) =
      ∑ j ∈ range (k + 1),
        C ((-1 : ℚ) ^ (k - j) * (k.choose j : ℚ) * (j : ℚ) ^ b) *
          (exp ℚ) ^ (j ^ m) := by
  ext n
  rw [egf, coeff_mk, map_sum]
  have hi := congrArg (Int.castRingHom ℚ)
    (D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion
      (m * n + b) k)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at hi
  have hq : (q k (m * n + b) : ℚ) =
      (k.factorial : ℚ) * (Nat.stirlingSecond (m * n + b) k : ℚ) := by simp [q]
  rw [hq, hi, sum_div]
  apply sum_congr rfl
  intro j hj
  simp only [coeff_C_mul, exp_pow_eq_rescale_exp, coeff_rescale, coeff_exp]
  simp only [Nat.cast_pow, pow_add, pow_mul]
  simp
  ring

private theorem transform_affine_column (k m b : ℕ) :
    logarithmicTransform (fun n => (q k (m * n + b) : ℚ)) =
      (affineColumn k m b).map (Int.castRingHom ℚ) := by
  rw [logarithmicTransform, egf_affine_column]
  rw [← coe_substAlgHom HasSubst.log]
  simp only [map_sum, map_mul, map_pow]
  simp only [coe_substAlgHom, subst_C]
  have he : PowerSeries.subst (log ℚ) (exp ℚ) = (1 : PowerSeries ℚ) + X :=
    subst_exp_log
  erw [he]
  simp [affineColumn]

private theorem transform_T_affine (a : ℕ → ℤ) (m b r : ℕ) :
    coeff r (logarithmicTransform (fun n => (T a (m * n + b) : ℚ))) =
      ((∑ k ∈ range (m * r + b + 1), a k * coeff r (affineColumn k m b) : ℤ) : ℚ) := by
  rw [coeff_transform]
  have he (n : ℕ) (hn : n ∈ range (r + 1)) :
      (T a (m * n + b) : ℚ) / (n.factorial : ℚ) * coeff r (log ℚ ^ n) =
        ∑ k ∈ range (m * r + b + 1), (a k : ℚ) *
          ((q k (m * n + b) : ℚ) / (n.factorial : ℚ) * coeff r (log ℚ ^ n)) := by
    have hnr : n ≤ r := Nat.le_of_lt_succ (mem_range.mp hn)
    rw [T_window a
      (Nat.add_le_add_right (Nat.mul_le_mul_left m hnr) b)]
    simp only [Int.cast_sum, Int.cast_mul, sum_div, sum_mul]
    apply sum_congr rfl
    intro k hk
    ring
  rw [sum_congr rfl he, sum_comm]
  simp only [← mul_sum]
  push_cast
  apply sum_congr rfl
  intro k hk
  rw [← coeff_transform, transform_affine_column, coeff_map]
  rfl

/-- The full arithmetic-subsequence assertion in OEIS A167540. -/
theorem result (K : Type*) [Field K] [CharZero K] (L : ℕ → K)
    (h : IntegralSeries (logarithmicTransform L)) (m : ℕ) (hm : 0 < m) (b : ℕ) :
    IntegralSeries (logarithmicTransform (fun n => L (m * n + b))) := by
  obtain ⟨a, ha⟩ := reconstruction L h
  intro r
  refine ⟨∑ k ∈ range (m * r + b + 1), a k * coeff r (affineColumn k m b), ?_⟩
  have he := congrArg (algebraMap ℚ K) (transform_T_affine a m b r)
  rw [← coeff_map, map_transform] at he
  simpa only [map_intCast, ← ha] using he

#print axioms result

end D5.S1.Recurrence.Algebraic.HannaLogarithmicAffineClosure
