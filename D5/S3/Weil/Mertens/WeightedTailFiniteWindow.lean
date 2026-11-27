/- GID: D5/S3/Weil/Mertens/WeightedTailFiniteWindow
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/WeightedTailFiniteWindow
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Finite logarithmic weighted-tail bound with a right endpoint correction. -/

import D5.S3.Weil.Mertens.WeightedTailInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Mertens.WeightedTailFiniteWindow

open Real Set MeasureTheory
open D5.S3.Weil.Mertens.WeightedTailTransport (tail weightedTail)
open D5.S3.Weil.Mertens.WeightedTailInverse
  (a v inverse a_pos v_nonneg v_le_inv reciprocal_sqrt_eq_rpow integral_rpow_neg_three_halves)

/-- A lower bound on the weighted tail over a finite closed window controls the
normalized unweighted tail at its left endpoint, given a bound on the defect at
its right endpoint. -/
theorem neg_sqrt_mul_tail_le {k : ℝ → ℝ} {x B A D : ℝ}
    (hx : exp 1 ≤ x) (hxB : x ≤ B) (hA : 0 ≤ A)
    (hk : IntegrableOn k (Ioi x))
    (hW : ∀ t ∈ Icc x B, -A / (sqrt t * log t) ≤ weightedTail k t)
    (hB : -D / sqrt B ≤ tail k B - a B * weightedTail k B) :
    -sqrt x * tail k x ≤ A * (log x / (1 + log x) + (2 / log x) * (1 - sqrt x / sqrt B)) +
      D * sqrt x / sqrt B := by
  have he2 : (2 : ℝ) ≤ exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hx2 : 2 ≤ x := he2.trans hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hB0 : 0 < B := hx0.trans_le hxB
  have hlogx : 0 < log x := log_pos hx1
  have hsqrtx : 0 < sqrt x := sqrt_pos.2 hx0
  have hsqrtB : 0 < sqrt B := sqrt_pos.2 hB0
  have hlogx1 : 0 < 1 + log x := by positivity

  obtain ⟨hIx, hQx⟩ := inverse hx2 hk
  obtain ⟨hIB, hQB⟩ := inverse (hx2.trans hxB) (hk.mono_set (Ioi_subset_Ioi hxB))
  have hfinite : IntegrableOn (fun t => v t * weightedTail k t) (Ioc x B) :=
    hIx.mono_set Ioc_subset_Ioi_self
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hfinite hIB
  rw [Ioc_union_Ioi_eq_Ioi hxB] at hsplit
  have htail_eq :
      tail k x = a x * weightedTail k x + (∫ t in Ioc x B, v t * weightedTail k t) +
        (tail k B - a B * weightedTail k B) := by
    linarith only [hQx, hsplit, hQB]

  have hpoint : ∀ t ∈ Ioc x B,
      (-A / log x) * t ^ (-(3 / 2 : ℝ)) ≤ v t * weightedTail k t := by
    intro t ht
    have ht0 : 0 < t := hx0.trans ht.1
    have hlogxt : log x ≤ log t := log_le_log hx0 ht.1.le
    have hlogt : 0 < log t := hlogx.trans_le hlogxt
    have hst : 0 < sqrt t := sqrt_pos.2 ht0
    have ht1 : 1 < t := hx1.trans ht.1
    have hcompare : v t / (sqrt t * log t) ≤ t ^ (-(3 / 2 : ℝ)) / log x := by
      calc
        v t / (sqrt t * log t) ≤ (1 / t) / (sqrt t * log t) :=
          div_le_div_of_nonneg_right (v_le_inv ht1) (mul_nonneg hst.le hlogt.le)
        _ ≤ (1 / t) / (sqrt t * log x) :=
          div_le_div_of_nonneg_left (one_div_nonneg.mpr ht0.le) (mul_pos hst hlogx)
            (mul_le_mul_of_nonneg_left hlogxt hst.le)
        _ = ((1 / t) / sqrt t) / log x := by simp only [div_div, mul_assoc]
        _ = t ^ (-(3 / 2 : ℝ)) / log x := by rw [reciprocal_sqrt_eq_rpow ht0]
    calc
      (-A / log x) * t ^ (-(3 / 2 : ℝ)) = -A * (t ^ (-(3 / 2 : ℝ)) / log x) := by ring
      _ ≤ -A * (v t / (sqrt t * log t)) :=
        mul_le_mul_of_nonpos_left hcompare (neg_nonpos.mpr hA)
      _ = v t * (-A / (sqrt t * log t)) := by ring
      _ ≤ v t * weightedTail k t :=
        mul_le_mul_of_nonneg_left (hW t (Ioc_subset_Icc_self ht)) (v_nonneg ht1)

  have hpow : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx0
  have hpowFinite := hpow.mono_set (Ioc_subset_Ioi_self : Ioc x B ⊆ Ioi x)
  have hmass : (∫ t in Ioc x B, t ^ (-(3 / 2 : ℝ))) = 2 / sqrt x - 2 / sqrt B := by
    have hadd := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hpowFinite
      (hpow.mono_set (Ioi_subset_Ioi hxB))
    rw [Ioc_union_Ioi_eq_Ioi hxB, integral_rpow_neg_three_halves hx0,
      integral_rpow_neg_three_halves hB0] at hadd
    linarith only [hadd]
  have hint : (-A / log x) * (2 / sqrt x - 2 / sqrt B) ≤
      ∫ t in Ioc x B, v t * weightedTail k t := by
    rw [← hmass, ← integral_const_mul]
    exact setIntegral_mono_on (hpowFinite.const_mul (-A / log x)) hfinite measurableSet_Ioc hpoint

  have hleft : (-A / sqrt x) * (log x / (1 + log x)) ≤ a x * weightedTail k x := by
    calc
      (-A / sqrt x) * (log x / (1 + log x)) = a x * (-A / (sqrt x * log x)) := by
        unfold a
        field_simp [hsqrtx.ne', hlogx.ne', hlogx1.ne'] <;> ring
      _ ≤ a x * weightedTail k x :=
        mul_le_mul_of_nonneg_left (hW x ⟨le_rfl, hxB⟩) (a_pos hx1).le
  have htail_le : (-A / sqrt x) * (log x / (1 + log x)) +
      (-A / log x) * (2 / sqrt x - 2 / sqrt B) + (-D / sqrt B) ≤ tail k x := by
    rw [htail_eq]
    exact add_le_add (add_le_add hleft hint) hB
  calc
    -sqrt x * tail k x ≤ -sqrt x * ((-A / sqrt x) * (log x / (1 + log x)) +
        (-A / log x) * (2 / sqrt x - 2 / sqrt B) + (-D / sqrt B)) :=
      mul_le_mul_of_nonpos_left htail_le (neg_nonpos.mpr hsqrtx.le)
    _ = _ := by field_simp [hsqrtx.ne', hsqrtB.ne', hlogx.ne', hlogx1.ne'] <;> ring

#print axioms neg_sqrt_mul_tail_le

end D5.S3.Weil.Mertens.WeightedTailFiniteWindow
