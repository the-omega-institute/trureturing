/- GID: D5/S3/Arith/Erdos699DenominatorGap
   generality: G
   mirror-B: D5/B/S3/Arith/Erdos699DenominatorGap
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact integrality of an Erdos 699 column ratio forces a strict denominator gap. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Erdos699DenominatorGap

-- Source search: no exact original-parameter bound in repository D5 or pinned Mathlib.
/-- Integrality of the column ratio bounds the denominator against the divisor scale. -/
theorem erdos699_denominator_gap
    (n L R j m D k : ℤ)
    (hn : 8 ≤ n) (hR : 0 < R)
    (hm : 0 < m) (hmL : 2 * m < L) (hD : 0 < D)
    (hnLR : n - 1 = L * R) (hj : j = 1 + m * R)
    (hint : D * (n - j) * (n - j - 1) = k * (n - 1) * (n - 2)) :
    4 * (n - 2) < D * L ^ 2 := by
  have hn' : n = L * R + 1 := by omega
  have hRne : R ≠ 0 := ne_of_gt hR
  have hr : 0 < L - m := by omega
  have hs : 0 < L - 2 * m := by omega
  have hfactor :
      R * ((D * (L - m) ^ 2 - k * L ^ 2) * (n - 2) - D * (L - m) * m) = 0 := by
    rw [hn', hj] at hint
    rw [hn']
    linear_combination L * hint
  have hcore :
      (D * (L - m) ^ 2 - k * L ^ 2) * (n - 2) = D * (L - m) * m := by
    have hzero := (mul_eq_zero.mp hfactor).resolve_left hRne
    linear_combination hzero
  have hproduct : 0 < D * (L - m) * m := by positivity
  have hcoef : 0 < D * (L - m) ^ 2 - k * L ^ 2 := by
    by_contra h
    have hnonpos : D * (L - m) ^ 2 - k * L ^ 2 ≤ 0 := le_of_not_gt h
    have hmul := mul_nonpos_of_nonpos_of_nonneg hnonpos (show 0 ≤ n - 2 by omega)
    omega
  have hcoef_one : 1 ≤ D * (L - m) ^ 2 - k * L ^ 2 := by omega
  have hgap : n - 2 ≤ D * (L - m) * m := by
    have hmul := mul_le_mul_of_nonneg_right hcoef_one (show 0 ≤ n - 2 by omega)
    simpa only [one_mul, hcore] using hmul
  have hquad : 4 * ((L - m) * m) < L ^ 2 := by
    nlinarith [sq_pos_of_pos hs]
  have hquadD := mul_lt_mul_of_pos_left hquad hD
  calc
    4 * (n - 2) ≤ 4 * (D * (L - m) * m) :=
      mul_le_mul_of_nonneg_left hgap (by norm_num)
    _ = D * (4 * ((L - m) * m)) := by ring
    _ < D * L ^ 2 := hquadD

#print axioms erdos699_denominator_gap

end D5.S3.Arith.Erdos699DenominatorGap
