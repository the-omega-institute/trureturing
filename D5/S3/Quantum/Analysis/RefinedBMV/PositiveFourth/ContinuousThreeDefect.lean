/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/ContinuousThreeDefect
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real-exponent confluent differences agree with the three-node sign polynomial. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FourthGapPolynomial

/-! The existing cleared polynomial also computes the real-exponent defect
on a tuple with one repeated node and two other distinct nodes. -/

noncomputable section

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

/-- Confluent four-node power defect on the tuple (a,a,b,c). -/
def confluentTwoOneOne (p a b c : ℝ) : ℝ :=
  let ab := (b ^ (p+3) - a ^ (p+3)) / (b-a)
  let bc := (c ^ (p+3) - b ^ (p+3)) / (c-b)
  let abc := (bc-ab) / (c-a)
  let aab := (ab - (p+3) * a ^ (p+2)) / (b-a)
  (abc-aab) / (c-a) -
    ((p+1)*(p+2)*(p+3)/6) * (a ^ (p/4))^2 * b ^ (p/4) * c ^ (p/4)

/-- The clearing identity holds for real degrees on pairwise distinct positive nodes. -/
theorem twoOneOnePolynomial_eq_confluent (p a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    twoOneOnePolynomial p a b c (a ^ (p/4)) (b ^ (p/4)) (c ^ (p/4)) =
      6 * ((a-b)^2*(a-c)^2*(b-c)) * confluentTwoOneOne p a b c := by
  have hfour (x : ℝ) (hx : 0 < x) : (x ^ (p/4))^4 = x ^ p := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    norm_num
  have hshift (x : ℝ) (hx : 0 < x) (n : ℕ) :
      x ^ (p + (n : ℝ)) = x^n * (x ^ (p/4))^4 := by
    rw [Real.rpow_add hx, Real.rpow_natCast, hfour x hx, mul_comm]
  unfold twoOneOnePolynomial confluentTwoOneOne
  rw [show a ^ (p+3) = a^3 * (a ^ (p/4))^4 from hshift a ha 3,
    show b ^ (p+3) = b^3 * (b ^ (p/4))^4 from hshift b hb 3,
    show c ^ (p+3) = c^3 * (c ^ (p/4))^4 from hshift c hc 3,
    show a ^ (p+2) = a^2 * (a ^ (p/4))^4 from hshift a ha 2]
  field_simp [sub_ne_zero.mpr hab.symm, sub_ne_zero.mpr hac.symm, sub_ne_zero.mpr hbc.symm]
  ring

#print axioms twoOneOnePolynomial_eq_confluent

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
