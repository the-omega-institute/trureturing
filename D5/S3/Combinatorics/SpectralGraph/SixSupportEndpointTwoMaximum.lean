/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointTwoMaximum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportEndpointTwoMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real maximum-exponent bound for the endpoint-two surface. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportSharpMiddle
import Mathlib.Tactic

/-! The original supplied 88 positive coefficients, from the complete
endpoint-two-maximum-tail source at blob819c660aaf4a429ba0d0e7ad9ca302be1df67048.
They describe an exact polynomial identity on the entire real domain;
no exponent enumeration or numerical spectral premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoMaximum
open SixSupportClassificationAlgebra

private def expansion (m t v : ℝ) : ℝ :=
  (17568+45392*m+41600*m^2+18120*m^3+3986*m^4+413*m^5+15*m^6)+
  (13008+22464*m+14200*m^2+4120*m^3+545*m^4+26*m^5)*v^1+
  (2616+3108*m+1286*m^2+219*m^3+13*m^4)*v^2+
  (156+116*m+27*m^2+2*m^3)*v^3+
  (59072+155168*m+144464*m^2+63824*m^3+14180*m^4+1466*m^5+51*m^6)*t^1+
  (45792+80528*m+52120*m^2+15548*m^3+2120*m^4+104*m^5)*t^1*v^1+
  (9552+11704*m+5036*m^2+898*m^3+56*m^4)*t^1*v^2+
  (584+460*m+114*m^2+9*m^3)*t^1*v^3+
  (74496+194048*m+181536*m^2+80912*m^3+18096*m^4+1856*m^5+60*m^6)*t^2+
  (55360+98880*m+65336*m^2+19948*m^3+2778*m^4+137*m^5)*t^2*v^1+
  (11672+14716*m+6554*m^2+1213*m^3+78*m^4)*t^2*v^2+
  (724+600*m+157*m^2+13*m^3)*t^2*v^3+
  (36864+93696*m+88064*m^2+40096*m^3+9296*m^4+1008*m^5+36*m^6)*t^3+
  (23424+42560*m+28816*m^2+9064*m^3+1304*m^4+66*m^5)*t^3*v^1+
  (4784+6200*m+2852*m^2+546*m^3+36*m^4)*t^3*v^2+
  (296+256*m+70*m^2+6*m^3)*t^3*v^3

private theorem expansion_positive (m t v : ℝ) (hm : 0 ≤ m)
    (ht : 0 ≤ t) (hv : 0 ≤ v) : 0 < expansion m t v := by
  unfold expansion
  positivity

private theorem identity (m t v : ℝ) (ht : 1+t ≠ 0) :
    (1+t)^3*h (4+m) ((4+m+(2*(4+m)-2)*t)/(1+t)) (3*(4+m)-4+v) 2 =
      expansion m t v := by
  rw [h_eq_value]
  dsimp [value,expansion]
  field_simp
  <;> ring

/-- Every ordered real triple with minimum at least four and maximum
at least3a-4 has a strictly positive endpoint-two value. All boundaries included. -/
theorem result (a b c : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : 3*a-4 ≤ c) : 0 < h a b c 2 := by
  by_cases hb : 2*a-2 ≤ b
  · have hs : SixSupportSharpMiddle.alpha < (4 : ℝ) := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
      have hn := Real.sqrt_nonneg (13 : ℝ)
      dsimp [SixSupportSharpMiddle.alpha]
      nlinarith
    have hz := SixSupportSharpMiddle.result a b c (hs.le.trans ha) hb hbc
    have hn : h a b c 2 ≠ 0 := by
      intro h
      have he := hz.2.mp h
      linarith [he.1]
    exact lt_of_le_of_ne hz.1 (Ne.symm hn)
  · have hd : 0 < 2*a-2-b := by linarith
    let t := (b-a)/(2*a-2-b)
    have ht : 0 ≤ t := div_nonneg (by linarith) hd.le
    have ht0 : 0 < 1+t := by linarith
    have hi := identity (a-4) t (c-(3*a-4)) ht0.ne'
    have haR : 4+(a-4) = a := by ring
    have hcR : 3*(4+(a-4))-4+(c-(3*a-4)) = c := by ring
    have htd : t*(2*a-2-b) = b-a := div_mul_cancel₀ (b-a) hd.ne'
    have hbR : (4+(a-4)+(2*(4+(a-4))-2)*t)/(1+t) = b := by
      apply (div_eq_iff ht0.ne').mpr
      nlinarith only [htd]
    rw [hcR,haR] at hi
    have hbR' : (a+(2*a-2)*t)/(1+t) = b := by simpa only [haR] using hbR
    rw [hbR'] at hi
    have hp := expansion_positive (a-4) t (c-(3*a-4)) (by linarith) ht (by linarith)
    have hmul : 0 < (1+t)^3*h a b c 2 := by rw [hi]; exact hp
    exact (mul_pos_iff_of_pos_left (pow_pos ht0 3)).mp hmul

#print axioms result
end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoMaximum
