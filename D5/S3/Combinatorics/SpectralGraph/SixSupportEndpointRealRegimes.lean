/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointRealRegimes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportEndpointRealRegimes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both strict spectral regimes on the complete unbounded real endpoint-one surface. -/
import D5.S3.Combinatorics.SpectralGraph.SixSupportMiddleSpectrum
import D5.S3.Combinatorics.SpectralGraph.SixSupportUniformTail

/-! Source: endpoint-one-root-hierarchy, revision
6d491f77b35dec808fc777b69939c56cdae5dc02, blob
6cb0e2bc4ef2fd8743678dc996645e3c4bb0b5d5. Both families below exist
for every real minimum a≥9. Their third exponents are real, and no
integer-point existence or exhaustion is asserted. The actual quotient
quartic and all three high roots are retained in the spectral consumer. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointRealRegimes
open Polynomial
open D5.S3.Combinatorics.SpectralGraph
open SixSupportClassificationAlgebra SixSupportEndpointOneArithmetic

/-- Full positive-coefficient identities on the two original real families. -/
theorem threshold_signs (a : ℝ) (ha : 9 ≤ a) :
    h a (a+3) ((a+3)*(a+5)-a) 1 < 0 ∧
    0 < h a (2*a) ((2*a)*(2*a+2)-a) 1 := by
  have hm : 0 ≤ a-9 := by linarith
  have hp : -h a (a+3) ((a+3)*(a+5)-a) 1 =
      2*(a-9)^8+170*(a-9)^7+6232*(a-9)^6+128076*(a-9)^5+
      1602214*(a-9)^4+12344554*(a-9)^3+55958484*(a-9)^2+
      130053564*(a-9)+102699872 := by simp [h,quintic]; ring
  have hn : h a (2*a) ((2*a)*(2*a+2)-a) 1 =
      64*(a-9)^8+5280*(a-9)^7+188308*(a-9)^6+3800112*(a-9)^5+
      47536335*(a-9)^4+377906718*(a-9)^3+1866318180*(a-9)^2+
      5238888768*(a-9)+6403637656 := by simp [h,quintic]; ring
  constructor
  · have : 0 < -h a (a+3) ((a+3)*(a+5)-a) 1 := by rw [hp]; positivity
    linarith
  · rw [hn]; positivity

private theorem diagonal_negative (a b : ℝ) (ha : 9 ≤ a)
    (hb : b = a+3 ∨ b = 2*a) : h a b b 1 < 0 := by
  have hm : 0 ≤ a-9 := by linarith
  rcases hb with rfl | rfl
  · have he : -h a (a+3) (a+3) 1 =
        4*(a-9)^6+252*(a-9)^5+6576*(a-9)^4+90928*(a-9)^3+
        702096*(a-9)^2+2867472*(a-9)+4833152 := by
      simp [h,quintic]; ring
    have : 0 < -h a (a+3) (a+3) 1 := by rw [he]; positivity
    linarith
  · have he : -h a (2*a) (2*a) 1 =
        64*(a-9)^6+3304*(a-9)^5+70924*(a-9)^4+810273*(a-9)^3+
        5195832*(a-9)^2+17730132*(a-9)+25151120 := by
      simp [h,quintic]; ring
    have : 0 < -h a (2*a) (2*a) 1 := by rw [he]; positivity
    linarith

/-- Both original strict regimes exist for every real minimum a≥9.
These are roots of the complete actual quotient endpoint polynomial. -/
theorem exponent_points (a : ℝ) (ha : 9 ≤ a) :
    (∃ c : ℝ, a+3 < c ∧ h a (a+3) c 1 = 0 ∧
      0 < c+a-(a+3)*(a+5)) ∧
    (∃ c : ℝ, 2*a < c ∧ h a (2*a) c 1 = 0 ∧
      c+a-(2*a)*(2*a+2) < 0) := by
  have hm : 0 ≤ a-9 := by linarith
  obtain ⟨hpos,hneg⟩ := threshold_signs a ha
  constructor
  · let l := (a+3)*(a+5)-a
    let u := 4*a^2-2*a
    have hbl : a+3 < l := by dsimp [l]; nlinarith [sq_nonneg (a-9)]
    have hlu : l < u := by dsimp [l,u]; nlinarith [sq_nonneg (a-9)]
    have hu := SixSupportUniformTail.one_positive a (a+3) u (by linarith)
      (by linarith) (hbl.trans hlu).le (by rfl)
    obtain ⟨c,hc,he⟩ := intermediate_value_Icc hlu.le
      (show ContinuousOn (fun c : ℝ => h a (a+3) c 1) (Set.Icc l u) by
        simp only [h_eq_value,value]; fun_prop)
      (show (0 : ℝ) ∈ Set.Icc (h a (a+3) l 1) (h a (a+3) u 1) from
        ⟨hpos.le,hu.le⟩)
    have hlc : l < c := by
      refine lt_of_le_of_ne hc.1 ?_
      intro heq
      have : h a (a+3) l 1 = 0 := by simpa [heq] using he
      exact hpos.ne this
    exact ⟨c,hbl.trans hlc,he,by dsimp [l] at hlc; linarith⟩
  · let u := (2*a)*(2*a+2)-a
    have hbu : 2*a < u := by dsimp [u]; nlinarith [sq_nonneg (a-9)]
    have hb := diagonal_negative a (2*a) ha (Or.inr rfl)
    obtain ⟨c,hc,he⟩ := intermediate_value_Icc hbu.le
      (show ContinuousOn (fun c : ℝ => h a (2*a) c 1) (Set.Icc (2*a) u) by
        simp only [h_eq_value,value]; fun_prop)
      (show (0 : ℝ) ∈ Set.Icc (h a (2*a) (2*a) 1) (h a (2*a) u 1) from
        ⟨hb.le,hneg.le⟩)
    have hbc : 2*a < c := by
      refine lt_of_le_of_ne hc.1 ?_
      intro heq
      have : h a (2*a) (2*a) 1 = 0 := by simpa [heq] using he
      exact hb.ne this
    have hcu : c < u := by
      refine lt_of_le_of_ne hc.2 ?_
      intro heq
      have : h a (2*a) u 1 = 0 := by simpa [heq] using he
      exact hneg.ne' this
    exact ⟨c,hbc,he,by dsimp [u] at hcu; linarith⟩

/-- Neither strict spectral regime eventually dominates the real
endpoint-one surface: every real a≥9 occurs in both, with the complete
residual quartic and its three high roots on each family. -/
theorem result (a : ℝ) (ha : 9 ≤ a) :
    (∃ c μ x y z : ℝ,
      a+3 < c ∧ h a (a+3) c 1 = 0 ∧ a+3 < μ ∧ μ < min c (2*a+3) ∧
      quartic a (a+3) c = (X-C μ)*(X-C x)*(X-C y)*(X-C z) ∧
      2*a+3+c < x ∧ 2*a+3+c < y ∧ 2*a+3+c < z) ∧
    (∃ c μ x y z : ℝ,
      2*a < c ∧ h a (2*a) c 1 = 0 ∧ a < μ ∧ μ < 2*a ∧
      quartic a (2*a) c = (X-C μ)*(X-C x)*(X-C y)*(X-C z) ∧
      3*a+c < x ∧ 3*a+c < y ∧ 3*a+c < z) := by
  have hsqrt : Real.sqrt (3 : ℝ) < 2 := by
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hacut : 2+Real.sqrt 3 < a := by linarith
  obtain ⟨⟨c,hbc,h1,hE⟩,⟨d,hbd,h2,hF⟩⟩ := exponent_points a ha
  obtain ⟨μ,x,y,z,hf,hμa,hμU,hx,hy,hz,hpos,heq,hneg⟩ :=
    SixSupportMiddleSpectrum.result a (a+3) c hacut (by linarith) hbc.le h1
  obtain ⟨ν,u,v,w,hg,hνa,hνU,hu,hv,hw,hpos',heq',hneg'⟩ :=
    SixSupportMiddleSpectrum.result a (2*a) d hacut (by linarith) hbd.le h2
  constructor
  · have hsum : a+(a+3) = 2*a+3 := by ring
    have hE' : 0 < c+a-(a+3)*(a+3+2) := by
      convert hE using 1 <;> ring
    rw [hsum] at hμU hx hy hz
    exact ⟨c,μ,x,y,z,hbc,h1,hpos.mp hE',hμU,hf,hx,hy,hz⟩
  · have hsum : a+2*a = 3*a := by ring
    rw [hsum] at hu hv hw
    exact ⟨d,ν,u,v,w,hbd,h2,hνa,hneg'.mp hF,hg,hu,hv,hw⟩

#print axioms threshold_signs
#print axioms exponent_points
#print axioms result
end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointRealRegimes
