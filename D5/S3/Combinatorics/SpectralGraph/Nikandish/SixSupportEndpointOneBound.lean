/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full ordered-real endpoint-one sum bound and exact equality locus. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Tactic

/-! The sum-bound portion of the original endpoint-one spectral theorem.
Its full spectral-order/separation assertions remain separate obligations. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointOneBound

open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

/-- The original q,z expression for the actual quintic at one. -/
def sumModel (a q z : ℝ) : ℝ :=
  (q-(4*a^2-2*a+1))*z^2-a*(a-1)*(q+2*a-1)*z +
    (a^2-1)*q^3+(a^3-a^2-3*a+3)*q^2-3*(a-1)^2*q-(a-1)^3

/-- Exact complete q=b+c,z=bc substitution. -/
theorem sumModel_identity (a b c : ℝ) : h a b c 1 = sumModel a (b+c) (b*c) := by
  simp [h, quintic, sumModel]
  ring

private def B (a t : ℝ) : ℝ :=
  a^3-2*a^2*t^2+a^2*t+a^2+3*a*t-3*a+t^2-2*t+1

private theorem B_negative (a t : ℝ) (ha : 2 ≤ a) (hat : a ≤ t) : B a t < 0 := by
  have ha0 : 0 < a := by linarith
  have hm : 0 ≤ a-2 := by linarith
  have hu : 0 ≤ t-a := by linarith
  have hA : 0 < 2*a^2-1 := by nlinarith [sq_nonneg (a-2)]
  have ha1 : 0 < 2*a-1 := by linarith
  have hid : -B a t = (2*a^2-1)*(t-a)^2 +
      ((a-2)*(4*a^2+7*a+9)+20)*(t-a) +
      (a-2)*(2*a^3+a*(2*a-1)+3)+5 := by dsimp [B]; ring
  have : 0 < -B a t := by rw [hid]; positivity
  linarith

private theorem decomposition (a b c : ℝ) :
    h a b c 1 =
      (b*c-a*(b+c-a))*
        ((b+c-(4*a^2-2*a+1))*(b*c+a*(b+c-a))-a*(a-1)*(b+c+2*a-1)) +
      (2*a^2-2*a+1-(b+c))*B a (b+c-a) := by
  simp [h, quintic, B]
  ring

private theorem comparison (a b c : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hq : b+c ≤ 2*a^2-2*a+1) :
    0 ≤ b*c-a*(b+c-a) ∧
    (b+c-(4*a^2-2*a+1))*(b*c+a*(b+c-a))-a*(a-1)*(b+c+2*a-1) < 0 ∧
    B a (b+c-a) < 0 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hdiff : 0 ≤ b*c-a*(b+c-a) := by
    have hprod : 0 ≤ (b-a)*(c-a) := mul_nonneg (by linarith) (by linarith)
    nlinarith only [hprod]
  have hk : b+c-(4*a^2-2*a+1) < 0 := by nlinarith [sq_nonneg a]
  have hz : 0 < b*c+a*(b+c-a) := by
    have hsum : 0 < b+c-a := by linarith
    positivity
  have hn : 0 < a*(a-1)*(b+c+2*a-1) := by
    have ha1 : 0 < a-1 := by linarith
    have ht : 0 < b+c+2*a-1 := by linarith
    positivity
  have hi : (b+c-(4*a^2-2*a+1))*(b*c+a*(b+c-a))-a*(a-1)*(b+c+2*a-1) < 0 :=
    sub_neg.mpr ((mul_neg_of_neg_of_pos hk hz).trans hn)
  exact ⟨hdiff, hi, B_negative a (b+c-a) ha (by linarith)⟩

/-- The complete real endpoint-one sum bound, with the exact equality locus. -/
theorem result (a b c : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hz : h a b c 1 = 0) :
    2*a^2-2*a+1 ≤ b+c ∧
      (b+c = 2*a^2-2*a+1 ↔ b = a ∧ c = (a-1)*(2*a-1)) := by
  have hbound : 2*a^2-2*a+1 ≤ b+c := by
    by_contra hn
    have hq : b+c < 2*a^2-2*a+1 := by linarith
    obtain ⟨hdiff, hi, hB⟩ := comparison a b c ha hab hbc hq.le
    have hfirst : (b*c-a*(b+c-a))*
        ((b+c-(4*a^2-2*a+1))*(b*c+a*(b+c-a))-a*(a-1)*(b+c+2*a-1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdiff hi.le
    have hsecond : (2*a^2-2*a+1-(b+c))*B a (b+c-a) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hB
    have heq := decomposition a b c
    linarith only [hfirst, hsecond, heq, hz]
  refine ⟨hbound, ?_⟩
  constructor
  · intro hq
    obtain ⟨hdiff, hi, hB⟩ := comparison a b c ha hab hbc hq.le
    have hprod : (b*c-a*(b+c-a))*
        ((b+c-(4*a^2-2*a+1))*(b*c+a*(b+c-a))-a*(a-1)*(b+c+2*a-1)) = 0 := by
      have heq := decomposition a b c
      have hs : 2*a^2-2*a+1-(b+c) = 0 := by linarith
      rw [hs, zero_mul, add_zero, hz] at heq
      exact heq.symm
    have hdiffzero : b*c-a*(b+c-a) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right hi.ne
    have hba : b = a := by
      have hp : (b-a)*(c-a) = 0 := by nlinarith only [hdiffzero]
      rcases mul_eq_zero.mp hp with hb | hc
      · linarith
      · linarith
    refine ⟨hba, ?_⟩
    rw [hba] at hq
    nlinarith only [hq]
  · rintro ⟨rfl, rfl⟩
    ring

/-- The original strict integer consequence used in the largest-root route. -/
theorem third_exponent_bound (a b c : ℕ) (ha : 2 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hz : h (a : ℝ) (b : ℝ) (c : ℝ) 1 = 0) : (a : ℤ)^2-a < c := by
  have hbound := (result a b c (by exact_mod_cast ha) (by exact_mod_cast hab.le)
    (by exact_mod_cast hbc) hz).1
  have hbcR : (b : ℝ) ≤ c := by exact_mod_cast hbc
  have hi : (a : ℝ)^2-a < (c : ℝ) := by linarith
  exact_mod_cast hi

#print axioms sumModel_identity
#print axioms result
#print axioms third_exponent_bound

end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointOneBound
