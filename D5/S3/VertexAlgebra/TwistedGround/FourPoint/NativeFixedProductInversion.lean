/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedProductInversion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedProductInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inversion of the convergent native Leech four-H product on its radial domain. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedInverseBPZ
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHAnalyticGluing

/-! The convergent four-H product is supported on one energy diagonal.
The fixed-source transpose reverses this diagonal at each energy. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedProductInversion

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering)
open NativeFixedPairAIterate (fixedAExponent)
open NativeFourHUpperProduct (fixedBProductCoeff)
open NativeFourHAnalyticGluing (fourHCorrelation fourH_actual_analytic_gluing)
open NativeFourHRealSewing (complexBTerm radialDomainB)
open NativeFixedInverseBPZ (fixedBProductCoeff_detector_reversal)
open private lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedInverseBPZ
open private bModes bCoeff b_outside integralTerm fourH_even_grades from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit false

private theorem energy_hasSum (M K L N : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {x z : ℂ} (h : (x, z) ∈ radialDomainB) :
    HasSum (fun E : ℕ => fixedBProductCoeff false false M K L N v w u b E *
      (z ^ ((2 * (E : ℤ) - (6 + (K : ℤ) + L)) / 2) *
        x ^ (((N : ℤ) - M - 2 * (E : ℤ)) / 2)))
      (fourHCorrelation u v w b (x, z)) := by
  have hinj : Function.Injective (bModes M K L N) := by
    intro E F hEF
    have hsnd := congrArg Prod.snd hEF
    dsimp [bModes] at hsnd
    omega
  have hoff (p : ℤ × ℤ) (hp : p ∉ Set.range (bModes M K L N)) :
      complexBTerm x z u v w b p = 0 := by
    rw [complexBTerm, integralTerm, b_outside M K L N u v w b hu hv hw hb p hp, zero_mul]
  have hs := (hinj.hasSum_iff hoff).mpr ((fourH_actual_analytic_gluing u v w b).2.2 (x, z) h)
  refine hs.congr_fun (fun E => ?_)
  have he : fixedAExponent K L E = 2 * (E : ℤ) - (6 + (K : ℤ) + L) := by
    unfold fixedAExponent
    ring
  simp only [Function.comp_apply, complexBTerm, integralTerm, bModes, he]
  rfl

/-- Simultaneous coordinate inversion and detector reversal of the actual
homogeneous four-H correlation on the radial B domain. Both external
lowering expansions retain the phases of the native fixed-source kernels. -/
theorem fourHCorrelation_detector_reversal (M K L N : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {x z : ℂ} (h : (x, z) ∈ radialDomainB) :
    fourHCorrelation u v w b (x, z) =
      I ^ ((M : ℤ) - K) * ∑ n ∈ Finset.range (M / 2 + 1), ∑ q ∈ Finset.range (K / 2 + 1),
        ((n.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹ *
          (x ^ ((n : ℤ) - 3 - M) * z ^ ((q : ℤ) - 3 - K))) *
            fourHCorrelation ((L₁ ^ q) v) ((L₁ ^ n) u) b w (z⁻¹, x⁻¹) := by
  have hz : 0 < ‖z‖ := h.1
  have hx : 0 < ‖x‖ := hz.trans h.2
  have hx₀ := norm_pos_iff.mp hx
  have hz₀ := norm_pos_iff.mp hz
  have hinv : (z⁻¹, x⁻¹) ∈ radialDomainB := by
    change 0 < ‖x⁻¹‖ ∧ ‖x⁻¹‖ < ‖z⁻¹‖
    rw [norm_inv, norm_inv]
    exact ⟨inv_pos.mpr hx, (inv_lt_inv₀ hx hz).mpr h.2⟩
  have hsum := energy_hasSum M K L N u v w b hu hv hw hb h
  by_cases hzero : u = 0 ∨ v = 0 ∨ w = 0 ∨ b = 0
  · have zero_value (A B C D : ℕ) (p r s t : TwistedEven)
        (hp : p.val ∈ actualGrade ℒ leechUnit A) (hr : r.val ∈ actualGrade ℒ leechUnit B)
        (hs : s.val ∈ actualGrade ℒ leechUnit C) (ht : t.val ∈ actualGrade ℒ leechUnit D)
        {a c : ℂ} (hac : (a, c) ∈ radialDomainB)
        (hzero' : p = 0 ∨ r = 0 ∨ s = 0 ∨ t = 0) : fourHCorrelation p r s t (a, c) = 0 := by
      have h' := energy_hasSum A B C D p r s t hp hr hs ht hac
      rw [← h'.tsum_eq]
      rcases hzero' with rfl | rfl | rfl | rfl <;> simp [fixedBProductCoeff]
    rw [zero_value M K L N u v w b hu hv hw hb h hzero]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro q hq
    rw [zero_value (K - 2 * q) (M - 2 * n) N L _ _ b w
      (lowered_grade hv (by simpa using hq)) (lowered_grade hu (by simpa using hn))
      hb hw hinv, mul_zero]
    rcases hzero with hU | hV | hW | hB
    · exact Or.inr (Or.inl (by simp [hU]))
    · exact Or.inl (by simp [hV])
    · exact Or.inr (Or.inr (Or.inr hW))
    · exact Or.inr (Or.inr (Or.inl hB))
  · obtain ⟨hM, hK, hL, hN⟩ := fourH_even_grades M K L N u v w b hu hv hw hb hzero
    let c (n q : ℕ) := (n.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹ *
      (x ^ ((n : ℤ) - 3 - M) * z ^ ((q : ℤ) - 3 - K))
    have hrev := (hasSum_sum (s := Finset.range (M / 2 + 1)) fun n hn =>
      hasSum_sum (s := Finset.range (K / 2 + 1)) fun q hq =>
      (energy_hasSum (K - 2 * q) (M - 2 * n) N L ((L₁ ^ q) v) ((L₁ ^ n) u) b w
        (lowered_grade hv (by simpa using hq)) (lowered_grade hu (by simpa using hn))
        hb hw hinv).mul_left (c n q)).mul_left (I ^ ((M : ℤ) - K))
    refine hsum.unique (hrev.congr_fun (fun E => ?_))
    rw [fixedBProductCoeff_detector_reversal false false M K L N v w u b E hu hv hw hb]
    simp only [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro q hq
    have hn' : n ≤ M / 2 := by simpa using hn
    have hq' : q ≤ K / 2 := by simpa using hq
    have hzpow : ((2 * (E : ℤ) - (6 + (K : ℤ) + L)) / 2) =
        ((q : ℤ) - 3 - K) - (((L : ℤ) - (K - 2 * q : ℕ) - 2 * (E : ℤ)) / 2) := by
      obtain ⟨k, hk⟩ := hK
      obtain ⟨l, hl⟩ := hL
      omega
    have hxpow : (((N : ℤ) - M - 2 * (E : ℤ)) / 2) =
        ((n : ℤ) - 3 - M) - ((2 * (E : ℤ) - (6 + ((M - 2 * n : ℕ) : ℤ) + N)) / 2) := by
      obtain ⟨m, hm⟩ := hM
      obtain ⟨nn, hnn⟩ := hN
      omega
    dsimp only [c]
    rw [hzpow, hxpow, zpow_sub₀ hx₀, zpow_sub₀ hz₀]
    simp only [inv_zpow, div_eq_mul_inv]
    ring

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedProductInversion
