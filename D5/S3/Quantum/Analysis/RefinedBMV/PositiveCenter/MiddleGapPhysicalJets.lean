/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapPhysicalJets
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual quadratic coefficients of the middle-gap physical inputs. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapJet
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapMoments
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

def gapAffine (origin direction s : ℝ) : ℝ := origin + s * direction

private theorem hasDerivAt_gapAffine (origin direction s : ℝ) :
    HasDerivAt (gapAffine origin direction) direction s := by
  have hd := (hasDerivAt_id' s).mul_const direction
  change HasDerivAt (fun t : ℝ ↦ origin + t * direction) direction s
  simpa only [zero_add, one_mul] using (hasDerivAt_const s origin).fun_add hd

namespace QuadraticJet

theorem affineH (h s x y : ℝ) :
    IsLineAt ⟨gapAffine h x s, 1, 0, 0, 0, 0⟩ (gapAffine h x) s x y := by
  refine ⟨by unfold gapAffine; fun_prop, rfl, ?_, ?_⟩
  · simp [(hasDerivAt_gapAffine h x s).deriv]
  · have he : deriv (gapAffine h x) = fun _ ↦ x :=
      funext fun t ↦ (hasDerivAt_gapAffine h x t).deriv
    rw [show iteratedDeriv 2 (gapAffine h x) = deriv (deriv (gapAffine h x)) by
      rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one], he]
    simp

theorem affineD (d s x y : ℝ) :
    IsLineAt ⟨gapAffine d y s, 0, 1, 0, 0, 0⟩ (gapAffine d y) s x y := by
  refine ⟨by unfold gapAffine; fun_prop, rfl, ?_, ?_⟩
  · simp [(hasDerivAt_gapAffine d y s).deriv]
  · have he : deriv (gapAffine d y) = fun _ ↦ y :=
      funext fun t ↦ (hasDerivAt_gapAffine d y t).deriv
    rw [show iteratedDeriv 2 (gapAffine d y) = deriv (deriv (gapAffine d y)) by
      rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one], he]
    simp

end QuadraticJet

theorem gapRhoLine (h₀ d₀ s x y : ℝ) :
    let H := gapAffine h₀ x
    let D := gapAffine d₀ y
    let h := H s
    let d := D s
    let q := Real.exp (-(h*d))
    QuadraticJet.IsLineAt ⟨q, -d*q, -h*q, d*d*q/2, (h*d-1)*q, h*h*q/2⟩
      (fun r ↦ Real.exp (-(H r * D r))) s x y := by
  let H := gapAffine h₀ x
  let D := gapAffine d₀ y
  let h := H s
  let d := D s
  let Q : ℝ → ℝ := fun t ↦ Real.exp (-(H t * D t))
  let W : ℝ → ℝ := fun t ↦ -x*D t - H t*y
  have hH (t : ℝ) : HasDerivAt H x t := hasDerivAt_gapAffine h₀ x t
  have hD (t : ℝ) : HasDerivAt D y t := hasDerivAt_gapAffine d₀ y t
  have hQ (t : ℝ) : HasDerivAt Q (W t * Q t) t := by
    have hh := ((hH t).fun_mul (hD t)).neg.exp
    change HasDerivAt Q (Q t * -(x*D t+H t*y)) t at hh
    exact hh.congr_deriv (by dsimp [W]; ring)
  have hW : HasDerivAt W (-x*y-x*y) s :=
    ((hD s).const_mul (-x)).fun_sub ((hH s).mul_const y)
  have hEq : deriv Q = fun t ↦ W t * Q t := funext fun t ↦ (hQ t).deriv
  refine ⟨by unfold gapAffine; fun_prop, rfl, ?_, ?_⟩
  · change deriv Q s = -d * Q s * x + -h * Q s * y
    rw [hEq]
    dsimp [W, h, d]
    ring
  · rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one]
    change deriv (deriv Q) s =
      2 * (d*d*Q s/2*x^2 + (h*d-1)*Q s*x*y + h*h*Q s/2*y^2)
    rw [hEq, (hW.fun_mul (hQ s)).deriv]
    dsimp [W, h, d]
    ring

theorem gapExpLine (d₀ s x y : ℝ) :
    let D := gapAffine d₀ y
    let z := Real.exp (-D s)
    QuadraticJet.IsLineAt ⟨z, 0, -z, 0, 0, z/2⟩ (fun r ↦ Real.exp (-D r)) s x y := by
  let D := gapAffine d₀ y
  let Z : ℝ → ℝ := fun t ↦ Real.exp (-D t)
  have hZ (t : ℝ) : HasDerivAt Z (-y*Z t) t := by
    have h := (hasDerivAt_gapAffine d₀ y t).neg.exp
    change HasDerivAt Z (Z t * -y) t at h
    exact h.congr_deriv (by ring)
  have hEq : deriv Z = fun t ↦ -y * Z t := funext fun t ↦ (hZ t).deriv
  refine ⟨by unfold gapAffine; fun_prop, rfl, ?_, ?_⟩
  · change deriv Z s = 0 * x + -Z s*y
    rw [hEq]
    ring
  · rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one]
    change deriv (deriv Z) s = 2 * (0*x^2 + 0*x*y + Z s/2*y^2)
    rw [hEq, ((hZ s).const_mul (-y)).deriv]
    ring

theorem gapAline (h₀ d₀ s x y : ℝ) (hh : 0 < gapAffine h₀ x s) :
    let H := gapAffine h₀ x
    let D := gapAffine d₀ y
    let h := H s
    let d := D s
    let q := Real.exp (-(h*d))
    QuadraticJet.IsLineAt ⟨gapDecayMoment 0 h d, -gapDecayMoment 1 h d, q,
      gapDecayMoment 2 h d / 2, -d*q, -h*q/2⟩ (fun r ↦ upperTailGap (H r) (D r)) s x y := by
  let H := gapAffine h₀ x
  let D := gapAffine d₀ y
  let h := H s
  let d := D s
  let Q : ℝ → ℝ := fun r ↦ Real.exp (-(H r * D r))
  let q := Q s
  let A : ℝ → ℝ := fun r ↦ upperTailGap (H r) (D r)
  have hH := QuadraticJet.affineH h₀ s x y
  have hQ := (QuadraticJet.IsLineAt.const s x y 1).sub (gapRhoLine h₀ d₀ s x y)
  have hH₁ : deriv H s = x := by simpa only [one_mul, zero_mul, add_zero] using hH.first_eq
  have hH₂ : iteratedDeriv 2 H s = 0 := by simpa using hH.second_eq
  have hA : ContDiffAt ℝ 2 A s := by
    have hne : H s ≠ 0 := hh.ne'
    change ContDiffAt ℝ 2 (fun r ↦ (1 - Q r) / H r) s
    unfold Q H D gapAffine at *
    fun_prop (disch := assumption)
  have hprod : A * H =ᶠ[𝓝 s] (fun _ ↦ 1) - Q := by
    have hc : ContinuousAt H s := hH.smooth.continuousAt
    filter_upwards [hc.eventually (eventually_gt_nhds hh)] with t ht
    change upperTailGap (H t) (D t) * H t = 1 - Real.exp (-(H t * D t))
    exact div_mul_cancel₀ _ ht.ne'
  have hfirst : deriv A s * h + A s*x = (d*x+h*y)*q := by
    have hp := hprod.deriv_eq
    rw [deriv_mul (hA.differentiableAt (by norm_num))
      (hH.smooth.differentiableAt (by norm_num)), hH₁, hQ.first_eq] at hp
    change _ = (0 - (-d*q))*x + (0 - (-h*q))*y at hp
    nlinarith only [hp]
  have hM₁ : h * gapDecayMoment 1 h d = A s - d*q := by
    simpa [gapDecayMoment_zero_eq (h := h) hh, h, d, q, Q, A] using
      gapDecayMoment_succ_identity (h := h) d 0
  have hA₁ : deriv A s = -gapDecayMoment 1 h d*x + q*y := by
    apply (mul_left_inj' hh.ne').mp
    linear_combination hfirst + x*hM₁
  have hsecond : iteratedDeriv 2 A s*h + 2*deriv A s*x =
      -(d*d*q*x^2 + 2*(h*d-1)*q*x*y + h*h*q*y^2) := by
    have hp := hprod.iteratedDeriv_eq 2
    rw [iteratedDeriv_mul hA hH.smooth, hQ.second_eq] at hp
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero, iteratedDeriv_one,
      Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.reduceSub,
      Nat.cast_one, zero_add, one_mul] at hp
    change A s * iteratedDeriv 2 H s + ((2 : ℕ) : ℝ) * deriv A s * deriv H s +
      iteratedDeriv 2 A s * h =
      2 * ((0 - d*d*q/2)*x^2 + (0 - (h*d-1)*q)*x*y + (0 - h*h*q/2)*y^2) at hp
    rw [hH₁, hH₂] at hp
    linear_combination hp
  have hM₂ : h * gapDecayMoment 2 h d = 2 * gapDecayMoment 1 h d - d^2*q := by
    have hv := gapDecayMoment_succ_identity (h := h) d 1
    norm_num at hv ⊢
    exact hv
  have hA₂ : iteratedDeriv 2 A s = gapDecayMoment 2 h d*x^2 - 2*d*q*x*y - h*q*y^2 := by
    apply (mul_left_inj' hh.ne').mp
    rw [hA₁] at hsecond
    linear_combination hsecond - x^2*hM₂
  refine ⟨hA, (gapDecayMoment_zero_eq hh d).symm, hA₁, ?_⟩
  rw [hA₂]
  dsimp only
  ring

end RefinedBMV.PositiveCenter
