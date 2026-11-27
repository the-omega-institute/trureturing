/- GID: D5/S3/Fourier/Concentration/FejerCollisionLimit
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FejerCollisionLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Differentiable limits of normalized collision ramps recover hard-band asymptotics. -/

import D5.S3.Fourier.Concentration.FejerCollisionSecants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

open Filter Set
open scoped Topology

namespace D5.S3.Fourier.Concentration.FejerCollisionLimit

/-- Two-sided eventual secant bounds transfer a differentiable pointwise limit to the slope. -/
private theorem secant_tendsto_of_hasDerivAt {ι : Type*} {l : Filter ι}
    (F : ι → ℝ → ℝ) (C : ι → ℝ) (f : ℝ → ℝ) (x d R : ℝ)
    (hR : 0 < R) (hd : HasDerivAt f d x)
    (hF : ∀ a : ℝ, |a-x| < R → Tendsto (fun n => F n a) l (𝓝 (f a)))
    (hsec : ∀ δ : ℝ, 0 < δ → δ < R →
      ∀ᶠ n in l, F n x-F n (x-δ) ≤ δ*C n ∧
        δ*C n ≤ F n (x+δ)-F n x) :
    Tendsto C l (𝓝 d) := by
  rw [tendsto_order]
  have hx := hF x (by simpa using hR)
  constructor
  · intro a ha
    have hA := hd.tendsto_slope_zero_left.eventually (eventually_gt_nhds ha)
    have hN : ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ), -R < t :=
      (eventually_gt_nhds (neg_lt_zero.mpr hR)).filter_mono nhdsWithin_le_nhds
    have hneg : ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ), t < 0 := self_mem_nhdsWithin
    obtain ⟨t,ht,htR,hq⟩ := (hneg.and (hN.and hA)).exists
    have ht' : t < 0 := ht
    let δ := -t
    have hδ : 0 < δ := neg_pos.mpr ht'
    have hδR : δ < R := by dsimp [δ]; linarith
    have hf := hx.sub (hF (x-δ) (by rw [sub_sub_cancel_left,abs_neg,abs_of_pos hδ]; exact hδR))
    have hlt : δ*a < f x-f (x-δ) := by
      rw [smul_eq_mul] at hq
      have hn := mul_lt_mul_of_neg_left hq ht'
      have he : t*(t⁻¹*(f (x+t)-f x)) = f (x+t)-f x := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_lt ht'),one_mul]
      rw [he] at hn
      dsimp [δ]
      rw [sub_neg_eq_add]
      linarith
    filter_upwards [hf.eventually_const_lt hlt,hsec δ hδ hδR] with n hn hs
    exact lt_of_mul_lt_mul_left (hn.trans_le hs.1) hδ.le
  · intro b hb
    have hA := hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds hb)
    have hN : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t < R :=
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨δ,hδ,hδR,hq⟩ := (hpos.and (hN.and hA)).exists
    have hδ' : 0 < δ := hδ
    have hf := (hF (x+δ) (by rw [add_sub_cancel_left,abs_of_pos hδ']; exact hδR)).sub hx
    have hlt : f (x+δ)-f x < δ*b := by
      rw [smul_eq_mul] at hq
      have hn := (mul_lt_mul_iff_of_pos_left hδ').2 hq
      have he : δ*(δ⁻¹*(f (x+δ)-f x)) = f (x+δ)-f x := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hδ'),one_mul]
      rwa [he] at hn
    filter_upwards [hf.eventually_lt_const hlt,hsec δ hδ' hδR] with n hn hs
    exact lt_of_mul_lt_mul_left (hs.2.trans_lt hn) hδ'.le

open Finset
open D5.S3.Fourier.Concentration.FejerCollisionSecants
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

universe u v

/-- Pointwise normalized ramp limits near a radius recover its normalized hard-band mass. -/
theorem collision_ramp_tendsto_hard {ι : Type u} {l : Filter ι} {I : ι → Type v}
    (s : ∀ n, Finset (I n)) (x c : ∀ n, I n → ℝ)
    (hc : ∀ᶠ n in l, ∀ i ∈ s n, ∀ j ∈ s n, 0 ≤ c n i*c n j)
    (B η : ι → ℝ) (hB : ∀ᶠ n in l, 0 ≤ B n)
    (f : ℝ → ℝ) (a d R : ℝ) (hR : 0 < R) (hd : HasDerivAt f d a) :
    let ramp := fun z : ℝ × ℝ => max 0 (z.1-z.2)
    let L := fun n t => ∑ i ∈ s n, ∑ j ∈ s n, c n i*c n j*ramp (t,|x n i-x n j|)
    (∀ t : ℝ, |t-a| < R → Tendsto (fun n => B n*L n (t*η n)) l (𝓝 (f t))) →
    Tendsto (fun n => (B n*η n)*nearCollisionMass (s n) (x n) (c n) (a*η n)) l (𝓝 d) := by
  intro ramp L hF
  let F := fun n t => B n*rampCollisionMass (s n) (x n) (c n) (t*η n)
  let C := fun n => (B n*η n)*nearCollisionMass (s n) (x n) (c n) (a*η n)
  apply secant_tendsto_of_hasDerivAt F C f a d R hR hd hF
  intro δ hδ hδR
  filter_upwards [hB,hc] with n hbn hcn
  rcases lt_trichotomy (η n) 0 with hn | hn | hn
  · have hs : 0 < -(δ*η n) := neg_pos.mpr (mul_neg_of_pos_of_neg hδ hn)
    have h := collision_ramp_secants (s n) (x n) (c n) hcn (a*η n) hs
    change rampCollisionMass _ _ _ (a*η n)-rampCollisionMass _ _ _ (a*η n- -(δ*η n)) ≤
        (-(δ*η n))*nearCollisionMass _ _ _ (a*η n) ∧
      (-(δ*η n))*nearCollisionMass _ _ _ (a*η n) ≤
        rampCollisionMass _ _ _ (a*η n+ -(δ*η n))-rampCollisionMass _ _ _ (a*η n) at h
    rw [sub_neg_eq_add, ← sub_eq_add_neg] at h
    dsimp [F,C]
    rw [sub_mul,add_mul]
    have hL := mul_le_mul_of_nonneg_left h.2 hbn
    have hU := mul_le_mul_of_nonneg_left h.1 hbn
    have hm : B n * (-(δ*η n) * nearCollisionMass (s n) (x n) (c n) (a*η n)) =
        -(δ * ((B n*η n) * nearCollisionMass (s n) (x n) (c n) (a*η n))) := by ring
    rw [hm, mul_sub] at hL hU
    exact ⟨by linarith only [hL], by linarith only [hU]⟩
  · simp [F,C,hn]
  · have h := collision_ramp_secants (s n) (x n) (c n) hcn (a*η n) (mul_pos hδ hn)
    change rampCollisionMass _ _ _ (a*η n)-rampCollisionMass _ _ _ (a*η n-δ*η n) ≤
        (δ*η n)*nearCollisionMass _ _ _ (a*η n) ∧
      (δ*η n)*nearCollisionMass _ _ _ (a*η n) ≤
        rampCollisionMass _ _ _ (a*η n+δ*η n)-rampCollisionMass _ _ _ (a*η n) at h
    dsimp [F,C]
    rw [sub_mul,add_mul]
    constructor
    · have hL := mul_le_mul_of_nonneg_left h.1 hbn
      rw [← mul_sub]
      convert hL using 1
      ring
    · have hU := mul_le_mul_of_nonneg_left h.2 hbn
      rw [← mul_sub]
      convert hU using 1
      ring

#print axioms collision_ramp_tendsto_hard

end D5.S3.Fourier.Concentration.FejerCollisionLimit
