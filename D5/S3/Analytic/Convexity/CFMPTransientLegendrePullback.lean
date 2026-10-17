/- GID: D5/S3/Analytic/Convexity/MonotoneLegendrePullback
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/MonotoneLegendrePullback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A continuous local right inverse of a monotone gradient has a differentiable Legendre pullback. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# A local Legendre pullback with a nonsmooth inverse

The primitive is an input. Monotonicity bounds its secants between the two endpoint
pairings. On a ball in the primitive domain, these bounds give a coupled remainder
of size `‖h‖ * ‖T (x + h) - T x‖`. Continuity of `T` at the base point suffices to
make this little-o of `h`; no derivative or local Lipschitz bound for `T` is needed.
-/

open Filter Set
open scoped Topology

namespace D5.S3.Analytic.Convexity.MonotoneLegendrePullback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A segment contained in the primitive domain has its secant between the two
endpoint gradient pairings. The ambient domain need not be convex. -/
private theorem secant_bounds {Ω : Set E} {G : E → E} {Q : E → ℝ} {z w : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, z + t • (w - z) ∈ Ω)
    (hQ : ∀ p ∈ Ω, HasFDerivAt Q (innerSL ℝ (G p)) p)
    (hmono : ∀ p ∈ Ω, ∀ q ∈ Ω, 0 ≤ inner ℝ (G p - G q) (p - q)) :
    inner ℝ (G z) (w - z) ≤ Q w - Q z ∧
      Q w - Q z ≤ inner ℝ (G w) (w - z) := by
  have hz : z ∈ Ω := by simpa using hseg 0 (by norm_num)
  have hzw : z + (w - z) = w := by module
  have hw : w ∈ Ω := by simpa only [one_smul, hzw] using hseg 1 (by norm_num)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => Q (z + s • (w - z)))
        (inner ℝ (G (z + t • (w - z))) (w - z)) t := by
    have hp : HasDerivAt (fun s : ℝ => z + s • (w - z)) (w - z) t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const (w - z)).const_add z
    simpa only [Function.comp_def, innerSL_apply_apply] using
      (hQ _ (hseg t ht)).comp_hasDerivAt t hp
  have hc : ContinuousOn (fun t : ℝ => Q (z + t • (w - z))) (Icc 0 1) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨t, ht, hs⟩ := exists_hasDerivAt_eq_slope
    (fun t : ℝ => Q (z + t • (w - z)))
    (fun t : ℝ => inner ℝ (G (z + t • (w - z))) (w - z))
    (by norm_num : (0 : ℝ) < 1) hc (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩)
  have hs' : inner ℝ (G (z + t • (w - z))) (w - z) = Q w - Q z := by
    simpa only [zero_smul, add_zero, one_smul, hzw, sub_zero, div_one] using hs
  have hp : z + t • (w - z) ∈ Ω := hseg t ⟨ht.1.le, ht.2.le⟩
  have hlo := hmono _ hp z hz
  rw [add_sub_cancel_left, real_inner_smul_right, inner_sub_left] at hlo
  have hvec : w - (z + t • (w - z)) = (1 - t) • (w - z) := by module
  have hhi := hmono w hw _ hp
  rw [hvec, real_inner_smul_right, inner_sub_left] at hhi
  constructor
  · rw [← hs']
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hlo ht.1)
  · rw [← hs']
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hhi (sub_pos.mpr ht.2))

/-- The Legendre expression has derivative `innerSL ℝ (T x)` when `T` is only
continuous at `x`, is locally a right inverse of the monotone field `G`, and `G`
is the actual derivative field of the supplied primitive `Q` on an open set. -/
theorem hasFDerivAt_legendre_pullback_of_monotone
    {Ω : Set E} {T G : E → E} {Q : E → ℝ} {x : E}
    (hΩ : IsOpen Ω)
    (hx : T x ∈ Ω)
    (hT : ContinuousAt T x)
    (hQ : ∀ z ∈ Ω, HasFDerivAt Q (innerSL ℝ (G z)) z)
    (hmono : ∀ z ∈ Ω, ∀ w ∈ Ω,
      0 ≤ inner ℝ (G z - G w) (z - w))
    (hinv : ∀ᶠ y in nhds x, G (T y) = y) :
    HasFDerivAt
      (fun y => inner ℝ y (T y) - Q (T y))
      (innerSL ℝ (T x)) x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ (T x) hx
  have hbase : G (T x) = x := hinv.self_of_nhds
  have hshift : Tendsto (fun h : E => x + h) (𝓝 0) (𝓝 x) := by
    have hs : Tendsto (fun h : E => x + h) (𝓝 (0 : E)) (𝓝 (x + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa only [add_zero] using hs
  have himage : Tendsto (fun h : E => T (x + h)) (𝓝 0) (𝓝 (T x)) :=
    hT.tendsto.comp hshift
  have hnear : ∀ᶠ h : E in 𝓝 0, T (x + h) ∈ Metric.ball (T x) r :=
    himage.eventually (Metric.ball_mem_nhds (T x) hr)
  have hinv' : ∀ᶠ h : E in 𝓝 0, G (T (x + h)) = x + h := hshift.eventually hinv
  let R : E → ℝ := fun h =>
    (inner ℝ (x + h) (T (x + h)) - Q (T (x + h))) -
      (inner ℝ x (T x) - Q (T x)) - inner ℝ (T x) h
  have hrem : ∀ᶠ h : E in 𝓝 0,
      0 ≤ R h ∧ R h ≤ ‖h‖ * ‖T (x + h) - T x‖ := by
    filter_upwards [hnear, hinv'] with h hh hi
    have hδ : ‖T (x + h) - T x‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hh
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
        T x + t • (T (x + h) - T x) ∈ Ω := by
      intro t ht
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hδ
    obtain ⟨hlo, hhi⟩ := secant_bounds hseg hQ hmono
    rw [hbase] at hlo
    rw [hi] at hhi
    have hidentity : R h =
        inner ℝ (x + h) (T (x + h) - T x) - (Q (T (x + h)) - Q (T x)) := by
      dsimp [R]
      simp only [inner_sub_right, inner_add_left, real_inner_comm (T x) h]
      ring
    have hR0 : 0 ≤ R h := by rw [hidentity]; linarith
    have hRinner : R h ≤ inner ℝ h (T (x + h) - T x) := by
      rw [hidentity, inner_add_left]
      linarith
    exact ⟨hR0, hRinner.trans ((le_abs_self _).trans (abs_real_inner_le_norm _ _))⟩
  have hdelta : Tendsto (fun h : E => ‖T (x + h) - T x‖) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (himage.sub (tendsto_const_nhds (x := T x))).norm
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hsmall : ∀ᶠ h : E in 𝓝 0, ‖T (x + h) - T x‖ < ε :=
    hdelta.eventually (gt_mem_nhds hε)
  filter_upwards [hrem, hsmall] with h hR hεh
  change ‖R h‖ ≤ ε * ‖h‖
  rw [Real.norm_eq_abs, abs_of_nonneg hR.1]
  exact hR.2.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hεh.le (norm_nonneg h))

end D5.S3.Analytic.Convexity.MonotoneLegendrePullback
