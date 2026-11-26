/- GID: D5/S3/Analytic/OriginalHalfBinomialDiskCorrection
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialDiskCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.HasPrimitives, mathlib/module/Mathlib.Analysis.Complex.RemovableSingularity]
   utility: none
   digest: Normalized holomorphic disk correction for the literal original period. -/

import D5.S3.Analytic.OriginalHalfBinomialWronskian
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The normalized continuation uses the literal original period and its native endpoint. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology

namespace D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
open OriginalHalfBinomialPeriod (period)

/-- The full complex unit disk. -/
def disk : Set ℂ := Metric.ball 0 1

/-- The reciprocal native Abel coefficient. -/
def R (r : ℂ) : ℂ := 1 / ((1 - r) * period r ^ 2)

/-- The removable difference quotient, including its derivative value at zero. -/
def G : ℂ → ℂ := dslope R 0

private lemma p_zero : period 0 = 1 := by
  rw [period, tsum_eq_single 0]
  · norm_num [D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.halfBinomial]
  · intro n hn
    simp only [zero_pow hn, mul_zero]

private lemma p_prime_zero : deriv period 0 = 1 / 4 := by
  have h := (OriginalHalfBinomialPeriod.picard_fuchs (z := 0) (by norm_num)).2.2
  rw [p_zero] at h
  norm_num at h ⊢
  linear_combination h

private lemma p_nonzero {r : ℂ} (hr : r ∈ disk) : period r ≠ 0 :=
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero
    (by simpa [disk] using hr)

private lemma one_sub_nonzero {r : ℂ} (hr : r ∈ disk) : 1 - r ≠ 0 := by
  intro he
  have : r = 1 := sub_eq_zero.mp he |>.symm
  simpa [disk, this] using hr

private lemma R_hasDerivAt {r : ℂ} (hr : r ∈ disk) :
    HasDerivAt R
      (-(-period r ^ 2 + (1 - r) * (2 * period r * deriv period r)) /
        ((1 - r) * period r ^ 2) ^ 2) r := by
  have hp := (OriginalHalfBinomialPeriod.picard_fuchs
    (z := r) (by simpa [disk] using hr)).1.hasDerivAt
  convert (((hasDerivAt_id r).const_sub 1).mul (hp.pow 2)).inv
    (mul_ne_zero (one_sub_nonzero hr) (pow_ne_zero 2 (p_nonzero hr))) using 1
  · funext z
    simp [R, one_div]
  · dsimp
    ring

private lemma R_zero : R 0 = 1 := by simp [R, p_zero]

private lemma R_prime_zero : deriv R 0 = 1 / 2 := by
  have h := (R_hasDerivAt (r := 0) (by simp [disk])).deriv
  norm_num [p_zero, p_prime_zero] at h ⊢
  exact h

private lemma G_holomorphic : DifferentiableOn ℂ G disk := by
  apply (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))).2
  exact fun r hr => (R_hasDerivAt hr).differentiableAt.differentiableWithinAt

private lemma primitive_exists : ∃ h : ℂ → ℂ, h 0 = 0 ∧
    ∀ r ∈ disk, HasDerivAt h (-Complex.I / (Real.pi : ℂ) * G r) r := by
  have hd : DifferentiableOn ℂ (fun r => -Complex.I / (Real.pi : ℂ) * G r)
      (Metric.ball 0 1) := G_holomorphic.const_mul _
  exact hd.isExactOn_ball.with_val_at 0 0

/-- The zero-normalized primitive of the removable native coefficient. -/
def H : ℂ → ℂ := Classical.choose primitive_exists

/-- Native normalization, removable quotient, and the unique normalized primitive
on the entire disk. -/
theorem disk_correction :
    period 0 = 1 ∧ deriv period 0 = 1 / 4 ∧
    R 0 = 1 ∧ deriv R 0 = 1 / 2 ∧
    DifferentiableOn ℂ R disk ∧ DifferentiableOn ℂ G disk ∧ G 0 = 1 / 2 ∧
    (∀ r : ℂ, r * G r = R r - 1) ∧
    H 0 = 0 ∧ (∀ r ∈ disk, HasDerivAt H (-Complex.I / (Real.pi : ℂ) * G r) r) ∧
    deriv H 0 = -Complex.I / (2 * (Real.pi : ℂ)) ∧
    (∀ h : ℂ → ℂ, h 0 = 0 →
      (∀ r ∈ disk, HasDerivAt h (-Complex.I / (Real.pi : ℂ) * G r) r) → EqOn h H disk) := by
  have hH : H 0 = 0 ∧ ∀ r ∈ disk,
      HasDerivAt H (-Complex.I / (Real.pi : ℂ) * G r) r :=
    Classical.choose_spec primitive_exists
  refine ⟨p_zero, p_prime_zero, R_zero, R_prime_zero,
    (fun r hr => (R_hasDerivAt hr).differentiableAt.differentiableWithinAt),
    G_holomorphic, ?_, ?_, hH.1, hH.2, ?_, ?_⟩
  · simpa [G, dslope_same] using R_prime_zero
  · intro r
    simpa only [G, sub_zero, smul_eq_mul, R_zero] using sub_smul_dslope R 0 r
  · rw [(hH.2 0 (by simp [disk])).deriv]
    have : G 0 = 1 / 2 := by simpa [G, dslope_same] using R_prime_zero
    rw [this]
    ring
  · intro h h0 hd r hr
    have he : ∀ z ∈ disk, HasDerivAt (fun w => h w - H w) 0 z := by
      intro z hz
      simpa only [sub_self] using! (hd z hz).sub (hH.2 z hz)
    have hc := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun z hz => (he z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (he z hz).deriv) hr (show (0 : ℂ) ∈ disk by simp [disk])
    exact sub_eq_zero.mp (by simpa only [h0, hH.1, sub_self] using hc)

end D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
