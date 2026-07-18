/- GID: D5/S3/Zeros/CompletedZeta
   generality: I
   mirror-B: D5/B/S3/Zeros/CompletedZeta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Build the entire completed-zeta reading and derive reflection-stable zero data. -/

import D5.S3.Weil.ReflectionLedger
import Mathlib.Analysis.Analytic.Uniqueness

namespace D5.S3.Zeros.CompletedZeta

open Filter Set
open D5.S3.Weil.Convention
open D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger
open scoped ComplexConjugate

/-- Two analytic continuations of the same local germ agree on their preconnected domain. -/
theorem analytic_continuation_unique {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hfg : f =ᶠ[nhds s₀] g) : Set.EqOn f g U := by
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU hs₀ hfg

/-- Mathlib's completed Riemann-zeta reading. -/
noncomputable def completedZetaReading (s : ℂ) : ℂ :=
  completedRiemannZeta s

/-- The entire xi reading, expressed through the pole-removed completed zeta. -/
noncomputable def xiReading (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- Away from the two totalized pole locations, the entire formula is `s(s-1) Lambda(s) / 2`. -/
theorem xi_reading_eq_completed_zeta {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    xiReading s = (1 / 2 : ℂ) * s * (s - 1) * completedZetaReading s := by
  have hOneSub : 1 - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  rw [xiReading, completedZetaReading, completedRiemannZeta_eq]
  field_simp [hs₀, hOneSub]
  all_goals ring

/-- The pole-removed definition makes the xi reading entire. -/
theorem xi_reading_differentiable : Differentiable ℂ xiReading := by
  unfold xiReading
  have hCompleted : Differentiable ℂ (fun s : ℂ ↦ completedRiemannZeta₀ s) :=
    differentiable_completedZeta₀
  fun_prop

/-- The entire xi reading is invariant under reflection about one half. -/
@[simp]
theorem xi_reading_reflection (s : ℂ) : xiReading (1 - s) = xiReading s := by
  unfold xiReading
  rw [completedRiemannZeta₀_one_sub]
  ring

/--
Conjugation and reflection symmetry of a completed reading generate its zero orbit, while
the conjugate-reflected partner reverses every scaling-ledger entry.
-/
theorem zero_quartet_scaling_spec (H : ℂ → ℂ)
    (hConjugation : ∀ s, H (conj s) = conj (H s))
    (hReflection : ∀ s, H (1 - s) = H s)
    {A : Type*} [AddMonoid A] (length : LedgerLength A) (rho : ℂ)
    (hZero : H rho = 0) :
    H rho = 0 ∧
      H (conj rho) = 0 ∧
      H (1 - rho) = 0 ∧
      H (1 - conj rho) = 0 ∧
      ∀ a, scalingLedger length (1 - conj rho) a = -scalingLedger length rho a := by
  have hConjugateZero : H (conj rho) = 0 := by
    rw [hConjugation rho, hZero]
    simp
  have hReflectedZero : H (1 - rho) = 0 := by
    rw [hReflection rho, hZero]
  have hMirrorZero : H (1 - conj rho) = 0 := by
    rw [hReflection (conj rho), hConjugateZero]
  refine ⟨hZero, hConjugateZero, hReflectedZero, hMirrorZero, ?_⟩
  intro a
  simpa [mirror, reflection] using (mirror_reversal_spec length rho).1 a

end D5.S3.Zeros.CompletedZeta
