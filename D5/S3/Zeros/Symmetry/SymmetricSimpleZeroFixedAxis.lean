/- GID: D5/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A symmetric simple zero remains reflection-fixed along its local continuation. -/

import D5.S3.Zeros.Symmetry.SimpleZeroNoBifurcation

namespace D5.S3.Zeros.Symmetry.SymmetricSimpleZeroFixedAxis

open Filter
open D5.S3.Weil.Convention D5.S3.Weil.ReflectionLedger
open D5.S3.Zeros.Symmetry.SimpleZeroNoBifurcation
open scoped ComplexConjugate Topology

/-- Every zero in the unique local continuation of a symmetric simple critical-line zero
is fixed by completed reflection and therefore has real part equal to the critical abscissa. -/
theorem symmetric_simple_zero_fixed_axis
    (F : ℝ → ℂ → ℂ)
    (dτ : ℝ → ℂ → ℝ →L[ℝ] ℂ)
    (ds : ℝ → ℂ → ℂ)
    (τ₀ : ℝ) (s₀ : ℂ)
    (hreflection : ∀ τ s, F τ (mirror s) = conj (F τ s))
    (hτ : ∀ᶠ v in 𝓝 (τ₀, s₀),
      HasFDerivAt (fun τ => F τ v.2) (dτ v.1 v.2) v.1)
    (hs : ∀ᶠ v in 𝓝 (τ₀, s₀),
      HasDerivAt (F v.1) (ds v.1 v.2) v.2)
    (hτ_cont : ContinuousAt (Function.uncurry dτ) (τ₀, s₀))
    (hs_cont : ContinuousAt
      (fun v : ℝ × ℂ => (ds v.1 v.2) • (1 : ℂ →L[ℝ] ℂ)) (τ₀, s₀)) :
    (F τ₀ s₀ = 0 ∧ ds τ₀ s₀ ≠ 0 ∧ mirror s₀ = s₀) →
      ∀ᶠ v in 𝓝 (τ₀, s₀),
        F v.1 v.2 = 0 →
          mirror v.2 = v.2 ∧ v.2.re = criticalAbscissa := by
  rintro ⟨hzero, hsimple, hfixed⟩
  have hcritical := mirror_fixed_re_eq s₀ hfixed
  have hlocal :=
    (simple_zero_no_bifurcation
      F dτ ds τ₀ s₀ hreflection hτ hs hτ_cont hs_cont).1
        ⟨hzero, hsimple, hcritical⟩
  filter_upwards [hlocal] with v hv hzero
  have hline := hv hzero
  exact
    ⟨((mirror_reversal_spec (Nat.castAddMonoidHom ℝ) v.2).2.2 hline).symm, hline⟩

#print axioms symmetric_simple_zero_fixed_axis

end D5.S3.Zeros.Symmetry.SymmetricSimpleZeroFixedAxis
