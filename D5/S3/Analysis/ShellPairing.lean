/- GID: D5/S3/Analysis/ShellPairing
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The squared norm of an integrated plane wave expands as a double pairing with a conjugated wave and the same spectral weight. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
Omega original.

The squared norm of an integrated plane wave expands as a double pairing
with a conjugated wave and the same spectral weight.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace Omega

variable {K X : Type*}

/-- A complex coefficient with a real oscillatory phase. -/
def shellWave (a : X → ℂ) (phase : K → X → ℝ) (k : K) (x : X) : ℂ :=
  a x * Complex.exp (Complex.I * (phase k x : ℂ))

/-- The integrand obtained by expanding the shell square. -/
def shellPair (w : K → ℝ) (a : X → ℂ) (phase : K → X → ℝ)
    (z : K × (X × X)) : ℂ :=
  (w z.1 : ℂ) * (star (shellWave a phase z.1 z.2.1) * shellWave a phase z.1 z.2.2)

private theorem norm_shellWave (a : X → ℂ) (phase : K → X → ℝ) (k : K) (x : X) :
    ‖shellWave a phase k x‖ = ‖a x‖ := by
  simp [shellWave, Complex.norm_exp_I_mul_ofReal]

variable [MeasurableSpace K] [MeasurableSpace X]
variable {μ : Measure X} {ν : Measure K} {w : K → ℝ} {a : X → ℂ} {phase : K → X → ℝ}

/-- A modulus-one phase preserves integrability of the wave coefficient. -/
theorem shellWave_integrable (ha : Integrable a μ)
    (hphase : Measurable (Function.uncurry phase)) (k : K) :
    Integrable (shellWave a phase k) μ := by
  have hp : Measurable (phase k) := hphase.comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (fun x : X => Complex.exp (Complex.I * (phase k x : ℂ))) :=
    Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hp))
  exact ha.norm.mono' (ha.aestronglyMeasurable.mul hm.aestronglyMeasurable)
    (.of_forall fun x => (norm_shellWave a phase k x).le)

/-- Integrable spectral weight and wave coefficients give an integrable
pairing on the product of the spectral space and two test spaces. -/
theorem shellPair_integrable [SFinite μ] [SFinite ν]
    (hw : Integrable w ν) (ha : Integrable a μ)
    (hphase : Measurable (Function.uncurry phase)) :
    Integrable (shellPair w a phase) (ν.prod (μ.prod μ)) := by
  let P : Measure (K × (X × X)) := ν.prod (μ.prod μ)
  have he (coord : K × (X × X) → X) (hc : Measurable coord) :
      Measurable (fun z : K × (X × X) =>
        Complex.exp (Complex.I * (phase z.1 (coord z) : ℂ))) :=
    Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.continuous_ofReal.measurable.comp (hphase.comp (measurable_fst.prodMk hc))))
  have hleft : AEStronglyMeasurable (fun z : K × (X × X) => shellWave a phase z.1 z.2.1) P :=
    (ha.aestronglyMeasurable.comp_fst.comp_snd).mul
      (he (fun z => z.2.1) (measurable_fst.comp measurable_snd)).aestronglyMeasurable
  have hright : AEStronglyMeasurable (fun z : K × (X × X) => shellWave a phase z.1 z.2.2) P :=
    (ha.aestronglyMeasurable.comp_snd.comp_snd).mul
      (he (fun z => z.2.2) (measurable_snd.comp measurable_snd)).aestronglyMeasurable
  have hc : AEStronglyMeasurable (fun k => (w k : ℂ)) ν :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have hd : AEStronglyMeasurable
      (fun z : K × (X × X) => star (shellWave a phase z.1 z.2.1)) P :=
    Complex.continuous_conj.comp_aestronglyMeasurable hleft
  have hm : AEStronglyMeasurable (shellPair w a phase) P := hc.comp_fst.mul (hd.mul hright)
  refine (hw.norm.mul_prod (ha.norm.mul_prod ha.norm)).mono' hm (.of_forall fun z => ?_)
  simp only [shellPair, norm_mul, norm_star, norm_shellWave, Complex.norm_real, le_refl]

/-- The real weighted integral of squared amplitudes is the real part
of the iterated integral of the expanded shell pairing. -/
theorem integral_shellWave_norm_sq [SFinite μ] [SFinite ν]
    (hw : Integrable w ν) (ha : Integrable a μ)
    (hphase : Measurable (Function.uncurry phase)) :
    (∫ k : K, w k * ‖∫ x : X, shellWave a phase k x ∂μ‖ ^ 2 ∂ν) =
      (∫ z : X × X, ∫ k : K, shellPair w a phase (k,z) ∂ν ∂(μ.prod μ)).re := by
  have hswap := integral_integral_swap (f := fun k z => shellPair w a phase (k,z))
    (shellPair_integrable hw ha hphase)
  have he (k : K) : (∫ z : X × X, shellPair w a phase (k,z) ∂(μ.prod μ)) =
      ((w k * ‖∫ x : X, shellWave a phase k x ∂μ‖ ^ 2 : ℝ) : ℂ) := by
    simp only [shellPair, integral_const_mul, Complex.ofReal_mul]
    rw [integral_prod_mul (fun x => star (shellWave a phase k x)) (shellWave a phase k)]
    simp only [Complex.star_def, integral_conj]
    have hnorm (c : ℂ) : (starRingEnd ℂ) c * c = (‖c‖ ^ 2 : ℝ) := by
      rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
    rw [hnorm]
  simp_rw [he] at hswap
  rw [← hswap, integral_complex_ofReal, Complex.ofReal_re]

end Omega
