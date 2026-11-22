/- GID: D5/S3/Analytic/Asymptotics/PositiveSpectralKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/PositiveSpectralKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded positive spectral filtering by an infinite product of moments. -/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-width positive spectral filter

A probability measure obtained from bounded independent displacements realizes the
product of the individual exponential moments. The two-atom factors cancel their
assigned conjugate frequencies and can retain a protected frequency.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace PositiveSpectralKernel

private def expKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (z * (x : ℂ))

/-- The forward exponential moment of a measure on the real line. -/
def expMoment (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ x, expKernel z x ∂ν

private theorem continuous_expKernel (z : ℂ) : Continuous (expKernel z) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

private theorem norm_expArgument_le (z : ℂ) {x a : ℝ} (hx : x ∈ Icc 0 a) :
    ‖z * (x : ℂ)‖ ≤ ‖z‖ * a := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact mul_le_mul_of_nonneg_left hx.2 (norm_nonneg _)

private theorem norm_expKernel_le (z : ℂ) {x a : ℝ} (hx : x ∈ Icc 0 a) :
    ‖expKernel z x‖ ≤ Real.exp (‖z‖ * a) :=
  (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (norm_expArgument_le z hx))

private theorem norm_expKernel_sub_one_le (z : ℂ) {x a A : ℝ}
    (hx : x ∈ Icc 0 a) (ha : a ≤ A) :
    ‖expKernel z x - 1‖ ≤ (‖z‖ * Real.exp (‖z‖ * A)) * a := by
  have hnorm := norm_expArgument_le z hx
  have hexp : Real.exp ‖z * (x : ℂ)‖ ≤ Real.exp (‖z‖ * A) :=
    Real.exp_le_exp.mpr (hnorm.trans (mul_le_mul_of_nonneg_left ha (norm_nonneg _)))
  calc
    ‖expKernel z x - 1‖ ≤ ‖z * (x : ℂ)‖ * Real.exp ‖z * (x : ℂ)‖ := by
      simpa [expKernel, Finset.sum_range_one] using
        Complex.norm_exp_sub_sum_le_norm_mul_exp (z * (x : ℂ)) 1
    _ ≤ (‖z‖ * a) * Real.exp (‖z‖ * A) :=
      mul_le_mul hnorm hexp (Real.exp_pos _).le
        (mul_nonneg (norm_nonneg _) (hx.1.trans hx.2))
    _ = (‖z‖ * Real.exp (‖z‖ * A)) * a := by ring

/-- The moment increment is bounded linearly in the interval width, uniformly for widths
bounded by A. -/
theorem norm_expMoment_sub_one_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (z : ℂ) {a A : ℝ} (hν : ν (Icc 0 a) = 1) (ha : a ≤ A) :
    ‖expMoment ν z - 1‖ ≤ (‖z‖ * Real.exp (‖z‖ * A)) * a := by
  have hsupport : ∀ᵐ x ∂ν, x ∈ Icc 0 a :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hν
  have hint : Integrable (expKernel z) ν := by
    refine (integrable_const (Real.exp (‖z‖ * a))).mono'
      (continuous_expKernel z).measurable.aestronglyMeasurable ?_
    exact hsupport.mono fun _ hx => norm_expKernel_le z hx
  have hsub : (∫ x, (expKernel z x - 1) ∂ν) = expMoment ν z - 1 := by
    rw [expMoment, integral_sub hint (integrable_const (1 : ℂ))]
    simp
  rw [← hsub]
  have hbound : ∀ᵐ x ∂ν, ‖expKernel z x - 1‖ ≤ (‖z‖ * Real.exp (‖z‖ * A)) * a :=
    hsupport.mono fun _ hx => norm_expKernel_sub_one_le z hx ha
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hbound

theorem summable_norm_expMoment_sub_one {μ : ℕ → Measure ℝ}
    [∀ j, IsProbabilityMeasure (μ j)] {a : ℕ → ℝ} (ha₀ : ∀ j, 0 ≤ a j)
    (ha : Summable a) (hμ : ∀ j, μ j (Icc 0 (a j)) = 1) (z : ℂ) :
    Summable (fun j => ‖expMoment (μ j) z - 1‖) := by
  let A : ℝ := ∑' j, a j
  have hmajorant : Summable (fun j => (‖z‖ * Real.exp (‖z‖ * A)) * a j) :=
    ha.mul_left _
  refine hmajorant.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro j
  exact norm_expMoment_sub_one_le (μ j) z (hμ j) (ha.le_tsum j fun i _ => ha₀ i)

private theorem integral_expKernel_partial_sum {μ : ℕ → Measure ℝ}
    [∀ j, IsProbabilityMeasure (μ j)] (z : ℂ) (s : Finset ℕ) :
    (∫ x : ℕ → ℝ, expKernel z (∑ j ∈ s, x j) ∂(Measure.infinitePi μ)) =
      ∏ j ∈ s, expMoment (μ j) z := by
  classical
  let P := Measure.infinitePi μ
  have heval (j : ℕ) : MeasurePreserving (Function.eval j) P (μ j) :=
    measurePreserving_eval_infinitePi μ j
  have hcoord : iIndepFun (fun j (x : ℕ → ℝ) => x j) P :=
    iIndepFun_infinitePi (P := μ) (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hfinite : iIndepFun (fun j : s => fun x : ℕ → ℝ => x j.1) P :=
    iIndepFun.precomp (g := fun j : s => j.1) Subtype.val_injective hcoord
  have hexp (x : ℕ → ℝ) :
      expKernel z (∑ j ∈ s, x j) = ∏ j : s, expKernel z (x j.1) := by
    simp only [expKernel, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    exact (Finset.prod_coe_sort s (fun j => expKernel z (x j))).symm
  calc
    (∫ x : ℕ → ℝ, expKernel z (∑ j ∈ s, x j) ∂P) =
        ∫ x : ℕ → ℝ, ∏ j : s, expKernel z (x j.1) ∂P :=
      integral_congr_ae (Eventually.of_forall hexp)
    _ = ∏ j : s, ∫ x : ℕ → ℝ, expKernel z (x j.1) ∂P :=
      hfinite.integral_fun_prod_comp (f := fun _ : s => expKernel z)
        (fun j => (heval j.1).measurable.aemeasurable)
        (fun _ => (continuous_expKernel z).measurable.aestronglyMeasurable)
    _ = ∏ j : s, expMoment (μ j.1) z := by
      apply Finset.prod_congr rfl
      intro j _
      change (∫ x : ℕ → ℝ, expKernel z (x j.1) ∂P) = ∫ u, expKernel z u ∂(μ j.1)
      rw [← (heval j.1).map_eq]
      exact (integral_map (heval j.1).measurable.aemeasurable
        (continuous_expKernel z).measurable.aestronglyMeasurable).symm
    _ = ∏ j ∈ s, expMoment (μ j) z :=
      Finset.prod_coe_sort s (fun j => expMoment (μ j) z)

/-- The law of the sum of independent bounded coordinates, with a common measure for all
complex exponential moments. -/
theorem exists_probability_hasProd_expMoment {μ : ℕ → Measure ℝ}
    [∀ j, IsProbabilityMeasure (μ j)] {a : ℕ → ℝ} (ha₀ : ∀ j, 0 ≤ a j)
    (ha : Summable a) (hμ : ∀ j, μ j (Icc 0 (a j)) = 1) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc 0 (∑' j, a j)) = 1 ∧
      ∀ z : ℂ, HasProd (fun j => expMoment (μ j) z) (expMoment ν z) := by
  let P := Measure.infinitePi μ
  let : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  let S : (ℕ → ℝ) → ℝ := fun x => ∑' j, x j
  let Sₙ : ℕ → (ℕ → ℝ) → ℝ := fun n x => ∑ j ∈ Finset.range n, x j
  let A : ℝ := ∑' j, a j
  have hS : Measurable S := Measurable.tsum fun j => measurable_pi_apply j
  have hSₙ (n : ℕ) : Measurable (Sₙ n) :=
    (Finset.range n).measurable_fun_sum fun j _ => measurable_pi_apply j
  have hcoords : ∀ᵐ x ∂P, ∀ j, x j ∈ Icc 0 (a j) := by
    refine ae_all_iff.2 fun j => ?_
    have heval : MeasurePreserving (Function.eval j) P (μ j) :=
      measurePreserving_eval_infinitePi μ j
    have hj : ∀ᵐ u ∂(P.map (Function.eval j)), u ∈ Icc 0 (a j) := by
      rw [heval.map_eq]
      exact (mem_ae_iff_prob_eq_one measurableSet_Icc).2 (hμ j)
    exact ae_of_ae_map heval.measurable.aemeasurable hj
  have hsummable {x : ℕ → ℝ} (hx : ∀ j, x j ∈ Icc 0 (a j)) : Summable x :=
    ha.of_nonneg_of_le (fun j => (hx j).1) (fun j => (hx j).2)
  have hS_mem : ∀ᵐ x ∂P, S x ∈ Icc 0 A := hcoords.mono fun x hx =>
    ⟨tsum_nonneg (fun j => (hx j).1), (hsummable hx).tsum_le_tsum (fun j => (hx j).2) ha⟩
  have hSₙ_mem (n : ℕ) : ∀ᵐ x ∂P, Sₙ n x ∈ Icc 0 A := by
    filter_upwards [hcoords] with x hx
    refine ⟨Finset.sum_nonneg (fun j _ => (hx j).1), ?_⟩
    calc
      Sₙ n x ≤ ∑ j ∈ Finset.range n, a j :=
        Finset.sum_le_sum (fun j _ => (hx j).2)
      _ ≤ A := ha.sum_le_tsum _ (fun j _ => ha₀ j)
  let ν : Measure ℝ := P.map S
  have hν : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure ν := hν
  refine ⟨ν, hν, ?_, ?_⟩
  · apply (mem_ae_iff_prob_eq_one measurableSet_Icc).1
    exact (ae_map_iff hS.aemeasurable measurableSet_Icc).2 hS_mem
  · intro z
    have hlim : ∀ᵐ x ∂P,
        Tendsto (fun n => expKernel z (Sₙ n x)) atTop (𝓝 (expKernel z (S x))) := by
      filter_upwards [hcoords] with x hx
      exact ((continuous_expKernel z).tendsto (S x)).comp
        (hsummable hx).hasSum.tendsto_sum_nat
    have hbound (n : ℕ) : ∀ᵐ x ∂P, ‖expKernel z (Sₙ n x)‖ ≤ Real.exp (‖z‖ * A) :=
      (hSₙ_mem n).mono fun _ hx => norm_expKernel_le z hx
    have hconv := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun n x => expKernel z (Sₙ n x)) (f := fun x => expKernel z (S x))
      (fun _ => Real.exp (‖z‖ * A))
      (fun n => ((continuous_expKernel z).measurable.comp (hSₙ n)).aestronglyMeasurable)
      (integrable_const _) hbound hlim
    have hpush : expMoment ν z = ∫ x, expKernel z (S x) ∂P :=
      integral_map hS.aemeasurable (continuous_expKernel z).measurable.aestronglyMeasurable
    have hfinite (n : ℕ) : (∫ x, expKernel z (Sₙ n x) ∂P) =
        ∏ j ∈ Finset.range n, expMoment (μ j) z :=
      integral_expKernel_partial_sum z (Finset.range n)
    have hdev := summable_norm_expMoment_sub_one ha₀ ha hμ z
    have hmul : Multipliable (fun j => expMoment (μ j) z) := by
      simpa only [add_sub_cancel] using
        (multipliable_one_add_of_summable (f := fun j => expMoment (μ j) z - 1) hdev)
    apply hmul.hasProd_iff_tendsto_nat.2
    simpa only [hfinite, ← hpush] using hconv

/-- Equal exponential moments to a product of factors remain nonzero when all those factors
are nonzero and the interval widths are summable. -/
theorem expMoment_ne_zero_of_factor_ne_zero {μ : ℕ → Measure ℝ} {ν : Measure ℝ}
    [∀ j, IsProbabilityMeasure (μ j)] {a : ℕ → ℝ} (ha₀ : ∀ j, 0 ≤ a j)
    (ha : Summable a) (hμ : ∀ j, μ j (Icc 0 (a j)) = 1) {z : ℂ}
    (hprod : HasProd (fun j => expMoment (μ j) z) (expMoment ν z))
    (hne : ∀ j, expMoment (μ j) z ≠ 0) : expMoment ν z ≠ 0 := by
  rw [← hprod.tprod_eq]
  simpa only [add_sub_cancel] using
    (tprod_one_add_ne_zero_of_summable (f := fun j => expMoment (μ j) z - 1)
      (fun j => by simpa only [add_sub_cancel] using hne j)
      (summable_norm_expMoment_sub_one ha₀ ha hμ z))

end PositiveSpectralKernel
