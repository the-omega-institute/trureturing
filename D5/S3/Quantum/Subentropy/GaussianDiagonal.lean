/- GID: D5/S3/Quantum/Subentropy/GaussianDiagonal
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/GaussianDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Constructions.Pi]
   utility: none
   digest: Diagonal subentropy is a Gaussian entropy expectation minus a fixed coordinate baseline. -/

import D5.S3.Quantum.Subentropy.GaussianEntropy
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

/-! Coordinate exchangeability cancels the linear entropy baseline. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Subentropy.GaussianDiagonal
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.GaussianEntropy

private theorem abs_entropy_bound (u : ℝ) (hu : 0 ≤ u) :
    |Real.negMulLog u| ≤ 1 + u^2 := by
  rcases le_total u 1 with hsmall | hlarge
  · rw [abs_of_nonneg (Real.negMulLog_nonneg hu hsmall)]
    have h := Real.negMulLog_le_one_sub_self hu
    nlinarith [sq_nonneg u]
  · have hup : 0 < u := lt_of_lt_of_le zero_lt_one hlarge
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hlarge
    have hneg : Real.negMulLog u ≤ 0 := by
      simp only [Real.negMulLog]
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hu hlog)
    rw [abs_of_nonpos hneg]
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hup) hu
    simp only [Real.negMulLog] at *
    nlinarith

/-- The entropy of one squared complex Gaussian coordinate is absolutely integrable.
The real and imaginary coordinates are independent standard real Gaussians. -/
private theorem integrable_gaussian_pair_entropy {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun z : (ι × Fin 2) → ℝ =>
      Real.negMulLog (((z (i,0))^2 + (z (i,1))^2) / 2))
        (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) := by
  have hm : Integrable (fun x : ℝ => ‖x‖^4) (gaussianReal 0 1) := by
    exact (memLp_id_gaussianReal (μ := 0) (v := 1) (4 : NNReal)).integrable_norm_pow
      (by norm_num : (4 : ℕ) ≠ 0)
  have hfour (j : ι × Fin 2) :
      Integrable (fun z : (ι × Fin 2) → ℝ => (z j)^4)
        (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) := by
    have h := integrable_comp_eval (μ := fun _ : ι × Fin 2 => gaussianReal 0 1)
      (i := j) hm
    have habs : Integrable (fun z : (ι × Fin 2) → ℝ => |(z j)^4|)
        (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) := by
      simpa only [Real.norm_eq_abs, pow_abs] using h
    exact habs.congr (Filter.Eventually.of_forall fun z => abs_of_nonneg (by positivity))
  refine ((integrable_const (1 : ℝ)).add ((hfour (i,0)).add (hfour (i,1)))).mono'
    (by fun_prop) ?_
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  change |Real.negMulLog (((z (i,0))^2 + (z (i,1))^2)/2)| ≤
    1 + ((z (i,0))^4 + (z (i,1))^4)
  have hu : 0 ≤ ((z (i,0))^2 + (z (i,1))^2) / 2 := by positivity
  have h := abs_entropy_bound _ hu
  have hsq := sq_nonneg ((z (i,0))^2 - (z (i,1))^2)
  nlinarith


private theorem coordinate_entropy_exchangeable {ι : Type*} [Fintype ι]
    (i j : ι) :
    (∫ z : (ι × Fin 2) → ℝ,
      Real.negMulLog (((z (i,0))^2 + (z (i,1))^2)/2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) =
    (∫ z : (ι × Fin 2) → ℝ,
      Real.negMulLog (((z (j,0))^2 + (z (j,1))^2)/2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) := by
  classical
  let e : (ι × Fin 2) ≃ (ι × Fin 2) :=
    Equiv.prodCongr (Equiv.swap i j) (Equiv.refl (Fin 2))
  have h := (measurePreserving_piCongrLeft
    (fun _ : ι × Fin 2 => gaussianReal 0 1) e).integral_comp'
    (fun z => Real.negMulLog (((z (i,0))^2 + (z (i,1))^2)/2))
  simpa [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, e] using h.symm

/-- In a fixed finite dimension, diagonal subentropy is the expected entropy
of the Gaussian quadratic form minus the entropy expectation of any one
coordinate. The quadratic-form entropy is integrable, including at zero weights. -/
theorem diagonal_subentropy_gaussian_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (i₀ : ι) :
    let γ := Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)
    let X := fun (z : (ι × Fin 2) → ℝ) (i : ι) => ((z (i,0))^2 + (z (i,1))^2)/2
    let a := fun z => ∑ i, p i * X z i
    Integrable (fun z => Real.negMulLog (a z)) γ ∧
      matrixSubentropy (diagonal (fun i => (p i : ℂ))) =
        (∫ z, Real.negMulLog (a z) ∂γ) - (∫ z, Real.negMulLog (X z i₀) ∂γ) := by
  classical
  let γ := Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)
  let X := fun (z : (ι × Fin 2) → ℝ) (i : ι) => ((z (i,0))^2 + (z (i,1))^2)/2
  let a := fun z => ∑ i, p i * X z i
  have hg := diagonal_subentropy_gaussian_gap p hp hs
  have hb : Integrable (fun z => ∑ i, p i * Real.negMulLog (X z i)) γ :=
    integrable_finsetSum Finset.univ
      (fun i _ => (integrable_gaussian_pair_entropy i).const_mul (p i))
  have ha : Integrable (fun z => Real.negMulLog (a z)) γ := by
    refine (hg.1.add hb).congr ?_
    exact Filter.Eventually.of_forall fun z => sub_add_cancel _ _
  have hbaseline : (∫ z, ∑ i, p i * Real.negMulLog (X z i) ∂γ) =
      ∫ z, Real.negMulLog (X z i₀) ∂γ := by
    rw [integral_finsetSum Finset.univ
      (fun i _ => (integrable_gaussian_pair_entropy i).const_mul (p i))]
    calc
      ∑ i, (∫ z, p i * Real.negMulLog (X z i) ∂γ) =
          ∑ i, p i * (∫ z, Real.negMulLog (X z i₀) ∂γ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
        exact congrArg (fun r => p i*r) (coordinate_entropy_exchangeable i i₀)
      _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
  refine ⟨ha, ?_⟩
  rw [hg.2, integral_sub ha hb, hbaseline]

end D5.S3.Quantum.Subentropy.GaussianDiagonal
