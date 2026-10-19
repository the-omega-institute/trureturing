/- GID: D5/S3/Quantum/Subentropy/GaussianEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/GaussianEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.JacobianOneDim]
   utility: none
   digest: Gaussian finite entropy gaps identify diagonal determinant-integral subentropy. -/

import D5.S3.Quantum.Subentropy.GaussianRepresentation
import D5.S3.Quantum.Subentropy.LaplaceEntropy
import D5.S3.Quantum.Subentropy.DensityKernel
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Nonnegative product kernels give a Gaussian entropy-gap representation. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Subentropy.GaussianEntropy
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.DensityKernel
open _root_.D5.S3.Quantum.Subentropy.GaussianRepresentation
open _root_.D5.S3.Quantum.Subentropy.LaplaceEntropy

private theorem reciprocal_kernel_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    let f := fun s : ℝ => ((1+s)⁻¹ - ∏ i, (1+s*p i)⁻¹) / s^2
    IntegrableOn f (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), f s) =
        matrixSubentropy (diagonal (fun i => (p i : ℂ))) := by
  let A : Matrix ι ι ℂ := diagonal (fun i => (p i : ℂ))
  have hA : A.PosSemidef := Matrix.PosSemidef.diagonal
    (fun i => by simpa [Complex.le_def] using hp i)
  have htr : A.trace = 1 := by
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, hs, Complex.ofReal_one]
  have himage : (Inv.inv : ℝ → ℝ) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact inv_pos.mpr (mem_Ioi.mp hy)
    · intro hx
      exact ⟨x⁻¹, mem_Ioi.mpr (inv_pos.mpr (mem_Ioi.mp hx)), inv_inv x⟩
  have hd : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (Inv.inv : ℝ → ℝ) (-(s^2)⁻¹) (Ioi 0) s := by
    intro s hs'
    exact (hasDerivAt_inv hs'.ne').hasDerivWithinAt
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd
    (inv_injective.injOn) (subentropyKernel A)
  have hv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd
    (inv_injective.injOn) (subentropyKernel A)
  rw [himage] at hi hv
  have heq : ∀ s ∈ Ioi (0 : ℝ),
      |-(s^2)⁻¹| • subentropyKernel A s⁻¹ =
        ((1+s)⁻¹ - ∏ i, (1+s*p i)⁻¹) / s^2 := by
    intro s hs'
    have hspos : 0 < s := hs'
    have hs0 : s ≠ 0 := hs'.ne'
    have hs1 : 1+s ≠ 0 := by linarith [hs'.out]
    have hsp : ∀ i, 1+s*p i ≠ 0 := by
      intro i
      have := hp i
      positivity
    rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg s)), smul_eq_mul,
      kernel_diagonal p s⁻¹ (inv_ne_zero hs0)]
    have hp' : ∀ i, s⁻¹ / (s⁻¹ + p i) = (1+s*p i)⁻¹ := by
      intro i
      field_simp [hs0, hsp i]
      <;> ring
    simp_rw [hp']
    have hfirst : s⁻¹/(1+s⁻¹) = (1+s)⁻¹ := by
      field_simp [hs0, hs1]
      <;> ring
    rw [hfirst]
    simp only [div_eq_mul_inv]
    ring
  refine ⟨(hi.mp (integrable_subentropy_kernel hA htr)).congr_fun heq measurableSet_Ioi, ?_⟩
  change (∫ s in Ioi (0 : ℝ), ((1+s)⁻¹ - ∏ i, (1+s*p i)⁻¹) / s^2) = _
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, ← hv]
  rfl

private def pairSquare {ι : Type*} (z : (ι × Fin 2) → ℝ) (i : ι) : ℝ :=
  ((z (i,0))^2 + (z (i,1))^2) / 2

private theorem pairSquare_nonneg {ι : Type*} (z : (ι × Fin 2) → ℝ) (i : ι) :
    0 ≤ pairSquare z i := by
  dsimp [pairSquare]
  positivity

private theorem weighted_gaussian_laplace {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s) :
    (∫ z : (ι × Fin 2) → ℝ, Real.exp (-s * ∑ i, p i * pairSquare z i)
      ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) =
        ∏ i, (1+s*p i)⁻¹ := by
  have heq : ∀ z : (ι × Fin 2) → ℝ,
      -s * ∑ i, p i * pairSquare z i = ∑ j : ι × Fin 2, -(s*p j.1)*(z j)^2/2 := by
    intro z
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.sum_univ_two, pairSquare]
    ring
  simp_rw [heq]
  exact diagonal_gaussian_laplace p hp s hs

private theorem coordinate_gaussian_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (s : ℝ) (hs : 0 ≤ s) :
    (∫ z : (ι × Fin 2) → ℝ, Real.exp (-s * pairSquare z i)
      ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) = (1+s)⁻¹ := by
  have h := weighted_gaussian_laplace (fun j : ι => if j=i then 1 else 0)
    (fun j => by split_ifs <;> norm_num) s hs
  have hprod : (∏ j : ι, (1+s*(if j=i then 1 else 0))⁻¹) = (1+s)⁻¹ := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [hprod] at h
  simpa using h

private theorem integrable_exp_nonpos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hneg : ∀ z, f z ≤ 0) :
    Integrable (fun z => Real.exp (f z)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (Real.continuous_exp.comp_aestronglyMeasurable hf) ?_
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (hneg z)

/-- Diagonal subentropy equals the expected finite entropy Jensen gap of
independent squared Gaussian coordinate pairs. The gap itself is integrable;
no exchange of two nonintegrable entropy terms is used. -/
theorem diagonal_subentropy_gaussian_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    let γ := Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)
    let X := fun (z : (ι × Fin 2) → ℝ) (i : ι) => ((z (i,0))^2 + (z (i,1))^2)/2
    let a := fun z => ∑ i, p i * X z i
    Integrable (fun z => Real.negMulLog (a z) - ∑ i, p i * Real.negMulLog (X z i)) γ ∧
      matrixSubentropy (diagonal (fun i => (p i : ℂ))) =
        ∫ z, (Real.negMulLog (a z) - ∑ i, p i * Real.negMulLog (X z i)) ∂γ := by
  classical
  let γ := Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let a : ((ι × Fin 2) → ℝ) → ℝ := fun z => ∑ i, p i * pairSquare z i
  let G := fun z => Real.negMulLog (a z) - ∑ i, p i * Real.negMulLog (pairSquare z i)
  let f : ℝ × ((ι × Fin 2) → ℝ) → ℝ := fun u =>
    (∑ i, p i * Real.exp (-u.1 * pairSquare u.2 i) - Real.exp (-u.1 * a u.2)) / u.1^2
  change Integrable G γ ∧ matrixSubentropy (diagonal (fun i => (p i : ℂ))) = ∫ z, G z ∂γ
  have hnonneg (s : ℝ) (z : (ι × Fin 2) → ℝ) : 0 ≤ f (s,z) := by
    apply div_nonneg _ (sq_nonneg s)
    have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := p)
      (p := fun i => -s * pairSquare z i) (fun i _ => hp i) hs
      (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at h
    have heq : ∑ i, p i * (-s * pairSquare z i) = -s * a z := by
      dsimp [a]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq] at h
    exact sub_nonneg.mpr h
  have hcoord (i : ι) (s : ℝ) (hs' : 0 ≤ s) :
      Integrable (fun z : (ι × Fin 2) → ℝ => Real.exp (-s * pairSquare z i)) γ := by
    apply integrable_exp_nonpos γ _ (by dsimp [pairSquare]; fun_prop)
    intro z
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs') (pairSquare_nonneg z i)
  have hweighted (s : ℝ) (hs' : 0 ≤ s) :
      Integrable (fun z : (ι × Fin 2) → ℝ => Real.exp (-s * a z)) γ := by
    apply integrable_exp_nonpos γ _ (by dsimp [a, pairSquare]; fun_prop)
    intro z
    apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs')
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (pairSquare_nonneg z i)
  have hinner (s : ℝ) (hs' : 0 ≤ s) : Integrable (fun z => f (s,z)) γ := by
    exact ((integrable_finsetSum Finset.univ
      (fun i _ => (hcoord i s hs').const_mul (p i))).sub (hweighted s hs')).div_const (s^2)
  have hmean (s : ℝ) (hs' : 0 ≤ s) :
      (∫ z, f (s,z) ∂γ) = ((1+s)⁻¹ - ∏ i, (1+s*p i)⁻¹) / s^2 := by
    dsimp only [f]
    rw [integral_div, integral_sub
      (integrable_finsetSum Finset.univ (fun i _ => (hcoord i s hs').const_mul (p i)))
      (hweighted s hs'),
      integral_finsetSum Finset.univ (fun i _ => (hcoord i s hs').const_mul (p i))]
    have heq : ∀ i, (∫ z : (ι × Fin 2) → ℝ,
        p i * Real.exp (-s * pairSquare z i) ∂γ) = p i * (1+s)⁻¹ := by
      intro i
      rw [integral_const_mul, coordinate_gaussian_laplace i s hs']
    simp_rw [heq]
    rw [weighted_gaussian_laplace p hp s hs', ← Finset.sum_mul, hs, one_mul]
  have hk := reciprocal_kernel_integral p hp hs
  have hprod : Integrable f (ν.prod γ) := by
    refine (integrable_prod_iff ((show Measurable f by dsimp [f, a, pairSquare]; fun_prop).aestronglyMeasurable)).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs'
      exact hinner s hs'.le
    · refine hk.1.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs'
      have heq : (∫ z, ‖f (s,z)‖ ∂γ) = ∫ z, f (s,z) ∂γ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => Real.norm_of_nonneg (hnonneg s z)
      rw [heq, hmean s hs'.le]
  have hcongr : (fun z => ∫ s, f (s,z) ∂ν) =ᵐ[γ] G := by
    apply Filter.Eventually.of_forall
    intro z
    have h := (entropy_jensen_laplace p (pairSquare z) hp hs (pairSquare_nonneg z)).2
    change (∫ s in Ioi (0 : ℝ),
      (∑ i, p i * Real.exp (-s*pairSquare z i) - Real.exp (-s*a z)) / s^2) = G z
    rw [h]
    dsimp only [G, Real.negMulLog]
    simp_rw [neg_mul, mul_neg, Finset.sum_neg_distrib]
    ring
  refine ⟨hprod.integral_prod_right.congr hcongr, ?_⟩
  rw [← integral_congr_ae hcongr]
  calc
    matrixSubentropy (diagonal (fun i => (p i : ℂ))) =
        ∫ s, ((1+s)⁻¹ - ∏ i, (1+s*p i)⁻¹) / s^2 ∂ν := hk.2.symm
    _ = ∫ s, ∫ z, f (s,z) ∂γ ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs'
      exact (hmean s hs'.le).symm
    _ = _ := integral_integral_swap hprod

end D5.S3.Quantum.Subentropy.GaussianEntropy
