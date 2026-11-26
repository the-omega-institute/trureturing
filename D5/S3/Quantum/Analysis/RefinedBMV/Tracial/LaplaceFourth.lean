/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/LaplaceFourth
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Laplace moments of the signed four-copy balanced trace. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.FourthEnergy
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Pi

namespace RefinedBMV.Tracial

open Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive diagonal factor in the balanced Laplace integrand. -/
def fourthLaplaceWeight (a w : ι → ℝ) (s : ℝ) : Matrix ι ι ℂ :=
  diagonal fun i ↦ ((w i * Real.exp (-(s * a i / 4)) : ℝ) : ℂ)

private theorem fourth_trace_le_separated (P C : Matrix ι ι ℂ)
    (hP : star P = P) (hC : star C = C) :
    (trace ((P * C) ^ 4)).re ≤ (trace (P ^ 4 * C ^ 4)).re := by
  let τ := tracePositiveLinearMap ι ℂ ℂ
  let X := P ^ 2 * C ^ 2 - C ^ 2 * P ^ 2
  let Y := C * P ^ 2 * C - P * C ^ 2 * P
  let Z := (P * C) ^ 2 - (C * P) ^ 2
  have heq := fourth_power_three_squares τ.toLinearMap
    (fun U V ↦ trace_mul_comm U V) P C hP hC
  have hreal := congrArg Complex.re heq
  change ((τ (star X * X) + τ (star Y * Y) + τ (star Z * Z))).re =
    (2 * (τ (P ^ 4 * C ^ 4) - τ ((P * C) ^ 4))).re at hreal
  have hpos (U : Matrix ι ι ℂ) : 0 ≤ (τ (star U * U)).re :=
    (Complex.nonneg_iff.mp (τ.map_nonneg (star_mul_self_nonneg U))).1
  have ht : (2 : ℂ).re = 2 := by norm_num
  have hi : (2 : ℂ).im = 0 := by norm_num
  simp only [Complex.add_re, Complex.mul_re, ht, hi, zero_mul, sub_zero, Complex.sub_re] at hreal
  change (τ ((P * C) ^ 4)).re ≤ (τ (P ^ 4 * C ^ 4)).re
  linarith only [hreal, hpos X, hpos Y, hpos Z]

private theorem fourth_weight_trace_nonneg (a w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (C : Matrix ι ι ℂ) (hC : C.IsHermitian) (s : ℝ) :
    0 ≤ (trace ((fourthLaplaceWeight a w s * C) ^ 4)).re := by
  let q (i : ι) := w i * Real.exp (-(s * a i / 4))
  let D : Matrix ι ι ℂ := diagonal fun i ↦ (Real.sqrt (q i) : ℂ)
  have hq (i : ι) : 0 ≤ q i := mul_nonneg (hw i) (Real.exp_nonneg _)
  have hD : D.IsHermitian := by
    change Dᴴ = D
    simp [D, diagonal_conjTranspose]
  have hsplit : fourthLaplaceWeight a w s = D * D := by
    simp only [fourthLaplaceWeight, D, diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hq i)]
  have htr : trace ((D * D * C) ^ 4) = trace ((D * C * D) ^ 4) := by
    rw [show (D * D * C) ^ 4 = D * (D * C * (D * D * C) ^ 3) by noncomm_ring,
      trace_mul_comm]
    congr 1
    noncomm_ring
  have hW : (D * C * D).IsHermitian := by
    change (D * C * D)ᴴ = D * C * D
    simp [conjTranspose_mul, hD.eq, hC.eq, mul_assoc]
  have hWpos : 0 ≤ (D * C * D) ^ 4 := by
    let W := D * C * D
    have hstar : star W = W := hW.eq
    change 0 ≤ W ^ 4
    rw [show W ^ 4 = star (W ^ 2) * W ^ 2 by rw [star_pow, hstar, ← pow_add]]
    exact star_mul_self_nonneg _
  rw [hsplit, htr]
  exact (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hWpos.posSemidef)).1

private theorem gamma_trace_weight (r : ℝ) (hr : -1 < r) {a : ℝ} (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), s ^ r * Real.exp (-(a * s))) =
      (1 / a) ^ (r + 1) * Real.Gamma (r + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := r + 1) (r := a) (by linarith) ha
  simpa only [add_sub_cancel_right] using h

private theorem gamma_trace_integrable (r : ℝ) (hr : -1 < r) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ ↦ s ^ r * Real.exp (-(a * s))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hr one_pos ha)

/-- Every integrable real Laplace moment of the signed balanced trace has the
separated moment upper bound. At orders three and four this is the
global positive average and its first derivative for the BMV kernel. -/
theorem fourth_laplace_moment_le (r : ℝ) (hr : -1 < r) (a w : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hw : ∀ i, 0 ≤ w i)
    (C : Matrix ι ι ℂ) (hC : C.IsHermitian) :
    (∫ s in Ioi (0 : ℝ), s ^ r * (trace ((fourthLaplaceWeight a w s * C) ^ 4)).re) ≤
      ∑ i, Real.Gamma (r + 1) * (w i ^ 4 * (1 / a i) ^ (r + 1)) * ((C ^ 4) i i).re := by
  let weight (i : ι) : ℝ := w i ^ 4 * ((C ^ 4) i i).re
  let g (s : ℝ) : ℝ := ∑ i, weight i * (s ^ r * Real.exp (-(a i * s)))
  have hg : IntegrableOn g (Ioi 0) := integrable_finsetSum _ fun i _ ↦
    (gamma_trace_integrable r hr (ha i)).const_mul (weight i)
  have hid (s : ℝ) : s ^ r * (trace (fourthLaplaceWeight a w s ^ 4 * C ^ 4)).re = g s := by
    simp only [fourthLaplaceWeight, Matrix.diagonal_pow, Matrix.trace, Matrix.diag_apply,
      Matrix.diagonal_mul, Pi.pow_apply, ← Complex.ofReal_pow, Complex.re_sum,
      Complex.re_ofReal_mul, Finset.mul_sum, g, weight]
    apply Finset.sum_congr rfl
    intro i _
    have hex : Real.exp (-(s * a i / 4)) ^ (4 : ℕ) = Real.exp (-(a i * s)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [mul_pow, hex]
    ring
  calc
    _ ≤ ∫ s in Ioi (0 : ℝ), g s := by
      refine integral_mono_of_nonneg ?_ hg ?_
      · change ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ s ^ r * (trace ((fourthLaplaceWeight a w s * C) ^ 4)).re
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Filter.Eventually.of_forall fun s hs ↦ mul_nonneg (Real.rpow_nonneg hs.le _)
          (fourth_weight_trace_nonneg a w hw C hC s)
      · change ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
          s ^ r * (trace ((fourthLaplaceWeight a w s * C) ^ 4)).re ≤ g s
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall fun s hs ↦ ?_
        have hp : star (fourthLaplaceWeight a w s) = fourthLaplaceWeight a w s := by
          rw [Matrix.star_eq_conjTranspose, fourthLaplaceWeight, diagonal_conjTranspose]
          congr 1
          funext i
          exact Complex.conj_ofReal _
        rw [← hid]
        exact mul_le_mul_of_nonneg_left (fourth_trace_le_separated _ C hp hC.eq)
          (Real.rpow_nonneg hs.le _)
    _ = _ := by
      unfold g
      rw [MeasureTheory.integral_finsetSum _ (fun i _ ↦
        (gamma_trace_integrable r hr (ha i)).const_mul (weight i))]
      apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.integral_const_mul, gamma_trace_weight r hr (ha i)]
      unfold weight
      ring


/-- Normalizing the diagonal Gamma mass sharpens the moment bound to a
single fourth power of a congruence of the signed second factor. -/
theorem fourth_laplace_moment_congruence_le (p : ℝ) (hp : -4 < p)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (C : Matrix ι ι ℂ) (hC : C.IsHermitian) :
    let E := diagonal fun i ↦ ((a i ^ (-(p / 8)) : ℝ) : ℂ)
    (∫ s in Ioi (0 : ℝ), s ^ (p + 3) * (trace ((fourthLaplaceWeight a a s * C) ^ 4)).re) ≤
      Real.Gamma (p + 4) * (trace ((E * C * E) ^ 4)).re := by
  let E : Matrix ι ι ℂ := diagonal fun i ↦ ((a i ^ (-(p / 8)) : ℝ) : ℂ)
  let w (i : ι) := a i ^ ((p + 4) / 4)
  have hw (i : ι) : 0 ≤ w i := Real.rpow_nonneg (ha i).le _
  have he : Eᴴ = E := by
    unfold E
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal _
  have hc : (E * C * E).IsHermitian := by
    change (E * C * E)ᴴ = E * C * E
    simp [conjTranspose_mul, he, hC.eq, mul_assoc]
  have hnorm (i : ι) : w i ^ 4 * (1 / a i) ^ (p + 3 + 1) = 1 := by
    unfold w
    rw [← Real.rpow_natCast, ← Real.rpow_mul (ha i).le, one_div, Real.inv_rpow (ha i).le,
      ← Real.rpow_neg (ha i).le, ← Real.rpow_add (ha i)]
    have hzero : ((p + 4) / 4) * ((4 : ℕ) : ℝ) + -(p + 3 + 1) = 0 := by
      norm_num
      ring
    rw [hzero, Real.rpow_zero]
  have hweight (s : ℝ) :
      E * fourthLaplaceWeight a w s * E = fourthLaplaceWeight a a s := by
    simp only [E, fourthLaplaceWeight, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [← Complex.ofReal_mul]
    congr 1
    have hpow : a i ^ (-(p / 8)) * w i * a i ^ (-(p / 8)) = a i := by
      unfold w
      rw [← Real.rpow_add (ha i), ← Real.rpow_add (ha i)]
      have hone : -(p / 8) + (p + 4) / 4 + -(p / 8) = 1 := by ring
      rw [hone, Real.rpow_one]
    rw [show a i ^ (-(p / 8)) * (w i * Real.exp (-(s * a i / 4))) * a i ^ (-(p / 8)) =
      (a i ^ (-(p / 8)) * w i * a i ^ (-(p / 8))) * Real.exp (-(s * a i / 4)) by ring,
      hpow]
  have htrace (s : ℝ) :
      trace ((fourthLaplaceWeight a w s * (E * C * E)) ^ 4) =
        trace ((fourthLaplaceWeight a a s * C) ^ 4) := by
    let Q := fourthLaplaceWeight a w s
    have hcycle (A B : Matrix ι ι ℂ) : trace ((A * B) ^ 4) = trace ((B * A) ^ 4) := by
      rw [show (A * B) ^ 4 = A * ((B * A) ^ 3 * B) by noncomm_ring, trace_mul_comm]
      congr 1
      noncomm_ring
    calc
      _ = trace (((Q * E * C) * E) ^ 4) := by simp only [Q, mul_assoc]
      _ = trace ((E * (Q * E * C)) ^ 4) := hcycle _ _
      _ = trace (((E * Q * E) * C) ^ 4) := by simp only [mul_assoc]
      _ = _ := by rw [show E * Q * E = _ from hweight s]
  have hmoment := fourth_laplace_moment_le (p + 3) (by linarith) a w ha hw (E * C * E) hc
  simp_rw [htrace, hnorm, mul_one] at hmoment
  rw [← Finset.mul_sum] at hmoment
  simpa only [trace, diag_apply, Complex.re_sum, show p + 3 + 1 = p + 4 by ring] using hmoment


/-- Integrating a power of the coordinate sum against a product of decaying
exponentials gives the complete homogeneous polynomial in the inverse rates. -/
theorem integral_orthant_sum_pow_mul_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x : ι → ℝ, (∑ i, x i) ^ m * Real.exp (-(∑ i, a i * x i))
      ∂(Measure.pi (fun _ : ι ↦ volume.restrict (Ioi (0 : ℝ))))) =
      (m.factorial : ℝ) *
        ∑ g ∈ Finset.piAntidiag (Finset.univ : Finset ι) m, ∏ i, (a i)⁻¹ ^ (g i + 1) := by
  let μ : ι → Measure ℝ := fun _ ↦ volume.restrict (Ioi 0)
  let _ : ∀ i : ι, SigmaFinite (μ i) := fun _ ↦ by dsimp [μ]; infer_instance
  let compositions : Finset (ι → ℕ) := Finset.piAntidiag Finset.univ m
  let c (g : ι → ℕ) : ℝ := Nat.multinomial Finset.univ g
  let f (g : ι → ℕ) (i : ι) (t : ℝ) : ℝ := t ^ g i * Real.exp (-(a i * t))
  have hf (g : ι → ℕ) (i : ι) : Integrable (f g i) (μ i) := by
    change IntegrableOn (fun t : ℝ ↦ t ^ g i * Real.exp (-(a i * t))) (Ioi 0)
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (g i : ℝ))
        (by linarith [Nat.cast_nonneg (α := ℝ) (g i)]) one_pos (ha i))
  have hf_prod (g : ι → ℕ) :
      Integrable (fun x : ι → ℝ ↦ ∏ i, f g i (x i)) (Measure.pi μ) :=
    Integrable.fintype_prod (hf g)
  have hf_integral (g : ι → ℕ) (i : ι) :
      (∫ t : ℝ, f g i t ∂(μ i)) = ((g i).factorial : ℝ) * (a i)⁻¹ ^ (g i + 1) := by
    change (∫ t in Ioi (0 : ℝ), t ^ g i * Real.exp (-(a i * t))) = _
    have h := gamma_trace_weight (g i : ℝ)
      (by linarith [Nat.cast_nonneg (α := ℝ) (g i)]) (ha i)
    rw [Real.Gamma_nat_eq_factorial, ← Nat.cast_succ, Real.rpow_natCast] at h
    simpa only [Real.rpow_natCast, one_div, Nat.succ_eq_add_one, mul_comm] using h
  have h_expand (x : ι → ℝ) :
      (∑ i, x i) ^ m * Real.exp (-(∑ i, a i * x i)) =
        ∑ g ∈ compositions, c g * ∏ i, f g i (x i) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum, Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp only [c, f, Finset.prod_mul_distrib, mul_assoc]
  change (∫ x : ι → ℝ, (∑ i, x i) ^ m *
    Real.exp (-(∑ i, a i * x i)) ∂(Measure.pi μ)) = _
  calc
    _ = ∫ x : ι → ℝ, (∑ g ∈ compositions, c g * ∏ i, f g i (x i)) ∂(Measure.pi μ) :=
      integral_congr_ae (Filter.Eventually.of_forall h_expand)
    _ = ∑ g ∈ compositions, c g * ∏ i, ((g i).factorial : ℝ) * (a i)⁻¹ ^ (g i + 1) := by
      rw [MeasureTheory.integral_finsetSum compositions (fun g _ ↦ (hf_prod g).const_mul (c g))]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_fintype_prod_eq_prod (f g)]
      simp_rw [hf_integral]
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg ↦ ?_
      have h_degree := (Finset.mem_piAntidiag.mp hg).1
      have h_nat := (Nat.multinomial_spec Finset.univ g).trans (congrArg Nat.factorial h_degree)
      have h_factorial : c g * (∏ i, ((g i).factorial : ℝ)) = (m.factorial : ℝ) := by
        simpa only [c, Nat.cast_mul, Nat.cast_prod, mul_comm] using
          congrArg (fun n : ℕ ↦ (n : ℝ)) h_nat
      rw [Finset.prod_mul_distrib, ← mul_assoc, h_factorial]


end

end RefinedBMV.Tracial
