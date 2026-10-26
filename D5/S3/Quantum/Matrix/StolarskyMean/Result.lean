/- GID: D5/S3/Quantum/Matrix/StolarskyMean/Result
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/StolarskyMean/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Reproducing, mathlib/module/Mathlib.Analysis.InnerProductSpace.Calculus, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Integrating positive mixed curvature gives conditional negativity of Stolarsky matrices. -/

import D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor
import D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Positive mixed curvature integrated through a Hilbert feature map. -/

noncomputable section
open scoped BigOperators Topology ComplexOrder
open MeasureTheory

namespace D5.S3.Quantum.Matrix.StolarskyMean.Result

open Defs Reduction

private theorem real_translation_psd {g : ℝ → ℝ}
    (hg : D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
      (fun t => (g t : ℂ))) :
    Matrix.PosSemidef (fun x y : ℝ => g (y - x)) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro x y
    have h := (hg 2 ![x, y]).isHermitian.apply 0 1
    have hr := congrArg Complex.re h
    simpa using hr
  · intro c
    let e := Fintype.equivFin ↥c.support
    have hp : Matrix.PosSemidef
        (fun i j : ↥c.support => (g ((j : ℝ) - (i : ℝ)) : ℂ)) := by
      have hp := (hg (Fintype.card ↥c.support) (fun i => (e.symm i : ℝ))).submatrix e
      change (Matrix.of fun i j : ↥c.support =>
        (g ((j : ℝ) - (i : ℝ)) : ℂ)).PosSemidef
      simpa only [Matrix.submatrix, Equiv.symm_apply_apply] using hp
    have h := hp.re_dotProduct_nonneg (fun i => ((c i : ℝ) : ℂ))
    change 0 ≤ Complex.re _ at h
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
      Finset.mul_sum, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at h
    have hs : (∑ i : ↥c.support, ∑ j : ↥c.support,
          c i * (g ((j : ℝ) - (i : ℝ)) * c j)) =
        ∑ i ∈ c.support, ∑ j ∈ c.support, c i * (g (j - i) * c j) := by
      calc
        _ = ∑ i : ↥c.support, ∑ j ∈ c.support, c i * (g (j - (i : ℝ)) * c j) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_coe_sort c.support
            (fun j : ℝ => c i * (g (j - (i : ℝ)) * c j))
        _ = _ := Finset.sum_coe_sort c.support
          (fun i : ℝ => ∑ j ∈ c.support, c i * (g (j - i) * c j))
    rw [hs] at h
    simpa only [Finsupp.sum, star_trivial, mul_assoc] using h

private def operatorKernel (g : ℝ → ℝ) : Matrix ℝ ℝ (ℝ →L[ℝ] ℝ) :=
  fun x y => g (y - x) • ContinuousLinearMap.id ℝ ℝ

private theorem operatorKernel_psd {g : ℝ → ℝ}
    (hg : Matrix.PosSemidef (fun x y : ℝ => g (y - x))) :
    (operatorKernel g).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro x y
    have he := hg.isHermitian.apply x y
    simpa [operatorKernel, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_id] using congrArg
      (fun r : ℝ => r • ContinuousLinearMap.id ℝ ℝ) he
  · intro c
    have he (a b : ℝ) : g (a - b) = g (b - a) := hg.isHermitian.apply a b
    simpa [operatorKernel, he, mul_assoc, mul_comm, mul_left_comm] using hg.2 c

private theorem constant_of_hasDerivAt_zero {F : ℝ → ℝ}
    (h : ∀ x, HasDerivAt F 0 x) (x y : ℝ) : F x = F y :=
  is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt)
    (fun x => (h x).deriv) x y

private theorem anchored_eq_inner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K Kx : ℝ → ℝ → ℝ} {v : ℝ → H} (hv : Continuous v)
    (hx : ∀ x y, HasDerivAt (fun u => K u y) (Kx x y) x)
    (hxy : ∀ x y, HasDerivAt (Kx x) (-inner ℝ (v x) (v y)) y)
    (x y : ℝ) :
    K x y - K x 0 - K 0 y + K 0 0 =
      -inner ℝ (∫ u in (0 : ℝ)..x, v u) (∫ u in (0 : ℝ)..y, v u) := by
  let V (x : ℝ) := ∫ u in (0 : ℝ)..x, v u
  have hV (x : ℝ) : HasDerivAt V (v x) x :=
    intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _)
      hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  have hfirst (u : ℝ) : Kx u y + inner ℝ (v u) (V y) = Kx u 0 := by
    have hd (t : ℝ) : HasDerivAt
        (fun z => Kx u z + inner ℝ (v u) (V z)) 0 t := by
      convert (hxy u t).add ((hasDerivAt_const t (v u)).inner ℝ (hV t)) using 1 <;>
        simp
    have hc := constant_of_hasDerivAt_zero hd y 0
    simpa [V] using hc
  have hd (t : ℝ) : HasDerivAt
      (fun z => K z y - K z 0 + inner ℝ (V z) (V y)) 0 t := by
    convert ((hx t y).sub (hx t 0)).add
      ((hV t).inner ℝ (hasDerivAt_const t (V y))) using 1
    simp only [inner_zero_right, zero_add]
    linarith [hfirst t]
  have hc := constant_of_hasDerivAt_zero hd x 0
  simp only [V, intervalIntegral.integral_same, inner_zero_left, add_zero] at hc
  change K x y - K x 0 + inner ℝ (V x) (V y) = K 0 y - K 0 0 at hc
  linarith

/-- A continuous Hilbert feature for the negative mixed derivative makes the
original kernel conditionally negative on every finite configuration. -/
theorem conditionallyNegative_of_mixed_feature
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K Kx : ℝ → ℝ → ℝ} {v : ℝ → H} (hv : Continuous v)
    (hx : ∀ x y, HasDerivAt (fun u => K u y) (Kx x y) x)
    (hxy : ∀ x y, HasDerivAt (Kx x) (-inner ℝ (v x) (v y)) y)
    {n : ℕ} (x : Fin n → ℝ) :
    Spectral.ConditionallyNegative (fun i j => K (x i) (x j)) := by
  intro c hc
  let V (u : ℝ) := ∫ z in (0 : ℝ)..u, v z
  have he (i j : Fin n) : K (x i) (x j) =
      K (x i) 0 + K 0 (x j) - K 0 0 - inner ℝ (V (x i)) (V (x j)) := by
    have h := anchored_eq_inner hv hx hxy (x i) (x j)
    change _ = -inner ℝ (V (x i)) (V (x j)) at h
    linarith
  change (∑ i, c i * ∑ j, K (x i) (x j) * c j) ≤ 0
  simp only [he, sub_mul, add_mul, mul_sub, mul_add, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, hc, mul_zero, Finset.sum_const_zero, sub_zero,
    zero_add, zero_sub, mul_neg, Finset.sum_neg_distrib]
  have hz : ∑ i, c i * ∑ j, K 0 (x j) * c j = 0 := by
    rw [← Finset.sum_mul, hc, zero_mul]
  rw [hz, zero_sub]
  have hs : (∑ i, c i * ∑ j, inner ℝ (V (x i)) (V (x j)) * c j) =
      inner ℝ (∑ i, c i • V (x i)) (∑ i, c i • V (x i)) := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm (V (x i)) (V (x j))]
    ring
  rw [hs]
  exact neg_nonpos.mpr (real_inner_self_nonneg)

/-- The exponential homogeneous kernel determined by a symmetric profile. -/
def logKernel (g : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.exp ((x + y) / 2) * g ((y - x) / 2)

private def logKernelDx (g : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.exp ((x + y) / 2) * (g ((y - x) / 2) - deriv g ((y - x) / 2)) / 2

private theorem logKernel_hasDerivAt_left {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (x y : ℝ) : HasDerivAt (fun u => logKernel g u y) (logKernelDx g x y) x := by
  have ha : HasDerivAt (fun u : ℝ => (u + y) / 2) (1 / 2) x := by
    convert ((hasDerivAt_id x).add_const y).div_const 2 using 1 <;>
      (try funext u) <;> (try dsimp) <;> ring
  have hb : HasDerivAt (fun u : ℝ => (y - u) / 2) (-1 / 2) x := by
    convert ((hasDerivAt_const x y).sub (hasDerivAt_id x)).div_const 2 using 1 <;>
      (try funext u) <;> (try dsimp) <;> ring
  convert ((Real.hasDerivAt_exp _).comp x ha).mul
    ((hg _).hasDerivAt.comp x hb) using 1 <;>
    (try funext u) <;> dsimp [logKernel, logKernelDx, Function.comp_def] <;> ring

private theorem logKernel_hasDerivAt_mixed {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (x y : ℝ) : HasDerivAt (logKernelDx g x)
      (-(Real.exp (x / 2) * Real.exp (y / 2) / 4 *
        (deriv (deriv g) ((y - x) / 2) - g ((y - x) / 2)))) y := by
  have ha : HasDerivAt (fun u : ℝ => (x + u) / 2) (1 / 2) y := by
    convert ((hasDerivAt_const y x).add (hasDerivAt_id y)).div_const 2 using 1 <;>
      (try funext u) <;> (try dsimp) <;> ring
  have hb : HasDerivAt (fun u : ℝ => (u - x) / 2) (1 / 2) y := by
    convert ((hasDerivAt_id y).sub_const x).div_const 2 using 1 <;>
      (try funext u) <;> (try dsimp) <;> ring
  have hd := (((Real.hasDerivAt_exp _).comp y ha).mul
    (((hg.differentiable (by norm_num) _).hasDerivAt.comp y hb).sub
      ((hg.differentiable_deriv_two _).hasDerivAt.comp y hb))).div_const 2
  convert hd using 1
  · rfl
  · dsimp [Function.comp_def]
    rw [show (x + y) / 2 = x / 2 + y / 2 by ring, Real.exp_add]
    ring

/-- Positive definite profile curvature gives conditional negativity after
the exponential homogeneous reconstruction. -/
theorem conditionallyNegative_logKernel {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hpd : D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
      (fun t => ((deriv (deriv g) t - g t : ℝ) : ℂ)))
    {n : ℕ} (x : Fin n → ℝ) :
    Spectral.ConditionallyNegative (fun i j => logKernel g (x i) (x j)) := by
  let f (t : ℝ) := deriv (deriv g) t - g t
  have hf : Continuous f :=
    ((hg.deriv' : ContDiff ℝ 1 (deriv g)).continuous_deriv (by norm_num)).sub hg.continuous
  let O := operatorKernel f
  have hscalar := real_translation_psd hpd
  letI : Fact O.PosSemidef := ⟨operatorKernel_psd hscalar⟩
  let H := RKHS.OfKernel O
  let w (t : ℝ) : H := RKHS.kerFun H t (1 : ℝ)
  have hkernel : RKHS.kernel (𝕜 := ℝ) (X := ℝ) (V := ℝ) H = O :=
    RKHS.OfKernel.kernel_ofKernel
  have hwc : Continuous w := by
    have hO : Continuous
        (fun p : ℝ × ℝ => RKHS.kernel (𝕜 := ℝ) (V := ℝ) H p.1 p.2) := by
      rw [hkernel]
      exact (hf.comp (continuous_snd.sub continuous_fst)).smul continuous_const
    exact ((RKHS.continuous_kernel_iff_continuous_kerFun H).mp hO).clm_apply
      continuous_const
  have hwi (a b : ℝ) : inner ℝ (w a) (w b) = f (b - a) := by
    have he := hscalar.isHermitian.apply a b
    simpa [w, ← RKHS.kernel_inner, hkernel, O, operatorKernel] using he
  let v (t : ℝ) : H := (Real.exp (t / 2) / 2) • w (t / 2)
  have hvc : Continuous v := by
    exact (Real.continuous_exp.comp (continuous_id.div_const 2) |>.div_const 2).smul
      (hwc.comp (continuous_id.div_const 2))
  apply conditionallyNegative_of_mixed_feature hvc
    (logKernel_hasDerivAt_left (hg.differentiable (by norm_num))) (x := x)
  intro a b
  convert logKernel_hasDerivAt_mixed hg a b using 1
  simp only [v, inner_smul_left, inner_smul_right, RCLike.conj_to_real, hwi]
  dsimp [f]
  rw [show b / 2 - a / 2 = (b - a) / 2 by ring]
  ring

/-- Every Stolarsky mean matrix with parameter at least two is conditionally negative. -/
theorem conditionallyNegative_stolarsky {γ : ℝ} (hγ : 2 ≤ γ)
    {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    Spectral.ConditionallyNegative (stolarskyMatrix γ a) := by
  have h := conditionallyNegative_logKernel
    (KernelFactor.psi_contDiff (n := 2) hγ) (KernelFactor.positiveDefinite_f hγ)
    (fun i => Real.log (a i))
  have heq : stolarskyMatrix γ a =
      (fun i j => logKernel (psi γ) (Real.log (a i)) (Real.log (a j))) := by
    ext i j
    rw [stolarskyMatrix, stolarsky_eq_profileKernel γ (ha i) (ha j)]
    dsimp [profileKernel, logKernel]
    congr 1
    have he (r : ℝ) (hr : 0 < r) : Real.sqrt r = Real.exp (Real.log r / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
      congr 1
      ring
    rw [he _ (ha i), he _ (ha j), ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact h

/-- Positive entries and conditional negativity give exactly one positive eigenvalue. -/
theorem inClassA_stolarsky {γ : ℝ} (hγ : 2 ≤ γ)
    {n : ℕ} (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 < a i) :
    InClassA (stolarskyMatrix γ a) := by
  apply Spectral.inClassA_of_conditionallyNegative
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa [stolarskyMatrix] using stolarsky_symm γ (a j) (a i)
  · exact fun i j => stolarsky_pos hγ (ha i) (ha j)
  · exact conditionallyNegative_stolarsky hγ a ha

/-- The two parameter ranges in the Stolarsky class A conjecture. -/
theorem result : claim := by
  constructor
  · intro γ hγ n a ha
    exact inClassA_stolarsky hγ a ha
  · intro γ hγ hγ2
    obtain ⟨z, hz, hcount⟩ := ThreePoint.exists_threePoint hγ hγ2
    refine ⟨3, ![Real.exp (-2 * z), 1, Real.exp (2 * z)], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [Real.exp_pos]
    · intro hA
      rw [hA.2] at hcount
      omega

end D5.S3.Quantum.Matrix.StolarskyMean.Result
