/- GID: D5/S3/Quantum/Divergence/InversePowerIntegralProbe
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/InversePowerIntegralProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual entropy loss controls supported inverse-square-root intertwining in L2. -/

import D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Supported inverse-square-root stability in the Euclidean L2 carrier. -/

noncomputable section
universe u v
open Matrix Set MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology

namespace D5.S3.Quantum.Divergence.InversePowerIntegralProbe

private def inversePowerKernel (alpha lambda t : ℝ) : ℝ :=
  t ^ (-alpha) / (lambda + t)

/-- Evaluate the normalizer already present in Mathlib's positive-power formula. -/
private theorem power_normalizer (p : ℝ) (hp : p ∈ Ioo 0 1) :
    (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1) =
      Real.pi / Real.sin (Real.pi * p) := by
  let phi : ℝ → ℝ := fun x => x / (1 - x)
  let g : ℝ → ℝ := fun t => t ^ (p - 1) / (1 + t)
  have hphi : phi '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact div_pos hx.1 (sub_pos.mpr hx.2)
    · intro ht
      have hden : 0 < 1 + t := by linarith
      have hx0 : 0 < t / (1 + t) := div_pos ht hden
      have hx1 : t / (1 + t) < 1 := (div_lt_one hden).2 (by linarith)
      refine ⟨t / (1 + t), ⟨hx0, hx1⟩, ?_⟩
      apply (div_eq_iff (sub_pos.mpr hx1).ne').2
      field_simp [hden.ne']
      <;> ring
  have hinj : InjOn phi (Ioo (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hsx : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
    have hsy : 1 - y ≠ 0 := (sub_pos.mpr hy.2).ne'
    have h := (div_eq_div_iff hsx hsy).mp hxy
    nlinarith
  have hder (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivWithinAt phi (((1 - x) ^ (2 : Nat))⁻¹) (Ioo 0 1) x := by
    have h := (hasDerivAt_id x).div ((hasDerivAt_id x).const_sub 1)
      (sub_pos.mpr hx.2).ne'
    convert h.hasDerivWithinAt using 1 <;> dsimp only [phi] <;> ring
  have hpoint (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      |((1 - x) ^ (2 : Nat))⁻¹| • g (phi x) =
        x ^ (p - 1) * (1 - x) ^ (-p) := by
    have hs : 0 < 1 - x := sub_pos.mpr hx.2
    have hden : 1 + x / (1 - x) = (1 - x)⁻¹ := by
      field_simp [hs.ne']
      <;> ring
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    dsimp only [g, phi]
    rw [smul_eq_mul, Real.div_rpow hx.1.le hs.le, hden,
      Real.rpow_sub_one hs.ne' p, Real.rpow_neg hs.le]
    field_simp [hs.ne', (Real.rpow_pos_of_pos hs p).ne']
    <;> ring
  have hsubst : (∫ t in Ioi (0 : ℝ), g t) =
      ∫ x in Ioo (0 : ℝ) 1, x ^ (p - 1) * (1 - x) ^ (-p) := by
    have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj g
    rw [hphi] at h
    exact h.trans (setIntegral_congr_fun measurableSet_Ioo hpoint)
  have hbeta :
      ((∫ x in Ioo (0 : ℝ) 1, x ^ (p - 1) * (1 - x) ^ (-p) : ℝ) : ℂ) =
        Complex.betaIntegral (p : ℂ) (1 - (p : ℂ)) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
    push_cast
    congr 1 <;> congr 1 <;> ring
  have hgamma : Complex.betaIntegral (p : ℂ) (1 - (p : ℂ)) =
      (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (p : ℂ)) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
      (s := (p : ℂ)) (t := 1 - (p : ℂ))
      (by simpa using hp.1) (by simpa using sub_pos.mpr hp.2)
    have hsum : (p : ℂ) + (1 - (p : ℂ)) = 1 := by ring
    rw [hsum, Complex.Gamma_one, one_mul] at h
    exact h.symm.trans (Complex.Gamma_mul_Gamma_one_sub (p : ℂ))
  have hkernel : (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1) =
      ∫ t in Ioi (0 : ℝ), g t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [Real.rpowIntegrand₀₁_eq_pow_div hp ht.le zero_le_one]
    simp only [g, mul_one, add_comm]
  apply Complex.ofReal_injective
  rw [hkernel, hsubst, hbeta, hgamma]
  simp only [Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul]

private theorem scalar_inverse_power_integral (alpha : ℝ) (halpha : alpha ∈ Ioo 0 1)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    IntegrableOn (inversePowerKernel alpha lambda) (Ioi (0 : ℝ)) ∧
      (Real.sin (Real.pi * alpha) / Real.pi) *
        (∫ t in Ioi (0 : ℝ), inversePowerKernel alpha lambda t) = lambda ^ (-alpha) := by
  have hp : 1 - alpha ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [halpha.1, halpha.2]
  have hkernel : EqOn
      (fun t => lambda⁻¹ * Real.rpowIntegrand₀₁ (1 - alpha) t lambda)
      (inversePowerKernel alpha lambda) (Ioi (0 : ℝ)) := by
    intro t ht
    rw [Real.rpowIntegrand₀₁_eq_pow_div hp ht.le hlambda.le]
    dsimp only [inversePowerKernel]
    rw [show (1 - alpha) - 1 = -alpha by ring]
    field_simp [hlambda.ne', ne_of_gt (add_pos ht hlambda),
      ne_of_gt (add_pos hlambda ht)]
    <;> ring
  have hraw := Real.integrableOn_rpowIntegrand₀₁_Ioi hp hlambda.le
  have hi : IntegrableOn (inversePowerKernel alpha lambda) (Ioi (0 : ℝ)) :=
    (hraw.const_mul lambda⁻¹).congr_fun hkernel measurableSet_Ioi
  have hsin : 0 < Real.sin (Real.pi * alpha) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos halpha.1)
      (by simpa using mul_lt_mul_of_pos_left halpha.2 Real.pi_pos)
  have hnorm : (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ (1 - alpha) t 1) =
      Real.pi / Real.sin (Real.pi * alpha) := by
    rw [power_normalizer (1 - alpha) hp,
      show Real.pi * (1 - alpha) = Real.pi - Real.pi * alpha by ring,
      Real.sin_pi_sub]
  refine ⟨hi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hkernel, integral_const_mul,
    Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp hlambda.le, hnorm]
  have hpow : lambda ^ (-alpha) = lambda ^ (1 - alpha) / lambda := by
    rw [← Real.rpow_sub_one hlambda.ne']
    congr 1
    ring
  rw [hpow]
  field_simp [Real.pi_ne_zero, hsin.ne', hlambda.ne']
  <;> ring

private theorem finite_inverse_power_integral
    {i : Type*} [Fintype i]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (alpha : ℝ) (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    (lambda : i → ℝ) (hlambda : ∀ j, 0 < lambda j) (c : i → E) :
    IntegrableOn (fun t : ℝ => ∑ j, inversePowerKernel alpha (lambda j) t • c j)
        (Ioi (0 : ℝ)) ∧
      (Real.sin (Real.pi * alpha) / Real.pi) •
        (∫ t in Ioi (0 : ℝ), ∑ j, inversePowerKernel alpha (lambda j) t • c j) =
        ∑ j, (lambda j) ^ (-alpha) • c j := by
  classical
  have hi (j : i) : IntegrableOn
      (fun t : ℝ => inversePowerKernel alpha (lambda j) t • c j) (Ioi (0 : ℝ)) :=
    (scalar_inverse_power_integral alpha halpha (lambda j) (hlambda j)).1.smul_const (c j)
  refine ⟨integrable_finsetSum Finset.univ (fun j _ => hi j), ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ => hi j), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_smul_const, smul_smul,
    (scalar_inverse_power_integral alpha halpha (lambda j) (hlambda j)).2]

private theorem cfc_vector_expansion_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian)
    (f : Real → Real) (a : n → Complex) :
    cfc f A *ᵥ a = ∑ j, f (hA.eigenvalues j) •
      (fun i => hA.eigenvectorUnitary i j * (hA.eigenvectorUnitaryᴴ *ᵥ a) j) := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul]
  simpa only [mul_assoc] using ResolventFunctionalRigidity.cfc_vector_expansion A hA f a i

/-- The positive-definite matrix-vector inverse-power formula on the
full positive axis. No L2/sup-norm identification is used in this statement. -/
private theorem matrix_inverse_power_integral {n : Type*} [Fintype n] [DecidableEq n]
    (alpha : ℝ) (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    (A : Matrix n n Complex) (hA : A.PosDef) (a : n → Complex) :
    IntegrableOn (fun t : Real => t ^ (-alpha) •
      ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a)) (Ioi (0 : Real)) ∧
      (Real.sin (Real.pi * alpha) / Real.pi) • (∫ t in Ioi (0 : Real), t ^ (-alpha) •
        ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a)) =
        cfc (fun x : Real => x ^ (-alpha)) A *ᵥ a := by
  classical
  let c : n → (n → Complex) := fun j i =>
    hA.1.eigenvectorUnitary i j * (hA.1.eigenvectorUnitaryᴴ *ᵥ a) j
  have hpoint (t : Real) (ht : 0 < t) :
      t ^ (-alpha) • ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a) =
        ∑ j, inversePowerKernel alpha (hA.1.eigenvalues j) t • c j := by
    rw [← ResolventFunctionalRigidity.cfc_shift_inverse A hA.posSemidef t ht,
      cfc_vector_expansion_sum A hA.1 (fun x : Real => (x + t)⁻¹) a,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    simp only [inversePowerKernel, div_eq_mul_inv, c]
  obtain ⟨hi, hv⟩ := finite_inverse_power_integral alpha halpha
    hA.1.eigenvalues hA.eigenvalues_pos c
  have hi' : IntegrableOn (fun t : Real => t ^ (-alpha) •
      ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a)) (Ioi (0 : Real)) :=
    hi.congr_fun (fun t ht => (hpoint t ht).symm) measurableSet_Ioi
  refine ⟨hi', ?_⟩
  calc
    (Real.sin (Real.pi * alpha) / Real.pi) • (∫ t in Ioi (0 : Real), t ^ (-alpha) •
        ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a)) =
        (Real.sin (Real.pi * alpha) / Real.pi) • (∫ t in Ioi (0 : Real),
          ∑ j, inversePowerKernel alpha (hA.1.eigenvalues j) t • c j) := by
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpoint t ht)
    _ = ∑ j, (hA.1.eigenvalues j) ^ (-alpha) • c j := hv
    _ = cfc (fun x : Real => x ^ (-alpha)) A *ᵥ a :=
      (cfc_vector_expansion_sum A hA.1 (fun x : Real => x ^ (-alpha)) a).symm

/-- Integrals pass through the genuine L2 equivalence and the finite matrix map. -/
theorem l2_inverse_power_integral
    {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (alpha : ℝ) (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    (A : Matrix n n ℂ) (B : Matrix k k ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (V : Matrix n k ℂ) (ξ : n → ℂ) (η : k → ℂ) :
    let w : ℝ → EuclideanSpace ℂ n := fun t => WithLp.toLp 2
      ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η))
    IntegrableOn (fun t : ℝ => (t ^ (-alpha)) • w t) (Ioi 0) ∧
      (Real.sin (Real.pi * alpha) / Real.pi) • (∫ t in Ioi (0 : ℝ), (t ^ (-alpha)) • w t) =
        WithLp.toLp 2 (cfc (fun x : ℝ => x ^ (-alpha)) A *ᵥ ξ -
          V *ᵥ (cfc (fun x : ℝ => x ^ (-alpha)) B *ᵥ η)) := by
  classical
  let T : (n → ℂ) ≃L[ℝ] EuclideanSpace ℂ n :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : n => ℂ)).symm
  let L : (k → ℂ) →L[ℝ] (n → ℂ) :=
    (V.mulVecLin.restrictScalars ℝ).toContinuousLinearMap
  let f : ℝ → (n → ℂ) := fun t => t ^ (-alpha) • ((A + t • 1)⁻¹ *ᵥ ξ)
  let g : ℝ → (k → ℂ) := fun t => t ^ (-alpha) • ((B + t • 1)⁻¹ *ᵥ η)
  obtain ⟨hf, hfval⟩ := matrix_inverse_power_integral alpha halpha A hA ξ
  obtain ⟨hg, hgval⟩ := matrix_inverse_power_integral alpha halpha B hB η
  have hdiff : IntegrableOn (fun t => f t - L (g t)) (Ioi (0 : ℝ)) :=
    hf.sub (L.integrable_comp hg)
  have hpoint (t : ℝ) (ht : 0 < t) :
      T (f t - L (g t)) = (t ^ (-alpha)) • (WithLp.toLp 2
        ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η)) : EuclideanSpace ℂ n) := by
    rw [map_sub, map_smul, map_smul]
    change t ^ (-alpha) • T ((A + t • 1)⁻¹ *ᵥ ξ) -
      T (t ^ (-alpha) • L ((B + t • 1)⁻¹ *ᵥ η)) = _
    rw [map_smul, ← smul_sub]
    rfl
  have hi : IntegrableOn (fun t : ℝ => (t ^ (-alpha)) • (WithLp.toLp 2
      ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η)) : EuclideanSpace ℂ n)) (Ioi 0) :=
    IntegrableOn.congr_fun (T.toContinuousLinearMap.integrable_comp hdiff)
      (fun t ht => hpoint t ht) measurableSet_Ioi
  refine ⟨hi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpoint t ht),
    T.integral_comp_comm, ← T.map_smul, integral_sub hf (L.integrable_comp hg),
    L.integral_comp_comm hg, smul_sub, ← L.map_smul, hfval, hgval]
  rfl


#print axioms l2_inverse_power_integral

end D5.S3.Quantum.Divergence.InversePowerIntegralProbe
