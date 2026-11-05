/- GID: D5/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual entropy loss controls supported inverse-square-root intertwining in L2. -/

import D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget
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
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI

namespace D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability

private def inversePowerKernel (alpha lambda t : ℝ) : ℝ :=
  t ^ (-alpha) / (lambda + t)

/-- Evaluate the normalizer already present in Mathlib's positive-power formula. -/
theorem power_normalizer (p : ℝ) (hp : p ∈ Ioo 0 1) :
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
      have ht0 : 0 < t := ht
      have hden : 0 < 1 + t := add_pos zero_lt_one ht0
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
    have hfun : (id / fun y : ℝ => 1 - id y) = phi := rfl
    rw [hfun] at h
    have hcoeff : (1 * (1 - id x) - id x * -1) / (1 - id x) ^ 2 =
        ((1 - x) ^ (2 : Nat))⁻¹ := by
      change (1 * (1 - x) - x * -1) / (1 - x) ^ 2 = ((1 - x) ^ (2 : Nat))⁻¹
      ring
    rw [hcoeff] at h
    exact h.hasDerivWithinAt
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
    dsimp only
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
    change Real.rpowIntegrand₀₁ p t 1 = g t
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
    change lambda⁻¹ * Real.rpowIntegrand₀₁ (1 - alpha) t lambda =
      inversePowerKernel alpha lambda t
    rw [Real.rpowIntegrand₀₁_eq_pow_div hp ht.le hlambda.le]
    dsimp only [inversePowerKernel]
    rw [show (1 - alpha) - 1 = -alpha by ring]
    field_simp [hlambda.ne', ne_of_gt (add_pos ht hlambda),
      ne_of_gt (add_pos hlambda ht)]
    <;> ring
  have hraw := Real.integrableOn_rpowIntegrand₀₁_Ioi hp hlambda.le
  have hi : IntegrableOn (inversePowerKernel alpha lambda) (Ioi (0 : ℝ)) :=
    IntegrableOn.congr_fun (hraw.const_mul lambda⁻¹) hkernel measurableSet_Ioi
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

private theorem reciprocal_sqrt_eq_rpow (t : Real) (ht : 0 ≤ t) :
    1 / Real.sqrt t = t ^ (-1 / 2 : Real) := by
  rw [show (-1 / 2 : Real) = -(1 / 2 : Real) by norm_num,
    Real.rpow_neg ht, ← Real.sqrt_eq_rpow, one_div]

private theorem near_kernel (a : Real) (ha : 0 < a) :
    IntegrableOn (fun t : Real => t ^ (-1 / 2 : Real)) (Ioc 0 a) ∧
      (∫ t in Ioc (0 : Real) a, t ^ (-1 / 2 : Real)) = 2 * Real.sqrt a := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := (0 : Real)) (b := a)
    (r := (-1 / 2 : Real)) (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le] at hi
  refine ⟨hi, ?_⟩
  rw [← intervalIntegral.integral_of_le ha.le,
    integral_rpow (Or.inl (by norm_num))]
  norm_num [show (-1 / 2 : Real) + 1 = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  <;> ring

private theorem tail_kernel (a : Real) (ha : 0 < a) :
    IntegrableOn (fun t : Real => (t⁻¹)^2) (Ioi a) ∧
      (∫ t in Ioi a, (t⁻¹)^2) = a⁻¹ := by
  have heq : EqOn (fun t : Real => t ^ (-2 : Real))
      (fun t : Real => (t⁻¹)^2) (Ioi a) := by
    intro t ht
    dsimp only
    rw [show (-2 : Real) = -(2 : Real) by norm_num,
      Real.rpow_neg (ha.le.trans ht.le), Real.rpow_two, inv_pow]
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) ha
  refine ⟨hi.congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq]
  simpa only [show (-2 : Real) + 1 = -1 by norm_num,
    Real.rpow_neg_one, div_neg, div_one, neg_neg] using
    (integral_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) ha)

/-- The direct near/tail estimate in the actual L2 carrier. -/
private theorem euclidean_split_bound {n : Type*} [Fintype n]
    (w : Real → EuclideanSpace Complex n)
    (e : EuclideanSpace Complex n) (m delta : Real) (_hm : 0 < m)
    (hi : IntegrableOn (fun t : Real => (1 / Real.sqrt t) • w t) (Ioi 0))
    (hE : IntegrableOn (fun t : Real => t * ‖w t‖^2) (Ioi 0))
    (hbudget : (∫ t in Ioi (0 : Real), t * ‖w t‖^2) ≤ delta)
    (hwbound : ∀ t : Real, 0 < t → ‖w t‖ ≤ 2 / m)
    (he : e = Real.pi⁻¹ • (∫ t in Ioi (0 : Real), (1 / Real.sqrt t) • w t))
    (a : Real) (ha : 0 < a) :
    ‖e‖ ≤ Real.pi⁻¹ * (4 * Real.sqrt a / m + Real.sqrt delta / Real.sqrt a) := by
  let N : Real → Real := fun t => ‖(1 / Real.sqrt t) • w t‖
  let E : Real → Real := fun t => t * ‖w t‖^2
  have hN : IntegrableOn N (Ioi (0 : Real)) := hi.norm
  have hNnear : IntegrableOn N (Ioc (0 : Real) a) :=
    hN.mono_set (fun t ht => ht.1)
  have hNtail : IntegrableOn N (Ioi a) :=
    hN.mono_set (Ioi_subset_Ioi ha.le)
  have hEtail : IntegrableOn E (Ioi a) :=
    hE.mono_set (Ioi_subset_Ioi ha.le)
  have hE0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : Real))] E := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (sq_nonneg _)
  have hEtailbudget : (∫ t in Ioi a, E t) ≤ delta := by
    exact (setIntegral_mono_set hE hE0
      (.of_forall (Ioi_subset_Ioi ha.le))).trans hbudget
  obtain ⟨hK, hKval⟩ := near_kernel a ha
  have hnear : (∫ t in Ioc (0 : Real) a, N t) ≤ 4 * Real.sqrt a / m := by
    have hpoint : ∀ t ∈ Ioc (0 : Real) a,
        N t ≤ (2 / m) * t ^ (-1 / 2 : Real) := by
      intro t ht
      dsimp only [N]
      rw [norm_smul, Real.norm_of_nonneg
        (one_div_nonneg.mpr (Real.sqrt_nonneg t)),
        ← reciprocal_sqrt_eq_rpow t ht.1.le]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hwbound t ht.1)
          (one_div_nonneg.mpr (Real.sqrt_nonneg t))
    calc
      (∫ t in Ioc (0 : Real) a, N t) ≤
          ∫ t in Ioc (0 : Real) a, (2 / m) * t ^ (-1 / 2 : Real) :=
        setIntegral_mono_on hNnear (hK.const_mul (2 / m)) measurableSet_Ioc hpoint
      _ = 4 * Real.sqrt a / m := by rw [integral_const_mul, hKval]; ring
  let F : Real → Real := fun t => Real.sqrt t * ‖w t‖
  let G : Real → Real := fun t => t⁻¹
  have hGcont : ContinuousOn G (Ioi a) :=
    continuousOn_id.inv₀ (fun t ht => (ha.trans ht).ne')
  have hFpoint : EqOn (fun t => E t) (fun t => F t ^ 2) (Ioi a) := by
    intro t ht
    dsimp only [E, F]
    rw [mul_pow, Real.sq_sqrt (ha.le.trans ht.le)]
  have hF2 : IntegrableOn (fun t => F t ^ 2) (Ioi a) :=
    hEtail.congr_fun hFpoint measurableSet_Ioi
  have hFval : (∫ t in Ioi a, F t ^ 2) = ∫ t in Ioi a, E t :=
    (setIntegral_congr_fun measurableSet_Ioi hFpoint).symm
  obtain ⟨hG2, hGval⟩ := tail_kernel a ha
  have hFmeas : AEStronglyMeasurable F (volume.restrict (Ioi a)) := by
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable
      hEtail.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [E, F]
    rw [Real.sqrt_mul (ha.le.trans ht.le), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  have hFLp : MemLp F 2 (volume.restrict (Ioi a)) :=
    (memLp_two_iff_integrable_sq hFmeas).2 hF2
  have hGLp : MemLp G 2 (volume.restrict (Ioi a)) :=
    (memLp_two_iff_integrable_sq
      (hGcont.aestronglyMeasurable measurableSet_Ioi)).2 hG2
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioi a)) (p := (2 : Real)) (q := (2 : Real))
    Real.HolderConjugate.two_two
    (.of_forall (fun t => mul_nonneg (Real.sqrt_nonneg t) (norm_nonneg (w t))))
    (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => inv_nonneg.mpr (ha.le.trans ht.le)))
    (by simpa using hFLp) (by simpa using hGLp)
  have hCS' : (∫ t in Ioi a, F t * G t) ≤
      Real.sqrt (∫ t in Ioi a, E t) * Real.sqrt (a⁻¹) := by
    change (∫ t in Ioi a, F t * G t) ≤
      (∫ t in Ioi a, F t ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ t in Ioi a, G t ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) at hCS
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, hFval, hGval, G] using hCS
  have hprod : EqOn (fun t => F t * G t) N (Ioi a) := by
    intro t ht
    have ht0 : 0 < t := ha.trans ht
    have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    dsimp only [F, G, N]
    rw [norm_smul, Real.norm_of_nonneg
      (one_div_nonneg.mpr (Real.sqrt_nonneg t))]
    have hratio : Real.sqrt t * t⁻¹ = 1 / Real.sqrt t := by
      apply (eq_div_iff hs).2
      calc
        (Real.sqrt t * t⁻¹) * Real.sqrt t = (Real.sqrt t)^2 * t⁻¹ := by ring
        _ = 1 := by rw [Real.sq_sqrt ht0.le, mul_inv_cancel₀ ht0.ne']
    calc
      (Real.sqrt t * ‖w t‖) * t⁻¹ = (Real.sqrt t * t⁻¹) * ‖w t‖ := by ring
      _ = (1 / Real.sqrt t) * ‖w t‖ := by rw [hratio]
  have htail : (∫ t in Ioi a, N t) ≤ Real.sqrt delta / Real.sqrt a := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hprod]
    calc
      (∫ t in Ioi a, F t * G t) ≤
          Real.sqrt (∫ t in Ioi a, E t) * Real.sqrt (a⁻¹) := hCS'
      _ ≤ Real.sqrt delta * Real.sqrt (a⁻¹) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hEtailbudget)
          (Real.sqrt_nonneg _)
      _ = Real.sqrt delta / Real.sqrt a := by
        rw [Real.sqrt_inv]
        simp only [div_eq_mul_inv]
  have hdisjoint : Disjoint (Ioc (0 : Real) a) (Ioi a) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  have hsplit : (∫ t in Ioi (0 : Real), N t) =
      (∫ t in Ioc (0 : Real) a, N t) + (∫ t in Ioi a, N t) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union hdisjoint measurableSet_Ioi hNnear hNtail
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
  calc
    ‖∫ t in Ioi (0 : Real), (1 / Real.sqrt t) • w t‖ ≤
        ∫ t in Ioi (0 : Real), N t := norm_integral_le_integral_norm _
    _ ≤ 4 * Real.sqrt a / m + Real.sqrt delta / Real.sqrt a := by
      rw [hsplit]
      exact add_le_add hnear htail

/-- The exact optimized fourth-root estimate, including the zero-budget case. -/
private theorem euclidean_inverse_sqrt_bound_from_budget {n : Type*} [Fintype n]
    (w : Real → EuclideanSpace Complex n)
    (e : EuclideanSpace Complex n) (m delta : Real) (hm : 0 < m)
    (hi : IntegrableOn (fun t : Real => (1 / Real.sqrt t) • w t) (Ioi 0))
    (hE : IntegrableOn (fun t : Real => t * ‖w t‖^2) (Ioi 0))
    (hbudget : (∫ t in Ioi (0 : Real), t * ‖w t‖^2) ≤ delta)
    (hwbound : ∀ t : Real, 0 < t → ‖w t‖ ≤ 2 / m)
    (he : e = Real.pi⁻¹ • (∫ t in Ioi (0 : Real), (1 / Real.sqrt t) • w t)) :
    ‖e‖ ≤ 4 / (Real.pi * Real.sqrt m) * delta ^ (1 / 4 : Real) := by
  have hE0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : Real))]
      (fun t : Real => t * ‖w t‖^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (sq_nonneg _)
  have hd0 : 0 ≤ delta := (integral_nonneg_of_ae hE0).trans hbudget
  by_cases hd : delta = 0
  · have hzero : (∫ t in Ioi (0 : Real), t * ‖w t‖^2) = 0 :=
      le_antisymm (hd ▸ hbudget) (integral_nonneg_of_ae hE0)
    have hAE := (integral_eq_zero_iff_of_nonneg_ae hE0 hE).mp hzero
    have hwzero : (fun t : Real => (1 / Real.sqrt t) • w t)
        =ᵐ[volume.restrict (Ioi (0 : Real))] 0 := by
      filter_upwards [hAE, ae_restrict_mem measurableSet_Ioi] with t hz ht
      have hn : ‖w t‖^2 = 0 :=
        (mul_eq_zero.mp hz).resolve_left (ne_of_gt ht)
      have hw0 : w t = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
      simp only [hw0, smul_zero, Pi.zero_apply]
    rw [he, integral_congr_ae hwzero]
    simp [hd]
  · have hdpos : 0 < delta := lt_of_le_of_ne hd0 (Ne.symm hd)
    let r : Real := Real.sqrt (Real.sqrt delta)
    let s : Real := Real.sqrt m
    have hr : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hdpos)
    have hs : 0 < s := Real.sqrt_pos.mpr hm
    have hr2 : r^2 = Real.sqrt delta := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hs2 : s^2 = m := Real.sq_sqrt hm.le
    have hquarter : delta ^ (1 / 4 : Real) = r := by
      dsimp only [r]
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hd0]
      norm_num
    let a : Real := (s * r / 2)^2
    have ha : 0 < a := sq_pos_of_pos (by positivity)
    have hasqrt : Real.sqrt a = s * r / 2 := by
      dsimp only [a]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
    have hb := euclidean_split_bound w e m delta hm hi hE hbudget hwbound he a ha
    rw [hasqrt] at hb
    have hopt : Real.pi⁻¹ *
        (4 * (s * r / 2) / m + Real.sqrt delta / (s * r / 2)) =
          4 / (Real.pi * Real.sqrt m) * delta ^ (1 / 4 : Real) := by
      rw [hquarter]
      change Real.pi⁻¹ * (4 * (s * r / 2) / m + Real.sqrt delta / (s * r / 2)) =
        4 / (Real.pi * s) * r
      rw [← hr2, ← hs2]
      field_simp [hr.ne', hs.ne', Real.pi_ne_zero]
      <;> ring
    exact hb.trans_eq hopt


theorem l2_norm_sq {n : Type*} [Fintype n] (x : n → ℂ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 = (star x ⬝ᵥ x).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, RCLike.re_to_complex]

theorem l2_contraction {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (V : Matrix n k ℂ) (hV : Vᴴ * V ≤ 1) (x : k → ℂ) :
    ‖(WithLp.toLp 2 (V *ᵥ x) : EuclideanSpace ℂ n)‖ ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ k)‖ := by
  have h := (Matrix.le_iff.mp hV).re_dotProduct_nonneg x
  change 0 ≤ (star x ⬝ᵥ ((1 - Vᴴ * V) *ᵥ x)).re at h
  have hpair : star (V *ᵥ x) ⬝ᵥ (V *ᵥ x) = star x ⬝ᵥ ((Vᴴ * V) *ᵥ x) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at h
  rw [← hpair, ← l2_norm_sq, ← l2_norm_sq] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (V *ᵥ x) : EuclideanSpace ℂ n),
    norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ k)]

theorem l2_resolvent_bound {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) (m : ℝ) (hm : 0 < m)
    (hfloor : m • (1 : Matrix n n ℂ) ≤ A) (x : n → ℂ) (t : ℝ) (ht : 0 < t) :
    ‖(WithLp.toLp 2 ((A + t • 1)⁻¹ *ᵥ x) : EuclideanSpace ℂ n)‖ ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ / m := by
  let H := A + t • (1 : Matrix n n ℂ)
  let y := H⁻¹ *ᵥ x
  have hH : H.PosDef := Matrix.PosDef.posSemidef_add hA.posSemidef (Matrix.PosDef.one.smul ht)
  have hy : H *ᵥ y = x := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H
      ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit), Matrix.one_mulVec]
  have hcoerce : m * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ n)‖^2 ≤
      (star y ⬝ᵥ x).re := by
    have hf := (Matrix.le_iff.mp hfloor).re_dotProduct_nonneg y
    change 0 ≤ (star y ⬝ᵥ ((A - m • 1) *ᵥ y)).re at hf
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, Complex.sub_re, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hf
    have henergy : (star y ⬝ᵥ x).re =
        (star y ⬝ᵥ (A *ᵥ y)).re + t * (star y ⬝ᵥ y).re := by
      rw [← hy]
      simp [H, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_add, dotProduct_smul, Complex.real_smul]
    rw [l2_norm_sq]
    have hn := (Matrix.PosSemidef.one).re_dotProduct_nonneg y
    change 0 ≤ (star y ⬝ᵥ ((1 : Matrix n n ℂ) *ᵥ y)).re at hn
    simp only [Matrix.one_mulVec] at hn
    nlinarith [mul_nonneg ht.le hn]
  have hcs : (star y ⬝ᵥ x).re ≤
      ‖(WithLp.toLp 2 y : EuclideanSpace ℂ n)‖ *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := by
    simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, RCLike.re_to_complex]
      using re_inner_le_norm (𝕜 := ℂ)
        (WithLp.toLp 2 y : EuclideanSpace ℂ n) (WithLp.toLp 2 x)
  change ‖(WithLp.toLp 2 y : EuclideanSpace ℂ n)‖ ≤ _
  by_cases hz : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ n)‖ = 0
  · rw [hz]
    exact div_nonneg (norm_nonneg _) hm.le
  · apply (le_div_iff₀ hm).2
    have hypos := lt_of_le_of_ne (norm_nonneg (WithLp.toLp 2 y : EuclideanSpace ℂ n))
      (Ne.symm hz)
    nlinarith

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

private theorem l2_inverse_sqrt_integral
    {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (A : Matrix n n ℂ) (B : Matrix k k ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (V : Matrix n k ℂ) (ξ : n → ℂ) (η : k → ℂ) :
    let w : ℝ → EuclideanSpace ℂ n := fun t => WithLp.toLp 2
      ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η))
    IntegrableOn (fun t : ℝ => (1 / Real.sqrt t) • w t) (Ioi 0) ∧
      Real.pi⁻¹ • (∫ t in Ioi (0 : ℝ), (1 / Real.sqrt t) • w t) =
        WithLp.toLp 2 (cfc (fun x : ℝ => 1 / Real.sqrt x) A *ᵥ ξ -
          V *ᵥ (cfc (fun x : ℝ => 1 / Real.sqrt x) B *ᵥ η)) := by
  obtain ⟨hi, he⟩ := l2_inverse_power_integral (1 / 2) (by norm_num)
    A B hA hB V ξ η
  have hAhalf : cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A =
      cfc (fun x : ℝ => 1 / Real.sqrt x) A := by
    apply cfc_congr
    intro x hx
    rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    simpa only [neg_div] using (reciprocal_sqrt_eq_rpow _ (hA.eigenvalues_pos i).le).symm
  have hBhalf : cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) B =
      cfc (fun x : ℝ => 1 / Real.sqrt x) B := by
    apply cfc_congr
    intro x hx
    rw [hB.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    simpa only [neg_div] using (reciprocal_sqrt_eq_rpow _ (hB.eigenvalues_pos i).le).symm
  have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      t ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt t := by
    simpa only [neg_div] using (reciprocal_sqrt_eq_rpow t ht.le).symm
  refine ⟨hi.congr_fun (fun t ht => by simpa only [hpoint t ht]) measurableSet_Ioi, ?_⟩
  rw [hAhalf, hBhalf] at he
  have hcoef : Real.sin (Real.pi * (1 / 2 : ℝ)) / Real.pi = Real.pi⁻¹ := by
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring, Real.sin_pi_div_two,
      one_div]
  rw [hcoef] at he
  rw [← he]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simpa only [hpoint t ht])

/-- Actual support-aware entropy loss controls inverse-square-root intertwining
in L2 under a common positive supported-carrier spectral floor. -/
theorem entropy_defect_inverse_sqrt_stability
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ)
    (m : ℝ) (hm : 0 < m) :
    let M := supported_relative_modular_model Φ ρ σ support
    m • 1 ≤ M.data.A → m • 1 ≤ M.data.B →
    let d := cfc (fun x : ℝ => 1 / Real.sqrt x) M.data.A *ᵥ M.data.ξ -
      M.data.V *ᵥ (cfc (fun x : ℝ => 1 / Real.sqrt x) M.data.B *ᵥ M.data.η)
    Real.sqrt (star d ⬝ᵥ d).re ≤ 4 / (Real.pi * Real.sqrt m) *
      (finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) ^ (1 / 4 : ℝ) := by
  classical
  let M := supported_relative_modular_model Φ ρ σ support
  change m • 1 ≤ M.data.A → m • 1 ≤ M.data.B → _
  intro hfloorA hfloorB
  let w : ℝ → EuclideanSpace ℂ (M.data.J × M.data.I) := fun t => WithLp.toLp 2
    ((M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
      M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η))
  let d := cfc (fun x : ℝ => 1 / Real.sqrt x) M.data.A *ᵥ M.data.ξ -
    M.data.V *ᵥ (cfc (fun x : ℝ => 1 / Real.sqrt x) M.data.B *ᵥ M.data.η)
  have hnξ : ‖(WithLp.toLp 2 M.data.ξ : EuclideanSpace ℂ (M.data.J × M.data.I))‖ = 1 := by
    have h := M.normξ
    rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 M.data.ξ)] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 M.data.ξ : EuclideanSpace ℂ (M.data.J × M.data.I))]
  have hnη : ‖(WithLp.toLp 2 M.data.η : EuclideanSpace ℂ (M.data.L × M.data.K))‖ = 1 := by
    have h := M.normη
    rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 M.data.η)] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 M.data.η : EuclideanSpace ℂ (M.data.L × M.data.K))]
  have hwbound (t : ℝ) (ht : 0 < t) : ‖w t‖ ≤ 2 / m := by
    have ha := l2_resolvent_bound M.data.A M.hA m hm hfloorA M.data.ξ t ht
    have hb := l2_resolvent_bound M.data.B M.hB m hm hfloorB M.data.η t ht
    rw [hnξ] at ha
    rw [hnη] at hb
    have hc := l2_contraction M.data.V M.hVnorm ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η)
    change ‖(WithLp.toLp 2 ((M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ) :
      EuclideanSpace ℂ (M.data.J × M.data.I)) -
      WithLp.toLp 2 (M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η))‖ ≤ _
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ 1 / m + 1 / m := add_le_add ha (hc.trans hb)
      _ = 2 / m := by ring
  obtain ⟨hE, hbudget⟩ :=
    EntropyDefectResolventIntegralBudget.entropy_defect_resolvent_integral_budget Φ ρ σ support
  have hE' : IntegrableOn (fun t : ℝ => t * ‖w t‖^2) (Ioi 0) := by
    simpa only [w, l2_norm_sq] using hE
  have hbudget' : (∫ t in Ioi (0 : ℝ), t * ‖w t‖^2) ≤
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
    simpa only [w, l2_norm_sq] using hbudget
  obtain ⟨hi, he⟩ := l2_inverse_sqrt_integral
    M.data.A M.data.B M.hA M.hB M.data.V M.data.ξ M.data.η
  have hfinal := euclidean_inverse_sqrt_bound_from_budget w (WithLp.toLp 2 d) m _ hm
    hi hE' hbudget' hwbound he.symm
  have hnorm : Real.sqrt (star d ⬝ᵥ d).re =
      ‖(WithLp.toLp 2 d : EuclideanSpace ℂ (M.data.J × M.data.I))‖ := by
    rw [← l2_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  change Real.sqrt (star d ⬝ᵥ d).re ≤ _
  rw [hnorm]
  exact hfinal

#print axioms entropy_defect_inverse_sqrt_stability

end D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
