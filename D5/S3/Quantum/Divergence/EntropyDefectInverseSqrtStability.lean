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

/-! Supported inverse-square-root stability in the Euclidean L2 carrier. -/

noncomputable section
universe u v
open Matrix Set MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI

namespace D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability

private def inverseHalfKernel (lambda t : Real) : Real :=
  t ^ (-1 / 2 : Real) / (lambda + t)

/-- The missing explicit normalization of Mathlib's positive-half-power integral. -/
private theorem half_power_normalizer :
    (integral (volume.restrict (Ioi (0 : Real)))
      (fun t => Real.rpowIntegrand₀₁ (1 / 2) t 1)) = Real.pi := by
  have hp : (1 / 2 : Real) ∈ Ioo 0 1 := by norm_num
  have hpoint (s : Real) (hs : 0 < s) :
      ((2 : Real) * s ^ ((2 : Real) - 1)) •
          Real.rpowIntegrand₀₁ (1 / 2) (s ^ (2 : Real)) 1 =
        2 * (1 + s ^ (2 : Nat))⁻¹ := by
    rw [Real.rpowIntegrand₀₁_eq_pow_div hp
      (Real.rpow_nonneg hs.le _) zero_le_one]
    have hpower : (s ^ (2 : Real)) ^ ((1 / 2 : Real) - 1) = s⁻¹ := by
      rw [← Real.rpow_mul hs.le]
      norm_num [Real.rpow_neg_one]
    rw [hpower]
    simp only [show (2 : Real) - 1 = 1 by norm_num,
      Real.rpow_one, Real.rpow_two, smul_eq_mul, mul_one]
    have hden : 1 + s ^ (2 : Nat) ≠ 0 := ne_of_gt (by positivity)
    have hden' : s ^ (2 : Nat) + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hs.ne', hden, hden']
    <;> ring
  calc
    (∫ t in Ioi (0 : Real), Real.rpowIntegrand₀₁ (1 / 2) t 1) =
        ∫ s in Ioi (0 : Real),
          ((2 : Real) * s ^ ((2 : Real) - 1)) •
            Real.rpowIntegrand₀₁ (1 / 2) (s ^ (2 : Real)) 1 :=
      (integral_comp_rpow_Ioi_of_pos
        (g := fun t => Real.rpowIntegrand₀₁ (1 / 2) t 1)
        (p := (2 : Real)) (by norm_num)).symm
    _ = ∫ s in Ioi (0 : Real), 2 * (1 + s ^ (2 : Nat))⁻¹ :=
      setIntegral_congr_fun measurableSet_Ioi (fun s hs => hpoint s hs)
    _ = Real.pi := by
      rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
      simp only [Real.arctan_zero, sub_zero]
      ring

/-- A genuine negative-half-power formula, obtained by dividing the positive
half-power formula by the positive spectral value. -/
private theorem scalar_inverse_sqrt_integral (lambda : Real) (hlambda : 0 < lambda) :
    IntegrableOn (inverseHalfKernel lambda) (Ioi (0 : Real)) ∧
      (∫ t in Ioi (0 : Real), inverseHalfKernel lambda t) =
        Real.pi / Real.sqrt lambda := by
  have hp : (1 / 2 : Real) ∈ Ioo 0 1 := by norm_num
  have hkernel : EqOn
      (fun t => lambda⁻¹ * Real.rpowIntegrand₀₁ (1 / 2) t lambda)
      (inverseHalfKernel lambda) (Ioi (0 : Real)) := by
    intro t ht
    dsimp only
    rw [Real.rpowIntegrand₀₁_eq_pow_div hp ht.le hlambda.le]
    dsimp only [inverseHalfKernel]
    have hexp : (1 / 2 : Real) - 1 = -1 / 2 := by norm_num
    rw [hexp]
    have hden : t + lambda ≠ 0 := ne_of_gt (add_pos ht hlambda)
    have hden' : lambda + t ≠ 0 := ne_of_gt (add_pos hlambda ht)
    field_simp [hlambda.ne', hden, hden']
    <;> ring
  have hraw : IntegrableOn (fun t : ℝ => Real.rpowIntegrand₀₁ (1 / 2) t lambda) (Ioi 0) :=
    Real.integrableOn_rpowIntegrand₀₁_Ioi hp hlambda.le
  have hint : IntegrableOn (inverseHalfKernel lambda) (Ioi (0 : Real)) :=
    IntegrableOn.congr_fun (hraw.const_mul lambda⁻¹) hkernel measurableSet_Ioi
  refine ⟨hint, ?_⟩
  calc
    (∫ t in Ioi (0 : Real), inverseHalfKernel lambda t) =
        ∫ t in Ioi (0 : Real),
          lambda⁻¹ * Real.rpowIntegrand₀₁ (1 / 2) t lambda :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => (hkernel ht).symm)
    _ = lambda⁻¹ * (lambda ^ (1 / 2 : Real) * Real.pi) := by
      rw [integral_const_mul,
        Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp hlambda.le,
        half_power_normalizer]
    _ = Real.pi * lambda ^ (-1 / 2 : Real) := by
      have hexp : (-1 / 2 : Real) = (1 / 2 : Real) - 1 := by norm_num
      rw [hexp, Real.rpow_sub_one hlambda.ne']
      ring
    _ = Real.pi / Real.sqrt lambda := by
      rw [show (-1 / 2 : Real) = -(1 / 2 : Real) by norm_num,
        Real.rpow_neg hlambda.le, ← Real.sqrt_eq_rpow]
      simp only [div_eq_mul_inv]

/-- Finite spectral sums commute with the negative-half-power integral.
This elementary Bochner lemma works for any complete real normed space. -/
private theorem finite_inverse_sqrt_integral
    {i : Type*} [Fintype i]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (lambda : i → Real) (hlambda : ∀ j, 0 < lambda j) (c : i → E) :
    IntegrableOn (fun t : Real => ∑ j, inverseHalfKernel (lambda j) t • c j)
        (Ioi (0 : Real)) ∧
      Real.pi⁻¹ • (∫ t in Ioi (0 : Real),
        ∑ j, inverseHalfKernel (lambda j) t • c j) =
        ∑ j, (1 / Real.sqrt (lambda j)) • c j := by
  classical
  have hi (j : i) : IntegrableOn
      (fun t : Real => inverseHalfKernel (lambda j) t • c j) (Ioi (0 : Real)) :=
    (scalar_inverse_sqrt_integral (lambda j) (hlambda j)).1.smul_const (c j)
  refine ⟨integrable_finsetSum Finset.univ (fun j _ => hi j), ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ => hi j), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_smul_const,
    (scalar_inverse_sqrt_integral (lambda j) (hlambda j)).2, smul_smul]
  congr 1
  field_simp [Real.pi_ne_zero]

private theorem cfc_vector_expansion_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian)
    (f : Real → Real) (a : n → Complex) :
    cfc f A *ᵥ a = ∑ j, f (hA.eigenvalues j) •
      (fun i => hA.eigenvectorUnitary i j * (hA.eigenvectorUnitaryᴴ *ᵥ a) j) := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul]
  simpa only [mul_assoc] using ResolventFunctionalRigidity.cfc_vector_expansion A hA f a i

/-- The positive-definite matrix-vector inverse-square-root formula on the
full positive axis. No L2/sup-norm identification is used in this statement. -/
private theorem matrix_inverse_sqrt_integral {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.PosDef) (a : n → Complex) :
    IntegrableOn (fun t : Real => t ^ (-1 / 2 : Real) •
      ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a)) (Ioi (0 : Real)) ∧
      Real.pi⁻¹ • (∫ t in Ioi (0 : Real), t ^ (-1 / 2 : Real) •
        ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a)) =
        cfc (fun x : Real => 1 / Real.sqrt x) A *ᵥ a := by
  classical
  let c : n → (n → Complex) := fun j i =>
    hA.1.eigenvectorUnitary i j * (hA.1.eigenvectorUnitaryᴴ *ᵥ a) j
  have hpoint (t : Real) (ht : 0 < t) :
      t ^ (-1 / 2 : Real) • ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a) =
        ∑ j, inverseHalfKernel (hA.1.eigenvalues j) t • c j := by
    rw [← ResolventFunctionalRigidity.cfc_shift_inverse A hA.posSemidef t ht,
      cfc_vector_expansion_sum A hA.1 (fun x : Real => (x + t)⁻¹) a,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    simp only [inverseHalfKernel, div_eq_mul_inv, c]
  obtain ⟨hi, hv⟩ := finite_inverse_sqrt_integral
    hA.1.eigenvalues hA.eigenvalues_pos c
  have hi' : IntegrableOn (fun t : Real => t ^ (-1 / 2 : Real) •
      ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a)) (Ioi (0 : Real)) :=
    hi.congr_fun (fun t ht => (hpoint t ht).symm) measurableSet_Ioi
  refine ⟨hi', ?_⟩
  calc
    Real.pi⁻¹ • (∫ t in Ioi (0 : Real), t ^ (-1 / 2 : Real) •
        ((A + t • (1 : Matrix n n Complex))⁻¹ *ᵥ a)) =
        Real.pi⁻¹ • (∫ t in Ioi (0 : Real),
          ∑ j, inverseHalfKernel (hA.1.eigenvalues j) t • c j) := by
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpoint t ht)
    _ = ∑ j, (1 / Real.sqrt (hA.1.eigenvalues j)) • c j := hv
    _ = cfc (fun x : Real => 1 / Real.sqrt x) A *ᵥ a :=
      (cfc_vector_expansion_sum A hA.1 (fun x : Real => 1 / Real.sqrt x) a).symm

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


private theorem l2_norm_sq {n : Type*} [Fintype n] (x : n → ℂ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 = (star x ⬝ᵥ x).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, RCLike.re_to_complex]

private theorem l2_contraction {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
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

private theorem l2_resolvent_bound {n : Type*} [Fintype n] [DecidableEq n]
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
  classical
  let T : (n → ℂ) ≃L[ℝ] EuclideanSpace ℂ n :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : n => ℂ)).symm
  let L : (k → ℂ) →L[ℝ] (n → ℂ) :=
    (V.mulVecLin.restrictScalars ℝ).toContinuousLinearMap
  let f : ℝ → (n → ℂ) := fun t => t ^ (-1 / 2 : ℝ) • ((A + t • 1)⁻¹ *ᵥ ξ)
  let g : ℝ → (k → ℂ) := fun t => t ^ (-1 / 2 : ℝ) • ((B + t • 1)⁻¹ *ᵥ η)
  obtain ⟨hf, hfval⟩ := matrix_inverse_sqrt_integral A hA ξ
  obtain ⟨hg, hgval⟩ := matrix_inverse_sqrt_integral B hB η
  have hdiff : IntegrableOn (fun t => f t - L (g t)) (Ioi (0 : ℝ)) :=
    hf.sub (L.integrable_comp hg)
  have hpoint (t : ℝ) (ht : 0 < t) :
      T (f t - L (g t)) = (1 / Real.sqrt t) • (WithLp.toLp 2
        ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η)) : EuclideanSpace ℂ n) := by
    rw [map_sub, map_smul, map_smul]
    change t ^ (-1 / 2 : ℝ) • T ((A + t • 1)⁻¹ *ᵥ ξ) -
      T (t ^ (-1 / 2 : ℝ) • L ((B + t • 1)⁻¹ *ᵥ η)) = _
    rw [map_smul, ← smul_sub, reciprocal_sqrt_eq_rpow t ht.le]
    rfl
  have hi : IntegrableOn (fun t : ℝ => (1 / Real.sqrt t) • (WithLp.toLp 2
      ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η)) : EuclideanSpace ℂ n)) (Ioi 0) :=
    IntegrableOn.congr_fun (T.toContinuousLinearMap.integrable_comp hdiff)
      (fun t ht => hpoint t ht) measurableSet_Ioi
  refine ⟨hi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpoint t ht),
    T.integral_comp_comm, ← T.map_smul, integral_sub hf (L.integrable_comp hg),
    L.integral_comp_comm hg, smul_sub, ← L.map_smul, hfval, hgval]
  rfl

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
