/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent Weyl commutants and square-summable squeezed Fock vectors. -/

import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
import D5.S3.Quantum.Analysis.NullConeGravity.CCRSqueezeInfinite
import D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
import D5.S3.Quantum.Algebra.StateApproximation.IrreducibleBoundedLift
import OmegaMath.Analysis.ConjugateDifferentiable
import OmegaMath.OperatorAlgebra.UnitaryIntertwining
import OmegaMath.Analysis.PlanarGaussian
import OmegaMath.Analysis.HilbertBasisFiniteModes
import OmegaMath.Analysis.SquareSummableProjection
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

/-! Scalar commutants of bosonic Weyl displacements and Gaussian occupation tests. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Complex MeasureTheory ContinuousLinearMap
open Omega.PlanarGaussian Omega.HilbertBasisFiniteModes
open Omega.SquareSummableProjection Omega.UnitaryIntertwining
open D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
open scoped ComplexOrder ComplexConjugate InnerProductSpace Topology BigOperators
open D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
open D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
open D5.S3.Quantum.Analysis.NullConeGravity.CCRSqueezeInfinite

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRFockFactorDisjointness

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "Fock" => BosonFock I

/-- The Weyl displacement as a bounded complex-linear endomorphism. -/
def weylMap (b : HilbertBasis I ℂ H) (z : H) : Fock →L[ℂ] Fock :=
  (fockWeyl b z).toLinearIsometry.toContinuousLinearMap

/-- Pairing with a coherent vector is entire along every affine complex line. -/
private theorem exponential_pairing_analytic (b : HilbertBasis I ℂ H) (v : BosonFock I)
    (x y : H) : AnalyticOnNhd ℂ (fun c : ℂ => ⟪v, fockExponential b (x + c • y)⟫_ℂ) univ := by
  classical
  apply (Complex.analyticOnNhd_iff_differentiableOn isOpen_univ).2
  apply Differentiable.differentiableOn
  intro z
  let R := ‖z‖ + 1
  let B := ‖x‖ + R * ‖y‖
  let C := Real.exp (B ^ 2 / 2)
  have hC : 0 < C := Real.exp_pos _
  let vFin (s : Finset (Occupation I)) : BosonFock I := ∑ α ∈ s, lp.single 2 α (v α)
  let f (s : Finset (Occupation I)) (c : ℂ) := ⟪vFin s, fockExponential b (x + c • y)⟫_ℂ
  have hf (s : Finset (Occupation I)) : Differentiable ℂ (f s) := by
    simp only [f, vFin, sum_inner, lp.inner_single_left, fockExponential_apply, RCLike.inner_apply]
    refine Differentiable.fun_sum fun α _ => Differentiable.mul ?_ (differentiable_const _)
    refine Differentiable.fun_finsetProd fun i _ => ?_
    have he (c : ℂ) : b.repr (x + c • y) i = b.repr x i + c * b.repr y i := by
      rw [map_add, map_smul]
      rfl
    simp_rw [he]
    fun_prop
  have hv : Tendsto vFin atTop (𝓝 v) := lp.hasSum_single ENNReal.ofNat_ne_top v
  have hU : TendstoUniformlyOn f (fun c => ⟪v, fockExponential b (x + c • y)⟫_ℂ)
      atTop (Metric.ball 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hv (ε / C) (div_pos hε hC)] with s hs c hc
    have hc' : ‖c‖ ≤ R := (mem_ball_zero_iff.mp hc).le
    have hB : ‖x + c • y‖ ≤ B := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      exact add_le_add_right (mul_le_mul_of_nonneg_right hc' (norm_nonneg y)) _
    have hnorm : ‖fockExponential b (x + c • y)‖ ≤ C := by
      have hsq : ‖fockExponential b (x + c • y)‖ ^ 2 ≤ C ^ 2 := by
        rw [fockExponential_norm_sq, show C ^ 2 = Real.exp (B ^ 2) by
          simp only [C, pow_two, ← Real.exp_add]
          congr 1
          ring]
        exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (norm_nonneg _) hB 2)
      nlinarith [norm_nonneg (fockExponential b (x + c • y))]
    change dist ⟪v, fockExponential b (x + c • y)⟫_ℂ
      ⟪vFin s, fockExponential b (x + c • y)⟫_ℂ < ε
    rw [dist_eq_norm, ← inner_sub_left]
    refine (norm_inner_le_norm _ _).trans_lt ?_
    calc
      ‖v - vFin s‖ * ‖fockExponential b (x + c • y)‖ ≤ ‖v - vFin s‖ * C :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ < ε := (lt_div_iff₀ hC).mp (by rwa [dist_eq_norm, norm_sub_rev] at hs)
  refine (hU.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun s => (hf s).differentiableOn) Metric.isOpen_ball).differentiableAt ?_
  exact Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by dsimp [R]; linarith))

private theorem coherent_commuting_kernel (b : HilbertBasis I ℂ H) (T : Fock →L[ℂ] Fock)
    (hcomm : ∀ z x, T (fockWeyl b z x) = fockWeyl b z (T x)) (v z : H) :
    ⟪fockExponential b v, T (fockExponential b z)⟫_ℂ =
      Complex.exp ⟪v, z⟫_ℂ * ⟪fockExponential b (v - z), T (fockVacuum I)⟫_ℂ := by
  let a := Complex.exp (-(‖z‖ : ℂ) ^ 2 / 2)
  have h := hcomm z (fockVacuum I)
  rw [← fockExponential_zero b, fockWeyl_exponential, inner_zero_right, sub_zero,
    add_zero, map_smul, fockExponential_zero] at h
  have hh := congrArg (fun x : Fock => ⟪fockExponential b v, x⟫_ℂ) h
  change ⟪fockExponential b v, a • T (fockExponential b z)⟫_ℂ =
    ⟪fockExponential b v, fockWeyl b z (T (fockVacuum I))⟫_ℂ at hh
  have hflip := (fockWeyl b z).symm.inner_map_eq_flip (fockExponential b v) (T (fockVacuum I))
  rw [LinearIsometryEquiv.symm_symm] at hflip
  rw [← hflip, fockWeyl_symm, fockWeyl_exponential, inner_smul_right,
    inner_smul_left, ← Complex.exp_conj, norm_neg, inner_neg_left, neg_add_eq_sub] at hh
  rw [show conj (-(‖z‖ : ℂ) ^ 2 / 2 - -⟪z, v⟫_ℂ) =
      -(‖z‖ : ℂ) ^ 2 / 2 + ⟪v, z⟫_ℂ by
    rw [sub_neg_eq_add, map_add, inner_conj_symm]
    congr 1
    have htwo : conj (2 : ℂ) = 2 := by exact map_ofNat (starRingEnd ℂ) 2
    rw [map_div₀, map_neg, map_pow, Complex.conj_ofReal, htwo]] at hh
  rw [Complex.exp_add, mul_assoc] at hh
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hh

/-- The Weyl displacements have scalar commutant for every Hilbert basis. -/
theorem fockWeyl_commutant_scalar (b : HilbertBasis I ℂ H) (T : Fock →L[ℂ] Fock)
    (hcomm : ∀ z x, T (fockWeyl b z x) = fockWeyl b z (T x)) :
    ∃ c : ℂ, T = c • (1 : Fock →L[ℂ] Fock) := by
  let vac := fockVacuum I
  let c := ⟪vac, T vac⟫_ℂ
  have hp (v : H) : ⟪fockExponential b v, T vac⟫_ℂ = c := by
    let f (z : ℂ) := ⟪vac, T (fockExponential b (z • (-v)))⟫_ℂ
    have hf (z : ℂ) : f z = ⟪fockExponential b (z • v), T vac⟫_ℂ := by
      have h := coherent_commuting_kernel b T hcomm 0 (z • (-v))
      simpa only [f, vac, fockExponential_zero, inner_zero_left, Complex.exp_zero, one_mul,
        zero_sub, smul_neg, neg_neg] using h
    have hd (w : Fock) (u : H) : Differentiable ℂ (fun z : ℂ =>
        ⟪w, fockExponential b (z • u)⟫_ℂ) := by
      intro z
      simpa only [zero_add] using
        ((exponential_pairing_analytic b w 0 u) z (Set.mem_univ _)).differentiableAt
    have hfd : Differentiable ℂ f := by
      have he : f = (fun z : ℂ => ⟪T.adjoint vac, fockExponential b (z • (-v))⟫_ℂ) := by
        funext z
        exact (ContinuousLinearMap.adjoint_inner_left T _ _).symm
      rw [he]
      exact hd _ _
    have hconj : Differentiable ℂ (fun z => conj (f z)) := by
      simpa only [hf, inner_conj_symm] using hd (T vac) v
    simpa only [hf, one_smul, zero_smul, fockExponential_zero, c, vac] using
      Omega.constant_of_differentiable_conj hfd hconj 1 0
  have hv : T vac = c • vac := by
    have h : (innerSL ℂ (T vac) : Fock →L[ℂ] ℂ) = innerSL ℂ (c • vac) := by
      apply ContinuousLinearMap.ext_on (fockExponential_dense_span b)
      rintro _ ⟨v, rfl⟩
      have hh : ⟪fockExponential b v, T vac⟫_ℂ =
          ⟪fockExponential b v, c • vac⟫_ℂ := by
        rw [hp, inner_smul_right, show vac = fockVacuum I from rfl, ← fockExponential_zero b,
          fockExponential_inner, inner_zero_right,
          Complex.exp_zero, mul_one]
      exact (inner_conj_symm _ _).symm.trans ((congrArg conj hh).trans (inner_conj_symm _ _))
    have hzero : ⟪T vac - c • vac, T vac - c • vac⟫_ℂ = 0 := by
      rw [inner_sub_left, sub_eq_zero]
      exact DFunLike.congr_fun h _
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  refine ⟨c, ContinuousLinearMap.ext_on (fockExponential_dense_span b) ?_⟩
  rintro _ ⟨w, rfl⟩
  have h := hcomm w vac
  have hd : fockWeyl b w vac =
      Complex.exp (-(‖w‖ : ℂ) ^ 2 / 2) • fockExponential b w := by
    simp [vac, ← fockExponential_zero b, fockWeyl_exponential]
  rw [hv, map_smul, hd, map_smul] at h
  let a := Complex.exp (-(‖w‖ : ℂ) ^ 2 / 2)
  have hh : a • T (fockExponential b w) = a • (c • fockExponential b w) := by
    change a • T (fockExponential b w) = c • (a • fockExponential b w) at h
    simpa only [smul_smul, mul_comm c a] using h
  have hcancel := congrArg (fun v : Fock => a⁻¹ • v) hh
  have ha : a ≠ 0 := Complex.exp_ne_zero _
  simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, one_smul,
    smul_apply, one_apply_eq_self] using hcancel

/-- The characteristic function supplied by the infinite squeeze construction. -/
def squeezedChar (b : HilbertBasis I ℂ H) (r : I → ℝ) (z : H) : ℂ :=
  Complex.exp (-(((∑' i : I, (Real.exp (2 * r i) * (b.repr z i).re ^ 2 +
    Real.exp (-2 * r i) * (b.repr z i).im ^ 2)) : ℝ) : ℂ) / 2)

theorem squeezedChar_infiniteSqueeze
    (b : HilbertBasis I ℂ H) (r : I → ℝ)
    (hr : Summable (fun i => (r i) ^ 2)) (z : H) :
    ⟪infiniteSqueeze r hr, fockWeyl b z (infiniteSqueeze r hr)⟫_ℂ =
      squeezedChar b r z := by
  simpa [squeezedChar] using infiniteSqueeze_weyl_inner b r hr z

theorem squeezed_in_fock_folium_of_summable_sq
    (b : HilbertBasis I ℂ H) (r : I → ℝ)
    (hr : Summable (fun i => (r i) ^ 2)) :
    ∃ ψ : Fock, ‖ψ‖ = 1 ∧ ∀ z : H,
      ⟪ψ, fockWeyl b z ψ⟫_ℂ = squeezedChar b r z := by
  refine ⟨infiniteSqueeze r hr, infiniteSqueeze_norm r hr, ?_⟩
  exact squeezedChar_infiniteSqueeze b r hr


/-- Every bounded map commutes with the commutant of the Fock Weyl displacements. -/
theorem fockWeyl_bicommutant_top (b : HilbertBasis I ℂ H) :
    Set.centralizer (Set.centralizer (Set.range (weylMap b))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro S
  apply Set.mem_centralizer_iff.mpr
  intro T hT
  obtain ⟨a, rfl⟩ := fockWeyl_commutant_scalar b T (fun z x => by
    have h := Set.mem_centralizer_iff.mp hT (weylMap b z) ⟨z, rfl⟩
    exact (DFunLike.congr_fun h x).symm)
  simp only [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- The center of the Fock Weyl bicommutant consists of scalars. -/
theorem fockWeyl_isFactor (b : HilbertBasis I ℂ H) :
    Set.centralizer (Set.centralizer (Set.centralizer (Set.range (weylMap b)))) =
      Set.range (fun c : ℂ => c • (1 : Fock →L[ℂ] Fock)) := by
  have hb := fockWeyl_bicommutant_top b
  rw [hb]
  ext T
  constructor
  · intro h
    obtain ⟨a, ha⟩ := fockWeyl_commutant_scalar b T (fun z x =>
      (DFunLike.congr_fun (Set.mem_centralizer_iff.mp h (weylMap b z) (Set.mem_univ _)) x).symm)
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact Set.mem_centralizer_iff.mpr (fun S _ => by
      simp only [smul_mul_assoc, one_mul, mul_smul_comm, mul_one])

section Gaussian

private def squeezedWeights (r : ℝ) : ℝ × ℝ :=
  ((1 + Real.exp (2 * r)) / 2, (1 + Real.exp (-2 * r)) / 2)

/-- Exact Lebesgue Gaussian average of the anisotropic characteristic function. -/
theorem squeezedChar_gaussian_avg (b : HilbertBasis I ℂ H) (r : I → ℝ) (F : Finset I) :
    (Real.pi : ℂ)⁻¹ ^ F.card *
        (∫ z : F → ℂ, (weight z : ℂ) * squeezedChar b r (modeEmbed b F z)) =
      ∏ i : F, ((Real.cosh (r i))⁻¹ : ℝ) := by
  classical
  have hterm (z : F → ℂ) :
      (∑' i, (Real.exp (2 * r i) * (b.repr (modeEmbed b F z) i).re ^ 2 +
        Real.exp (-2 * r i) * (b.repr (modeEmbed b F z) i).im ^ 2)) =
      ∑ i : F, (Real.exp (2 * r i) * (z i).re ^ 2 + Real.exp (-2 * r i) * (z i).im ^ 2) := by
    rw [tsum_eq_sum (s := F)]
    · rw [← Finset.sum_attach F]
      apply Finset.sum_congr rfl
      intro i _
      simp only [repr_modeEmbed, i.property, dite_true]
    · intro i hi
      simp [repr_modeEmbed, hi]
  have he (z : F → ℂ) : (weight z : ℂ) * squeezedChar b r (modeEmbed b F z) =
      ∏ i : F, planarGaussian (squeezedWeights (r i)).1 (squeezedWeights (r i)).2 0 0 (z i) := by
    rw [squeezedChar, hterm, weight, Complex.ofReal_exp, ← Complex.exp_add]
    simp only [planarGaussian, realGaussian, zero_mul, add_zero, ← Complex.exp_add,
      ← Complex.exp_sum, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_sum]
    congr 1
    simp only [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [squeezedWeights, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod, ← Fintype.card_coe F, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_planarGaussian (by unfold squeezedWeights; positivity)
    (by unfold squeezedWeights; positivity)]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, add_zero, Complex.exp_zero, mul_one]
  have hprod (x : ℝ) : (squeezedWeights x).1 * (squeezedWeights x).2 = Real.cosh x ^ 2 := by
    simp only [squeezedWeights, Real.cosh_eq, show 2 * x = x + x by ring,
      show -2 * x = -x + -x by ring, Real.exp_add]
    have h : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hsq := congrArg (fun a : ℝ => a ^ 2) h
    simp only [mul_pow, one_pow] at hsq
    nlinarith [h, hsq]
  have hval : Real.sqrt (Real.pi / (squeezedWeights (r i)).1) *
      Real.sqrt (Real.pi / (squeezedWeights (r i)).2) = Real.pi / Real.cosh (r i) := by
    rw [← Real.sqrt_mul (by unfold squeezedWeights; positivity), div_mul_div_comm,
      hprod, ← pow_two Real.pi, ← div_pow, Real.sqrt_sq (by positivity)]
  rw [hval, Complex.ofReal_div, Complex.ofReal_inv]
  field_simp [Real.pi_ne_zero, (Real.cosh_pos _).ne']


/-- Orthogonal projection onto occupations with no particles in the specified modes. -/
def vacuumProj (F : Finset I) : Fock →L[ℂ] Fock :=
  cut (fun α : Occupation I => Disjoint α.support F)

private theorem vacuumProj_apply (F : Finset I) (ψ : Fock) (α : Occupation I) :
    vacuumProj F ψ α =
      @ite ℂ (Disjoint α.support F) (Classical.propDecidable _) (ψ α) 0 :=
  cut_apply _ _ _

private theorem vacuumProj_coherent (b : HilbertBasis I ℂ H) (F : Finset I) (w : H) :
    vacuumProj F (fockExponential b w) =
      fockExponential b (w - modeEmbed b F (fun i => b.repr w i)) := by
  classical
  apply lp.ext
  funext α
  simp only [vacuumProj_apply, fockExponential_apply]
  have hz (i : I) :
      b.repr (w - modeEmbed b F (fun i => b.repr w i)) i =
        if i ∈ F then 0 else b.repr w i := by
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_modeEmbed]
    split_ifs <;> simp
  simp_rw [hz]
  split_ifs with hd
  · exact Finset.prod_congr rfl fun i hi => by
      rw [ite_eq_right (Finset.disjoint_left.mp hd hi)]
  · obtain ⟨i, hi, hF⟩ := Finset.not_disjoint_iff.mp hd
    exact (Finset.prod_eq_zero hi (by rw [ite_eq_left hF,
      zero_pow (Finsupp.mem_support_iff.mp hi), zero_div])).symm

private theorem continuous_orbit (b : HilbertBasis I ℂ H) (F : Finset I) (ψ : Fock) :
    Continuous (fun z : F → ℂ => fockWeyl b (modeEmbed b F z) ψ) :=
  (fockWeyl_strongContinuous b ψ).comp (by unfold modeEmbed; fun_prop)

private theorem weyl_average_integrable (b : HilbertBasis I ℂ H) (F : Finset I) (ψ : Fock) :
    Integrable (fun z : F → ℂ => (weight z : ℂ) • fockWeyl b (modeEmbed b F z) ψ) :=
  weighted_integrable _ (continuous_orbit b F) ψ

private def weylAverage (b : HilbertBasis I ℂ H) (F : Finset I) : Fock →L[ℂ] Fock :=
  weightedAverage _ (continuous_orbit b F) ((Real.pi : ℂ)⁻¹ ^ F.card)

private theorem coherent_avg (b : HilbertBasis I ℂ H) (F : Finset I) (v w : H) :
    ⟪fockExponential b v, weylAverage b F (fockExponential b w)⟫_ℂ =
      ⟪fockExponential b v, vacuumProj F (fockExponential b w)⟫_ℂ := by
  classical
  let u (i : F) := conj (b.repr v i) - b.repr w i
  let t (i : F) := Complex.I * (conj (b.repr v i) + b.repr w i)
  change ⟪fockExponential b v, ((Real.pi : ℂ)⁻¹ ^ F.card) • ∫ z : F → ℂ,
    (weight z : ℂ) • fockWeyl b (modeEmbed b F z) (fockExponential b w)⟫_ℂ = _
  rw [inner_smul_right]
  have hi := (innerSL ℂ (fockExponential b v)).integral_comp_comm
    (weyl_average_integrable b F (fockExponential b w))
  change (∫ z : F → ℂ, ⟪fockExponential b v, (weight z : ℂ) •
    fockWeyl b (modeEmbed b F z) (fockExponential b w)⟫_ℂ) =
    ⟪fockExponential b v, ∫ z : F → ℂ, (weight z : ℂ) •
      fockWeyl b (modeEmbed b F z) (fockExponential b w)⟫_ℂ at hi
  rw [← hi]
  have he (z : F → ℂ) :
      ⟪fockExponential b v, (weight z : ℂ) •
          fockWeyl b (modeEmbed b F z) (fockExponential b w)⟫_ℂ =
        Complex.exp ⟪v, w⟫_ℂ * ∏ i, planarGaussian 1 1 (u i) (t i) (z i) := by
    rw [inner_smul_right, fockWeyl_exponential, inner_smul_right, fockExponential_inner,
      inner_add_right, ← Complex.ofReal_pow, modeEmbed_norm_sq, weight, Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    have hconj : ⟪modeEmbed b F z, w⟫_ℂ = ∑ i, conj (z i) * b.repr w i := by
      rw [← inner_conj_symm, inner_modeEmbed, map_sum]
      simp only [map_mul, starRingEnd_self_apply, mul_comm]
    rw [inner_modeEmbed, hconj]
    simp only [planarGaussian, realGaussian, ← Complex.exp_add, ← Complex.exp_sum,
      Complex.ofReal_sum, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    congr 1
    have hpoint (i : F) : -(↑‖z i‖ ^ 2 : ℂ) +
        (conj (b.repr v i) * z i - conj (z i) * b.repr w i) =
        -(1 : ℂ) * (z i).re ^ 2 + u i * (z i).re +
          (-(1 : ℂ) * (z i).im ^ 2 + t i * (z i).im) := by
      rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.ofReal_add, Complex.ofReal_mul, u, t]
      have hz := Complex.re_add_im (z i)
      have hc := congrArg (starRingEnd ℂ) hz
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I] at hc
      rw [← hc]
      conv_lhs => arg 2; arg 1; arg 2; rw [← hz]
      ring
    simp only [Complex.ofReal_one]
    rw [Finset.sum_congr rfl (fun i _ => (hpoint i).symm)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]
    ring
  simp_rw [he, integral_const_mul, integral_fintype_prod_volume_eq_prod]
  have hp (i : F) : (∫ z : ℂ, planarGaussian 1 1 (u i) (t i) z) =
      (Real.pi : ℂ) * Complex.exp (-(conj (b.repr v i) * b.repr w i)) := by
    rw [integral_planarGaussian zero_lt_one zero_lt_one, div_one,
      Real.mul_self_sqrt Real.pi_pos.le]
    congr 2
    simp only [Complex.ofReal_one, mul_one, t, u, mul_pow, Complex.I_sq]
    ring
  simp_rw [hp, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    ← Complex.exp_sum]
  have hcancel : ((Real.pi : ℂ)⁻¹) ^ F.card * (Real.pi : ℂ) ^ F.card = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_pow]
  rw [mul_left_comm _ (Complex.exp _), ← mul_assoc ((Real.pi : ℂ)⁻¹ ^ F.card),
    hcancel, one_mul, ← Complex.exp_add,
    vacuumProj_coherent, fockExponential_inner, inner_sub_right, inner_modeEmbed]
  congr 1
  simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The normalized Gaussian Weyl average is the unoccupied-modes projection. -/
theorem fockWeyl_gaussian_avg_eq_vacuumProj (b : HilbertBasis I ℂ H) (F : Finset I) (ψ : Fock) :
    (Real.pi : ℂ)⁻¹ ^ F.card *
        (∫ z : F → ℂ, (weight z : ℂ) * ⟪ψ, fockWeyl b (modeEmbed b F z) ψ⟫_ℂ) =
      (‖vacuumProj F ψ‖ ^ 2 : ℝ) := by
  have he : weylAverage b F = vacuumProj F := by
    apply ContinuousLinearMap.ext_on (fockExponential_dense_span b)
    rintro _ ⟨w, rfl⟩
    let D := weylAverage b F (fockExponential b w) - vacuumProj F (fockExponential b w)
    have hz : innerSL ℂ D = 0 := by
      apply ContinuousLinearMap.ext_on (fockExponential_dense_span b)
      rintro _ ⟨v, rfl⟩
      change ⟪D, fockExponential b v⟫_ℂ = 0
      rw [← inner_conj_symm, show ⟪fockExponential b v, D⟫_ℂ = 0 by
        rw [inner_sub_right, coherent_avg, sub_self], map_zero]
    have hD : D = 0 := inner_self_eq_zero.mp (DFunLike.congr_fun hz D)
    exact sub_eq_zero.mp hD
  have hi := (innerSL ℂ ψ).integral_comp_comm (weyl_average_integrable b F ψ)
  change (∫ z : F → ℂ, ⟪ψ, (weight z : ℂ) • fockWeyl b (modeEmbed b F z) ψ⟫_ℂ) = _ at hi
  simp only [inner_smul_right] at hi
  rw [hi]
  change (Real.pi : ℂ)⁻¹ ^ F.card * ⟪ψ, ∫ z : F → ℂ, (weight z : ℂ) •
    fockWeyl b (modeEmbed b F z) ψ⟫_ℂ = _
  rw [← inner_smul_right]
  change ⟪ψ, weylAverage b F ψ⟫_ℂ = _
  rw [he, vacuumProj, inner_cut]


/-- Countable vector folium on the finitely supported Weyl algebra. -/
def SqueezedInFockFolium (b : HilbertBasis I ℂ H) (r : I → ℝ) : Prop :=
  ∃ ψ : ℕ → Fock, HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ) ∧
    ∀ (F : Finset I) (z : F → ℂ),
      HasSum (fun n => ⟪ψ n, fockWeyl b (modeEmbed b F z) (ψ n)⟫_ℂ)
        (squeezedChar b r (modeEmbed b F z))

private theorem tight_vacuum {ψ : ℕ → Fock} (hψ : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ)) :
    ∃ S : Finset I, ∀ F : Finset I, Disjoint F S →
      1 / 2 ≤ ∑' n, ‖vacuumProj F (ψ n)‖ ^ 2 := by
  classical
  let a (n : ℕ) (α : Occupation I) := ‖ψ n α‖ ^ 2
  let g (F : Finset I) (n : ℕ) (α : Occupation I) := ‖vacuumProj F (ψ n) α‖ ^ 2
  have ha : Summable (Function.uncurry a) := (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨fun n => (lp_sq (ψ n)).1, hψ.summable.congr (fun n => (lp_sq (ψ n)).2.symm)⟩
  have hv : HasSum (Function.uncurry a) (1 : ℝ) := by
    apply ha.hasSum_iff.mpr
    rw [ha.tsum_prod]
    simpa only [Function.uncurry_apply_pair, a, (lp_sq _).2] using hψ.tsum_eq
  obtain ⟨E, hE⟩ := eventually_atTop.mp
    (hv.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)))
  refine ⟨E.biUnion (fun p => p.2.support), fun F hF => ?_⟩
  have hg (p : ℕ × Occupation I) : Function.uncurry (g F) p ≤ Function.uncurry a p := by
    rcases p with ⟨n, α⟩
    dsimp [g, a]
    rw [vacuumProj_apply]
    split_ifs <;> simp
  have hgs : Summable (Function.uncurry (g F)) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hg ha
  have hEq : ∑ p ∈ E, Function.uncurry a p = ∑ p ∈ E, Function.uncurry (g F) p := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hd := hF.symm.mono_left (Finset.subset_biUnion_of_mem (fun p => p.2.support) hp)
    dsimp [Function.uncurry, a, g]
    rw [vacuumProj_apply, ite_eq_left hd]
  have hsum : (∑ p ∈ E, Function.uncurry (g F) p) ≤
      ∑' p, Function.uncurry (g F) p := hgs.sum_le_tsum E (fun _ _ => sq_nonneg _)
  have htotal : (∑' p, Function.uncurry (g F) p) = ∑' n, ‖vacuumProj F (ψ n)‖ ^ 2 := by
    rw [hgs.tsum_prod]
    exact tsum_congr (fun n => (lp_sq (vacuumProj F (ψ n))).2)
  exact (hE E le_rfl).le.trans (hEq.le.trans (hsum.trans_eq htotal))

private theorem average_folium (b : HilbertBasis I ℂ H) {r : I → ℝ} (F : Finset I)
    {ψ : ℕ → Fock} (hn : HasSum (fun n => ‖ψ n‖ ^ 2) (1 : ℝ))
    (hψ : ∀ z : F → ℂ, HasSum (fun n => ⟪ψ n, fockWeyl b (modeEmbed b F z) (ψ n)⟫_ℂ)
        (squeezedChar b r (modeEmbed b F z))) :
    (∑' n, ‖vacuumProj F (ψ n)‖ ^ 2) = ∏ i : F, (Real.cosh (r i))⁻¹ := by
  let f (n : ℕ) (z : F → ℂ) := (weight z : ℂ) * ⟪ψ n, fockWeyl b (modeEmbed b F z) (ψ n)⟫_ℂ
  have hf (n : ℕ) : Integrable (f n) := by
    have hi := (innerSL ℂ (ψ n)).integrable_comp (weyl_average_integrable b F (ψ n))
    simpa only [innerSL_apply_apply, inner_smul_right, f] using hi
  have hb (n : ℕ) (z : F → ℂ) : ‖f n z‖ ≤ weight z * ‖ψ n‖ ^ 2 := by
    dsimp only [f]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ weight z from (Real.exp_pos _).le)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    simpa only [LinearIsometryEquiv.norm_map, pow_two] using
      norm_inner_le_norm (𝕜 := ℂ) (ψ n) (fockWeyl b (modeEmbed b F z) (ψ n))
  have hs : Summable (fun n => ∫ z, ‖f n z‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
      (hn.summable.mul_left (∫ z : F → ℂ, weight z))
    intro n
    rw [← integral_mul_const]
    exact integral_mono (hf n).norm (weight_integrable.mul_const _) (hb n)
  let c : ℂ := (Real.pi : ℂ)⁻¹ ^ F.card
  have he (z : F → ℂ) : (∑' n, f n z) = (weight z : ℂ) * squeezedChar b r (modeEmbed b F z) := by
    simp only [f, tsum_mul_left, (hψ z).tsum_eq]
  have hs' (n : ℕ) : c * (∫ z, f n z) = ((‖vacuumProj F (ψ n)‖ ^ 2 : ℝ) : ℂ) :=
    fockWeyl_gaussian_avg_eq_vacuumProj b F (ψ n)
  have h := congrArg (c * ·) (integral_tsum_of_summable_integral_norm hf hs)
  simp only [← tsum_mul_left, hs', he, c, squeezedChar_gaussian_avg] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_prod, Complex.ofReal_tsum] using h

private theorem single_folium (b : HilbertBasis I ℂ H) (r : I → ℝ) (ψ : Fock)
    (hn : ‖ψ‖ = 1) (hψ : ∀ (F : Finset I) (z : F → ℂ),
      ⟪ψ, fockWeyl b (modeEmbed b F z) ψ⟫_ℂ = squeezedChar b r (modeEmbed b F z)) :
    SqueezedInFockFolium b r := by
  refine ⟨fun n => if n = 0 then ψ else 0, ?_, ?_⟩
  · convert hasSum_ite_eq (0 : ℕ) (1 : ℝ) using 1
    funext n
    by_cases h : n = 0 <;> simp [h, hn]
  · intro F z
    convert hasSum_ite_eq 0 (squeezedChar b r (modeEmbed b F z)) using 1
    funext n
    by_cases h : n = 0 <;> simp [h, hψ F z]

/-- Square-summability is necessary and sufficient for countable normal Fock folium membership. -/
theorem squeezed_in_fock_folium_iff (b : HilbertBasis I ℂ H) (r : I → ℝ) :
    SqueezedInFockFolium b r ↔ Summable (fun i => (r i) ^ 2) := by
  constructor
  · rintro ⟨ψ, hn, hψ⟩
    obtain ⟨S, hS⟩ := tight_vacuum hn
    refine summable_sq_of_prod S (fun F hF => ?_)
    rw [← Finset.prod_attach F]
    rw [Finset.attach_eq_univ, ← average_folium b F hn (hψ F)]
    exact hS F hF
  · intro hr
    obtain ⟨ψ, hψ, hcoeff⟩ := squeezed_in_fock_folium_of_summable_sq b r hr
    exact single_folium b r ψ hψ (fun F z => hcoeff (modeEmbed b F z))

/-- The same sharp criterion in terms of excitability by countable Fock vectors. -/
theorem squeezed_excitable_iff_summable_sq (b : HilbertBasis I ℂ H) (r : I → ℝ) :
    SqueezedInFockFolium b r ↔ Summable (fun i => (r i) ^ 2) :=
  squeezed_in_fock_folium_iff b r

/-- A nonsummable square family is outside the normal Fock folium. -/
theorem squeezed_not_excitable_of_not_summable_sq (b : HilbertBasis I ℂ H) {r : I → ℝ}
    (h : ¬ Summable (fun i => (r i) ^ 2)) : ¬ SqueezedInFockFolium b r :=
  fun hf => h ((squeezed_excitable_iff_summable_sq b r).mp hf)

end Gaussian


open Physicslib4.GNS in
/-- Any cyclic representation realizing the pure squeezed state is disjoint from Fock
when the squeezing parameters fail to be square-summable. -/
theorem squeezed_gns_disjoint_of_not_summable_sq
    {A S Y : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [AddCommGroup S] [Module ℝ S] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    {σ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} (W : WeylSystem (A := A) σ)
    (b : HilbertBasis I ℂ H) (z : S → H)
    (hz : ∀ (F : Finset I) (w : F → ℂ), ∃ s, z s = modeEmbed b F w)
    (r : I → ℝ) (hr : ¬ Summable (fun i => (r i) ^ 2))
    (ω : State A) (hpure : IsPure ω) (π : A →⋆ₐ[ℂ] (Y →L[ℂ] Y)) (Ω : Y)
    (hcyc : IsCyclicVector π Ω) (hrep : ∀ a, ω a = ⟪Ω, π a Ω⟫_ℂ) (hΩ : ‖Ω‖ = 1)
    (hchar : ∀ (F : Finset I) (w : F → ℂ) (s : S), z s = modeEmbed b F w →
      ω (W.weyl s) = squeezedChar b r (modeEmbed b F w))
    (T : Fock →L[ℂ] Y) (hT : ∀ s, T.comp (weylMap b (z s)) = (π (W.weyl s)).comp T) :
    T = 0 := by
  have hd := dense_range_of_modeEmbed b hz
  have hU : ScalarCommutant (fun s => weylMap b (z s)) := by
    intro R hR
    apply fockWeyl_commutant_scalar b R
    intro w x
    refine hd.induction (fun u hu => ?_) (isClosed_eq ?_ (fockWeyl_strongContinuous b (R x))) w
    · obtain ⟨s, rfl⟩ := hu
      exact DFunLike.congr_fun (hR s) x
    · exact R.continuous.comp (fockWeyl_strongContinuous b x)
  have hV : ScalarCommutant (fun s => π (W.weyl s)) := by
    intro R hR
    apply isIrreducible_of_isPure hcyc hrep hpure R
    let L : A →L[ℂ] (Y →L[ℂ] Y) := ⟨π.toLinearMap,
      NonUnitalStarAlgHom.instContinuousLinearMapClassComplex.map_continuous π⟩
    have hcomm : ((mul ℂ (Y →L[ℂ] Y)).flip R).comp L = ((mul ℂ _) R).comp L :=
      ContinuousLinearMap.ext_on W.dense_span (by rintro _ ⟨s, rfl⟩; exact (hR s).symm)
    exact fun a => DFunLike.congr_fun hcomm a
  have hu (s : S) : weylMap b (z s) * (weylMap b (z s)).adjoint = 1 := by
    change (↑(fockWeyl b (z s)) : Fock →L[ℂ] Fock) *
      adjoint (↑(fockWeyl b (z s)) : Fock →L[ℂ] Fock) = 1
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    exact (fockWeyl b (z s)).apply_symm_apply
  have hv (s : S) : adjoint (π (W.weyl s)) * π (W.weyl s) = 1 := by
    rw [← star_eq_adjoint, ← map_star, ← map_mul, (weyl_unitary W s).1, map_one]
  rcases irreducible_intertwiner_isometry_or_zero _ _ hu hv hU hV T hT with h | ⟨_, U, _, _, hU⟩
  · exact h
  exfalso
  apply squeezed_not_excitable_of_not_summable_sq b hr
  apply single_folium b r (U.symm Ω) (by simpa only [LinearIsometryEquiv.norm_map] using hΩ)
  intro F w
  obtain ⟨s, hs⟩ := hz F w
  rw [← hs, ← U.inner_map_map]
  change ⟪U (U.symm Ω), U (weylMap b (z s) (U.symm Ω))⟫_ℂ = _
  rw [hU s, U.apply_symm_apply, ← hrep, hchar F w s hs, hs]

end D5.S3.Quantum.Analysis.NullConeGravity.CCRFockFactorDisjointness
