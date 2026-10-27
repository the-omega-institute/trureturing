/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianStrictEnergy
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Strict weighted mass for a globally nonzero finite real Gaussian source. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianMellin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Strict weighted mass for a globally nonzero finite real Gaussian source.
Repeated sites and signed coefficients are allowed. Nonvanishing is assumed
on the whole real line, and is transported to every right half-line by real
analytic uniqueness. No positive-half-line nonvanishing is assumed. -/

set_option autoImplicit false
noncomputable section
namespace FiniteGaussianCap4
open MeasureTheory Set Filter
open scoped BigOperators Topology

private theorem feature_analytic {ι : Type*} [Fintype ι] (c site : ι → ℝ) :
    AnalyticOnNhd ℝ (gaussianFeature c site) univ := by
  unfold gaussianFeature gaussianAtom
  exact Finset.analyticOnNhd_fun_sum Finset.univ fun i _ =>
    analyticOnNhd_const.mul
      (analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)).rexp

private theorem feature_continuous {ι : Type*} [Fintype ι] (c site : ι → ℝ) :
    Continuous (gaussianFeature c site) := by
  unfold gaussianFeature gaussianAtom
  fun_prop

private theorem feature_nonzero_on_ray {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (hF : gaussianFeature c site ≠ 0) (b : ℝ) :
    ∃ x : ℝ, b < x ∧ gaussianFeature c site x ≠ 0 := by
  by_contra! hz
  have hev : gaussianFeature c site =ᶠ[𝓝 (b + 1)] (0 : ℝ → ℝ) := by
    filter_upwards [Ioi_mem_nhds (show b < b + 1 by linarith)] with x hx
    exact hz x hx
  exact hF ((feature_analytic c site).eq_of_eventuallyEq analyticOnNhd_const hev)

private theorem atom_product_integrable (a b s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * gaussianAtom a x * gaussianAtom b x)
      (Ioi 0) := by
  let r : ℝ := Real.exp (2 * a) + Real.exp (2 * b)
  have hr : 0 < r := add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hi : IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-r * x)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := s) (p := 1) (b := r) hs (by norm_num) hr)
  apply (hi.const_mul (Real.exp ((9 / 2 : ℝ) * (a + b)))).congr
  filter_upwards with x
  have he : gaussianAtom a x * gaussianAtom b x =
      Real.exp ((9 / 2 : ℝ) * (a + b)) * Real.exp (-r * x) := by
    unfold gaussianAtom
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [r]
    ring
  rw [mul_assoc (x ^ s), he]
  ring

private theorem feature_square_integrable {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * gaussianFeature c site x ^ 2) (Ioi 0) := by
  classical
  have hi (i j : ι) : IntegrableOn
      (fun x : ℝ => (c i * c j) *
        (x ^ s * gaussianAtom (site i) x * gaussianAtom (site j) x)) (Ioi 0) :=
    (atom_product_integrable (site i) (site j) s hs).const_mul _
  have he : (fun x : ℝ => x ^ s * gaussianFeature c site x ^ 2) =
      (fun x : ℝ => ∑ i, ∑ j, (c i * c j) *
        (x ^ s * gaussianAtom (site i) x * gaussianAtom (site j) x)) := by
    funext x
    simp only [gaussianFeature, pow_two, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hi i j

/-- The literal source has positive mass on every positive right half-line,
and its full weighted mass strictly exceeds the endpoint-weighted tail.
There is no assumed integrability, expansion, norm positivity or tail witness. -/
theorem finite_gaussian_strict_weighted_mass {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (hF : gaussianFeature c site ≠ 0)
    (b p : ℝ) (hb : 0 < b) (hp : 0 < p) :
    0 < (∫ x : ℝ in Ioi b, gaussianFeature c site x ^ 2) ∧
      b ^ p * (∫ x : ℝ in Ioi b, gaussianFeature c site x ^ 2) <
        ∫ x : ℝ in Ioi 0, x ^ p * gaussianFeature c site x ^ 2 := by
  let F := gaussianFeature c site
  have hc : Continuous F := feature_continuous c site
  have hsq0 : IntegrableOn (fun x : ℝ => F x ^ 2) (Ioi 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      feature_square_integrable c site 0 (by norm_num)
  have hw0 : IntegrableOn (fun x : ℝ => x ^ p * F x ^ 2) (Ioi 0) :=
    feature_square_integrable c site p (by linarith)
  have hsq := hsq0.mono_set (Ioi_subset_Ioi hb.le)
  have hw := hw0.mono_set (Ioi_subset_Ioi hb.le)
  obtain ⟨x, hbx, hx⟩ := feature_nonzero_on_ray c site hF b
  have hmass : 0 < ∫ x : ℝ in Ioi b, F x ^ 2 := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (fun x : ℝ => sq_nonneg (F x))) hsq).2
    apply ((hc.pow 2).isOpen_support.inter isOpen_Ioi).measure_pos volume
    exact ⟨x, pow_ne_zero 2 hx, hbx⟩
  let g : ℝ → ℝ := fun x => (x ^ p - b ^ p) * F x ^ 2
  have hgc : Continuous g :=
    ((Real.continuous_rpow_const hp.le).sub continuous_const).mul (hc.pow 2)
  have hgi : IntegrableOn g (Ioi b) := by
    exact (hw.sub (hsq.const_mul (b ^ p))).congr_fun
      (fun x _ => by dsimp [g]; ring) measurableSet_Ioi
  have hgn : 0 ≤ᵐ[volume.restrict (Ioi b)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg
      (sub_nonneg.mpr (Real.rpow_le_rpow hb.le hy.le hp.le)) (sq_nonneg _)
  have hgp : 0 < ∫ y : ℝ in Ioi b, g y := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hgn hgi).2
    apply (hgc.isOpen_support.inter isOpen_Ioi).measure_pos volume
    refine ⟨x, ?_, hbx⟩
    exact (mul_pos (sub_pos.mpr (Real.rpow_lt_rpow hb.le hbx hp))
      (sq_pos_of_ne_zero hx)).ne'
  have he : (∫ y : ℝ in Ioi b, g y) =
      (∫ y : ℝ in Ioi b, y ^ p * F y ^ 2) -
        b ^ p * (∫ y : ℝ in Ioi b, F y ^ 2) := by
    dsimp [g]
    simp_rw [sub_mul]
    rw [integral_sub hw (hsq.const_mul _), integral_const_mul]
  have hm : (∫ y : ℝ in Ioi b, y ^ p * F y ^ 2) ≤
      ∫ y : ℝ in Ioi 0, y ^ p * F y ^ 2 := by
    apply setIntegral_mono_set hw0
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (Real.rpow_nonneg hy.le _) (sq_nonneg _)
    · exact Eventually.of_forall (fun y hy => lt_trans hb hy)
  refine ⟨hmass, ?_⟩
  have hstrict := sub_pos.mp (he ▸ hgp)
  exact lt_of_lt_of_le hstrict hm

end FiniteGaussianCap4
