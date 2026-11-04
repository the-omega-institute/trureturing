/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianPhysicalSynthesis
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-synthesis)
   anchors: []
   utility: none
   digest: Actual reflected Gaussian functions realize the dense weighted synthesis core. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianCoefficientCore
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The actual Gaussian and Lp representatives are identified by uniqueness
of subsequential limits. No Laguerre completeness, closed synthesis image,
original-domain surjectivity or identification with the original H6 charge
is assumed. The imported Laguerre supplier retains its upstream attribution. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis

private theorem single_feature_eq (n : ℕ) (a x : ℝ) :
    finiteFeature (Finsupp.single n a) x =
      a / coefficientWeight n * centralPsi x (2 * n) := by
  classical
  rw [finiteFeature_eq]
  by_cases ha : a = 0
  · simp [ha, finiteCoefficients]
  · simp [ha, finiteCoefficients]

private theorem synthesis_coordinate_ae_of_hasSum
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (μ : Measure ℝ)
    (P : PhysicalSpace →L[ℝ] Lp ℝ p μ)
    (hfinite : ∀ v : ℕ →₀ ℝ,
      (P (finiteSynthesis v) : ℝ → ℝ) =ᵐ[μ] finiteFeature v)
    (w : Coeff) (F : ℝ → ℝ)
    (hpoint : ∀ x : ℝ, HasSum
      (fun k => w k / coefficientWeight k * centralPsi x (2 * k)) (F x)) :
    (P (synthesis w) : ℝ → ℝ) =ᵐ[μ] F := by
  let u : ℕ → Lp ℝ p μ := fun k => P (finiteSynthesis (Finsupp.single k (w k)))
  have hu : HasSum u (P (synthesis w)) := P.hasSum (synthesis_hasSum w)
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hu.tendsto_sum_nat).exists_seq_tendsto_ae
  have he : ∀ᵐ x ∂μ, ∀ k : ℕ,
      u k x = w k / coefficientWeight k * centralPsi x (2 * k) := by
    rw [ae_all_iff]
    intro k
    exact (hfinite (Finsupp.single k (w k))).mono (fun x hx => by
      simp only [u, hx, single_feature_eq])
  have hsum : ∀ᵐ x ∂μ, ∀ N : ℕ,
      (∑ k ∈ Finset.range N, u k : Lp ℝ p μ) x =
        ∑ k ∈ Finset.range N, u k x := by
    rw [ae_all_iff]
    exact fun N => Lp.coeFn_fun_finsetSum _ _
  filter_upwards [he, hsum, hlim] with x hex hsumx hx
  have hF := (hpoint x).tendsto_sum_nat.comp hns.tendsto_atTop
  have hv : Tendsto
      (fun j => (∑ k ∈ Finset.range (ns j), u k : Lp ℝ p μ) x)
      atTop (𝓝 (F x)) := by
    simpa only [Function.comp_def, hsumx, hex] using hF
  exact tendsto_nhds_unique hx hv

private theorem reflected_even_hasSum (a x : ℝ) :
    HasSum (fun k =>
      finiteGaussianNormalizedCoefficient RHGaussianDilationCore.reflectedSourceCoefficient
          (RHGaussianDilationCore.reflectedSourceSite a) (2 * k) * centralPsi x (2 * k))
      (gaussianFeature RHGaussianDilationCore.reflectedSourceCoefficient
        (RHGaussianDilationCore.reflectedSourceSite a) x) := by
  let c := RHGaussianDilationCore.reflectedSourceCoefficient
  let site := RHGaussianDilationCore.reflectedSourceSite a
  have hc : ∀ i : Fin 3, c ((Equiv.swap (0 : Fin 3) 1) i) = c i := by
    intro i
    fin_cases i <;> norm_num [c, RHGaussianDilationCore.reflectedSourceCoefficient,
      Equiv.swap_apply_def]
  have hs : ∀ i : Fin 3, site ((Equiv.swap (0 : Fin 3) 1) i) = -site i := by
    intro i
    fin_cases i <;> simp [site, RHGaussianDilationCore.reflectedSourceSite,
      Equiv.swap_apply_def]
  have hraw : HasSum (fun n =>
      finiteGaussianNormalizedCoefficient c site n * centralPsi x n)
      (gaussianFeature c site x) := by
    convert finite_gaussian_hasSum c site x using 1
    funext n
    unfold finiteGaussianNormalizedCoefficient centralPsi
    field_simp [(centralNormalization_pos n).ne']
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro i j hij
    dsimp only at hij
    omega
  have hout : ∀ n : ℕ, n ∉ Set.range (fun k : ℕ => 2 * k) →
      finiteGaussianNormalizedCoefficient c site n * centralPsi x n = 0 := by
    intro n hn
    obtain ⟨k, he | ho⟩ := Nat.even_or_odd' n
    · exact (hn ⟨k, he.symm⟩).elim
    · rw [ho, finiteGaussianNormalizedCoefficient,
        finite_gaussian_odd_coefficient_zero c site (Equiv.swap (0 : Fin 3) 1)
          hc hs (2 * k + 1) ⟨k, by omega⟩, zero_div, zero_mul]
  exact (hinj.hasSum_iff hout).2 hraw

/-- The same actual weighted Gaussian core has literal reflected Gaussian
representatives in both constructed physical spaces. -/
theorem actual_reflected_gaussian_physical_synthesis :
    ∃ f : ℝ → Coeff,
      (∀ t : ℝ, 0 < t → t < 1 / 36 → ∀ n : ℕ,
        f t n = RHGaussianDilationCore.coeffWeight n *
          RHGaussianDilationCore.actualReflectedCurveCoefficient t n) ∧
      RHGaussianDilationCore.positiveCurveSpan f (1 / 36) =
        (RHGaussianDilationCore.coeffCharge
          RHGaussianDilationCore.actualCentralChargeVector).ker ∧
      ∀ t : ℝ, 0 < t → t < 1 / 36 →
        let a := RHGaussianDilationCore.positiveGaussianSite t
        let F := fun x => gaussianFeature RHGaussianDilationCore.reflectedSourceCoefficient
          (RHGaussianDilationCore.reflectedSourceSite a) x /
            (2 * gaussianSiteAmplitude a)
        (((synthesis (f t)).1 : ℝ → ℝ) =ᵐ[graphMeasure] F) ∧
        (((synthesis (f t)).2 : ℝ → ℝ) =ᵐ[mellinMeasure] F) := by
  obtain ⟨f, hf, hspan⟩ := RHGaussianDilationCore.actual_reflected_gaussian_coefficient_core
  refine ⟨f, hf, hspan, ?_⟩
  intro t ht ht1
  dsimp only
  let a := RHGaussianDilationCore.positiveGaussianSite t
  let F := fun x => gaussianFeature RHGaussianDilationCore.reflectedSourceCoefficient
    (RHGaussianDilationCore.reflectedSourceSite a) x / (2 * gaussianSiteAmplitude a)
  have hcoord (k : ℕ) : f t k / coefficientWeight k =
      finiteGaussianNormalizedCoefficient RHGaussianDilationCore.reflectedSourceCoefficient
        (RHGaussianDilationCore.reflectedSourceSite a) (2 * k) /
          (2 * gaussianSiteAmplitude a) := by
    rw [hf t ht ht1 k]
    change coefficientWeight k *
      (finiteGaussianNormalizedCoefficient RHGaussianDilationCore.reflectedSourceCoefficient
        (RHGaussianDilationCore.reflectedSourceSite a) (2 * k) /
          (2 * gaussianSiteAmplitude a)) / coefficientWeight k = _
    exact mul_div_cancel_left₀ _ (by unfold coefficientWeight; positivity)
  have hpoint (x : ℝ) : HasSum
      (fun k => f t k / coefficientWeight k * centralPsi x (2 * k)) (F x) := by
    convert (reflected_even_hasSum a x).div_const (2 * gaussianSiteAmplitude a) using 1
    funext k
    rw [hcoord]
    ring
  constructor
  · exact synthesis_coordinate_ae_of_hasSum graphMeasure
      (ContinuousLinearMap.fst ℝ (Lp ℝ 2 graphMeasure) (Lp ℝ 1 mellinMeasure))
      (fun v => (finiteFeature_graph_memLp v).coeFn_toLp) (f t) F hpoint
  · exact synthesis_coordinate_ae_of_hasSum mellinMeasure
      (ContinuousLinearMap.snd ℝ (Lp ℝ 2 graphMeasure) (Lp ℝ 1 mellinMeasure))
      (fun v => (finiteFeature_mellin_memLp v).coeFn_toLp) (f t) F hpoint

end FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis
