/- GID: D5/S3/Weil/TestFunctions/FiniteAtomicBudgetedCompletion
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/FiniteAtomicBudgetedCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose an even active-contact optimizer into finitely many symmetric Dirac pairs. -/

import D5.S3.Weil.TestFunctions.ActiveFiniteContactCompletion
import D5.S3.Weil.TestFunctions.ComplementaryContactSupport

/- Library-search audit trail (2026-08-31):
   * D5 exact-statement searches found no real-line finite symmetric Dirac
     decomposition owner. The circle-valued active finite-contact theorem covers
     a different atom and constructs a moment-matching replacement measure.
   * D5 body-shape searches found the canonical `fourierLaplace_neg` and
     `complementary_contact_support` owners, which are imported and applied here.
   * Pinned Mathlib provides `Measure.ae_mem_finset_iff`, finite-measure sums,
     Dirac mapping laws, Schwartz decay, and analytic isolated-zero machinery,
     but no packaged theorem with this source statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
open D5.S3.Weil
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions.ComplementaryContactSupport

namespace D5.S3.Weil.TestFunctions.FiniteAtomicBudgetedCompletion

/-- A positive active pressure confines the complementary-contact zero set.
An even residual optimizer supported there is therefore an exact finite sum
of symmetric Dirac pairs, together with a nonnegative zero coefficient. -/
theorem finite_atomic_budgeted_completion
    (a theta : Real) (lambda : NNReal) (ha : 0 < a) (htheta : 0 < theta)
    (phi : WeilTestFunction) (hreal : forall x, conj (phi x) = phi x)
    (residual completion : Measure Real)
    (contactNonnegative : forall xi : Real,
      0 <= (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2))
    (contactIntegrable : Integrable
      (fun xi : Real => (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2))
      residual)
    (residualBudgetIntegrable : Integrable
      (fun xi : Real => 1 / (xi ^ 2 + a ^ 2)) residual)
    (complementarity :
      (∫ xi : Real, (fourierLaplace phi xi).re +
        theta / (xi ^ 2 + a ^ 2) ∂residual) = 0)
    (residualEven : Measure.map (fun xi : Real => -xi) residual = residual)
    (completionSplit : completion =
      ENNReal.ofReal ((lambda : Real) / (2 * Real.pi)) • volume + residual) :
    exists (I : Type) (_ : Fintype I) (point : I -> Real)
        (weight : I -> ENNReal) (weightZero : ENNReal),
      (forall r, weight r ≠ ∞) ∧
      weightZero ≠ ∞ ∧
      (forall r,
        (((point r : Real) : Complex) ^ 2 + (a : Complex) ^ 2) *
            fourierLaplace phi (point r) + theta = 0 /\
        (((-point r : Real) : Complex) ^ 2 + (a : Complex) ^ 2) *
            fourierLaplace phi (-point r) + theta = 0) /\
      completion = ENNReal.ofReal ((lambda : Real) / (2 * Real.pi)) • volume +
        (∑ r, weight r •
          (Measure.dirac (point r) + Measure.dirac (-point r))) +
        weightZero • Measure.dirac 0 := by
  classical
  have contactConclusion := complementary_contact_support a theta ha htheta.le phi hreal
    residual contactNonnegative contactIntegrable complementarity
  dsimp only at contactConclusion
  have supportOnEntireZeros : residual.support <= {xi : Real |
      (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
        fourierLaplace phi xi + theta) = 0} :=
    contactConclusion.2.2.2
  let schwartz : SchwartzMap Real Complex :=
    phi.hasCompactSupport.toSchwartzMap phi.contDiff
  let c : Real := 2 * Real.pi
  let bound : Real :=
    SchwartzMap.seminorm Real 3 0 (FourierTransform.fourier schwartz)
  let radius : Real := max 1 (max (abs a) (2 * (bound + 1) * c ^ 3 / theta))
  let zeros : Set Real := {xi : Real |
    (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
      fourierLaplace phi xi + theta) = 0}
  have zerosConfined : zeros <= Set.Icc (-radius) radius := by
    intro xi xiZero
    by_contra outside
    have xiBeyond : radius < |xi| := by
      apply lt_of_not_ge
      intro xiInside
      apply outside
      exact ⟨(abs_le.mp xiInside).1, (abs_le.mp xiInside).2⟩
    have xiBeyondOne : 1 < |xi| := lt_of_le_of_lt (le_max_left _ _) xiBeyond
    have xiBeyondA : |a| < |xi| := lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right 1 _)) xiBeyond
    have xiBeyondBound : 2 * (bound + 1) * c ^ 3 / theta < |xi| :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) xiBeyond
    have seminormBound := SchwartzMap.norm_pow_mul_le_seminorm Real
      (FourierTransform.fourier schwartz) 3 (c⁻¹ * xi)
    have transformIdentity : fourierLaplace phi xi =
        (FourierTransform.fourier schwartz) (c⁻¹ * xi) := by
      rw [fourierLaplace_real_eq_fourier]
      rw [show mathlibFrequency xi = c⁻¹ * xi by
        unfold mathlibFrequency c
        ring]
      exact congrFun (SchwartzMap.fourier_coe schwartz).symm _
    have transformSmall :
        norm (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
          fourierLaplace phi xi) < theta := by
      have cPositive : 0 < c := by
        dsimp [c]
        positivity
      have boundNonnegative : 0 <= bound := by
        dsimp [bound]
        positivity
      have frequencyAbs : |c⁻¹ * xi| = |xi| / c := by
        rw [abs_mul, abs_inv, abs_of_pos cPositive]
        simp only [div_eq_mul_inv]
        ring
      have scaledTransform :
          |xi| ^ 3 * norm ((FourierTransform.fourier schwartz) (c⁻¹ * xi)) <=
            bound * c ^ 3 := by
        rw [Real.norm_eq_abs, frequencyAbs] at seminormBound
        calc
          |xi| ^ 3 * norm ((FourierTransform.fourier schwartz) (c⁻¹ * xi)) =
              c ^ 3 * ((|xi| / c) ^ 3 *
                norm ((FourierTransform.fourier schwartz) (c⁻¹ * xi))) := by
                field_simp [cPositive.ne']
          _ <= c ^ 3 * bound :=
            mul_le_mul_of_nonneg_left seminormBound (by positivity)
          _ = bound * c ^ 3 := by ring
      have polynomialBound :
          norm ((xi : Complex) ^ 2 + (a : Complex) ^ 2) <= 2 * |xi| ^ 2 := by
        calc
          norm ((xi : Complex) ^ 2 + (a : Complex) ^ 2) <=
              norm ((xi : Complex) ^ 2) + norm ((a : Complex) ^ 2) := norm_add_le _ _
          _ = |xi| ^ 2 + |a| ^ 2 := by simp [norm_pow, Real.norm_eq_abs]
          _ <= 2 * |xi| ^ 2 := by
            have squares : |a| ^ 2 <= |xi| ^ 2 :=
              (sq_le_sq₀ (abs_nonneg a) (abs_nonneg xi)).2 xiBeyondA.le
            linarith
      have productBound :
          norm (((xi : Complex) ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi xi) <=
            2 * |xi| ^ 2 *
              norm ((FourierTransform.fourier schwartz) (c⁻¹ * xi)) := by
        rw [norm_mul, transformIdentity]
        exact mul_le_mul_of_nonneg_right polynomialBound (norm_nonneg _)
      have pressureBound : 2 * bound * c ^ 3 < theta * |xi| := by
        have strictBound : 2 * bound * c ^ 3 < 2 * (bound + 1) * c ^ 3 := by
          nlinarith [pow_pos cPositive 3]
        exact strictBound.trans (by
          simpa [mul_comm] using (div_lt_iff₀ htheta).mp xiBeyondBound)
      refine lt_of_le_of_lt productBound ?_
      have multipliedBound :
          (2 * |xi| ^ 2 *
              norm ((FourierTransform.fourier schwartz) (c⁻¹ * xi))) * |xi| <
            theta * |xi| := by
        calc
          (2 * |xi| ^ 2 *
              norm ((FourierTransform.fourier schwartz) (c⁻¹ * xi))) * |xi| =
              2 * (|xi| ^ 3 *
                norm ((FourierTransform.fourier schwartz) (c⁻¹ * xi))) := by ring
          _ <= 2 * (bound * c ^ 3) := by nlinarith
          _ < theta * |xi| := by nlinarith
      exact lt_of_mul_lt_mul_right multipliedBound (show 0 <= |xi| by positivity)
    have transformNormEquals :
        norm (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
          fourierLaplace phi xi) = theta := by
      change (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
        fourierLaplace phi xi + theta) = 0 at xiZero
      rw [← neg_eq_iff_add_eq_zero] at xiZero
      calc
        norm (((xi : Complex) ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi xi) =
            norm (-(((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
              fourierLaplace phi xi)) := (norm_neg _).symm
        _ = norm (theta : Complex) := congrArg norm xiZero
        _ = theta := by simp [htheta.le]
    linarith
  have zerosFinite : zeros.Finite := by
    by_contra zerosInfinite
    have zerosInfinite' : zeros.Infinite := zerosInfinite
    obtain ⟨xi, _xiInInterval, accumulation⟩ :=
      zerosInfinite'.exists_accPt_of_subset_isCompact isCompact_Icc zerosConfined
    have zeroFrequently :
        ∃ᶠ y : Real in 𝓝[≠] xi,
          (((y : Complex) ^ 2 + (a : Complex) ^ 2) *
            fourierLaplace phi y + theta) = 0 := by
      exact (accPt_iff_frequently_nhdsNE.mp accumulation).mono fun y hy => hy
    have analyticReal : AnalyticOnNhd Real
        (fun y : Real => (((y : Complex) ^ 2 + (a : Complex) ^ 2) *
          fourierLaplace phi y + theta)) univ := by
      intro y _
      have transformAnalytic : AnalyticAt Complex (fourierLaplace phi) (y : Complex) :=
        (fourierLaplace_entire phi).analyticAt _
      have complexAnalytic : AnalyticAt Complex
          (fun z : Complex =>
            (z ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi z + theta)
          (y : Complex) := by
        fun_prop
      exact complexAnalytic.restrictScalars.comp (Complex.ofRealCLM.analyticAt y)
    have identicallyZero := analyticReal.eq_of_frequently_eq
      analyticOnNhd_const zeroFrequently
    have outsideInterval : radius + 1 ∉ Set.Icc (-radius) radius := by simp
    have outsideZeros : radius + 1 ∉ zeros := fun hz =>
      outsideInterval (zerosConfined hz)
    apply outsideZeros
    simpa only [zeros, Set.mem_setOf_eq] using congrFun identicallyZero (radius + 1)
  let zeroFinset : Finset Real := zerosFinite.toFinset
  have residualOnZeroFinset : ∀ᵐ xi ∂residual, xi ∈ zeroFinset := by
    filter_upwards [Measure.support_mem_ae] with xi xiInSupport
    exact zerosFinite.mem_toFinset.mpr (supportOnEntireZeros xiInSupport)
  let I := {xi // xi ∈ zeroFinset}
  letI : Fintype I := Finset.Subtype.fintype zeroFinset
  let point : I -> Real := fun xi => xi
  let weight : I -> ENNReal := fun xi => (2 : ENNReal)⁻¹ * residual {xi.1}
  let weightZero : ENNReal := 0
  have residualSingletonFinite (xi : Real) : residual {xi} ≠ ∞ := by
    have singletonIntegrable : IntegrableOn
        (fun y : Real => 1 / (y ^ 2 + a ^ 2)) {xi} residual :=
      residualBudgetIntegrable.integrableOn
    rcases (integrableOn_singleton_iff (μ := residual) (x := xi)).mp
      singletonIntegrable with valueZero | measureFinite
    · have valuePositive : 0 < (1 / (xi ^ 2 + a ^ 2) : Real) := by
        positivity
      exact (valuePositive.ne' (enorm_eq_zero.mp valueZero)).elim
    · exact measureFinite.ne
  have weightFinite (r : I) : weight r ≠ ∞ := by
    dsimp only [weight]
    exact ENNReal.mul_ne_top (by simp) (residualSingletonFinite r.1)
  have weightZeroFinite : weightZero ≠ ∞ := by
    simp [weightZero]
  have residualFinsetExpansion :
      residual = ∑ xi ∈ zeroFinset, residual {xi} • Measure.dirac xi :=
    Measure.ae_mem_finset_iff.mp residualOnZeroFinset
  have residualExpansion :
      (∑ xi : I, residual {xi.1} • Measure.dirac xi.1) = residual := by
    change (∑ xi : {xi // xi ∈ zeroFinset},
      residual {xi.1} • Measure.dirac xi.1) = residual
    calc
      _ = ∑ xi ∈ zeroFinset, residual {xi} • Measure.dirac xi :=
        Finset.sum_coe_sort zeroFinset
          (fun xi => residual {xi} • Measure.dirac xi)
      _ = residual := residualFinsetExpansion.symm
  have reflectedExpansion :
      (∑ xi : I, residual {xi.1} • Measure.dirac (-xi.1)) = residual := by
    calc
      (∑ xi : I, residual {xi.1} • Measure.dirac (-xi.1)) =
          Measure.map (fun xi : Real => -xi)
            (∑ xi : I, residual {xi.1} • Measure.dirac xi.1) := by
        rw [Measure.map_finset_sum' measurable_neg.aemeasurable]
        simp
      _ = Measure.map (fun xi : Real => -xi) residual := by rw [residualExpansion]
      _ = residual := residualEven
  have pairedExpansion : residual =
      ∑ xi : I, ((2 : ENNReal)⁻¹ * residual {xi.1}) •
        (Measure.dirac xi.1 + Measure.dirac (-xi.1)) := by
    calc
      residual = (2 : ENNReal)⁻¹ • residual + (2 : ENNReal)⁻¹ • residual := by
        rw [← add_smul]
        rw [ENNReal.inv_two_add_inv_two, one_smul]
      _ = (2 : ENNReal)⁻¹ •
            (∑ xi : I, residual {xi.1} • Measure.dirac xi.1) +
          (2 : ENNReal)⁻¹ •
            (∑ xi : I, residual {xi.1} • Measure.dirac (-xi.1)) := by
        rw [residualExpansion, reflectedExpansion]
      _ = ∑ xi : I, ((2 : ENNReal)⁻¹ * residual {xi.1}) •
          (Measure.dirac xi.1 + Measure.dirac (-xi.1)) := by
        rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro xi _
        rw [smul_add, smul_smul, smul_smul]
  refine ⟨I, inferInstance, point, weight, weightZero, weightFinite,
    weightZeroFinite, ?_, ?_⟩
  · intro r
    have pointZero :
        (((r.1 : Complex) ^ 2 + (a : Complex) ^ 2) *
          fourierLaplace phi r.1 + theta) = 0 :=
      zerosFinite.mem_toFinset.mp r.2
    refine ⟨pointZero, ?_⟩
    simpa only [Complex.ofReal_neg, neg_sq, fourierLaplace_neg] using pointZero
  · dsimp only [point, weight, weightZero]
    rw [zero_smul, add_zero, ← pairedExpansion]
    exact completionSplit

#print axioms finite_atomic_budgeted_completion

end D5.S3.Weil.TestFunctions.FiniteAtomicBudgetedCompletion
