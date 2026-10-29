/- GID: D5/S3/Arith/Robin/ForwardKernel/KappaGap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/KappaGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive logarithmic transforms constrain the complete forward response. -/

import D5.S3.Arith.Robin.ForwardKernel.MellinResidue
import D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction
import D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Positive logarithmic transforms turn zeta poles into one-sided oscillation bounds. -/

namespace D5.S3.Arith.Robin.ForwardKernel.KappaGap

open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology
open ForwardKernel.Transport (forwardResponse)
open ForwardKernel.MellinConvergence (forwardMellin)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

noncomputable section

/-- The supremum of the real parts of zeros in the open critical strip. -/
def zeroAbscissa : ℝ := sSup (Complex.re '' {ρ : ℂ | IsNontrivialZero ρ})

private lemma zero_real_parts_nonempty :
    (Complex.re '' {ρ : ℂ | IsNontrivialZero ρ}).Nonempty :=
  D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction.isNontrivialZero_infinite.nonempty.image _

private lemma zero_real_parts_bddAbove :
    BddAbove (Complex.re '' {ρ : ℂ | IsNontrivialZero ρ}) := by
  refine ⟨1, ?_⟩
  rintro r ⟨ρ, hρ, rfl⟩
  exact hρ.2.2.le

private lemma zero_re_le_abscissa {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ρ.re ≤ zeroAbscissa :=
  le_csSup zero_real_parts_bddAbove ⟨ρ, hρ, rfl⟩

private lemma zeroAbscissa_nonnegative : 0 ≤ zeroAbscissa := by
  obtain ⟨ρ, hρ⟩ :=
    D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction.isNontrivialZero_infinite.nonempty
  exact hρ.2.1.le.trans (zero_re_le_abscissa hρ)

private lemma zeroAbscissa_eq_half (hRH : RiemannHypothesis) : zeroAbscissa = 1 / 2 := by
  apply le_antisymm
  · apply csSup_le zero_real_parts_nonempty
    rintro r ⟨ρ, hρ, rfl⟩
    exact (Zeta23.RH_implies_on_line hRH hρ).le
  · obtain ⟨ρ, hρ⟩ :=
      D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction.isNontrivialZero_infinite.nonempty
    simpa only [Zeta23.RH_implies_on_line hRH hρ] using zero_re_le_abscissa hρ

private lemma exists_right_zero_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 1 / 2 < ρ.re := by
  by_contra! hnone
  apply hRH
  apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro ρ hzero hhalf hone
  have hρ : IsNontrivialZero ρ := ⟨hzero, by linarith, hone⟩
  exact (not_lt_of_ge (hnone ρ hρ)) hhalf

private lemma near_abscissa_right_zero
    (hzero : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 1 / 2 < ρ.re) :
    ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 1 / 2 < ρ.re ∧ zeroAbscissa - 1 / 5 < ρ.re := by
  obtain ⟨ρ0, hρ0, hhalf⟩ := hzero
  have hsup : 1 / 2 < zeroAbscissa := hhalf.trans_le (zero_re_le_abscissa hρ0)
  have hmax : max (1 / 2) (zeroAbscissa - 1 / 5) < zeroAbscissa := by
    apply max_lt_iff.mpr
    constructor <;> linarith
  obtain ⟨r, ⟨ρ, hρ, rfl⟩, hr⟩ := exists_lt_of_lt_csSup zero_real_parts_nonempty hmax
  exact ⟨ρ, hρ, lt_of_le_of_lt (le_max_left _ _) hr,
    lt_of_le_of_lt (le_max_right _ _) hr⟩

/-- A positive measure records a one-sided bound on the response in logarithmic coordinates. -/
def budgetMeasure (x0 e k : ℝ) : Measure ℝ :=
  ((volume.restrict (Ioi x0)).withDensity
    (fun x => ENNReal.ofReal ((e * forwardResponse x + k) / x))).map Real.log

private lemma budget_density_measurable (e k : ℝ) :
    Measurable (fun x => ENNReal.ofReal ((e * forwardResponse x + k) / x)) :=
  ENNReal.measurable_ofReal.comp
    (((ForwardKernel.MellinConvergence.response_measurable.const_mul e).add_const k).div
      measurable_id)

private lemma budget_cpow_identity (e k : ℝ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (((e * forwardResponse x + k) / x : ℝ) : ℂ) *
        Complex.exp (-s * (Real.log x : ℂ)) =
      ((e : ℂ) * (forwardResponse x : ℂ) + k) * (x : ℂ) ^ (-s - 1) := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : Complex.exp (-s * (Real.log x : ℂ)) = (x : ℂ) ^ (-s) := by
    rw [Complex.cpow_def_of_ne_zero hxne, ← Complex.ofReal_log hx.le]
    congr 1
    ring
  rw [hp, Complex.cpow_sub _ _ hxne, Complex.cpow_one]
  push_cast
  ring

/-- The budget measure is supported on nonnegative logarithmic coordinates. -/
lemma budgetMeasure_nonnegative {x0 : ℝ} (hx0 : 1 ≤ x0) (e k : ℝ) :
    ∀ᵐ y ∂budgetMeasure x0 e k, 0 ≤ y := by
  apply (ae_map_iff Real.measurable_log.aemeasurable measurableSet_Ici).2
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact Real.log_nonneg (hx0.trans hx.le)

/-- The pointwise response estimate gives a genuine initial convergence half-plane. -/
theorem budget_exponential_integrable {α x0 e k σ : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    (hx0 : 3 ≤ x0)
    (hbudget : ∀ x : ℝ, x0 ≤ x → 0 ≤ e * forwardResponse x + k)
    (hσ : max 0 (α - 3 / 10) < σ) :
    Integrable (fun y : ℝ => Real.exp (-σ * y)) (budgetMeasure x0 e k) := by
  have hresponse := ForwardKernel.MellinConvergence.forwardMellin_integrable hα hE hx0
    (s := (σ : ℂ)) (lt_of_le_of_lt (le_max_right _ _) hσ)
  have hσ0 : 0 < σ := lt_of_le_of_lt (le_max_left _ _) hσ
  have hpower : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(σ : ℂ) - 1)) (Ioi x0) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) (by linarith)
  have hsum : IntegrableOn (fun x : ℝ =>
      ((e : ℂ) * (forwardResponse x : ℂ) + k) * (x : ℂ) ^ (-(σ : ℂ) - 1)) (Ioi x0) := by
    apply ((hresponse.const_mul (e : ℂ)).add (hpower.const_mul (k : ℂ))).congr
    filter_upwards [] with x
    dsimp
    ring
  have hi : Integrable (fun x : ℝ => Complex.exp (-(σ : ℂ) * (Real.log x : ℂ)))
      ((volume.restrict (Ioi x0)).withDensity
        (fun x => ENNReal.ofReal ((e * forwardResponse x + k) / x))) := by
    apply (integrable_withDensity_iff_integrable_smul' (budget_density_measurable e k)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
    apply hsum.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := (by linarith : 0 < x0).trans hx
    rw [ENNReal.toReal_ofReal (div_nonneg (hbudget x hx.le) hxpos.le), Complex.real_smul]
    exact (budget_cpow_identity e k (σ : ℂ) hxpos).symm
  have himap : Integrable (fun y : ℝ => Complex.exp (-(σ : ℂ) * (y : ℂ)))
      (budgetMeasure x0 e k) := by
    apply (integrable_map_measure (by fun_prop) Real.measurable_log.aemeasurable).2
    exact hi
  convert himap.norm using 1
  ext y
  simp [Complex.norm_exp]

/-- A nonnegative one-sided budget has precisely the shifted forward Mellin transform. -/
theorem budget_transform {α x0 e k : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    (hx0 : 3 ≤ x0)
    (hbudget : ∀ x : ℝ, x0 ≤ x → 0 ≤ e * forwardResponse x + k)
    {s : ℂ} (hs : max 0 (α - 3 / 10) < s.re) :
    complexMGF id (budgetMeasure x0 e k) (-s) =
      (e : ℂ) * forwardMellin x0 s + (k : ℂ) * (x0 : ℂ) ^ (-s) / s := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsα : α - 3 / 10 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hresponse := ForwardKernel.MellinConvergence.forwardMellin_integrable hα hE hx0 hsα
  have hpower : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi x0) :=
    integrableOn_Ioi_cpow_of_lt (by simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith)
      (by linarith)
  unfold budgetMeasure
  rw [complexMGF_id_map Real.measurable_log.aemeasurable, complexMGF,
    integral_withDensity_eq_integral_toReal_smul (budget_density_measurable e k)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun x => (ENNReal.ofReal ((e * forwardResponse x + k) / x)).toReal •
      Complex.exp (-s * (Real.log x : ℂ))) =ᵐ[volume.restrict (Ioi x0)]
      (fun x => ((e : ℂ) * (forwardResponse x : ℂ) + k) * (x : ℂ) ^ (-s - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := (by linarith : 0 < x0).trans hx
    rw [ENNReal.toReal_ofReal (div_nonneg (hbudget x hx.le) hxpos.le), Complex.real_smul]
    exact budget_cpow_identity e k s hxpos
  rw [integral_congr_ae heq]
  have hpval := integral_Ioi_cpow_of_lt
    (a := -s - 1) (by simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith)
    (c := x0) (by linarith)
  simp only [sub_add_cancel, neg_div_neg_eq] at hpval
  calc
    _ = (e : ℂ) * forwardMellin x0 s +
        (k : ℂ) * ∫ x in Ioi x0, (x : ℂ) ^ (-s - 1) := by
      unfold forwardMellin
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        (hresponse.const_mul (e : ℂ)) (hpower.const_mul (k : ℂ))]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      ring
    _ = _ := by rw [hpval]; ring

private lemma power_budget_constraints {α x0 e k : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    (hx0 : 3 ≤ x0) (he : |e| = 1)
    (hbudget : ∀ x : ℝ, x0 ≤ x → 0 ≤ e * forwardResponse x + k) :
    (∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re - 1 / 2 ≤ max (α - 7 / 10) 0) ∧
      (α < 7 / 10 → ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re = 1 / 2 → 1 / 2 ≤ k) := by
  obtain ⟨R, hR, hidentity⟩ :=
    ForwardKernel.MellinResidue.forward_kernel_mellin_residue hα hE hx0
  let B : ℝ := max 0 (α - 3 / 10)
  let R' : ℂ → ℂ := fun s => (e : ℂ) * R s
  have hR' : DifferentiableOn ℂ R' {s : ℂ | α - 7 / 10 < s.re} := hR.const_mul _
  have hconv : ∀ σ : ℝ, B < σ →
      Integrable (fun y : ℝ => Real.exp (-σ * y)) (budgetMeasure x0 e k) :=
    fun σ hσ => budget_exponential_integrable hα hE hx0 hbudget hσ
  have hident : ∀ s : ℂ, max B (max (α - 7 / 10) (1 / 2)) < s.re →
      complexMGF id (budgetMeasure x0 e k) (-s) =
        (e : ℂ) * D5.S3.Analytic.Zeta.ZetaLogDerivativeRegularity.regularizedPrincipal s +
          R' s + (k : ℂ) * (x0 : ℂ) ^ (-s) / s := by
    intro s hs
    have hsB : B < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hshalf : 1 / 2 < s.re :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
    have hsα : α - 3 / 10 < s.re :=
      lt_of_le_of_lt (le_max_right _ _) hsB
    have hsne : s ≠ 1 / 2 := by
      intro h
      have := hshalf
      simp [h] at this
    have hζ : riemannZeta (s + 1 / 2) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp only [Complex.add_re]; norm_num; linarith)
    rw [budget_transform hα hE hx0 hbudget hsB,
      hidentity s (max_lt_iff.mpr ⟨hshalf, hsα⟩),
      D5.S3.Analytic.Zeta.ZetaLogDerivativeRegularity.regularizedPrincipal_eq hsne hζ]
    dsimp [R']
    ring
  refine ⟨?_, ?_⟩
  · intro ρ hρ
    exact D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction.no_positive_pole
      (budgetMeasure_nonnegative (by linarith : 1 ≤ x0) e k)
      (by linarith : 1 < x0) he hR' hconv hident hρ
  · intro hαsmall ρ hρ hρre
    exact D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction.critical_pole_budget
      (budgetMeasure_nonnegative (by linarith : 1 ≤ x0) e k)
      (by linarith : 1 < x0) he hR' hconv hident (by linarith) hρ hρre

private theorem no_budget_of_right_zero
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε))
    (hzero : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 1 / 2 < ρ.re)
    {x0 e k : ℝ} (hx0 : 3 ≤ x0) (he : |e| = 1)
    (hbudget : ∀ x : ℝ, x0 ≤ x → 0 ≤ e * forwardResponse x + k) : False := by
  obtain ⟨ρ, hρ, hhalf, hnear⟩ := near_abscissa_right_zero hzero
  let ε : ℝ := (ρ.re - zeroAbscissa + 1 / 5) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC⟩ := hΘ ε hε
  have hα : 0 ≤ zeroAbscissa + ε := add_nonneg zeroAbscissa_nonnegative hε.le
  have hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε) := ⟨C, 2, hC⟩
  have hpole := (power_budget_constraints hα hE hx0 he hbudget).1 ρ hρ
  have hright : max (zeroAbscissa + ε - 7 / 10) 0 < ρ.re - 1 / 2 := by
    apply max_lt_iff.mpr
    constructor
    · dsimp [ε]
      linarith
    · linarith
  exact hright.not_ge hpole

private theorem rh_budget_minimum
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε))
    (hRH : RiemannHypothesis)
    {x0 e k : ℝ} (hx0 : 3 ≤ x0) (he : |e| = 1)
    (hbudget : ∀ x : ℝ, x0 ≤ x → 0 ≤ e * forwardResponse x + k) : 1 / 2 ≤ k := by
  obtain ⟨C, hC⟩ := hΘ (1 / 10) (by norm_num)
  have hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (3 / 5 : ℝ) := by
    refine ⟨C, 2, ?_⟩
    intro t ht
    simpa only [zeroAbscissa_eq_half hRH, show (1 / 2 : ℝ) + 1 / 10 = 3 / 5 by norm_num]
      using hC t ht
  obtain ⟨ρ, hρ⟩ :=
    D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction.isNontrivialZero_infinite.nonempty
  exact (power_budget_constraints (by norm_num : (0 : ℝ) ≤ 3 / 5) hE hx0 he hbudget).2
    (by norm_num) ρ hρ (Zeta23.RH_implies_on_line hRH hρ)

/-- A zero strictly to the right of the critical line precludes every eventual lower bound. -/
theorem forward_response_unbounded_below_of_right_zero
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε))
    (hzero : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 1 / 2 < ρ.re) :
    ∀ L X : ℝ, ∃ x : ℝ, X ≤ x ∧ forwardResponse x < L := by
  intro L X
  by_contra! hbound
  apply no_budget_of_right_zero hΘ hzero (x0 := max 3 X) (e := 1) (k := -L)
    (le_max_left _ _) (by norm_num)
  intro x hx
  have h := hbound x ((le_max_right _ _).trans hx)
  simp only [one_mul]
  linarith

/-- Constants below one half are exceeded by arbitrarily late negative excursions. -/
theorem forward_response_lower_kappa_gap
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε)) :
    ∀ κ : ℝ, κ < 1 / 2 → ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ forwardResponse x < -κ := by
  intro κ hκ X
  by_cases hRH : RiemannHypothesis
  · by_contra! hbound
    have hmin := rh_budget_minimum hΘ hRH (x0 := max 3 X) (e := 1) (k := κ)
      (le_max_left _ _) (by norm_num) (by
        intro x hx
        have h := hbound x ((le_max_right _ _).trans hx)
        simp only [one_mul]
        linarith)
    linarith
  · exact forward_response_unbounded_below_of_right_zero hΘ (exists_right_zero_of_not_rh hRH) (-κ) X

/-- Under RH, every constant below one half is exceeded by arbitrarily late positive excursions. -/
theorem forward_response_upper_kappa_gap_of_rh
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε))
    (hRH : RiemannHypothesis) :
    ∀ K : ℝ, K < 1 / 2 → ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ K < forwardResponse x := by
  intro K hK X
  by_contra! hbound
  have hmin := rh_budget_minimum hΘ hRH (x0 := max 3 X) (e := -1) (k := K)
    (le_max_left _ _) (by norm_num) (by
      intro x hx
      have h := hbound x ((le_max_right _ _).trans hx)
      simp only [neg_mul, one_mul]
      linarith)
  linarith

/-- Failure of RH precludes every eventual upper bound on the complete forward response. -/
theorem forward_response_unbounded_above_of_not_rh
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε))
    (hRH : ¬ RiemannHypothesis) :
    ∀ L X : ℝ, ∃ x : ℝ, X ≤ x ∧ L < forwardResponse x := by
  intro L X
  by_contra! hbound
  apply no_budget_of_right_zero hΘ (exists_right_zero_of_not_rh hRH)
    (x0 := max 3 X) (e := -1) (k := L) (le_max_left _ _) (by norm_num)
  intro x hx
  have h := hbound x ((le_max_right _ _).trans hx)
  simp only [neg_mul, one_mul]
  linarith

#print axioms budget_exponential_integrable
#print axioms budget_transform
#print axioms forward_response_unbounded_below_of_right_zero
#print axioms forward_response_lower_kappa_gap
#print axioms forward_response_upper_kappa_gap_of_rh
#print axioms forward_response_unbounded_above_of_not_rh

end
end D5.S3.Arith.Robin.ForwardKernel.KappaGap
