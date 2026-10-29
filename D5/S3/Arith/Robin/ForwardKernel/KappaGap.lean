/- GID: D5/S3/Arith/Robin/ForwardKernel/KappaGap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/KappaGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive logarithmic transforms force two-sided unboundedness of the complete forward response. -/

import D5.S3.Arith.Robin.ForwardKernel.MellinResidue
import D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction
import D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.ZeroData.RiemannVonMangoldtCountGrowth
import D5.S3.Weil.ZetaRvm.NcountWindow
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Positive logarithmic transforms turn zeta residues and zero counts into unbounded excursions. -/

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

private lemma power_budget_continuation {α x0 e k : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    (hx0 : 3 ≤ x0)
    (hbudget : ∀ x : ℝ, x0 ≤ x → 0 ≤ e * forwardResponse x + k) :
    ∃ R : ℂ → ℂ,
      DifferentiableOn ℂ R {s : ℂ | α - 7 / 10 < s.re} ∧
      (∀ σ : ℝ, max 0 (α - 3 / 10) < σ →
        Integrable (fun y : ℝ => Real.exp (-σ * y)) (budgetMeasure x0 e k)) ∧
      (∀ s : ℂ, max (max 0 (α - 3 / 10)) (max (α - 7 / 10) (1 / 2)) < s.re →
        complexMGF id (budgetMeasure x0 e k) (-s) =
          (e : ℂ) * D5.S3.Analytic.Zeta.ZetaLogDerivativeRegularity.regularizedPrincipal s +
            R s + (k : ℂ) * (x0 : ℂ) ^ (-s) / s) := by
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
  exact ⟨R', hR', hconv, hident⟩

private lemma power_budget_constraints {α x0 e k : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    (hx0 : 3 ≤ x0) (he : |e| = 1)
    (hbudget : ∀ x : ℝ, x0 ≤ x → 0 ≤ e * forwardResponse x + k) :
    (∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re - 1 / 2 ≤ max (α - 7 / 10) 0) ∧
      (α < 7 / 10 → ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re = 1 / 2 → 1 / 2 ≤ k) ∧
      (e = 1 → α < 7 / 10 → ∀ Z : Finset ℂ,
        (∀ ρ ∈ Z, IsNontrivialZero ρ ∧ ρ.re = 1 / 2) →
          (Z.card : ℝ) ≤ 16 * k ^ 2) := by
  obtain ⟨R', hR', hconv, hident⟩ := power_budget_continuation hα hE hx0 hbudget
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hρ
    exact D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction.no_positive_pole
      (budgetMeasure_nonnegative (by linarith : 1 ≤ x0) e k)
      (by linarith : 1 < x0) he hR' hconv hident hρ
  · intro hαsmall ρ hρ hρre
    exact D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction.critical_pole_budget
      (budgetMeasure_nonnegative (by linarith : 1 ≤ x0) e k)
      (by linarith : 1 < x0) he hR' hconv hident (by linarith) hρ hρre
  · intro heq hαsmall Z hZ
    subst e
    exact D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction.critical_zeros_budget
      (budgetMeasure_nonnegative (by linarith : 1 ≤ x0) 1 k)
      (by linarith : 1 < x0) hR' hconv hident (by linarith) Z hZ

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

private lemma rh_power_estimate
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε))
    (hRH : RiemannHypothesis) :
    ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC⟩ := hΘ (1 / 10) (by norm_num)
  refine ⟨C, 2, ?_⟩
  intro t ht
  simpa only [zeroAbscissa_eq_half hRH, show (1 / 2 : ℝ) + 1 / 10 = 3 / 5 by norm_num]
    using hC t ht

private theorem rh_budget_minimum
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε))
    (hRH : RiemannHypothesis)
    {x0 e k : ℝ} (hx0 : 3 ≤ x0) (he : |e| = 1)
    (hbudget : ∀ x : ℝ, x0 ≤ x → 0 ≤ e * forwardResponse x + k) : 1 / 2 ≤ k := by
  have hE := rh_power_estimate hΘ hRH
  obtain ⟨ρ, hρ⟩ :=
    D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction.isNontrivialZero_infinite.nonempty
  exact (power_budget_constraints (by norm_num : (0 : ℝ) ≤ 3 / 5) hE hx0 he hbudget).2.1
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

/-- The complete forward response has arbitrarily late negative excursions of every size. -/
theorem forward_response_unbounded_below
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε)) :
    ∀ L X : ℝ, ∃ x : ℝ, X ≤ x ∧ forwardResponse x < L := by
  intro L X
  by_cases hRH : RiemannHypothesis
  · by_contra! hbound
    obtain ⟨n, hn⟩ := exists_nat_gt (16 * (-L) ^ 2)
    obtain ⟨Z, hZ, hcard⟩ :=
      D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction.isNontrivialZero_infinite.exists_subset_card_eq n
    have hbudget : ∀ x : ℝ, max 3 X ≤ x → 0 ≤ 1 * forwardResponse x + -L := by
      intro x hx
      have h := hbound x ((le_max_right _ _).trans hx)
      linarith
    have hmin := (power_budget_constraints (by norm_num : (0 : ℝ) ≤ 3 / 5)
      (rh_power_estimate hΘ hRH) (le_max_left 3 X) (by norm_num : |(1 : ℝ)| = 1)
      hbudget).2.2 rfl (by norm_num) Z (fun ρ hρ =>
        ⟨hZ hρ, Zeta23.RH_implies_on_line hRH (hZ hρ)⟩)
    rw [hcard] at hmin
    linarith
  · exact forward_response_unbounded_below_of_right_zero hΘ
      (exists_right_zero_of_not_rh hRH) L X

/-- Constants below one half are exceeded by arbitrarily late negative excursions. -/
theorem forward_response_lower_kappa_gap
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε)) :
    ∀ κ : ℝ, κ < 1 / 2 → ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ forwardResponse x < -κ := by
  intro κ _ X
  exact forward_response_unbounded_below hΘ (-κ) X

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

private theorem no_uniform_window_budget
    (hRH : RiemannHypothesis)
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig)
    {B : ℝ} (hB : 0 ≤ B)
    (hwindow : ∃ δ : ℝ, 0 < δ ∧ ∀ Z : Finset ℂ,
      (∀ ρ ∈ Z, IsNontrivialZero ρ ∧ ρ.re = 1 / 2) →
      (∀ ρ ∈ Z, ∀ τ ∈ Z, |ρ.im - τ.im| < δ) →
      ∑ ρ ∈ Z, (Zeta23.zeroMult ρ : ℝ) ≤ B) : False := by
  classical
  obtain ⟨δ, hδ, hbudget⟩ := hwindow
  let d : ℝ := δ / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hdδ : d < δ := by dsimp [d]; linarith
  have hshort (t : ℝ) : (Zeta23.Ncount t (t + d) : ℝ) ≤ B := by
    let hfin := Zeta23.zerosIn_finite t (t + d)
    have h := hbudget hfin.toFinset (by
      intro ρ hρ
      have hz := hfin.mem_toFinset.mp hρ
      exact ⟨hz.1, Zeta23.RH_implies_on_line hRH hz.1⟩) (by
      intro ρ hρ τ hτ
      have hzρ := hfin.mem_toFinset.mp hρ
      have hzτ := hfin.mem_toFinset.mp hτ
      apply abs_lt.mpr
      constructor <;> linarith [hzρ.2.1, hzρ.2.2, hzτ.2.1, hzτ.2.2])
    simpa only [Zeta23.Ncount,
      finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum] using h
  have hblocks (t : ℝ) (n : ℕ) :
      (Zeta23.Ncount t (t + n * d) : ℝ) ≤ n * B := by
    induction n with
    | zero =>
      have hzero : Zeta23.zerosIn t t = ∅ := by
        ext ρ
        simp only [Zeta23.zerosIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, hlt, hle⟩
        exact hlt.not_ge hle
      simp [Zeta23.Ncount, hzero]
    | succ n ih =>
      rw [Nat.cast_succ, show t + (↑n + 1) * d = (t + n * d) + d by ring]
      rw [Zeta23.Ncount_add (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hd.le))
        (by linarith : t + n * d ≤ (t + n * d) + d), Nat.cast_add]
      have hs := hshort (t + n * d)
      nlinarith
  have hlinear (T : ℝ) (hT : 0 < T) :
      (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) ≤ B * (T / d + 1) := by
    let n : ℕ := ⌈T / d⌉₊
    have hnlow : T / d ≤ (n : ℝ) := Nat.le_ceil _
    have hnup : (n : ℝ) < T / d + 1 := Nat.ceil_lt_add_one (by positivity)
    have hcover : 2 * T ≤ T + n * d := by
      have := (div_le_iff₀ hd).mp hnlow
      linarith
    have hm : (Zeta23.Ncount T (2 * T) : ℝ) ≤
        (Zeta23.Ncount T (T + n * d) : ℝ) := by
      exact_mod_cast Zeta23.Ncount_mono (le_refl T) hcover
    rw [Zeta23.zetaZeroConfig_N]
    exact hm.trans ((hblocks T n).trans (by nlinarith))
  have hlower := D5.S3.Weil.ZeroData.RiemannVonMangoldtCountGrowth.dyadic_zero_count_eventually_ge
    Zeta23.zetaZeroConfig hRvM
  have hlog := D5.S3.Weil.ZeroData.RiemannVonMangoldtCountGrowth.tendsto_l_atTop.eventually_gt_atTop
    (4 * Real.pi * (B / d + B + 1))
  obtain ⟨T, hT, hlow, hlogT⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and (hlower.and hlog)).exists
  have hTpos : 0 < T := by linarith
  have hup := hlinear T hTpos
  have hmain : T * Zeta23.l T ≤
      (B * (T / d + 1)) * (4 * Real.pi) := by
    exact (div_le_iff₀ (by positivity)).mp (hlow.trans hup)
  have hlogmul : T * (4 * Real.pi * (B / d + B + 1)) < T * Zeta23.l T :=
    mul_lt_mul_of_pos_left hlogT hTpos
  have hBT : B ≤ B * T := by nlinarith
  have heq : B * (T / d + 1) = B / d * T + B := by ring
  rw [heq] at hmain
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscaled := mul_le_mul_of_nonneg_right hBT (show 0 ≤ 4 * Real.pi by positivity)
  nlinarith [mul_pos hTpos hpi]

/-- Riemann-von Mangoldt precludes every eventual upper bound on the complete forward response. -/
theorem forward_response_unbounded_above
    (hΘ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (zeroAbscissa + ε))
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    ∀ L X : ℝ, ∃ x : ℝ, X ≤ x ∧ L < forwardResponse x := by
  intro L X
  by_cases hRH : RiemannHypothesis
  · by_contra! hbound
    have hbudget : ∀ x : ℝ, max 3 X ≤ x → 0 ≤ -1 * forwardResponse x + L := by
      intro x hx
      have h := hbound x ((le_max_right _ _).trans hx)
      linarith
    obtain ⟨R, hR, hconv, hident⟩ :=
      power_budget_continuation (by norm_num : (0 : ℝ) ≤ 3 / 5)
        (rh_power_estimate hΘ hRH) (le_max_left 3 X) hbudget
    have hwindow := D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction.critical_window_budget (k := L)
      (budgetMeasure_nonnegative ((by norm_num : (1 : ℝ) ≤ 3).trans (le_max_left 3 X)) (-1) L)
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) (le_max_left 3 X))
      hR hconv (by simpa only [Complex.ofReal_neg, Complex.ofReal_one] using hident) (by norm_num)
    exact no_uniform_window_budget hRH hRvM (by positivity : 0 ≤ 4 * L ^ 2) hwindow
  · exact forward_response_unbounded_above_of_not_rh hΘ hRH L X

#print axioms budget_exponential_integrable
#print axioms budget_transform
#print axioms forward_response_unbounded_below_of_right_zero
#print axioms forward_response_unbounded_below
#print axioms forward_response_lower_kappa_gap
#print axioms forward_response_upper_kappa_gap_of_rh
#print axioms forward_response_unbounded_above_of_not_rh
#print axioms forward_response_unbounded_above

end
end D5.S3.Arith.Robin.ForwardKernel.KappaGap
