import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster
import Reg.Support.SingleDependentReadout

/-! The real-part observation determines the upper-bound line. At β = 1 the
actual line is empty, whereas the constant observation 1 selects every zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Complex.re) (fun e => nomatch e)

def constantOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ (β : ℝ),
    let realPart := V.readout () ()
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    ∀ (A : ℝ → ℝ), (∀ᶠ B in atTop, 2 ≤ A B ∧ A B ≤ B) →
      Tendsto (fun B => Real.log (B / A B)) atTop atTop → ∀ y : ℝ,
        MapClusterPt y atTop (fun B : ℝ =>
          (∫ x in A B..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (β - 1 / 2)) ↔
        ∃ h ∈ closure (range phaseOrbit), y = phaseWindowInfinite realPart β h

private theorem actual_window_at_one (h : ℕ → Circle) :
    phaseWindowInfinite Complex.re 1 h = 0 := by
  have hcut (k : ℕ) : rightmostCoeff Complex.re 1 k = 0 :=
    if_neg (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2.ne
  change (∫ s in Ioi (0 : ℝ),
    Real.exp (-(1 - 1 / 2) * s) * max (-phaseProfile Complex.re 1 h (-s)) 0) = 0
  simp [phaseProfile, hcut]

private theorem constant_window_positive :
    0 < phaseWindowInfinite (fun _ => 1) 1 (1 : ℕ → Circle) := by
  let term (s : ℝ) (k : ℕ) := actualCoeff k * (phaseOrbit (-s) k : ℂ)
  let series (s : ℝ) := ∑' k : ℕ, term s k
  let f (s : ℝ) := Real.exp (-(1 / 2) * s) * max (series s).re 0
  let C := ∑' k : ℕ, ‖actualCoeff k‖
  have hcoeff := actualCoeff_hasSum.summable.norm
  have hterm (s : ℝ) (k : ℕ) : ‖term s k‖ = ‖actualCoeff k‖ := by
    simp [term, norm_mul]
  have hseries (s : ℝ) : (series s).re ≤ C := by
    have hs : Summable (fun k => ‖term s k‖) := by simpa only [hterm] using hcoeff
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
      ((norm_tsum_le_tsum_norm hs).trans_eq (tsum_congr (hterm s))))
  have hzero : 0 < (series 0).re := by
    have hsum := Complex.hasSum_re actualCoeff_hasSum
    have hpos (k : ℕ) : 0 < (actualCoeff k).re := by
      have hk := actualData.zero_isNontrivial (actualOccurrenceEquiv k).1
      exact (heightRefinement_pairWeight_strip hk.2.1 hk.2.2).1
    simpa only [series, term, neg_zero, phaseOrbit, zero_mul, Circle.exp_zero, Circle.coe_one,
      mul_one, actualCoeff_hasSum.tsum_eq, Complex.ofReal_re, hsum.tsum_eq] using
      hsum.summable.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  have heq (s : ℝ) : -phaseProfile (fun _ => 1) 1 (1 : ℕ → Circle) (-s) = (series s).re := by
    simp [phaseProfile, rightmostCoeff, series, term]
  have hcont : Continuous f := by
    have hw : Continuous (fun s : ℝ => Real.exp (-(1 / 2) * s)) := by fun_prop
    have hf : Continuous (fun s : ℝ => -phaseProfile (fun _ => 1) 1 (1 : ℕ → Circle) (-s)) :=
      ((phaseProfile_continuous _ _).comp (continuous_const.prodMk continuous_neg)).neg
    simp_rw [heq] at hf
    exact hw.mul (hf.max continuous_const)
  have hnonneg (s : ℝ) : 0 ≤ f s := mul_nonneg (Real.exp_nonneg _) (le_max_right _ _)
  have hint (a : ℝ) : IntegrableOn f (Ioi a) := by
    have hmajor := (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) a).const_mul C
    refine hmajor.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [Real.norm_of_nonneg (hnonneg s), mul_comm C]
    exact mul_le_mul_of_nonneg_left
      (max_le (hseries s) (tsum_nonneg fun _ => norm_nonneg _)) (Real.exp_nonneg _)
  have hpos : 0 < ∫ s in (0 : ℝ)..1, f s :=
    intervalIntegral.integral_pos zero_lt_one hcont.continuousOn (fun s _ => hnonneg s)
      ⟨0, by simp, mul_pos (Real.exp_pos _) (hzero.trans_le (le_max_left _ _))⟩
  change 0 < ∫ s in Ioi (0 : ℝ),
    Real.exp (-(1 - 1 / 2) * s) * max (-phaseProfile (fun _ => 1) 1 (1 : ℕ → Circle) (-s)) 0
  simp_rw [heq, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  change 0 < ∫ s in Ioi (0 : ℝ), f s
  rw [← intervalIntegral.integral_interval_add_Ioi (hint 0) (hint 1)]
  exact add_pos_of_pos_of_nonneg hpos (integral_nonneg hnonneg)

private theorem constant_one_fails : ¬ arena.Law constantOne := by
  intro law
  let A (_ : ℝ) : ℝ := 2
  have hA : ∀ᶠ B in atTop, 2 ≤ A B ∧ A B ≤ B :=
    (eventually_ge_atTop (2 : ℝ)).mono fun _ h => ⟨le_rfl, h⟩
  have hgrow : Tendsto (fun B => Real.log (B / A B)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  let y := phaseWindowInfinite (fun _ => 1) 1 (1 : ℕ → Circle)
  have hone : (1 : ℕ → Circle) ∈ closure (range phaseOrbit) := by
    refine subset_closure ⟨0, ?_⟩
    funext k
    simp [phaseOrbit]
  have hcluster := (law 1 (by norm_num) (fun _ _ => le_rfl) A hA hgrow y).2 ⟨1, hone, rfl⟩
  obtain ⟨h, _, hy⟩ := (prime_tail_growing_width_cluster_iff_of_upper_bound 1
    (by norm_num) (fun _ hz => hz.2.2.le) A hA hgrow y).1 hcluster
  rw [actual_window_at_one h] at hy
  exact (ne_of_gt constant_window_positive) hy

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family :
    Registration arena (type_of% @prime_tail_growing_width_cluster_iff_of_upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_growing_width_cluster_iff_of_upper_bound, constantOne, constant_one_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual constantOne constant_one_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_growing_width_cluster_iff_of_upper_bound) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_growing_width_cluster_iff_of_upper_bound "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Complex.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster
