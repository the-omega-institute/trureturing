import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster
import Reg.Support.SingleDependentReadout

/-! The real-part observation determines the upper-bound line. At β = 1
the actual line is empty and the constant observation 1 selects every zero. -/

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

theorem actual_window_at_one (h : ℕ → Circle) :
    phaseWindowInfinite Complex.re 1 h = 0 := by
  have hcut (k : ℕ) : rightmostCoeff Complex.re 1 k = 0 :=
    ite_eq_right (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2.ne
  change (∫ s in Ioi (0 : ℝ),
    Real.exp (-(1 - 1 / 2) * s) * max (-phaseProfile Complex.re 1 h (-s)) 0) = 0
  simp [phaseProfile, hcut]

private theorem constant_density_continuous :
    Continuous (fun q : (ℕ → Circle) × ℝ =>
      Real.exp (-((1 : ℝ) - 1 / 2) * q.2) * max (-phaseProfile (fun _ => 1) 1 q.1 (-q.2)) 0) := by
  apply Continuous.mul (by fun_prop)
  exact (((phaseProfile_continuous (fun _ => 1) 1).comp
    (continuous_fst.prodMk continuous_snd.neg)).neg.max continuous_const)

theorem constant_window_continuous : Continuous (phaseWindow (fun _ => 1) 1 1) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    constant_density_continuous 0 1

theorem constant_window_finite_positive :
    0 < phaseWindow (fun _ => 1) 1 1 (1 : ℕ → Circle) := by
  have hsum := Complex.hasSum_re actualCoeff_hasSum
  have hpos (k : ℕ) : 0 < (actualCoeff k).re := by
    have hk := actualData.zero_isNontrivial (actualOccurrenceEquiv k).1
    exact (heightRefinement_pairWeight_strip hk.2.1 hk.2.2).1
  have hzero : 0 < -phaseProfile (fun _ => 1) 1 (1 : ℕ → Circle) 0 := by
    simpa [phaseProfile, rightmostCoeff, phaseOrbit, actualCoeff_hasSum.tsum_eq, hsum.tsum_eq]
      using hsum.summable.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  have hcont : Continuous (fun s : ℝ =>
      Real.exp (-((1 : ℝ) - 1 / 2) * s) * max (-phaseProfile (fun _ => 1) 1 (1 : ℕ → Circle) (-s)) 0) :=
    constant_density_continuous.comp (continuous_const.prodMk continuous_id)
  unfold phaseWindow
  refine intervalIntegral.integral_pos zero_lt_one hcont.continuousOn
    (fun s _ => mul_nonneg (Real.exp_nonneg _) (le_max_right _ _)) ⟨0, by simp, ?_⟩
  exact mul_pos (Real.exp_pos _) (by simpa only [neg_zero] using hzero.trans_le (le_max_left _ _))

theorem constant_window_le_infinite (h : ℕ → Circle) :
    phaseWindow (fun _ => 1) 1 1 h ≤ phaseWindowInfinite (fun _ => 1) 1 h := by
  let term (s : ℝ) (k : ℕ) :=
    actualCoeff k * (h k : ℂ) * (phaseOrbit (-s) k : ℂ)
  let series (s : ℝ) := ∑' k : ℕ, term s k
  let f (s : ℝ) := Real.exp (-((1 : ℝ) - 1 / 2) * s) * max (series s).re 0
  let C := ∑' k : ℕ, ‖actualCoeff k‖
  have hcoeff := actualCoeff_hasSum.summable.norm
  have hterm (s : ℝ) (k : ℕ) : ‖term s k‖ = ‖actualCoeff k‖ := by
    simp [term]
  have hseries (s : ℝ) : (series s).re ≤ C := by
    have hs : Summable (fun k => ‖term s k‖) := by simpa only [hterm] using hcoeff
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
      ((norm_tsum_le_tsum_norm hs).trans_eq (tsum_congr (hterm s))))
  have heq (s : ℝ) : -phaseProfile (fun _ => 1) 1 h (-s) = (series s).re := by
    simp [phaseProfile, rightmostCoeff, series, term]
  have hcont : Continuous f := by
    have hc := constant_density_continuous.comp
      (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (h, s))
    simpa only [Function.comp_def, heq, f] using hc
  have hnonneg (s : ℝ) : 0 ≤ f s := mul_nonneg (Real.exp_nonneg _) (le_max_right _ _)
  have hint (a : ℝ) : IntegrableOn f (Ioi a) := by
    have hmajor := (integrableOn_exp_mul_Ioi (by norm_num : -((1 : ℝ) - 1 / 2) < 0) a).const_mul C
    refine hmajor.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [Real.norm_of_nonneg (hnonneg s), mul_comm C]
    exact mul_le_mul_of_nonneg_left
      (max_le (hseries s) (tsum_nonneg fun _ => norm_nonneg _)) (Real.exp_nonneg _)
  change (∫ s in (0 : ℝ)..1,
    Real.exp (-(1 - 1 / 2) * s) * max (-phaseProfile (fun _ => 1) 1 h (-s)) 0) ≤
      ∫ s in Ioi (0 : ℝ), Real.exp (-(1 - 1 / 2) * s) * max (-phaseProfile (fun _ => 1) 1 h (-s)) 0
  simp_rw [heq]
  change (∫ s in (0 : ℝ)..1, f s) ≤ ∫ s in Ioi (0 : ℝ), f s
  rw [← intervalIntegral.integral_interval_add_Ioi (hint 0) (hint 1)]
  exact le_add_of_nonneg_right (integral_nonneg hnonneg)

theorem one_mem_phase_hull : (1 : ℕ → Circle) ∈ closure (range phaseOrbit) := by
  refine subset_closure ⟨0, ?_⟩
  funext k
  simp [phaseOrbit]

private theorem constant_one_fails : ¬ arena.Law constantOne := by
  intro law
  let A (_ : ℝ) : ℝ := 2
  have hA : ∀ᶠ B in atTop, 2 ≤ A B ∧ A B ≤ B :=
    (eventually_ge_atTop (2 : ℝ)).mono fun _ h => ⟨le_rfl, h⟩
  have hgrow : Tendsto (fun B => Real.log (B / A B)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  let y := phaseWindowInfinite (fun _ => 1) 1 (1 : ℕ → Circle)
  have hcluster := (law 1 (by norm_num) (fun _ _ => le_rfl) A hA hgrow y).2
    ⟨1, one_mem_phase_hull, rfl⟩
  obtain ⟨h, _, hy⟩ := (prime_tail_growing_width_cluster_iff_of_upper_bound 1
    (by norm_num) (fun _ hz => hz.2.2.le) A hA hgrow y).1 hcluster
  rw [actual_window_at_one h] at hy
  exact (ne_of_gt
    (constant_window_finite_positive.trans_le (constant_window_le_infinite 1))) hy

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family :
    Registration arena (type_of% @prime_tail_growing_width_cluster_iff_of_upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨prime_tail_growing_width_cluster_iff_of_upper_bound, constantOne, constant_one_fails⟩
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

def extentArena : Arena where
  signature := signature
  Law V := ∀ (β : ℝ),
    let realPart := V.readout () ()
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    ∃ K ≥ 0, ∀ ε > 0, ∀ᶠ B : ℝ in atTop, ∀ a ∈ Icc 2 B,
      let p := β - 1 / 2
      let error := (∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ p -
        phaseWindowInfinite realPart β (phaseOrbit (Real.log B))
      |error| ≤ ε + K * (a / B) ^ p ∧ error ≤ ε

private theorem constant_one_fails_extent : ¬ extentArena.Law constantOne := by
  intro law
  obtain ⟨K, _, hbad⟩ := law 1 (by norm_num) (fun _ _ => le_rfl)
  obtain ⟨_, _, hactual⟩ := prime_tail_window_extent_bound_of_upper_bound 1
    (by norm_num) (fun _ hz => hz.2.2.le)
  let g := phaseWindow (fun _ => 1) 1 1
  let q := g (1 : ℕ → Circle)
  have hq : 0 < q := constant_window_finite_positive
  have hε : 0 < q / 4 := by positivity
  let p : ℝ := 1 - 1 / 2
  have hp : 0 < p := by norm_num [p]
  have hdecay : Tendsto (fun B : ℝ => K * (2 / B) ^ p) atTop (𝓝 0) := by
    refine ((tendsto_rpow_atTop hp).const_div_atTop (K * (2 : ℝ) ^ p)).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    rw [Real.div_rpow (by norm_num) hB, mul_div_assoc]
  have hle : ∀ᶠ B : ℝ in atTop, g (phaseOrbit (Real.log B)) ∈ Iic (3 * (q / 4)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hactual (q / 4) hε, hbad (q / 4) hε,
      hdecay.eventually_lt_const hε] with B hB htrue hfalse hsmall
    have hleft : (2 : ℝ) ∈ Icc 2 B := ⟨le_rfl, hB⟩
    have htrue' := (htrue 2 hleft).2
    have hfalse' := neg_le_of_abs_le (hfalse 2 hleft).1
    have hminor := constant_window_le_infinite (phaseOrbit (Real.log B))
    change (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ p -
      phaseWindowInfinite Complex.re 1 (phaseOrbit (Real.log B)) ≤ q / 4 at htrue'
    rw [actual_window_at_one, sub_zero] at htrue'
    change -(q / 4 + K * (2 / B) ^ p) ≤
      (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ p -
        phaseWindowInfinite (fun _ => 1) 1 (phaseOrbit (Real.log B)) at hfalse'
    change g (phaseOrbit (Real.log B)) ≤ _ at hminor ⊢
    linarith only [htrue', hfalse', hminor, hsmall]
  have hc := ((phaseOrbit_cluster_iff 1).mpr one_mem_phase_hull).continuousAt_comp
    constant_window_continuous.continuousAt
  have hlog : MapClusterPt q atTop (g ∘ phaseOrbit ∘ Real.log) := by
    apply MapClusterPt.of_comp Real.tendsto_exp_atTop
    apply hc.congrFun
    exact Eventually.of_forall fun t => by simp only [g, Function.comp_def, Real.log_exp]
  have hclosed : q ∈ Iic (3 * (q / 4)) := isClosed_Iic.mem_of_mapClusterPt hlog hle
  change q ≤ 3 * (q / 4) at hclosed
  linarith only [hq, hclosed]

def extentFamily :
    Registration extentArena (type_of% @prime_tail_window_extent_bound_of_upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨prime_tail_window_extent_bound_of_upper_bound, constantOne, constant_one_fails_extent⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    extentArena.Law actual constantOne constant_one_fails_extent
  dependence := actual_dependence

def extentRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_window_extent_bound_of_upper_bound) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_window_extent_bound_of_upper_bound "__information_unit"
  realizationName := ``extentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨extentArena⟩
  objectArena := .source ⟨extentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source extentArena ⟨extentFamily⟩
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
