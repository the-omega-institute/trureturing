import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalTwoLines
import Reg.Support.SingleDependentReadout

/-! The line profile is a dependent observation. Replacing it by a constant
negative profile on the line at one makes both laws fail at the closed strip bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalTwoLines
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalTwoLines

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => (ℕ → Circle) → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => phaseProfile Complex.re) (fun e => nomatch e)

def negativeLineAtOne : Realization signature :=
  realize signature (fun _ _ α _ _ => if α = 1 then -1 else 0) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (actualZero 0).re, 2, fun h => ?_⟩
  have heval := congrFun (congrFun h (phaseOrbit 0)) 0
  change phaseProfile Complex.re (actualZero 0).re (phaseOrbit 0) 0 =
    phaseProfile Complex.re 2 (phaseOrbit 0) 0 at heval
  have htwo : phaseProfile Complex.re 2 (phaseOrbit 0) 0 = 0 := by
    have hk (k : ℕ) : (actualZero k).re ≠ 2 :=
      ((actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2.trans
        (by norm_num)).ne
    simp [phaseProfile, rightmostCoeff, hk]
  have hneg : phaseProfile Complex.re (actualZero 0).re (phaseOrbit 0) 0 < 0 := by
    have hs : Summable (fun k => rightmostCoeff Complex.re (actualZero 0).re k) :=
      actualCoeff_hasSum.summable.norm.of_norm_bounded (fun k => by
        unfold rightmostCoeff
        split_ifs <;> simp)
    have hpos (k : ℕ) : 0 < (actualCoeff k).re := by
      have hk := actualData.zero_isNontrivial (actualOccurrenceEquiv k).1
      exact (heightRefinement_pairWeight_strip hk.2.1 hk.2.2).1
    have hre := Complex.hasSum_re hs.hasSum
    have hsum : 0 < (∑' k : ℕ, (rightmostCoeff Complex.re (actualZero 0).re k).re) := by
      refine hre.summable.tsum_pos (fun k => ?_) 0 (by simpa [rightmostCoeff] using hpos 0)
      unfold rightmostCoeff
      split_ifs
      · exact (hpos k).le
      · simp
    simpa [phaseProfile, phaseOrbit, neg_lt_zero, hre.tsum_eq] using hsum
  exact hneg.ne (heval.trans htwo)

private theorem strip_upper_two (z : ℂ) (hz : IsNontrivialZero z) : z.re ≤ 2 :=
  hz.2.2.le.trans (by norm_num)

private theorem strip_upper_one (z : ℂ) (hz : IsNontrivialZero z) (_ : z.re < 2) :
    z.re ≤ 1 := hz.2.2.le

private theorem prime_tail_on_exp_tendsto_zero :
    Tendsto (fun t : ℝ => primeTail (Real.exp t)) atTop (𝓝 0) :=
  (tendsto_integral_Ioi_zero tendsto_id).comp Real.tendsto_exp_atTop

def approximationArena : Arena where
  signature := signature
  Law V := ∀ β γ : ℝ,
    let profile := V.readout () ()
    1 / 2 < γ → γ < β →
    (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
    (∀ z : ℂ, IsNontrivialZero z → z.re < β → z.re ≤ γ) →
    Tendsto (fun t : ℝ => Real.exp ((1 - γ) * t) * primeTail (Real.exp t) -
      Real.exp ((β - γ) * t) * profile β (phaseOrbit t) 0 - profile γ (phaseOrbit t) 0)
      atTop (𝓝 0)

private theorem negativeLineAtOne_fails_approximation :
    ¬ approximationArena.Law negativeLineAtOne := by
  intro law
  have hbad := law 2 1 (by norm_num) (by norm_num) strip_upper_two strip_upper_one
  change Tendsto (fun t : ℝ => Real.exp ((1 - 1) * t) * primeTail (Real.exp t) -
    Real.exp ((2 - 1) * t) * (if (2 : ℝ) = 1 then -1 else 0) -
    (if (1 : ℝ) = 1 then -1 else 0)) atTop (𝓝 0) at hbad
  norm_num at hbad
  have htrue := prime_tail_on_exp_tendsto_zero.add_const 1
  have heq : (0 : ℝ) = 1 := tendsto_nhds_unique hbad (by simpa only [zero_add] using htrue)
  norm_num at heq

def approximationFamily :
    Registration approximationArena (type_of% @prime_tail_two_line_approx) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_two_line_approx, negativeLineAtOne,
    negativeLineAtOne_fails_approximation⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    approximationArena.Law actual negativeLineAtOne negativeLineAtOne_fails_approximation
  dependence := actual_dependence

def approximationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_two_line_approx) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_two_line_approx "__information_unit"
  realizationName := ``approximationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨approximationArena⟩
  objectArena := .source ⟨approximationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source approximationArena ⟨approximationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => phaseProfile Complex.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalTwoLines
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def contactArena : Arena where
  signature := signature
  Law V := ∀ β γ W : ℝ,
    let profile := V.readout () ()
    0 < W → 1 / 2 < γ → γ < β →
    (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
    (∀ z : ℂ, IsNontrivialZero z → z.re < β → z.re ≤ γ) →
    ((∀ h ∈ closure (range phaseOrbit), ∃ s ∈ Icc (0 : ℝ) W, profile β h (-s) ≤ 0) ∨
      (∀ U > W, Filter.liminf (fun B : ℝ =>
        (∫ x in B * Real.exp (-U)..B, max (-primeTail x) 0 / Real.sqrt x) /
          B ^ (β - 1 / 2)) atTop ≠ 0)) →
    (∀ h ∈ closure (range phaseOrbit), ∀ s ∈ Icc (0 : ℝ) W,
      profile β h (-s) = 0 →
      (∀ v ∈ Icc (0 : ℝ) W, 0 ≤ profile β h (-v)) →
      profile γ h (-s) < 0) →
    ∃ c > 0, ∃ T : ℝ, ∀ t ≥ T,
      (∃ u ∈ Icc (t - W) t, Real.exp ((1 - γ) * u) * primeTail (Real.exp u) ≤ -c) ∧
      0 < ∫ x in Real.exp t * Real.exp (-W)..Real.exp t, max (-primeTail x) 0 / Real.sqrt x

private theorem negativeLineAtOne_fails_contact : ¬ contactArena.Law negativeLineAtOne := by
  intro law
  obtain ⟨c, hc, T, hT⟩ := law 2 1 1 (by norm_num) (by norm_num) (by norm_num)
    strip_upper_two strip_upper_one
    (Or.inl fun _ _ => ⟨0, by simp, by
      change (if (2 : ℝ) = 1 then -1 else 0) ≤ (0 : ℝ)
      norm_num⟩)
    (fun _ _ _ _ _ _ => by
      change (if (1 : ℝ) = 1 then -1 else 0) < (0 : ℝ)
      norm_num)
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (prime_tail_on_exp_tendsto_zero.eventually_const_lt (neg_lt_zero.mpr hc))
  obtain ⟨u, hu, htail⟩ := (hT (max T (S + 1)) (le_max_left _ _)).1
  have huS : S ≤ u :=
    (le_sub_iff_add_le.mpr (le_max_right T (S + 1))).trans hu.1
  norm_num at htail
  exact (hS u huS).not_ge htail

def contactFamily :
    Registration contactArena (type_of% @prime_tail_negative_windows_of_two_line_contact) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_negative_windows_of_two_line_contact, negativeLineAtOne,
    negativeLineAtOne_fails_contact⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    contactArena.Law actual negativeLineAtOne negativeLineAtOne_fails_contact
  dependence := actual_dependence

def contactRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_negative_windows_of_two_line_contact) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_negative_windows_of_two_line_contact "__information_unit"
  realizationName := ``contactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨contactArena⟩
  objectArena := .source ⟨contactArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source contactArena ⟨contactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => phaseProfile Complex.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalTwoLines
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalTwoLines
