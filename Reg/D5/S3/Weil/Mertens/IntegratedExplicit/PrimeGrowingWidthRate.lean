import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthRate
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster

/-! A constant real-part observation selects every occurrence and makes the gap
premises automatic. The resulting phase prediction overestimates the actual
mass along returns to the identity phase. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthRate
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualData)
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthRate

open PrimeGrowingWidthCluster (signature actual constantOne actual_window_at_one
  constant_window_continuous constant_window_finite_positive constant_window_le_infinite
  one_mem_phase_hull)

def arena : Arena where
  signature := signature
  Law V := ∀ (ρ : ℂ), IsNontrivialZero ρ →
    let realPart := V.readout () ()
    let β := realPart ρ
    1 / 2 < β →
    (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    (∀ z : ℂ, IsNontrivialZero z → realPart z < β → realPart z ≤ 1 / 2) →
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B₀ : ℝ, ∀ B ≥ B₀,
      let error := (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) -
        B ^ (β - 1 / 2) * phaseWindowInfinite realPart β (phaseOrbit (Real.log B))
      c * Real.log B ≤ error ∧ error ≤ C * Real.log B

private theorem frequently_negative_error_at_one :
    ∃ m > (0 : ℝ), ∃ᶠ B : ℝ in atTop, 2 ≤ B ∧
      (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ ((1 : ℝ) - 1 / 2) -
        phaseWindowInfinite (fun _ => 1) 1 (phaseOrbit (Real.log B)) < -m := by
  let m := phaseWindow (fun _ => 1) 1 1 (1 : ℕ → Circle) / 2
  have hm : 0 < m := half_pos constant_window_finite_positive
  have hfreq : ∃ᶠ t : ℝ in atTop, m < phaseWindow (fun _ => 1) 1 1 (phaseOrbit t) := by
    have hrec := ((phaseOrbit_cluster_iff (1 : ℕ → Circle)).2 one_mem_phase_hull
      ).continuousAt_comp constant_window_continuous.continuousAt
    exact hrec.frequently (lt_mem_nhds (half_lt_self constant_window_finite_positive))
  obtain ⟨_, _, hmass⟩ := prime_tail_window_extent_bound_of_upper_bound 1
    (by norm_num) (fun _ hz => hz.2.2.le)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hmass (m / 2) (half_pos hm))
  refine ⟨m / 2, half_pos hm, frequently_atTop.mpr fun X => ?_⟩
  let Y := max 2 (max A X)
  have hY : 0 < Y := (by norm_num : (0 : ℝ) < 2).trans_le (le_max_left _ _)
  obtain ⟨t, ht, hphase⟩ := frequently_atTop.mp hfreq (Real.log Y)
  let B := Real.exp t
  have hyB : Y ≤ B := by
    rw [← Real.exp_log hY]
    exact Real.exp_le_exp.mpr ht
  have h2B : 2 ≤ B := (le_max_left _ _).trans hyB
  have hBA : A ≤ B := ((le_max_left A X).trans (le_max_right 2 _)).trans hyB
  have hBX : X ≤ B := ((le_max_right A X).trans (le_max_right 2 _)).trans hyB
  have hupper := (hA B hBA 2 ⟨le_rfl, h2B⟩).2
  rw [actual_window_at_one, sub_zero] at hupper
  have hstrict := hphase.trans_le (constant_window_le_infinite (phaseOrbit t))
  refine ⟨B, hBX, h2B, ?_⟩
  rw [show Real.log B = t from Real.log_exp t]
  linarith only [hupper, hstrict]

private theorem constant_one_fails : ¬ arena.Law constantOne := by
  intro law
  have hex := law (actualData.zero 0) (actualData.zero_isNontrivial 0)
  change ((1 / 2 : ℝ) < 1 → (∀ z : ℂ, IsNontrivialZero z → (1 : ℝ) ≤ 1) →
      (∀ z : ℂ, IsNontrivialZero z → (1 : ℝ) < 1 → (1 : ℝ) ≤ 1 / 2) → _) at hex
  obtain ⟨c, hc, _, _, B₀, hB₀⟩ :=
    hex (by norm_num) (fun _ _ => le_rfl) (fun _ _ h => (lt_irrefl _ h).elim)
  obtain ⟨m, hm, hfreq⟩ := frequently_negative_error_at_one
  obtain ⟨B, hB, h2B, hsmall⟩ := frequently_atTop.mp hfreq B₀
  have hlower := (hB₀ B hB).1
  change c * Real.log B ≤ (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) -
    B ^ ((1 : ℝ) - 1 / 2) * phaseWindowInfinite (fun _ => 1) 1 (phaseOrbit (Real.log B)) at hlower
  have hpow : 0 < B ^ ((1 : ℝ) - 1 / 2) :=
    Real.rpow_pos_of_pos ((by norm_num : (0 : ℝ) < 2).trans_le h2B) _
  have hstrict : (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) <
      B ^ ((1 : ℝ) - 1 / 2) * phaseWindowInfinite (fun _ => 1) 1 (phaseOrbit (Real.log B)) := by
    rw [mul_comm]
    exact (div_lt_iff₀ hpow).1 (sub_neg.mp (hsmall.trans (neg_neg_of_pos hm)))
  have hnonneg : 0 ≤ c * Real.log B :=
    mul_nonneg hc.le (Real.log_nonneg (one_le_two.trans h2B))
  linarith only [hlower, hstrict, hnonneg]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena (type_of% @prime_tail_cumulative_error_log_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_cumulative_error_log_order, constantOne, constant_one_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual constantOne constant_one_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_cumulative_error_log_order) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_cumulative_error_log_order "__information_unit"
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
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthRate
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

def upperArena : Arena where
  signature := signature
  Law V := ∀ (β γ : ℝ),
    let realPart := V.readout () ()
    1 / 2 ≤ γ → γ < β →
    (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    (∀ z : ℂ, IsNontrivialZero z → realPart z < β → realPart z ≤ γ) →
    ∃ K > (0 : ℝ), ∀ B : ℝ, ∀ a ∈ Icc 2 B,
      let p := β - 1 / 2
      let r := γ - 1 / 2
      let error := (∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ p -
        phaseWindowInfinite realPart β (phaseOrbit (Real.log B))
      |error| ≤ K * ((a / B) ^ p +
        if γ = 1 / 2 then B ^ (-p) * Real.log (B / a) else (B ^ r - a ^ r) / B ^ p)

private theorem constant_one_upper_fails : ¬ upperArena.Law constantOne := by
  intro law
  obtain ⟨K, hK₀, hK⟩ :=
    law 1 (3 / 4) (by norm_num) (by norm_num) (fun _ _ => le_rfl)
      (fun _ _ h => (lt_irrefl _ h).elim)
  let p : ℝ := 1 - 1 / 2
  let r : ℝ := 3 / 4 - 1 / 2
  have hp : 0 < p := by norm_num [p]
  have hdecay : Tendsto (fun B : ℝ => K * ((2 / B) ^ p + B ^ ((3 : ℝ) / 4 - 1)))
      atTop (𝓝 0) := by
    have hleft : Tendsto (fun B : ℝ => (2 / B) ^ p) atTop (𝓝 0) := by
      have hquotient : Tendsto (fun B : ℝ => (2 : ℝ) ^ p / B ^ p) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hp)
      apply hquotient.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hB]
    have hright : Tendsto (fun B : ℝ => B ^ ((3 : ℝ) / 4 - 1)) atTop (𝓝 0) := by
      simpa only [neg_sub] using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 - 3 / 4)
    simpa only [add_zero, mul_zero] using (hleft.add hright).const_mul K
  obtain ⟨m, hm, hfreq⟩ := frequently_negative_error_at_one
  obtain ⟨B, ⟨h2B, hnegative⟩, hsmall⟩ :=
    (hfreq.and_eventually (hdecay.eventually_lt_const hm)).exists
  have h := hK B 2 ⟨le_rfl, h2B⟩
  dsimp only at h
  rw [ite_eq_right (by norm_num : (3 : ℝ) / 4 ≠ 1 / 2)] at h
  change |(∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ p -
      phaseWindowInfinite (fun _ => 1) 1 (phaseOrbit (Real.log B))| ≤
    K * ((2 / B) ^ p + (B ^ r - (2 : ℝ) ^ r) / B ^ p) at h
  have hB₀ : 0 < B := (by norm_num : (0 : ℝ) < 2).trans_le h2B
  have hrate : (B ^ r - (2 : ℝ) ^ r) / B ^ p ≤ B ^ ((3 : ℝ) / 4 - 1) := by
    calc
      _ ≤ B ^ r / B ^ p := div_le_div_of_nonneg_right
        (sub_le_self _ (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hB₀.le _)
      _ = _ := by
        rw [← Real.rpow_sub hB₀, show r - p = (3 : ℝ) / 4 - 1 by norm_num [r, p]]
  have hupper := h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hrate) hK₀.le)
  linarith only [(abs_le.mp hupper).1, hnegative, hsmall]

def upperFamily :
    Registration upperArena (type_of% @prime_tail_window_error_of_lower_spectral_bound) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨prime_tail_window_error_of_lower_spectral_bound, constantOne, constant_one_upper_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    upperArena.Law actual constantOne constant_one_upper_fails
  dependence := actual_dependence

def upperRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_window_error_of_lower_spectral_bound) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_window_error_of_lower_spectral_bound "__information_unit"
  realizationName := ``upperFamily
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena⟩
  objectArena := .source ⟨upperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena ⟨upperFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Complex.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthRate
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

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthRate
