import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.RobinCenteredChord
import Reg.Support.SingleDependentReadout

/-! The centered Robin chord and its weighted mass as observations of the coordinate,
ramp, and Chebyshev kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance (activationDensity)
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Weil.Mertens.RobinWeightedRamp (R u)
open _root_.D5.S3.Weil.Mertens.RobinCenteredChord
open _root_.D5.S3.Weil.Mertens.WeightedTailInverse renaming a → inverseWeight
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (r weightedTail)
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)

namespace Reg.D5.S3.Weil.Mertens.RobinCenteredChord

abbrev scalarSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

abbrev massSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ → ℝ)

private def scalar (f : ℝ → ℝ) : Realization scalarSignature :=
  realize scalarSignature (fun _ _ => f) (fun e => nomatch e)

private def mass (f : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Realization massSignature :=
  realize massSignature (fun _ _ => f) (fun e => nomatch e)

def balanceArena : Arena where
  signature := scalarSignature
  Law V := ∀ {a b x p q : ℝ}, 1 < a → x ∈ Icc a b →
    p + q = 1 → p * u a + q * u b = u x →
    let C := p * (u x - u a) / u x
    p * u a * (∫ t in a..x, activationDensity t) = C ∧
      q * u b * (∫ t in x..b, activationDensity t) = C ∧
        q * (V.readout () () b - u x) / u x = C

def transferArena : Arena where
  signature := scalarSignature
  Law V := ∀ {a b x p q : ℝ}, 2 ≤ a → x ∈ Icc a b →
    p + q = 1 → p * u a + q * u b = u x → ∀ m : ℝ,
    V.readout () () x - p * R a - q * R b =
      p * u a * (∫ t in a..x, (Chebyshev.psi t - t - m) * activationDensity t) -
        q * u b * (∫ t in x..b, (Chebyshev.psi t - t - m) * activationDensity t)

def errorArena : Arena where
  signature := scalarSignature
  Law V := ∀ {a b x p q L U : ℝ}, 2 ≤ a → x ∈ Icc a b →
    0 ≤ p → 0 ≤ q → p + q = 1 → p * u a + q * u b = u x →
    (∀ t ∈ Icc a b, L ≤ Chebyshev.psi t - t ∧ Chebyshev.psi t - t ≤ U) →
    |V.readout () () x - p * R a - q * R b| ≤ (U - L) * (p * (u x - u a) / u x)

def coefficientArena : Arena where
  signature := scalarSignature
  Law V := ∀ {a b x p q : ℝ}, 1 < a → a < b → x ∈ Icc a b →
    p + q = 1 → p * u a + q * u b = u x →
    let C := p * (u x - u a) / u x
    C = (u x - u a) * (u b - u x) / (u x * (u b - u a)) ∧
      C ≤ (V.readout () () b - u a) / (4 * u a)

def massArena : Arena where
  signature := massSignature
  Law V := ∀ {a b L U : ℝ}, exp 1 ≤ a → a < b → b ≤ 2 * a →
    (∀ t ∈ Icc a b, L ≤ Chebyshev.psi t - t ∧ Chebyshev.psi t - t ≤ U) →
    let q (t : ℝ) := (u t - u a) / (u b - u a)
    let H (t : ℝ) := (1 - q t) * R a + q t * R b
    |V.readout () () psiErrorKernel a b -
        (∫ t in a..b, (log t / (1 + log t)) / (t * sqrt t) * max (H t) 0)| ≤
      3 * (U - L) * (b - a) ^ 2 / (4 * a ^ 2 * sqrt a)

private lemma u_two_pos : 0 < u 2 := by
  unfold u
  positivity

private lemma coordinate_dependence : ObservationalDependence scalarSignature (scalar u) := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change u 1 ≠ u 2
  simpa [u, log_one] using u_two_pos.ne'

private lemma ramp_dependence : ObservationalDependence scalarSignature (scalar R) := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change R 0 ≠ R 1
  norm_num [R, u]

private lemma singleton_range :
    ∀ t ∈ Icc (2 : ℝ) 2, Chebyshev.psi 2 - 2 ≤ Chebyshev.psi t - t ∧
      Chebyshev.psi t - t ≤ Chebyshev.psi 2 - 2 := by
  intro t ht
  obtain rfl : t = 2 := le_antisymm ht.2 ht.1
  exact ⟨le_rfl, le_rfl⟩

private lemma balance_rejected :
    ¬ balanceArena.Law (scalar (fun t => u t + 1)) := by
  intro law
  have h := (law (a := 2) (b := 2) (x := 2) (p := 0) (q := 1)
    (by norm_num) ⟨le_rfl, le_rfl⟩ (by norm_num) (by simp)).2.2
  change 1 * (u 2 + 1 - u 2) / u 2 = 0 * (u 2 - u 2) / u 2 at h
  have hn : 0 < (1 : ℝ) / u 2 := one_div_pos.mpr u_two_pos
  have he : (1 : ℝ) / u 2 = 0 := by simpa using h
  exact hn.ne' he

private lemma transfer_rejected :
    ¬ transferArena.Law (scalar (fun t => R t + 1)) := by
  intro law
  have h := law (a := 2) (b := 2) (x := 2) (p := 1) (q := 0)
    le_rfl ⟨le_rfl, le_rfl⟩ (by norm_num) (by simp) 0
  change R 2 + 1 - 1 * R 2 - 0 * R 2 =
    1 * u 2 * (∫ t in (2 : ℝ)..2, (Chebyshev.psi t - t - 0) * activationDensity t) -
      0 * u 2 * (∫ t in (2 : ℝ)..2, (Chebyshev.psi t - t - 0) * activationDensity t) at h
  simp at h

private lemma error_rejected :
    ¬ errorArena.Law (scalar (fun t => R t + 1)) := by
  intro law
  have h := law (a := 2) (b := 2) (x := 2) (p := 1) (q := 0)
    le_rfl ⟨le_rfl, le_rfl⟩ (by norm_num) le_rfl (by norm_num) (by simp) singleton_range
  change |R 2 + 1 - 1 * R 2 - 0 * R 2| ≤
    (Chebyshev.psi 2 - 2 - (Chebyshev.psi 2 - 2)) * (1 * (u 2 - u 2) / u 2) at h
  norm_num at h

private lemma coefficient_rejected :
    ¬ coefficientArena.Law (scalar (fun _ => u 2 - 1)) := by
  intro law
  have h := (law (a := 2) (b := 3) (x := 2) (p := 1) (q := 0)
    (by norm_num) (by norm_num) ⟨le_rfl, by norm_num⟩ (by norm_num) (by simp)).2
  change 1 * (u 2 - u 2) / u 2 ≤ (u 2 - 1 - u 2) / (4 * u 2) at h
  have hneg : (u 2 - 1 - u 2) / (4 * u 2) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity [u_two_pos])
  exact hneg.not_ge (by simpa only [sub_self, mul_zero, zero_div] using h)

private def massTestKernel (t : ℝ) : ℝ := -exp (-t) / r t

private lemma mass_test_tail {t : ℝ} (ht : 1 < t) :
    weightedTail massTestKernel t = -exp (-t) := by
  have he : (∫ z in Ioi t, exp (-z)) = exp (-t) := by
    simpa only [neg_one_mul, neg_div_neg_eq, div_one, one_mul] using
      integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) t
  unfold weightedTail
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun z => -exp (-z))]
  · rw [integral_neg, he]
  · intro z hz
    have hlog := log_pos (ht.trans (mem_Ioi.mp hz))
    exact div_mul_cancel₀ _ (by unfold r; positivity)

private lemma mass_test_pos : 0 < weightedNegativeMass massTestKernel 3 4 := by
  let f (t : ℝ) := (inverseWeight t / sqrt t) * exp (-t)
  have hf : EqOn (fun t => (inverseWeight t / sqrt t) *
      max (-weightedTail massTestKernel t) 0) f (uIcc 3 4) := by
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)]
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) ht.1
    simp [f, mass_test_tail ht1, (exp_pos (-t)).le]
  have hc : ContinuousOn f (Icc 3 4) := by
    have hlog : ContinuousOn log (Icc 3 4) := fun t ht =>
      (continuousAt_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) ht.1).ne').continuousWithinAt
    have hden (t : ℝ) (ht : t ∈ Icc 3 4) : 1 + log t ≠ 0 := by
      have hlogpos := log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) ht.1)
      positivity
    have hsqrt (t : ℝ) (ht : t ∈ Icc 3 4) : sqrt t ≠ 0 :=
      (sqrt_pos.2 (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) ht.1)).ne'
    exact (((hlog.pow 2).div (hlog.const_add 1) hden).div
      continuous_sqrt.continuousOn hsqrt).mul (continuous_exp.comp continuous_neg).continuousOn
  unfold weightedNegativeMass
  rw [intervalIntegral.integral_congr hf]
  have hpos (t : ℝ) (ht : 3 ≤ t) : 0 < f t := by
    have hlogpos := log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) ht)
    have ht0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) ht
    unfold f inverseWeight
    positivity
  exact intervalIntegral.integral_pos (by norm_num) hc
    (fun t ht => (hpos t ht.1.le).le) ⟨3, ⟨le_rfl, by norm_num⟩, hpos 3 le_rfl⟩

private lemma mass_dependence :
    ObservationalDependence massSignature (mass weightedNegativeMass) := by
  intro _
  refine ⟨(), (fun _ => 0), massTestKernel, ?_⟩
  intro he
  have h := congrFun (congrFun he 3) 4
  change weightedNegativeMass (fun _ => 0) 3 4 = weightedNegativeMass massTestKernel 3 4 at h
  have hz : weightedNegativeMass (fun _ => 0) 3 4 = 0 := by
    simp [weightedNegativeMass, weightedTail]
  exact mass_test_pos.ne' (h.symm.trans hz)

private def lower : ℝ := Chebyshev.psi 3 - 4
private def upper : ℝ := Chebyshev.psi 4 - 3

private lemma cell_range :
    ∀ t ∈ Icc (3 : ℝ) 4, lower ≤ Chebyshev.psi t - t ∧ Chebyshev.psi t - t ≤ upper := by
  intro t ht
  exact ⟨sub_le_sub (Chebyshev.psi_mono ht.1) ht.2,
    sub_le_sub (Chebyshev.psi_mono ht.2) ht.1⟩

private def cellBound : ℝ :=
  3 * (upper - lower) * (4 - 3) ^ 2 / (4 * (3 : ℝ) ^ 2 * sqrt 3)

private def shiftedMass : (ℝ → ℝ) → ℝ → ℝ → ℝ :=
  fun k a b => weightedNegativeMass k a b + (2 * cellBound + 1)

private lemma mass_rejected : ¬ massArena.Law (mass shiftedMass) := by
  intro law
  have hbad := law (a := 3) (b := 4) exp_one_lt_three.le (by norm_num) (by norm_num) cell_range
  have hgood := abs_mass_sub_chord_le (a := 3) (b := 4)
    exp_one_lt_three.le (by norm_num) (by norm_num) cell_range
  dsimp only at hbad hgood
  rw [abs_le] at hbad hgood
  change _ ∧ shiftedMass psiErrorKernel 3 4 - _ ≤ cellBound at hbad
  change -cellBound ≤ weightedNegativeMass psiErrorKernel 3 4 - _ ∧ _ at hgood
  unfold shiftedMass at hbad
  linarith only [hbad.2, hgood.1]

def balanceEvidence : Registration balanceArena (type_of% @chord_weight_balance) where
  actual := realize scalarSignature (fun _ _ => u) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@chord_weight_balance, scalar (fun t => u t + 1), balance_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    balanceArena.Law (scalar u) (scalar (fun t => u t + 1)) balance_rejected
  dependence := coordinate_dependence

def balanceAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chord_weight_balance) (Realization scalarSignature) Unit Unit where
  unitName := .str ``chord_weight_balance "__information_unit"
  realizationName := ``balanceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨balanceArena⟩
  objectArena := .source ⟨balanceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source balanceArena ⟨balanceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ => u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinCenteredChord
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def transferEvidence : Registration transferArena (type_of% @ramp_chord_centered) where
  actual := realize scalarSignature (fun _ _ => R) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@ramp_chord_centered, scalar (fun t => R t + 1), transfer_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    transferArena.Law (scalar R) (scalar (fun t => R t + 1)) transfer_rejected
  dependence := ramp_dependence

def transferAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ramp_chord_centered) (Realization scalarSignature) Unit Unit where
  unitName := .str ``ramp_chord_centered "__information_unit"
  realizationName := ``transferEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨transferArena⟩
  objectArena := .source ⟨transferArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transferArena ⟨transferEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ => R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinCenteredChord
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def errorEvidence : Registration errorArena (type_of% @abs_ramp_chord_error_le) where
  actual := realize scalarSignature (fun _ _ => R) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@abs_ramp_chord_error_le, scalar (fun t => R t + 1), error_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    errorArena.Law (scalar R) (scalar (fun t => R t + 1)) error_rejected
  dependence := ramp_dependence

def errorAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_ramp_chord_error_le) (Realization scalarSignature) Unit Unit where
  unitName := .str ``abs_ramp_chord_error_le "__information_unit"
  realizationName := ``errorEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨errorArena⟩
  objectArena := .source ⟨errorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source errorArena ⟨errorEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ => R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinCenteredChord
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def coefficientEvidence : Registration coefficientArena (type_of% @chord_weight_coefficient) where
  actual := realize scalarSignature (fun _ _ => u) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@chord_weight_coefficient, scalar (fun _ => u 2 - 1), coefficient_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    coefficientArena.Law (scalar u) (scalar (fun _ => u 2 - 1)) coefficient_rejected
  dependence := coordinate_dependence

def coefficientAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chord_weight_coefficient) (Realization scalarSignature) Unit Unit where
  unitName := .str ``chord_weight_coefficient "__information_unit"
  realizationName := ``coefficientEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coefficientArena⟩
  objectArena := .source ⟨coefficientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coefficientArena ⟨coefficientEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ => u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinCenteredChord
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def massEvidence : Registration massArena (type_of% @abs_mass_sub_chord_le) where
  actual := realize massSignature (fun _ _ => weightedNegativeMass) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@abs_mass_sub_chord_le, mass shiftedMass, mass_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    massArena.Law (mass weightedNegativeMass) (mass shiftedMass) mass_rejected
  dependence := mass_dependence

def massAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_mass_sub_chord_le) (Realization massSignature) Unit Unit where
  unitName := .str ``abs_mass_sub_chord_le "__information_unit"
  realizationName := ``massEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨massArena⟩
  objectArena := .source ⟨massArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source massArena ⟨massEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => weightedNegativeMass) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinCenteredChord
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.RobinCenteredChord
