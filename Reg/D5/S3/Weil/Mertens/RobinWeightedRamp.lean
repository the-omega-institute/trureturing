import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.RobinWeightedRamp
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! The Robin ramp and its positive endpoint samples as observations of real inputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set Finset LeanInformationAudit
open ArithmeticFunction (vonMangoldt)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass
  (weightedNegativeMass weightedNegativeMass_nonneg)
open _root_.D5.S3.Weil.Mertens.RobinWeightedRamp

namespace Reg.D5.S3.Weil.Mertens.RobinWeightedRamp

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

private def observe (f : ℝ → ℝ) : Realization signature :=
  realize signature (fun _ _ => f) (fun e => nomatch e)

private lemma ramp_zero : R 0 = 0 := by simp [R, u]
private lemma ramp_one : R 1 = 1 := by simp [R, u]

private lemma ramp_dependence : ObservationalDependence signature (observe R) := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change R 0 ≠ R 1
  rw [ramp_zero, ramp_one]
  exact zero_ne_one

private lemma sample_dependence :
    ObservationalDependence signature (observe (fun x => max (R x) 0)) := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change max (R 0) 0 ≠ max (R 1) 0
  rw [ramp_zero, ramp_one]
  norm_num

def tailArena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ}, 2 ≤ x →
    V.readout () () x = -u x * weightedTail psiErrorKernel x

def sumArena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ} {N : ℕ}, 2 ≤ x → ⌊x⌋₊ ≤ N →
    V.readout () () x = (∑ n ∈ Finset.Icc 2 N,
      vonMangoldt n * max (u x / u (n : ℝ) - 1) 0) -
      u x * (log (log x) + eulerMascheroniConstant) + x

private def shifted : Realization signature := observe (fun x => R x + 1)

private lemma tail_rejected : ¬ tailArena.Law shifted := by
  intro law
  have h := law (x := 2) le_rfl
  change R 2 + 1 = -u 2 * weightedTail psiErrorKernel 2 at h
  linarith [ramp_eq_neg_weightedTail (x := 2) le_rfl]

private lemma sum_rejected : ¬ sumArena.Law shifted := by
  intro law
  have hfloor : ⌊(2 : ℝ)⌋₊ ≤ (2 : ℕ) := by norm_num
  have h := law (x := 2) (N := 2) le_rfl hfloor
  change R 2 + 1 = _ at h
  linarith [ramp_eq_sum (x := 2) le_rfl hfloor]

def tailEvidence : Registration tailArena (type_of% @ramp_eq_neg_weightedTail) where
  actual := realize signature (fun _ _ => R) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@ramp_eq_neg_weightedTail, shifted, tail_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    tailArena.Law (observe R) shifted tail_rejected
  dependence := ramp_dependence

def sumEvidence : Registration sumArena (type_of% @ramp_eq_sum) where
  actual := realize signature (fun _ _ => R) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@ramp_eq_sum, shifted, sum_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sumArena.Law (observe R) shifted sum_rejected
  dependence := ramp_dependence

def chordArena : Arena where
  signature := signature
  Law V := ∀ {a b x p q : ℝ}, exp 1 ≤ a → a < b → b ≤ 2 * a → x ∈ Set.Icc a b →
    0 ≤ p → 0 ≤ q → p + q = 1 → p * u a + q * u b = u x →
    V.readout () () x ≤ p * R a + q * R b + 3 * (b - a) ^ 2 / a

private def raisedInterior : Realization signature :=
  observe (fun _ => max (R 3) 0 + max (R 5) 0 + 5)

private lemma chord_rejected : ¬ chordArena.Law raisedInterior := by
  intro law
  have hmono : StrictMonoOn u (Set.Ici (exp (-1))) := Real.mul_log_strictMonoOn
  have hbase : exp (-1 : ℝ) ≤ 1 := by simp
  have h3 : (3 : ℝ) ∈ Set.Ici (exp (-1)) := hbase.trans (by norm_num)
  have h4 : (4 : ℝ) ∈ Set.Ici (exp (-1)) := hbase.trans (by norm_num)
  have h5 : (5 : ℝ) ∈ Set.Ici (exp (-1)) := hbase.trans (by norm_num)
  have h34 : u 3 < u 4 := hmono h3 h4 (by norm_num)
  have h45 : u 4 < u 5 := hmono h4 h5 (by norm_num)
  have hgap := sub_pos.mpr (h34.trans h45)
  let q := (u 4 - u 3) / (u 5 - u 3)
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr h34.le) hgap.le
  have hp : 0 ≤ 1 - q := sub_nonneg.mpr ((div_le_one hgap).2 (by linarith))
  have hcoord : (1 - q) * u 3 + q * u 5 = u 4 := by
    have h := div_mul_cancel₀ (u 4 - u 3) hgap.ne'
    change q * (u 5 - u 3) = u 4 - u 3 at h
    linarith only [h]
  have h := law (a := 3) (b := 5) (x := 4) (p := 1 - q) (q := q)
    exp_one_lt_three.le (by norm_num) (by norm_num) (by norm_num [Set.mem_Icc])
      hp hq (sub_add_cancel _ _) hcoord
  change max (R 3) 0 + max (R 5) 0 + 5 ≤ (1 - q) * R 3 + q * R 5 +
    3 * (5 - 3) ^ 2 / 3 at h
  have hleft : (1 - q) * R 3 ≤ max (R 3) 0 := by
    calc
      _ ≤ (1 - q) * max (R 3) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hp
      _ ≤ _ := mul_le_of_le_one_left (le_max_right _ _) (by linarith)
  have hright : q * R 5 ≤ max (R 5) 0 := by
    calc
      _ ≤ q * max (R 5) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hq
      _ ≤ _ := mul_le_of_le_one_left (le_max_right _ _) (by linarith)
  linarith only [h, hleft, hright]

def chordEvidence : Registration chordArena (type_of% @ramp_chord) where
  actual := realize signature (fun _ _ => R) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@ramp_chord, raisedInterior, chord_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    chordArena.Law (observe R) raisedInterior chord_rejected
  dependence := ramp_dependence

def cellArena : Arena where
  signature := signature
  Law V := ∀ {a b c d : ℝ}, exp 1 ≤ a → a < b → b ≤ 2 * a → a ≤ c → c ≤ d → d ≤ b →
    weightedNegativeMass psiErrorKernel c d ≤
      (d - c) / (a * sqrt a) *
        (V.readout () () a + max (R b) 0 + 3 * (b - a) ^ 2 / a)

def quarticArena : Arena where
  signature := signature
  Law V := ∀ {n : ℕ}, 6 ≤ n → ∀ {c d : ℝ},
    (n : ℝ) ^ 4 ≤ c → c ≤ d → d ≤ ((n : ℝ) + 1) ^ 4 →
    weightedNegativeMass psiErrorKernel c d ≤ (d - c) / (n : ℝ) ^ 4 *
      ((V.readout () () ((n : ℝ) ^ 4) + max (R (((n : ℝ) + 1) ^ 4)) 0) /
        (n : ℝ) ^ 2 + 675)

private def negativeSample (right : ℝ) : Realization signature :=
  observe (fun _ => -max (R right) 0 - 25000)

private lemma cell_rejected : ¬ cellArena.Law (negativeSample 4) := by
  intro law
  have h := law (a := 3) (b := 4) (c := 3) (d := 4)
    exp_one_lt_three.le (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl
  change weightedNegativeMass psiErrorKernel 3 4 ≤
    (4 - 3) / (3 * sqrt 3) * (-max (R 4) 0 - 25000 + max (R 4) 0 +
      3 * (4 - 3) ^ 2 / 3) at h
  have hneg : -max (R 4) 0 - 25000 + max (R 4) 0 + 3 * (4 - 3) ^ 2 / 3 < 0 := by
    linarith
  exact (mul_neg_of_pos_of_neg (by positivity) hneg).not_ge
    ((weightedNegativeMass_nonneg (by norm_num) (by norm_num)).trans h)

private lemma quartic_rejected : ¬ quarticArena.Law (negativeSample (((6 : ℝ) + 1) ^ 4)) := by
  intro law
  have h := law (n := 6) (c := 1296) (d := 2401)
    le_rfl (by norm_num) (by norm_num) (by norm_num)
  change weightedNegativeMass psiErrorKernel 1296 2401 ≤
    (2401 - 1296) / (6 : ℝ) ^ 4 *
      ((-max (R (((6 : ℝ) + 1) ^ 4)) 0 - 25000 + max (R (((6 : ℝ) + 1) ^ 4)) 0) /
        (6 : ℝ) ^ 2 + 675) at h
  have hneg : (-max (R (((6 : ℝ) + 1) ^ 4)) 0 - 25000 + max (R (((6 : ℝ) + 1) ^ 4)) 0) /
      (6 : ℝ) ^ 2 + 675 < 0 := by linarith
  exact (mul_neg_of_pos_of_neg (by positivity) hneg).not_ge
    ((weightedNegativeMass_nonneg (by norm_num) (by norm_num)).trans h)

def cellEvidence : Registration cellArena (type_of% @mass_le_of_cell) where
  actual := realize signature (fun _ _ x => max (R x) 0) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@mass_le_of_cell, negativeSample 4, cell_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    cellArena.Law (observe (fun x => max (R x) 0)) (negativeSample 4) cell_rejected
  dependence := sample_dependence

def quarticEvidence : Registration quarticArena (type_of% @quartic_mass_le) where
  actual := realize signature (fun _ _ x => max (R x) 0) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@quartic_mass_le, negativeSample (((6 : ℝ) + 1) ^ 4), quartic_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    quarticArena.Law (observe (fun x => max (R x) 0))
      (negativeSample (((6 : ℝ) + 1) ^ 4)) quartic_rejected
  dependence := sample_dependence

def tailAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ramp_eq_neg_weightedTail) (Realization signature) Unit Unit where
  unitName := .str ``ramp_eq_neg_weightedTail "__information_unit"
  realizationName := ``tailEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinWeightedRamp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def sumAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ramp_eq_sum) (Realization signature) Unit Unit where
  unitName := .str ``ramp_eq_sum "__information_unit"
  realizationName := ``sumEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨sumArena⟩
  objectArena := .source ⟨sumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumArena ⟨sumEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinWeightedRamp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def chordAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ramp_chord) (Realization signature) Unit Unit where
  unitName := .str ``ramp_chord "__information_unit"
  realizationName := ``chordEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨chordArena⟩
  objectArena := .source ⟨chordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chordArena ⟨chordEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinWeightedRamp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def cellAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mass_le_of_cell) (Realization signature) Unit Unit where
  unitName := .str ``mass_le_of_cell "__information_unit"
  realizationName := ``cellEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨cellArena⟩
  objectArena := .source ⟨cellArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cellArena ⟨cellEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => max (R x) 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinWeightedRamp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def quarticAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quartic_mass_le) (Realization signature) Unit Unit where
  unitName := .str ``quartic_mass_le "__information_unit"
  realizationName := ``quarticEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨quarticArena⟩
  objectArena := .source ⟨quarticArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quarticArena ⟨quarticEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => max (R x) 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinWeightedRamp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.RobinWeightedRamp
