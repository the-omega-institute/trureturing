import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicHellingerCut
import Batteries.Tactic.OpenPrivate

/-! Source-bound real readouts of the endpoint crossing and the physical angular loss. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap (Mat)
open _root_.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open _root_.D5.S3.Quantum.Semigroups.WuCubicHellingerCut
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private cutA cutB c e gamma bias from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicHellingerCut

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def le : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def reverseStrict : Realization signature :=
  realize signature (fun _ _ x y => y < x) (fun e => nomatch e)

private theorem le_dependence : ObservationalDependence signature le := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun h 0) (le_rfl : (0 : ℝ) ≤ 0))

private abbrev focalR : ℝ := 21 / 20
private abbrev focalM : ℝ := (20 / 21) ^ 2 + 1 / 1024
private abbrev focalN : ℝ := 20 / 21 + 1 / 2048
private abbrev focalEta : ℝ := 1 / 1000000000

private theorem focal_r_ge_one : 1 ≤ focalR := by norm_num [focalR]
private theorem focal_m_nonneg : 0 ≤ focalM := by norm_num [focalM]
private theorem focal_m_le_n : focalM ≤ focalN := by norm_num [focalM, focalN]
private theorem focal_n_le_one : focalN ≤ 1 := by norm_num [focalN]

private theorem focal_occupation_eq :
    normalizedDeficit focalR 1 focalM focalN focalN =
      occupationDeficit focalR focalM focalN focalN := by
  have hn : 0 ≤ focalN := focal_m_nonneg.trans focal_m_le_n
  exact occupation_deficit_eq focal_r_ge_one focal_m_nonneg hn hn

namespace LongCrossing

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : unitary Mat,
    R.readout () ()
      ((Real.sqrt (oddTilt U 0) - Real.sqrt (oddTilt U 3)) ^ 2 / 2)
      (longCrossing U)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (long_crossing_ge_hellinger 1)) (h 1)

def family : Registration arena (type_of% @long_crossing_ge_hellinger) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@long_crossing_ge_hellinger, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@long_crossing_ge_hellinger) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicHellingerCut.long_crossing_ge_hellinger.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicHellingerCut.LongCrossing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicHellingerCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LongCrossing

namespace DeficitBound

private abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {r m n q η : ℝ} (U : unitary Mat),
    1 ≤ r → 0 ≤ m → m ≤ n → n ≤ q → q ≤ 1 →
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let L₀ := matchedMixture A B
    let κ := longCoeff r m n q / 4
    let P₀ := (A 0 + Z₀ - L₀) / 2
    let P₂ := (A 2 + Z₂ - L₀) / 2
    let p := P₀ + P₂
    let k := (P₀ - P₂) / p
    let j := P₀ * P₂ / p - L₀ / 4
    let G₀ := B 0 / 2 - 2 * P₀
    let G₂ := B 2 / 2 - 2 * P₂
    let gs := G₀ + G₂
    let R := G₀ - G₂ - k * gs
    0 ≤ L₀ → L₀ ≤ Z₀ → L₀ ≤ Z₂ →
    0 < P₀ → 0 < P₂ → 0 < κ → 0 ≤ j → 0 ≤ η →
    0 ≤ (1 - k ^ 2) * η ^ 2 + (4 * κ - k * R) * η - R ^ 2 / 4 →
    observation.readout () ()
      (occupationDeficit r m n q - (max 0 (2 * η - gs)) ^ 2 / (4 * p))
      (normalizedDeficit r U m n q)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have reverse := h (r := focalR) (m := focalM) (n := focalN) (q := focalN)
    (η := focalEta) 1 focal_r_ge_one focal_m_nonneg focal_m_le_n le_rfl focal_n_le_one
  dsimp only at reverse
  have bad := reverse ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    try
      change normalizedDeficit focalR 1 focalM focalN focalN < _ at bad
      rw [focal_occupation_eq] at bad
      revert bad
    norm_num [focalR, focalM, focalN, focalEta, cutEnergy, cutBias, matchedMixture, lowerCoeff,
      upperCoeff, longCoeff, crossCoeff, directedCoeff, cutA, cutB, c, e, gamma, bias,
      max_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]

def family : Registration arena (type_of% @hellinger_deficit_bound) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@hellinger_deficit_bound, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hellinger_deficit_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicHellingerCut.hellinger_deficit_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicHellingerCut.DeficitBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicHellingerCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeficitBound

end Reg.D5.S3.Quantum.Semigroups.WuCubicHellingerCut
