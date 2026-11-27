import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import Batteries.Tactic.OpenPrivate

/-! Source-bound real readouts of the physical cubic deficit and its angular bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped BigOperators Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
  (Mat frameVector oddProbability)
open _root_.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge (G GInv D generator)
open _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic (alpha)
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private cutA cutB c e bias gamma from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def le : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def reverseStrict : Realization signature :=
  realize signature (fun _ _ x y => y < x) (fun e => nomatch e)

private def equal : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def unequal : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private theorem le_dependence : ObservationalDependence signature le := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun h 0) (le_rfl : (0 : ℝ) ≤ 0))

private theorem equal_dependence : ObservationalDependence signature equal := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (show (1 : ℝ) = 0 from Eq.mp (congrFun h 0) rfl)

/-- The occupation frame has zero extreme odd tilt. -/
private theorem identity_tiltSum : tiltSum (1 : unitary Mat) = 0 := by
  norm_num [tiltSum, oddTilt, oddProbability, frameVector, Matrix.one_apply]

/-- Positive cut weights with a strictly larger refined mixture. -/
private abbrev testA : Fin 3 → ℝ := fun _ => 1
private abbrev testB : Fin 3 → ℝ := fun _ => 2

private theorem testA_nonneg : ∀ i, 0 ≤ testA i := fun _ => zero_le_one
private theorem testB_nonneg : ∀ i, 0 ≤ testB i := fun _ => by norm_num [testB]
private theorem test_matched : matchedMixture testA testB = 0 := by
  norm_num [matchedMixture, testA, testB]

/-- A spectrum with three positive gaps and a strictly positive refined increment. -/
private abbrev testEnergy : Fin 3 → ℝ := cutEnergy 2 (1 / 4) (1 / 2) (3 / 5)
private abbrev testBias : Fin 3 → ℝ := cutBias 2 (1 / 4) (1 / 2) (3 / 5)

private theorem spectral_test_mixture : matchedMixture testEnergy testBias = 1 / 50 := by
  change cutB 2 (1 / 2) (3 / 5) / 2 - cutA 2 (1 / 2) (3 / 5) = 1 / 50
  norm_num [cutA, cutB, c, e, bias, gamma]

private theorem spectral_test_lower : lowerCoeff 2 (1 / 4) (1 / 2) (3 / 5) = 13 / 400 := by
  norm_num [lowerCoeff, crossCoeff, directedCoeff, c, e, gamma]

private theorem spectral_test_upper : upperCoeff 2 (1 / 2) (3 / 5) = 19 / 250 := by
  norm_num [upperCoeff, crossCoeff, directedCoeff, c, e, gamma]

private theorem spectral_test_end : min (testBias 0) (testBias 2) = 9 / 128 := by
  change min (cutB 2 (1 / 4) (1 / 2)) (cutB 2 (3 / 5) 1) = 9 / 128
  norm_num [cutB, bias, e, gamma, min_def]

namespace LongProduct

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat),
    R.readout () ()
      (tiltDiff U ^ 2 / 4)
      (tiltSum U * longCrossing U)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (long_crossing_mul 1)) (h 1)

def family : Registration arena (type_of% @long_crossing_mul) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@long_crossing_mul, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@long_crossing_mul) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.long_crossing_mul.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.LongProduct.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
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

end LongProduct

namespace LongCrossing

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat),
    R.readout () ()
      (longFactor (tiltSum U) * tiltDiff U ^ 2 / 4)
      (longCrossing U)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (long_crossing_ge 1)) (h 1)

def family : Registration arena (type_of% @long_crossing_ge) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@long_crossing_ge, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@long_crossing_ge) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.long_crossing_ge.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.LongCrossing.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
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

namespace MatchedCuts

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ Zlong : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hZlong : 0 ≤ Zlong)
    (hL : 0 ≤ matchedMixture A B) (hL₀ : matchedMixture A B ≤ Z₀)
    (hL₂ : matchedMixture A B ≤ Z₂),
    let L₀ := matchedMixture A B
    R.readout () ()
      (occupationCost A B Z₀ Z₂ + singletonCorrection U A B Z₀ Z₂ L₀ +
        (Zlong / 4 * longFactor (tiltSum U) - L₀ / 4) * tiltDiff U ^ 2)
      (retainedCost U A B Z₀ Z₂ Zlong)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hL : 0 ≤ matchedMixture testA testB := by simp [test_matched]
  have hZ : matchedMixture testA testB ≤ 1 := by rw [test_matched]; exact zero_le_one
  exact (not_lt_of_ge (matched_cut_bound 1 testA testB 1 1 1
    testA_nonneg testB_nonneg zero_le_one hL hZ hZ))
    (h 1 testA testB 1 1 1 testA_nonneg testB_nonneg zero_le_one hL hZ hZ)

def family : Registration arena (type_of% @matched_cut_bound) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@matched_cut_bound, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@matched_cut_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.matched_cut_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.MatchedCuts.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MatchedCuts

namespace ChargeAdmissibility

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) (A B : Fin 3 → ℝ) (L : ℝ)
    (hA : 0 ≤ A 1) (hL : 0 ≤ L)
    (hsmall : (A 1 + L) * tiltSum U / 2 ≤ L - matchedMixture A B)
    (hend : L - matchedMixture A B ≤ min (B 0) (B 2)),
    R.readout () () 0 (refinedCharge U A B L) ∧
      refinedCharge U A B L ≤ min (B 0) (B 2)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hA : 0 ≤ testA 1 := testA_nonneg 1
  have hsmall : (testA 1 + 1) * tiltSum (1 : unitary Mat) / 2 ≤
      1 - matchedMixture testA testB := by
    norm_num [identity_tiltSum, test_matched]
  have hend : 1 - matchedMixture testA testB ≤ min (testB 0) (testB 2) := by
    norm_num [test_matched, testB]
  exact (not_lt_of_ge (refined_charge_admissible 1 testA testB 1
    hA zero_le_one hsmall hend).1) (h 1 testA testB 1 hA zero_le_one hsmall hend).1

def family : Registration arena (type_of% @refined_charge_admissible) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@refined_charge_admissible, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@refined_charge_admissible) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.refined_charge_admissible.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.ChargeAdmissibility.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChargeAdmissibility

namespace RefinedCuts

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ Zlong : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB₁ : 0 ≤ B 1) (hZlong : 0 ≤ Zlong)
    (hL₀ : 0 ≤ matchedMixture A B)
    (hLleft : matchedMixture A B ≤ Z₀) (hLright : matchedMixture A B ≤ Z₂)
    (hsmall : (A 1 + min Z₀ Z₂) * tiltSum U / 2 ≤ min Z₀ Z₂ - matchedMixture A B)
    (hend : min Z₀ Z₂ - matchedMixture A B ≤ min (B 0) (B 2)),
    let L₀ := matchedMixture A B
    let L := min Z₀ Z₂
    let ell := L - L₀
    R.readout () ()
      (occupationCost A B Z₀ Z₂ + singletonCorrection U A B Z₀ Z₂ L₀ +
        B 1 / 8 * tiltSum U ^ 2 +
        (Zlong / 4 * longFactor (tiltSum U) - ell / 4 - L ^ 2 / (4 * (3 * A 1 + L))) *
          tiltDiff U ^ 2)
      (retainedCost U A B Z₀ Z₂ Zlong)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hL : 0 ≤ matchedMixture testA testB := by simp [test_matched]
  have hZ : matchedMixture testA testB ≤ 1 := by rw [test_matched]; exact zero_le_one
  have hsmall : (testA 1 + min (1 : ℝ) 1) * tiltSum (1 : unitary Mat) / 2 ≤
      min 1 1 - matchedMixture testA testB := by
    norm_num [identity_tiltSum, test_matched]
  have hend : min (1 : ℝ) 1 - matchedMixture testA testB ≤
      min (testB 0) (testB 2) := by
    norm_num [test_matched, testB]
  exact (not_lt_of_ge (refined_cut_bound 1 testA testB 1 1 1
    testA_nonneg (testB_nonneg 1) zero_le_one hL hZ hZ hsmall hend))
    (h 1 testA testB 1 1 1 testA_nonneg (testB_nonneg 1)
      zero_le_one hL hZ hZ hsmall hend)

def family : Registration arena (type_of% @refined_cut_bound) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@refined_cut_bound, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@refined_cut_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.refined_cut_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.RefinedCuts.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RefinedCuts

namespace OperatorIdentity

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (hr : 1 ≤ r)
    (U : unitary Mat) (m n q : ℝ),
    let V := physicalFrame U
    let M := V * diagonal (fun i => (levelsAt m n q i : ℂ)) * Vᴴ
    let X := GInv r * M * GInv r
    R.readout () ()
      (normalizedDeficit r U m n q)
      ((9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re -
          alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
            (M ^ 3).trace.re * Real.log (M ^ 3).trace.re))

private theorem rejected_law : ¬ arena.Law unequal := by
  intro h
  have hr : (1 : ℝ) ≤ 2 := by norm_num
  exact (h (r := 2) hr 1 0 (1 / 2) (1 / 2))
    (normalized_deficit_eq_ordinary_trace (r := 2) hr 1 0 (1 / 2) (1 / 2))

def family : Registration arena (type_of% @normalized_deficit_eq_ordinary_trace) where
  actual := equal
  bridge := Iff.rfl
  variation := ⟨@normalized_deficit_eq_ordinary_trace, unequal, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equal unequal rejected_law
  dependence := equal_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalized_deficit_eq_ordinary_trace) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.normalized_deficit_eq_ordinary_trace.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.OperatorIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OperatorIdentity

namespace CutIdentity

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (hr : 1 ≤ r) (U : unitary Mat)
    {m n q : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q),
    R.readout () ()
      (normalizedDeficit r U m n q)
      (thermalCenter r m n q +
        retainedCost U (cutEnergy r m n q) (cutBias r m n q)
          (lowerCoeff r m n q) (upperCoeff r n q) (longCoeff r m n q) +
        directedCost r U m n q)

private theorem rejected_law : ¬ arena.Law unequal := by
  intro h
  have hr : (1 : ℝ) ≤ 2 := by norm_num
  have hn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact (h (r := 2) hr 1 (m := 0) (n := 1 / 2) (q := 1 / 2) le_rfl hn hn)
    (normalized_deficit_eq_cuts (r := 2) hr 1 (m := 0) (n := 1 / 2) (q := 1 / 2)
      le_rfl hn hn)

def family : Registration arena (type_of% @normalized_deficit_eq_cuts) where
  actual := equal
  bridge := Iff.rfl
  variation := ⟨@normalized_deficit_eq_cuts, unequal, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equal unequal rejected_law
  dependence := equal_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalized_deficit_eq_cuts) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.normalized_deficit_eq_cuts.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.CutIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CutIdentity

namespace OccupationIdentity

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (hr : 1 ≤ r)
    {m n q : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q),
    R.readout () ()
      (normalizedDeficit r 1 m n q)
      (occupationDeficit r m n q)

private theorem rejected_law : ¬ arena.Law unequal := by
  intro h
  have hr : (1 : ℝ) ≤ 2 := by norm_num
  have hn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact (h (r := 2) hr (m := 0) (n := 1 / 2) (q := 1 / 2) le_rfl hn hn)
    (occupation_deficit_eq (r := 2) hr (m := 0) (n := 1 / 2) (q := 1 / 2)
      le_rfl hn hn)

def family : Registration arena (type_of% @occupation_deficit_eq) where
  actual := equal
  bridge := Iff.rfl
  variation := ⟨@occupation_deficit_eq, unequal, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equal unequal rejected_law
  dependence := equal_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@occupation_deficit_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.occupation_deficit_eq.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.OccupationIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OccupationIdentity

namespace MatchedDeficit

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r m n q : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hL : 0 ≤ matchedMixture (cutEnergy r m n q) (cutBias r m n q))
    (hleft : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ lowerCoeff r m n q)
    (hright : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ upperCoeff r n q),
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let L₀ := matchedMixture A B
    R.readout () ()
      (occupationDeficit r m n q +
        singletonCorrection U A B (lowerCoeff r m n q) (upperCoeff r n q) L₀ +
        (longCoeff r m n q / 4 * longFactor (tiltSum U) - L₀ / 4) * tiltDiff U ^ 2)
      (normalizedDeficit r U m n q)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hr : (1 : ℝ) ≤ 2 := by norm_num
  have hm : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hmn : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hnq : (1 / 2 : ℝ) ≤ 3 / 5 := by norm_num
  have hq1 : (3 / 5 : ℝ) ≤ 1 := by norm_num
  have hL : 0 ≤ matchedMixture testEnergy testBias := by
    rw [spectral_test_mixture]; norm_num
  have hleft : matchedMixture testEnergy testBias ≤ lowerCoeff 2 (1 / 4) (1 / 2) (3 / 5) := by
    rw [spectral_test_mixture, spectral_test_lower]; norm_num
  have hright : matchedMixture testEnergy testBias ≤ upperCoeff 2 (1 / 2) (3 / 5) := by
    rw [spectral_test_mixture, spectral_test_upper]; norm_num
  exact (not_lt_of_ge (matched_deficit_bound (r := 2) (m := 1 / 4) (n := 1 / 2)
    (q := 3 / 5) 1 hr hm hmn hnq hq1 hL hleft hright))
    (h (r := 2) (m := 1 / 4) (n := 1 / 2) (q := 3 / 5)
      1 hr hm hmn hnq hq1 hL hleft hright)

def family : Registration arena (type_of% @matched_deficit_bound) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@matched_deficit_bound, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@matched_deficit_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.matched_deficit_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.MatchedDeficit.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MatchedDeficit

namespace RefinedDeficit

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r m n q : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hL : 0 ≤ matchedMixture (cutEnergy r m n q) (cutBias r m n q))
    (hleft : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ lowerCoeff r m n q)
    (hright : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ upperCoeff r n q)
    (hsmall : (cutEnergy r m n q 1 + min (lowerCoeff r m n q) (upperCoeff r n q)) *
      tiltSum U / 2 ≤
      min (lowerCoeff r m n q) (upperCoeff r n q) -
        matchedMixture (cutEnergy r m n q) (cutBias r m n q))
    (hend : min (lowerCoeff r m n q) (upperCoeff r n q) -
      matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤
        min (cutBias r m n q 0) (cutBias r m n q 2)),
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let L₀ := matchedMixture A B
    let L := min (lowerCoeff r m n q) (upperCoeff r n q)
    R.readout () ()
      (occupationDeficit r m n q +
        singletonCorrection U A B (lowerCoeff r m n q) (upperCoeff r n q) L₀ +
        B 1 / 8 * tiltSum U ^ 2 +
        (longCoeff r m n q / 4 * longFactor (tiltSum U) - (L - L₀) / 4 -
          L ^ 2 / (4 * (3 * A 1 + L))) * tiltDiff U ^ 2)
      (normalizedDeficit r U m n q)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hr : (1 : ℝ) ≤ 2 := by norm_num
  have hm : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hmn : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hnq : (1 / 2 : ℝ) ≤ 3 / 5 := by norm_num
  have hq1 : (3 / 5 : ℝ) ≤ 1 := by norm_num
  have hL : 0 ≤ matchedMixture testEnergy testBias := by
    rw [spectral_test_mixture]; norm_num
  have hleft : matchedMixture testEnergy testBias ≤ lowerCoeff 2 (1 / 4) (1 / 2) (3 / 5) := by
    rw [spectral_test_mixture, spectral_test_lower]; norm_num
  have hright : matchedMixture testEnergy testBias ≤ upperCoeff 2 (1 / 2) (3 / 5) := by
    rw [spectral_test_mixture, spectral_test_upper]; norm_num
  have hsmall : (testEnergy 1 + min (lowerCoeff 2 (1 / 4) (1 / 2) (3 / 5))
      (upperCoeff 2 (1 / 2) (3 / 5))) * tiltSum (1 : unitary Mat) / 2 ≤
      min (lowerCoeff 2 (1 / 4) (1 / 2) (3 / 5)) (upperCoeff 2 (1 / 2) (3 / 5)) -
        matchedMixture testEnergy testBias := by
    rw [identity_tiltSum, spectral_test_lower, spectral_test_upper, spectral_test_mixture]
    norm_num [min_def]
  have hend : min (lowerCoeff 2 (1 / 4) (1 / 2) (3 / 5)) (upperCoeff 2 (1 / 2) (3 / 5)) -
      matchedMixture testEnergy testBias ≤ min (testBias 0) (testBias 2) := by
    rw [spectral_test_lower, spectral_test_upper, spectral_test_mixture, spectral_test_end]
    norm_num [min_def]
  exact (not_lt_of_ge (refined_deficit_bound (r := 2) (m := 1 / 4) (n := 1 / 2)
    (q := 3 / 5) 1 hr hm hmn hnq hq1 hL hleft hright hsmall hend))
    (h (r := 2) (m := 1 / 4) (n := 1 / 2) (q := 3 / 5)
      1 hr hm hmn hnq hq1 hL hleft hright hsmall hend)

def family : Registration arena (type_of% @refined_deficit_bound) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@refined_deficit_bound, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@refined_deficit_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.refined_deficit_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.RefinedDeficit.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RefinedDeficit

namespace RepeatedMiddle

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r m n : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hn1 : n ≤ 1),
    R.readout () ()
      (occupationDeficit r m n n +
        singletonCorrection U (cutEnergy r m n n) (cutBias r m n n) 0 0 0 +
        longCoeff r m n n / 4 * longFactor (tiltSum U) * tiltDiff U ^ 2)
      (normalizedDeficit r U m n n)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hr : (1 : ℝ) ≤ 2 := by norm_num
  have hn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hn1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  exact (not_lt_of_ge (repeated_middle_angular_bound (r := 2) (m := 0) (n := 1 / 2)
    1 hr le_rfl hn hn1)) (h (r := 2) (m := 0) (n := 1 / 2) 1 hr le_rfl hn hn1)

def family : Registration arena (type_of% @repeated_middle_angular_bound) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@repeated_middle_angular_bound, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@repeated_middle_angular_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.repeated_middle_angular_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate.RepeatedMiddle.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RepeatedMiddle

end Reg.D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
