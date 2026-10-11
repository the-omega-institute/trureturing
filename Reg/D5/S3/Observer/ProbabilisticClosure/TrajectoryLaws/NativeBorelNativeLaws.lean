import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeFullResidual FourthSegmentStoppedLaw NativeBorelCommonFlow NativeBorelNativeLaws
open NativeConditionalControl.Tail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped ENNReal NNReal

abbrev tailsSignature : Signature where
  Params := unitInterval
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def tailsArena : Arena where
  signature := tailsSignature
  Law R := ∀ (r : unitInterval) (j : ℕ),
    R.readout 0 r j = (alphaMass r * betaMass r) ^ j ∧
    R.readout 1 r j = alphaMass r * (alphaMass r * betaMass r) ^ j

def tailsActual : Realization tailsSignature :=
  realize tailsSignature (fun i r j =>
    if i = 0 then (native .p r : Measure _) (tailSet .p j)
    else (native .beta r : Measure _) (tailSet .beta j)) (fun e => nomatch e)

def tailsRejected : Realization tailsSignature :=
  realize tailsSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem tailsRejected_law : ¬ tailsArena.Law tailsRejected := by
  intro h
  have h0 := (h lowerRate 0).1
  simpa [tailsRejected, realize] using h0

def tailsRecord : Registration tailsArena (type_of% (@native_tails)) where
  actual := tailsActual
  bridge := Iff.rfl
  variation := ⟨native_tails, tailsRejected, tailsRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      change Fin 2 at i
      let bad : Realization tailsSignature := realize tailsSignature
        (fun k r j => if k = i then 0 else tailsActual.readout k r j) (fun e => nomatch e)
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro k hki
        funext r j
        simp [bad, realize, hki]
      · intro h
        fin_cases i
        · have ht := (h lowerRate 0).1
          simpa [bad, realize] using ht
        · have ht := (h lowerRate 0).2
          change (0 : ℝ≥0∞) = alphaMass lowerRate * _ at ht
          have hr := congrArg ENNReal.toReal ht
          norm_num [alphaMass, lowerRate] at hr
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨lowerRate, (0 : ℕ), (1 : ℕ), ?_⟩
    intro h
    fin_cases i
    · change (native .p lowerRate : Measure _) (tailSet .p 0) =
        (native .p lowerRate : Measure _) (tailSet .p 1) at h
      rw [(native_tails _ _).1, (native_tails _ _).1] at h
      have hr := congrArg ENNReal.toReal h
      norm_num [alphaMass, betaMass, lowerRate, unitInterval.coe_toNNReal,
        unitInterval.symm, ENNReal.toReal_mul] at hr
    · change (native .beta lowerRate : Measure _) (tailSet .beta 0) =
        (native .beta lowerRate : Measure _) (tailSet .beta 1) at h
      rw [(native_tails _ _).2, (native_tails _ _).2] at h
      have hr := congrArg ENNReal.toReal h
      norm_num [alphaMass, betaMass, lowerRate, unitInterval.coe_toNNReal,
        unitInterval.symm, ENNReal.toReal_mul] at hr

def tailsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_tails)
    (type_of% (realize tailsSignature (fun i r j =>
      if i = 0 then (native .p r : Measure _) (tailSet .p j)
      else (native .beta r : Measure _) (tailSet .beta j)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws.tails,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws.tailsRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨tailsArena⟩, objectArena := .source ⟨tailsArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source tailsArena ⟨tailsRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize tailsSignature (fun i r j =>
    if i = 0 then (native .p r : Measure _) (tailSet .p j)
    else (native .beta r : Measure _) (tailSet .beta j)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws,
    definition := none, coordinates := #[0], readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }, {
      path := #["body", "body", "arg", "fn", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


abbrev coordinateSignature : Signature where
  Params := Σ _ : ActivePhase, unitInterval
  State p := ValidTail p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateArena : Arena where
  signature := coordinateSignature
  Law R := ∀ (s : ActivePhase) (r : unitInterval) (t : ValidTail s),
    R.readout () ⟨s, r⟩ t = explicitStoppedWordLaw s r {t.val}

def coordinateActual : Realization coordinateSignature :=
  realize coordinateSignature (fun _ p t => (native p.1 p.2 : Measure _) {t})
    (fun e => nomatch e)

def coordinateRejected : Realization coordinateSignature :=
  realize coordinateSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem coordinateRejected_law : ¬ coordinateArena.Law coordinateRejected := by
  intro h
  have ht := h .p lowerRate (pAtom 0 0)
  change (0 : ℝ≥0∞) = explicitStoppedWordLaw .p lowerRate {(pAtom 0 0).val} at ht
  rw [← native_coordinate, (native_atoms _).1] at ht
  have hr := congrArg ENNReal.toReal ht
  norm_num [alphaMass, lowerRate] at hr

def coordinateRecord : Registration coordinateArena (type_of% (@native_coordinate)) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨native_coordinate, coordinateRejected, coordinateRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coordinateRejected, ?_, rfl, coordinateRejected_law⟩
      intro j hj
      exact False.elim (hj (show j = i from by cases i; cases j; rfl))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨.p, lowerRate⟩, pAtom 0 0, infinity .p, ?_⟩
    intro h
    change (native .p lowerRate : Measure _) {pAtom 0 0} =
      (native .p lowerRate : Measure _) {infinity .p} at h
    rw [(native_atoms _).1, (native_atoms _).2.2.2] at h
    have hr := congrArg ENNReal.toReal h
    norm_num [alphaMass, lowerRate] at hr

def coordinateRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_coordinate)
    (type_of% (realize coordinateSignature
      (fun _ p t => (native p.1 p.2 : Measure _) {t}) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws.coordinate,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws.coordinateRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨coordinateArena⟩, objectArena := .source ⟨coordinateArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source coordinateArena ⟨coordinateRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize coordinateSignature
    (fun _ p t => (native p.1 p.2 : Measure _) {t}) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws,
    definition := none, coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

abbrev emissionSignature : Signature where
  Params := ActivePhase × unitInterval
  State _ := Unit
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def emissionActual : Realization emissionSignature :=
  realize _ (fun i p _ => if i = 0 then emission p.1 (native p.1 p.2) else alphaMass p.2) (fun e => nomatch e)

def emissionArena : Arena where
  signature := emissionSignature
  Law R := ∀ s r, R.readout 0 (s, r) () = R.readout 1 (s, r) ()

theorem emission_bridge : (type_of% (@native_emission)) ↔
    emissionArena.Law emissionActual := Iff.rfl

theorem emission_actual_law : emissionArena.Law emissionActual :=
  emission_bridge.mp native_emission


end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws
