import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration
import Reg.Support.DependentFamily

/-! The actual paid post-update reply at a particular old cherry certifies
access to its previously hidden historical orientation bit. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

abbrev signature : Signature where
  Params := Address
  State _ := Labelled
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => present w (p ++ [false, false])) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (n : Nat) (s : Shape) (_hn : 2 ≤ n)
    (_hs : s ∈ rankedShapes n) (t w : Labelled) (_ht : t ∈ currentFiber n s) (_hw : Step t w),
    (∀ p : Address, p ∈ cherries s → F.readout () p w = terminalBit t p) ∧
    run (present s) (present w) (calibrationProgram s) = some (t, oldSemanticAdapter t) ∧
    (∀ f, FrameHistory n t f → oldSemanticAdapter t = composeOldFrames t f) ∧
    trace (present s) (present w) (calibrationProgram s) = calibrationAddresses s ∧
    ((calibrationAddresses s).Nodup ∧
      ∀ p, p ++ [false, false] ∈ calibrationAddresses s ↔ p ∈ cherries s) ∧
    (let ws := trace (present s) (present w) (calibrationProgram s)
     updateCount (present s) (present w) (calibrationProgram s) = 1 ∧
     readQ ws = (cherries s).card ∧
     readW ws = ∑ p ∈ cherries s, (p.length + 2) ∧
     readM ws = (cherries s).sup (fun p => p.length + 2)) ∧
    (∀ P : OneUpdate Labelled,
      (∀ (x : ↥(currentFiber n s)) (v : Labelled), Step x.val v →
        run (present s) (present v) P = x.val) →
      let ws := trace (present s) (present w) P
      (cherries s).card ≤ readQ ws ∧
      (∑ p ∈ cherries s, (p.length + 2)) ≤ readW ws ∧
      (cherries s).sup (fun p => p.length + 2) ≤ readM ws) ∧
    (∀ v, v ∈ currentFiber (n + 1) (shape w) ↔ Step t v) ∧
    freshBetaSites t = cherries (shape w) ∧
    (freshBetaSites t).card = Nat.fib n ∧
    (currentFiber (n + 1) (shape w)).card = 2 ^ Nat.fib n ∧
    Function.Bijective (fun (u : ↥(currentFiber (n + 1) (shape w))) (p : ↥(freshBetaSites t)) =>
      terminalBit u.val p.val) ∧
    (∀ v, Step t v → present v = present w)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : cherry ∈ rankedShapes 2 := by decide
  have ht : FreeMagma.mul beta alpha ∈ currentFiber 2 cherry := by decide
  have eq := (h 2 cherry (by decide) hs (.mul beta alpha) (.mul (.mul beta alpha) beta) ht
    (.branch .betaLeft .alphaToBeta)).1 [] (by decide)
  cases eq

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨[], .mul (.mul beta alpha) beta, .mul beta (.mul alpha beta), ?_⟩
  intro h
  cases h

def family : Registration arena (type_of% exact_one_update_calibration) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_one_update_calibration, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_one_update_calibration (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration
    definition := none
    coordinates := #[8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration
