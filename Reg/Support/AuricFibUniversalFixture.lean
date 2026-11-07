import LeanInformationAuditInterface.Contract.AuricFib
import Reg.D5.S0.Diagonal.PigeonholeFiber
import Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
import Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber

namespace AuricFibUniversalCompiled
open D5.S3.Arith.FibonacciAtomic
open ImmediateWindowStateCapacity
open LeanInformationAudit.AuricFib.Contract

private def acquiredNullMass : Nat := 1

def acquiredMasses : Masses where
  nullMass := acquiredNullMass
  lowMass := 1
  highMass := 1
  endsMass := 1
  middleMass := 1
  denominator := 5
  positive := by decide
  normalized := by decide

def reader : LiteralWindowEnd.Window → RawState 0 :=
  fun a => rawTransition (rawMachine 0).start a

def reply : LiteralWindowEnd.Window → Option Int :=
  fun a => rawOutput (rawTransition (reader a) .high)

def bridge : NativeBridge where
  reader := reader
  reply := reply
  reader_eq := rfl
  reply_eq := rfl

def declared : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.declared "compiled source fixture" acquiredMasses)
    [] [.seam, .guard, .reply, .atom]

def absent : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.absent "unacquired compiled source")
    [] [.seam, .guard, .reply, .atom]

def empirical : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.empirical "compiled archive" [.zero, .ends, .middle])
    [] [.seam, .guard, .reply, .atom]

def apex : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.declared "apex fixture" {
    nullMass := 0, lowMass := 0, highMass := 0, endsMass := 0, middleMass := 1,
    denominator := 1, positive := by decide, normalized := by decide })
    [] [.seam, .guard, .reply, .atom]

def zeroCondition : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.declared "zero event fixture" {
    nullMass := 1, lowMass := 0, highMass := 0, endsMass := 0, middleMass := 0,
    denominator := 1, positive := by decide, normalized := by decide })
    [] [.seam, .guard, .reply, .atom]

def unsupported : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .unsupported "unbounded history source has no supported finite arena"

def rejected : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.absent "incomplete readout contract") [] [.seam]

theorem noise : True := trivial

theorem unrelated : True := trivial

/-- Propositional transport can inhabit a typed record; it does not supply the
original telescope. Compiled source reconstruction must reject this fixture. -/
def wrongSource : NativeSource unrelated where
  reconstruction := by
    have h : True = (type_of% NativeContinuation.NullReplyFiber.native_execution) :=
      propext ⟨fun _ => NativeContinuation.NullReplyFiber.native_execution, fun _ => trivial⟩
    rw [← h]
    exact .exact

def wrongTarget : Application.{0,0,0,0,0,0} unrelated where
  evidence := .native wrongSource bridge (.absent "unrelated statement") [] [.seam, .guard, .reply, .atom]

def parameterized (_n : Nat) : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact } bridge (.absent "parameterized contract") [] [.seam, .guard, .reply, .atom]


open LeanInformationAudit.AuricFib

/-- The same original source supplies both a positive invariant and concrete
counterexamples for weaker observations. The one-window source law stays absent. -/
def predictionClosed : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .memory, actions := NativePrediction.allActions,
    evidence := .closed (NativePrediction.memory_closed _) } }

def predictionQuantity : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .seamReply, actions := NativePrediction.allActions,
    evidence := .separated NativePrediction.quantitySeparation } }

def predictionRejection : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .reply, actions := NativePrediction.allActions,
    evidence := .separated NativePrediction.rejectionSeparation } }

def predictionUnknown : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .seamReply, actions := NativePrediction.allActions,
    evidence := .unknown "no operation evidence supplied" } }

/-- Closure over an empty input type covers only the empty continuation. -/
def predictionEmpty : Application.{0,0,0,0,0,0} NativeContinuation.NullReplyFiber.native_execution where
  evidence := absent.evidence
  prediction := some { source := { reconstruction := .exact }, contract := {
    summary := .reply, actions := [],
    evidence := .closed (by intro action; exact False.elim (by simpa using action.property)) } }

/-- Prediction evidence cannot turn a non-native occurrence into this source. -/
def predictionWrongSource : Application.{0,0,0,0,0,0} unrelated where
  evidence := .typed {
    source := LeanInformationAudit.Analysis.Source.unobserved unrelated
      `Reg.Support.AuricFibUniversalFixture
    plan := { task := (), initial := [], additions := [] }
    acquisition := .unavailable "no finite presentation requested" }
  prediction := some { source := wrongSource, contract := {
    summary := .memory, actions := NativePrediction.allActions,
    evidence := .closed (NativePrediction.memory_closed _) } }

end AuricFibUniversalCompiled

namespace AuricFibUniversalProduction
open LeanInformationAudit.Analysis
open LeanInformationAudit.AuricFib.Contract
open Reg.D5.S0.Diagonal.PigeonholeFiber
universe u v

/-- Production clients retain their actual source-owned implementation. -/
def finite := finiteAnalysis
def constant := constantAnalysis
def quotient := quotientAnalysis
def restricted := restrictedAnalysis
noncomputable def infinite := infiniteAnalysis
def dependentFamily := familyAnalysis.{u}
def history :=
  Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.analysis.{u,v}
def native := Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.initializedWindow
def nativeDeclared := AuricFibUniversalCompiled.declared
def nativeAbsent := AuricFibUniversalCompiled.absent
def nativeEmpirical := AuricFibUniversalCompiled.empirical
def nativeApex := AuricFibUniversalCompiled.apex
def nativeZeroCondition := AuricFibUniversalCompiled.zeroCondition
def nativeUnsupported := AuricFibUniversalCompiled.unsupported
def nativeRejected := AuricFibUniversalCompiled.rejected
def nativeWrongTarget := AuricFibUniversalCompiled.wrongTarget
def nativeParameterized := AuricFibUniversalCompiled.parameterized

/-- Normalization is proved, but the numeric metadata is not literal data. -/
def nativeUnavailableLaw : Application.{0,0,0,0,0,0}
    D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact }
    AuricFibUniversalCompiled.bridge
    (.declared "law requires computation" {
      nullMass := Nat.add 0 1, lowMass := 1, highMass := 1, endsMass := 1, middleMass := 1,
      denominator := 5, positive := by decide, normalized := by decide })
    [] [.seam, .guard, .reply, .atom]

def wrongOwnerSource : Source (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) :=
  { source.{0} with selection := { source.{0}.selection with owner := `Unrelated } }

def wrongOwner : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := wrongOwnerSource
    plan := { task := (), initial := [()], additions := [] }
    acquisition := .unavailable "finite presentation unacquired" }

/-- A lawful table-producing function remains outside the literal acquisition
format. Its mathematical client and qualitative source binding remain valid. -/
abbrev computedPresentation : FinitePresentation plan threeDomain := {
  threePresentation with
  values := fun _ x => if x.val == 1 then .bool true else .bool false
  values_correct := by decide }

def undecoded : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source, plan := plan,
    acquisition := .finite threeDomain computedPresentation }

def delayedPlan : Plan source.{0} where
  task := ()
  initial := []
  additions := [[], [()], []]

abbrev delayedPresentation : FinitePresentation delayedPlan threeDomain where
  stateFintype := threePresentation.stateFintype
  stateDecidableEq := threePresentation.stateDecidableEq
  enumeration := threePresentation.enumeration
  values := threePresentation.values
  decode := threePresentation.decode
  values_correct := threePresentation.values_correct
  kernel := threePresentation.kernel
  kernel_correct := threePresentation.kernel_correct
  taskValues := threePresentation.taskValues
  task_correct := threePresentation.task_correct
  layers := ![fun _ _ => true, fun _ _ => true,
    ![![true, false, true], ![false, true, false], ![true, false, true]],
    ![![true, false, true], ![false, true, false], ![true, false, true]]]
  layers_correct := by decide

def delayed : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source, plan := delayedPlan,
    acquisition := .finite threeDomain delayedPresentation }

abbrev singletonDomain : Domain source.{0} := Domain.fiber source ⟨Unit, Unit, id⟩
abbrev singletonPresentation : FinitePresentation plan singletonDomain where
  stateFintype := inferInstanceAs (Fintype Unit)
  stateDecidableEq := inferInstanceAs (DecidableEq Unit)
  enumeration := { states := [()], nodup := by decide, complete := by decide }
  values _ _ := .unit
  decode _ _ := some ()
  values_correct := by decide
  kernel _ _ _ := true
  kernel_correct := by decide
  taskValues _ := .unit
  task_correct := by decide
  layers _ _ _ := true
  layers_correct := by decide

def singleton : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source, plan := plan,
    acquisition := .finite singletonDomain singletonPresentation }

abbrev emptyDomain : Domain source.{0} := Domain.fiber source ⟨Fin 0, Unit, fun _ => ()⟩
abbrev emptyPresentation : FinitePresentation plan emptyDomain where
  stateFintype := inferInstanceAs (Fintype (Fin 0))
  stateDecidableEq := inferInstanceAs (DecidableEq (Fin 0))
  enumeration := { states := [], nodup := by decide, complete := by decide }
  values _ _ := .unit
  decode _ _ := some ()
  values_correct := by decide
  kernel _ _ _ := true
  kernel_correct := by decide
  taskValues _ := .unit
  task_correct := by decide
  layers _ _ _ := true
  layers_correct := by decide

def empty : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source, plan := plan,
    acquisition := .finite emptyDomain emptyPresentation }

/-- Display codes need not be actual observations; the decoded value is seven. -/
abbrev decodedDomain : Domain source.{0} := Domain.fiber source ⟨Bool, Nat, fun _ => 7⟩
abbrev decodedPresentation : FinitePresentation plan decodedDomain where
  stateFintype := inferInstanceAs (Fintype Bool)
  stateDecidableEq := inferInstanceAs (DecidableEq Bool)
  enumeration := { states := [false, true], nodup := by decide, complete := by decide }
  values _ _ := .text "seven"
  decode _ _ := some 7
  values_correct := by decide
  kernel _ _ _ := true
  kernel_correct := by decide
  taskValues _ := .text "seven"
  task_correct := by decide
  layers _ _ _ := true
  layers_correct := by decide

def decodedNat : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source, plan := plan,
    acquisition := .finite decodedDomain decodedPresentation }

opaque hiddenAdditions : List (List Unit) := [[], [()]]
def unmaterializedPlan : Plan source.{0} where
  task := ()
  initial := []
  additions := hiddenAdditions

def opaqueLayers : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source, plan := unmaterializedPlan,
    acquisition := .unavailable "finite presentation unacquired" }

/-- A definition-backed theorem keeps the original universe declaration even
when the client explicitly selects universe zero. -/
def definedStatement : Prop :=
  type_of% @D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{u}
theorem definedTheorem : definedStatement.{u} :=
  @D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{u}
def definedSource : Source (@definedTheorem.{u}) where
  signature := source.{u}.signature
  actual := source.{u}.actual
  rebuild := source.{u}.rebuild
  reconstruction := .exact
  selection := { source.{u}.selection with
    owner := `Reg.Support.AuricFibUniversalFixture
    definition := some {
      owner := `Reg.Support.AuricFibUniversalFixture
      name := `AuricFibUniversalProduction.definedStatement
      path := #[] } }

def specializedDefinition : Application (@definedTheorem.{0}) where
  evidence := .typed {
    source := definedSource
    plan := { task := (), initial := [], additions := [] }
    acquisition := .unavailable "no finite presentation requested" }

theorem joinedTheorem : definedStatement.{max u v} :=
  @D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{max u v}
def joinedSource : Source (@joinedTheorem.{u,v}) where
  signature := source.{max u v}.signature
  actual := source.{max u v}.actual
  rebuild := source.{max u v}.rebuild
  reconstruction := .exact
  selection := definedSource.{max u v}.selection

def joinedDefinition : Application (@joinedTheorem.{0,0}) where
  evidence := .typed {
    source := joinedSource
    plan := { task := (), initial := [], additions := [] }
    acquisition := .unavailable "no finite presentation requested" }

theorem absentContract : True := trivial

/-- A bare proposition has a complete source binding without data observations. -/
def dataFreeSource := Source.unobserved absentContract
  (owner := `Reg.Support.AuricFibUniversalFixture)

def dataFreeClient : Client.{0,0,0,0,0,0,0} absentContract where
  source := dataFreeSource
  plan := { task := (), initial := [], additions := [[], [()], []] }
  acquisition := .unavailable "no finite presentation requested"

/-- A complete terminal table still supplies no original source data domain. -/
def terminalPresentation : FinitePresentation dataFreeClient.plan
    (Domain.fiber dataFreeSource ()) where
  stateFintype := inferInstanceAs (Fintype Unit)
  stateDecidableEq := inferInstanceAs (DecidableEq Unit)
  enumeration := {
    states := [()]
    nodup := List.nodup_singleton _
    complete := by
      change ([()] : List Unit).toFinset = (Finset.univ : Finset Unit)
      decide }
  values _ _ := .unit
  decode _ _ := some ()
  values_correct _ _ := rfl
  kernel _ _ _ := true
  kernel_correct _ _ _ := ⟨fun _ => rfl, fun _ => rfl⟩
  taskValues _ := .unit
  task_correct _ := rfl
  layers _ _ _ := true
  layers_correct _ _ _ := ⟨fun _ _ _ => rfl, fun _ => rfl⟩

/-- Empty selection cannot smuggle a data-bearing model into source binding. -/
def unobservedMismatch : Source absentContract where
  signature := { LeanInformationAudit.Analysis.unobservedSignature with State := fun _ => Bool }
  actual := { readout := fun _ _ _ => (), anchor := fun e => nomatch e }
  rebuild _ := True
  reconstruction := .exact
  selection := dataFreeSource.selection

end AuricFibUniversalProduction
namespace AuricFibUniversalProduction
open LeanInformationAudit.Analysis LeanInformationAudit.AuricFib.Contract
universe u
def dataFree : Application absentContract where
  evidence := .typed dataFreeClient
def terminalCounts : Application absentContract where
  evidence := .typed {
    source := dataFreeSource, plan := dataFreeClient.plan,
    acquisition := .finite (Domain.fiber dataFreeSource ()) terminalPresentation }
def dataFreeBad : Application absentContract where
  evidence := .typed {
    source := unobservedMismatch
    plan := { task := (), initial := [], additions := [] }
    acquisition := .unavailable "no finite presentation requested" }
def unobservedFamily : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{u}) where
  evidence := .typed {
    source := Source.unobserved _ `D5.S0.Diagonal.PigeonholeFiber
    plan := { task := (), initial := [], additions := [[], [()]] }
    acquisition := .unavailable "no finite presentation requested" }
end AuricFibUniversalProduction
