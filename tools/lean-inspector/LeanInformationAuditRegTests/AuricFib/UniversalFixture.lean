import Reg.D5.S0.Diagonal.PigeonholeFiber
import Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
import Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
import LeanInformationAuditRegTests.AuricFib.CompiledFixture

namespace LeanInformationAuditRegTests.AuricFib.UniversalFixture
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
def nativeDeclared := LeanInformationAuditRegTests.AuricFib.CompiledFixture.declared
def nativeAbsent := LeanInformationAuditRegTests.AuricFib.CompiledFixture.absent
def nativeEmpirical := LeanInformationAuditRegTests.AuricFib.CompiledFixture.empirical
def nativeApex := LeanInformationAuditRegTests.AuricFib.CompiledFixture.apex
def nativeZeroCondition := LeanInformationAuditRegTests.AuricFib.CompiledFixture.zeroCondition
def nativeUnsupported := LeanInformationAuditRegTests.AuricFib.CompiledFixture.unsupported
def nativeRejected := LeanInformationAuditRegTests.AuricFib.CompiledFixture.rejected
def nativeWrongTarget := LeanInformationAuditRegTests.AuricFib.CompiledFixture.wrongTarget
def nativeParameterized := LeanInformationAuditRegTests.AuricFib.CompiledFixture.parameterized

/-- Normalization is proved, but the numeric metadata is not literal data. -/
def nativeUnavailableLaw : Application.{0,0,0,0,0,0}
    D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution where
  evidence := .native { reconstruction := .exact }
    LeanInformationAuditRegTests.AuricFib.CompiledFixture.bridge
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
    owner := `LeanInformationAuditRegTests.AuricFib.UniversalFixture
    definition := some {
      owner := `LeanInformationAuditRegTests.AuricFib.UniversalFixture
      name := `LeanInformationAuditRegTests.AuricFib.UniversalFixture.definedStatement
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
end LeanInformationAuditRegTests.AuricFib.UniversalFixture
