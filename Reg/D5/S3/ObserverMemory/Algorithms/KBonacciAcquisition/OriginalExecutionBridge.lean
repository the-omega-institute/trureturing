import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalExecutionBridge
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

local notation "scannedRecord" =>
  (fun (k : ℕ) (hk : 0 < k) (w : List Bool) =>
    Option.map
      (fun tail => LiveRecord.mk (NarrowWindowCost.value k 0 w)
        (List.length w : ZMod (k + 1)) (Fin.val tail))
      (PartialDFA.eval (NarrowWindowCost.scanner k hk) w))

/-- Equality is observed as a function on data. Every source assumption stays in Law. -/
@[reducible] def recordSignature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State k := Option (LiveRecord k)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Option (LiveRecord k) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def recordActual : Realization recordSignature :=
  realize recordSignature (fun _ _ q r => q = r) (fun e => nomatch e)

def recordRejected : Realization recordSignature :=
  realize recordSignature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Dependence is existential in the whole family, with no per-fiber variation claim. -/
theorem recordDependence : ObservationalDependence recordSignature recordActual := by
  intro i
  refine ⟨2, none, some ⟨0,0,0⟩, ?_⟩
  intro h
  have atNone := congrFun h none
  change ((none : Option (LiveRecord 2)) = none) =
    ((some ⟨0,0,0⟩ : Option (LiveRecord 2)) = none) at atNone
  have impossible : (some ⟨0,0,0⟩ : Option (LiveRecord 2)) = none := atNone ▸ rfl
  cases impossible

@[reducible] def recordAppendArena : Arena.{0,0,0,0,0} where
  signature := recordSignature
  Law R := ∀ (k : ℕ) (hk : 2 ≤ k) (w b : List Bool),
    R.readout () k (scannedRecord k (by omega) (w++b))
      (runWord (bitUpdate k) b (scannedRecord k (by omega) w))

theorem recordAppendPositive : recordAppendArena.Law recordActual := record_append

theorem recordAppendNegative : ¬ recordAppendArena.Law recordRejected := by
  intro law
  exact law 2 (by decide) [] []

def recordAppendEvidence : Registration recordAppendArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.record_append)) where
  actual := recordActual
  bridge := Iff.rfl
  variation := ⟨recordAppendPositive, recordRejected, recordAppendNegative⟩
  sensitivity := ⟨fun i => ⟨recordRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, recordAppendNegative⟩,
    fun i => nomatch i⟩
  dependence := recordDependence

noncomputable def recordAppendRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.record_append)
      (type_of% (realize recordSignature recordActual.readout recordActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.record_append
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge/recordAppendArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.recordAppendEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨recordAppendArena⟩, objectArena := .source ⟨recordAppendArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source recordAppendArena ⟨recordAppendEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize recordSignature recordActual.readout recordActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

@[reducible] def outputSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := Option (ZMod 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (ZMod 2) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def outputActual : Realization outputSignature :=
  realize outputSignature (fun _ _ q r => q = r) (fun e => nomatch e)

def outputRejected : Realization outputSignature :=
  realize outputSignature (fun _ _ _ _ => False) (fun e => nomatch e)

@[reducible] def outputArena : Arena.{0,0,0,0,0} where
  signature := outputSignature
  Law R := ∀ (k : ℕ) (hk : 0 < k) (w : List Bool),
    R.readout () () (NarrowWindowCost.output k hk w)
      (endpointReading (scannedRecord k hk w))

theorem outputPositive : outputArena.Law outputActual := output_record

theorem outputNegative : ¬ outputArena.Law outputRejected := by
  intro law
  exact law 1 (by decide) []

def outputEvidence : Registration outputArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.output_record)) where
  actual := outputActual
  bridge := Iff.rfl
  variation := ⟨outputPositive, outputRejected, outputNegative⟩
  sensitivity := ⟨fun i => ⟨outputRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, outputNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), none, some 0, ?_⟩
    intro h
    have atNone := congrFun h none
    change ((none : Option (ZMod 2)) = none) =
      ((some 0 : Option (ZMod 2)) = none) at atNone
    have impossible : (some 0 : Option (ZMod 2)) = none := atNone ▸ rfl
    cases impossible

noncomputable def outputRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.output_record)
      (type_of% (realize outputSignature outputActual.readout outputActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.output_record
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge/outputArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.outputEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨outputArena⟩, objectArena := .source ⟨outputArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source outputArena ⟨outputEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize outputSignature outputActual.readout outputActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

/-- The original label universe is rigid; empty and subsingleton labels remain in Law. -/
@[reducible] def executeSignature : Signature.{z+1,z,0,z,0} where
  Params := Type z
  State Y := Option (Y × ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ Y := Option (Y × ℕ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def executeActual : Realization executeSignature.{z} :=
  realize executeSignature (fun _ _ q r => q = r) (fun e => nomatch e)

def executeRejected : Realization executeSignature.{z} :=
  realize executeSignature (fun _ _ _ _ => False) (fun e => nomatch e)

@[reducible] def executeArena : Arena.{z+1,z,0,z,0} where
  signature := executeSignature.{z}
  Law R := ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ) (w : List Bool)
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m),
    R.readout () Y (NarrowWindowCost.execute k (by omega) π d w y₀ archive)
      (NativeExecute π d (scannedRecord k (by omega) w) y₀ archive)

theorem executePositive : executeArena.{z}.Law executeActual := @execute_same.{z}

theorem executeNegative : ¬ executeArena.{z}.Law executeRejected := by
  intro law
  exact law (Y := ULift.{z} Unit) 2 0 (by decide)
    (fun _ _ => Sum.inl (ULift.up ())) 0 [] none []

def executeEvidence : Registration executeArena.{z}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.execute_same.{z})) where
  actual := executeActual
  bridge := Iff.rfl
  variation := ⟨executePositive, executeRejected, executeNegative⟩
  sensitivity := ⟨fun i => ⟨executeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, executeNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨ULift.{z} Unit, none, some (ULift.up (), 0), ?_⟩
    intro h
    have atNone := congrFun h none
    change ((none : Option (ULift.{z} Unit × ℕ)) = none) =
      ((some (ULift.up (), 0) : Option (ULift.{z} Unit × ℕ)) = none) at atNone
    have impossible : (some (ULift.up (), 0) : Option (ULift.{z} Unit × ℕ)) = none :=
      atNone ▸ rfl
    cases impossible

noncomputable def executeRegistration :
    LeanInformationAudit.Contract.Registration.{z+1,0,1,0,0,0,z+1,z,0,z,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.execute_same.{z})
      (type_of% (realize executeSignature.{z} executeActual.readout executeActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.execute_same
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge/executeArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.executeEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨executeArena.{z}⟩, objectArena := .source ⟨executeArena.{z}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source executeArena.{z} ⟨executeEvidence.{z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize executeSignature.{z} executeActual.readout executeActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

@[reducible] def recordHistoryArena : Arena.{0,0,0,0,0} where
  signature := recordSignature
  Law R := ∀ (k m : ℕ) (hk : 2 ≤ k) (localAlphabet : Bool)
    (history : List (AllowedBlock k m localAlphabet)),
    R.readout () k
      (scannedRecord k (by omega) (history.flatMap (fun action => List.ofFn action.val)))
      (historyRecord history)

theorem recordHistoryPositive : recordHistoryArena.Law recordActual := record_history

theorem recordHistoryNegative : ¬ recordHistoryArena.Law recordRejected := by
  intro law
  exact law 2 0 (by decide) false []

def recordHistoryEvidence : Registration recordHistoryArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.record_history)) where
  actual := recordActual
  bridge := Iff.rfl
  variation := ⟨recordHistoryPositive, recordRejected, recordHistoryNegative⟩
  sensitivity := ⟨fun i => ⟨recordRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, recordHistoryNegative⟩,
    fun i => nomatch i⟩
  dependence := recordDependence

noncomputable def recordHistoryRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.record_history)
      (type_of% (realize recordSignature recordActual.readout recordActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.record_history
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge/recordHistoryArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.recordHistoryEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨recordHistoryArena⟩, objectArena := .source ⟨recordHistoryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source recordHistoryArena ⟨recordHistoryEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize recordSignature recordActual.readout recordActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms recordAppendEvidence
#print axioms recordAppendRegistration
#print axioms outputEvidence
#print axioms outputRegistration
#print axioms executeEvidence
#print axioms executeRegistration
#print axioms recordHistoryEvidence
#print axioms recordHistoryRegistration

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge
