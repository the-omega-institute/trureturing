import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Resource.VandermondeHyperbolicRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.Resource.VandermondeHyperbolicRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Resource.MinimumRetrievalTime
open _root_.D5.S3.Resource.VandermondeHyperbolicRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (model : FiniteFieldModel) : Prop :=
  @hyperbolicBound model.carrier model.field

private theorem witness_exists : ∃ model : FiniteFieldModel, ¬ predicate model := by
  classical
  exact not_forall.mp _root_.D5.S3.Resource.VandermondeHyperbolicRefutation.result

private def embed : Fin 1 → FiniteFieldModel :=
  fun _ => Classical.choose witness_exists

private def decision : ∀ witness : Fin 1, Decidable (predicate (embed witness)) :=
  fun _ => .isFalse (Classical.choose_spec witness_exists)

private def arena := WitnessArena.ofCarrier (Fin 1) FiniteFieldModel predicate embed decision
private def reads := arena.realization

private instance : DecidableEq arena.State := arena.stateDecidableEq

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩

private theorem bridge : WitnessPrimitiveRealization arena
    (¬ _root_.D5.S3.Resource.VandermondeHyperbolicRefutation.claim) reads :=
  ⟨arena.law_refutes⟩

private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law

private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{3, 3, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1} (@_root_.D5.S3.Resource.VandermondeHyperbolicRefutation.result) (type_of% (arena)) (type_of% (arena)) (type_of% (@counterexampleRealization (Fin 1) arena.check)) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (FiniteFieldModel)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "VandermondeHyperbolicRefutation") 0) "D5") "S3") "Resource") "VandermondeHyperbolicRefutation") "result") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "VandermondeHyperbolicRefutation") 0) "Reg") "D5") "S3") "Resource") "VandermondeHyperbolicRefutation") "bridge"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .witness (arena) (Reg.D5.S3.Resource.VandermondeHyperbolicRefutation.reads) (reads.toPrimitiveBundle) ⟨(bridge)⟩ (And.left (variation)),
  readout := some (@counterexampleRealization (Fin 1) arena.check),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (FiniteFieldModel),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end
end Reg.D5.S3.Resource.VandermondeHyperbolicRefutation
