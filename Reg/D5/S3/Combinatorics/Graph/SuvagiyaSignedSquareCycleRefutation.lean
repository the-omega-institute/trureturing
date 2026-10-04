import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (m : Int) : Prop := 4 ≤ m →
  ∃ r : ℝ, IsGreatest quarticRoots r ∧ IsLeast (radiusValues (8 * m.toNat)) r

private theorem failure : ∃ m : Int, ¬ predicate m := by
  simpa only [claim, predicate, not_forall] using result

private def embed : Fin 1 → Int := fun _ => Classical.choose failure

private def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failure)

private def arena := WitnessArena.ofCarrier (Fin 1) Int
  (fun m => predicate m) (fun w => embed w) (fun w => decision w)
private def reads := arena.realization

private instance : DecidableEq arena.State := arena.stateDecidableEq

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation.result) (type_of% (arena)) (type_of% (arena)) (type_of% (@counterexampleRealization (Fin 1) arena.check)) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (Int)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Combinatorics") "Graph") "SuvagiyaSignedSquareCycleRefutation") 0) "D5") "S3") "Combinatorics") "Graph") "SuvagiyaSignedSquareCycleRefutation") "result") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Combinatorics") "Graph") "SuvagiyaSignedSquareCycleRefutation") 0) "Reg") "D5") "S3") "Combinatorics") "Graph") "SuvagiyaSignedSquareCycleRefutation") "bridge"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .witness (arena) (Reg.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation.reads) (reads.toPrimitiveBundle) ⟨(bridge)⟩ (And.left (variation)),
  readout := some (@counterexampleRealization (Fin 1) arena.check),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (Int),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end
end Reg.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation
