import LeanInformationAuditInterface.Contract.Registration
import D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (n : ℕ) : Prop :=
  6 ≤ n → ∃ d : ℕ, (graph n).ediam = (d : ℕ∞) ∧ (d : ℚ) = formula n

private theorem failedPoint : ∃ n : ℕ, ¬ predicate n :=
  not_forall.mp result

private def embed : Fin 1 → ℕ := fun _ => Classical.choose failedPoint

private def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failedPoint)

private def arena := WitnessArena.ofCarrier (Fin 1) ℕ
  (fun n => 6 ≤ n → ∃ d : ℕ, (graph n).ediam = (d : ℕ∞) ∧ (d : ℚ) = formula n)
  embed decision
private def reads := arena.realization

private instance : DecidableEq arena.State := arena.stateDecidableEq

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.result) (type_of% (arena)) (type_of% (arena)) (type_of% (@counterexampleRealization (Fin 1) arena.check)) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (Nat)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "CayleyGrowth") "ConsecutiveFourCycleDiameterRefutation") 0) "CayleyGrowth") "ConsecutiveFourCycleDiameterRefutation") "result") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "CayleyGrowth") "ConsecutiveFourCycleDiameterRefutation") 0) "Reg") "D5") "S0") "CayleyGrowth") "ConsecutiveFourCycleDiameterRefutation") "bridge"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .witness (arena) (Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.reads) (reads.toPrimitiveBundle) ⟨(bridge)⟩ (And.left (variation)),
  readout := some (@counterexampleRealization (Fin 1) arena.check),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (Nat),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end
end Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
