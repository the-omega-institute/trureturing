import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation

noncomputable section

open LeanInformationAudit Matrix Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

private def predicate (η : ℝ) : Prop :=
  0 < η → ∀ (n q L : ℕ) (A : Fin n → Matrix (Fin q) (Fin q) ℝ)
    (ρ : (Fin n → ℤ) →+ (Fin L → ZMod 2)),
    0 < q → (∀ j, (A j).PosSemidef) → (∑ j, A j).PosDef →
    ∀ (m : ℕ) (V : Fin m → Fin n → ℕ) (ε : Fin m → ℤ) (u : Fin n → ℕ),
      evenIndex ρ (Matrix.vecMul (fun _ => 1) V) → (∀ i, ε i = 1 ∨ ε i = -1) →
      (∀ j, 0 < u j) → evenIndex ρ u → 0 ≤ pggSum A ρ V ε u η

private theorem failure : ∃ η, ¬ predicate η := not_forall.mp result

private noncomputable def embed : Fin 1 → ℝ := fun _ => Classical.choose failure

private noncomputable def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failure)

private noncomputable def arena := WitnessArena.ofCarrier (Fin 1) ℝ predicate embed decision
private def reads := counterexampleRealization (fun _ : Fin 1 => false)

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation.result) (type_of% (arena)) (type_of% (arena)) (type_of% (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (Real)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "StatisticalMechanics") "PaddedGinibreNonHalfIntegerRefutation") 0) "D5") "S3") "StatisticalMechanics") "PaddedGinibreNonHalfIntegerRefutation") "result") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "StatisticalMechanics") "PaddedGinibreNonHalfIntegerRefutation") 0) "Reg") "D5") "S3") "StatisticalMechanics") "PaddedGinibreNonHalfIntegerRefutation") "bridge"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .witness (arena) (Reg.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation.reads) (reads.toPrimitiveBundle) ⟨(bridge)⟩ (And.left (variation)),
  readout := some (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (Real),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end

end Reg.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation
