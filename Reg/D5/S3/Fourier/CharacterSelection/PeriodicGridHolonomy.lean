import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
open LeanInformationAudit
open Lean Meta

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N + 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (M N : ℕ) [NeZero M] [NeZero N],
    Fintype.card {y : EdgeLabel M N // Flat y} = R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N _ _
  simpa [actual, realize, signature] using flat_label_card M N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1
  have hc := flat_label_card 1 1
  change Fintype.card {y : EdgeLabel 1 1 // Flat y} = 0 at hh
  rw [hc] at hh
  exact (by decide : 2 ^ (1 * 1 + 1) ≠ 0) hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change (2 ^ (1 * 1 + 1) : ℕ) ≠ 2 ^ (1 * 2 + 1)
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_label_card) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N + 1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridHolonomy") "flat_label_card") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N + 1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_label_card, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.anchorEnumeration }


def dimensionActual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => M * N + 1) (fun e => nomatch e)

def dimensionRejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0) (fun e => nomatch e)

def dimensionArena : Arena where
  signature := signature
  Law R := ∀ (M N : ℕ) [NeZero M] [NeZero N],
    Module.finrank (ZMod 2) (LinearMap.range (plaquetteLinear M N)) = M * N - 1 ∧
    Module.finrank (ZMod 2) (flatSubspace M N) = R.readout () M N ∧
    0 < (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) ∧
    0 < (Fintype.card (EdgeLabel M N) : ℚ) ∧
    (Fintype.card {y : EdgeLabel M N //
      ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} : ℚ) /
        (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) = 1 / 4 ∧
    (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) /
        (Fintype.card (EdgeLabel M N) : ℚ) =
          1 / (2 : ℚ) ^ (M * N - 1) ∧
    (Fintype.card {y : EdgeLabel M N //
      ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} : ℚ) /
        (Fintype.card (EdgeLabel M N) : ℚ) =
          1 / (2 : ℚ) ^ (M * N + 1)

theorem dimension_actual_law : dimensionArena.Law dimensionActual := by
  intro M N _ _
  simpa [dimensionArena, dimensionActual, realize, signature] using
    periodic_grid_linear_statistics M N

theorem dimension_rejected_law : ¬ dimensionArena.Law dimensionRejected := by
  intro h
  have hh := (h 1 1).2.1
  have hc := (periodic_grid_linear_statistics 1 1).2.1
  change Module.finrank (ZMod 2) (flatSubspace 1 1) = 0 at hh
  norm_num at hc
  omega

theorem dimension_sensitivity_proof : Sensitivity dimensionArena dimensionActual := by
  constructor
  · intro i
    refine ⟨dimensionRejected, ?_, rfl, dimension_rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dimension_dependence_proof : ObservationalDependence signature dimensionActual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  norm_num [dimensionActual, realize, signature]

def dimensionRegistration : Registration dimensionArena (dimensionArena.Law dimensionActual) where
  actual := dimensionActual
  bridge := Iff.rfl
  variation := ⟨dimension_actual_law, dimensionRejected, dimension_rejected_law⟩
  sensitivity := dimension_sensitivity_proof
  dependence := dimension_dependence_proof

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.periodic_grid_linear_statistics) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => M * N + 1)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridHolonomy") "periodic_grid_linear_statistics") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(dimensionArena)⟩,
  objectArena := .source ⟨(dimensionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (dimensionArena) ⟨(dimensionRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => M * N + 1)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.periodic_grid_linear_statistics, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.anchorEnumeration }


namespace HolonomyConstant

abbrev signature : Signature where
  Params := Σ M : ℕ, Σ N : ℕ, EdgeLabel M N
  State := fun p => Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => rowHolonomy p.2.2 i)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (hy : Flat y),
    (∀ i, R.readout () ⟨M, N, y⟩ i = rowHolonomy y 0) ∧
      (∀ j, columnHolonomy y j = columnHolonomy y 0)

theorem actual_law : arena.Law actual := by
  intro M N _ _ y hy
  simpa [actual, realize, signature] using flat_holonomy_constant y hy

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let y : EdgeLabel 1 1 := ⟨fun _ _ => 0, fun _ _ => 0⟩
  have hy : Flat y := by intro i j; simp [plaquette, y]
  have hh := (h y hy).1 0
  norm_num [rejected, realize, rowHolonomy, y] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨2, 1, ⟨(fun i _ => if i = 0 then 0 else 1), fun _ _ => 0⟩⟩,
    0, 1, ?_⟩
  norm_num [actual, realize, rowHolonomy]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_holonomy_constant) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p i => rowHolonomy p.2.2 i)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridHolonomy") "flat_holonomy_constant") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p i => rowHolonomy p.2.2 i)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, definition := none, coordinates := #[0, 1, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_holonomy_constant, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.anchorEnumeration }


end HolonomyConstant

namespace EdgeCardinality

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (2 * M * N))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ M N : ℕ, Fintype.card (EdgeLabel M N) = R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N
  simpa [actual, realize, signature] using edge_label_card M N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1
  rw [edge_label_card] at hh
  norm_num [rejected, realize, signature] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.edge_label_card) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (2 * M * N))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridHolonomy") "edge_label_card") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (2 * M * N))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.edge_label_card, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.anchorEnumeration }


end EdgeCardinality

namespace AnchoredVertexCard

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ M N : ℕ, [NeZero M] → [NeZero N] →
    Fintype.card {x : Fin M → Fin N → ZMod 2 // x 0 0 = 0} = R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N _ _
  simpa [actual, realize, signature] using anchored_vertex_card M N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : NeZero 1 := inferInstance
  have hh := h 1 1
  rw [anchored_vertex_card] at hh
  norm_num [rejected, realize, signature] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨2, 0, 1, ?_⟩
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_5 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.anchored_vertex_card) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridHolonomy") "anchored_vertex_card") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.anchored_vertex_card, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.anchorEnumeration }


end AnchoredVertexCard

namespace HolonomySectorCard

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (M N : ℕ) [NeZero M] [NeZero N] (h v : ZMod 2),
    Fintype.card {y : EdgeLabel M N // Flat y ∧ rowHolonomy y 0 = h ∧
      columnHolonomy y 0 = v} = R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N _ _ h v
  simpa [actual, realize, signature] using holonomy_sector_card M N h v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 0 0
  rw [holonomy_sector_card] at hh
  norm_num [rejected, realize, signature] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨2, 0, 1, ?_⟩
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_6 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.holonomy_sector_card) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridHolonomy") "holonomy_sector_card") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.holonomy_sector_card, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.anchorEnumeration }


end HolonomySectorCard

namespace ExactLabelCard

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (M N : ℕ) [NeZero M] [NeZero N],
    Fintype.card {y : EdgeLabel M N // ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} =
      R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N _ _
  simpa [actual, realize, signature] using exact_label_card M N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1
  rw [exact_label_card] at hh
  norm_num [rejected, realize, signature] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨2, 0, 1, ?_⟩
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_7 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.exact_label_card) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridHolonomy") "exact_label_card") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.exact_label_card, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.anchorEnumeration }


end ExactLabelCard

namespace SeamHolonomy

abbrev signature : Signature where
  Params := Σ M : ℕ, Σ N : ℕ, ZMod 2
  State := fun _ => ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M N : ℕ} [NeZero M] [NeZero N] (h v : ZMod 2),
    (∀ i, rowHolonomy (seam (M := M) (N := N) h v) i = h) ∧
      (∀ j, columnHolonomy (seam (M := M) (N := N) h v) j =
        R.readout () ⟨M, N, h⟩ v)

theorem actual_law : arena.Law actual := by
  intro M N _ _ h v
  simpa [actual, realize, signature] using seam_holonomy h v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (M := 1) (N := 1) 0 1).2 0
  norm_num [rejected, realize, seam, columnHolonomy] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, 1, 0⟩, 0, 1, ?_⟩
  exact zero_ne_one

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_8 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.seam_holonomy) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ v => v) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridHolonomy") "seam_holonomy") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ v => v) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, definition := none, coordinates := #[0, 1, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.seam_holonomy, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.anchorEnumeration }


end SeamHolonomy

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof
#print axioms dimension_actual_law
#print axioms dimension_rejected_law
#print axioms dimension_sensitivity_proof
#print axioms dimension_dependence_proof
#print axioms HolonomyConstant.registration
#print axioms EdgeCardinality.registration
#print axioms AnchoredVertexCard.registration
#print axioms HolonomySectorCard.registration
#print axioms ExactLabelCard.registration
#print axioms SeamHolonomy.registration

end Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionArena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionArena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.arena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"seam_holonomy\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.seam_holonomy, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.observation0 : {M N : Nat} →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] →
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
      (h v : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        (j : Fin N) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.signature PUnit.unit.{1}
            (@Sigma.mk.{0, 0} Nat
              (fun (M : Nat) =>
                @Sigma.{0, 0} Nat fun (N : Nat) => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              M
              (@Sigma.mk.{0, 0} Nat
                (fun (N : Nat) => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) N h)) :=
  fun {M N : Nat} [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N]
    (h v : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (j : Fin N) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (M : Nat) =>
        @Sigma.{0, 0} Nat fun (N : Nat) => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      M
      (@Sigma.mk.{0, 0} Nat (fun (N : Nat) => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) N h))
    v

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"seam_holonomy\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.seam_holonomy, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"seam_holonomy\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.seam_holonomy, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"SeamHolonomy\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.SeamHolonomy.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.arena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"exact_label_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.exact_label_card, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.observation0 : (M N : Nat) →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] →
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature PUnit.unit.{1} M :=
  fun (M N : Nat) [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.actual PUnit.unit.{1} M N

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"exact_label_card\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.exact_label_card, part := .type, path := [.body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"exact_label_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.exact_label_card, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"ExactLabelCard\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.ExactLabelCard.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.arena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"edge_label_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.edge_label_card, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.observation0 : (M N : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature PUnit.unit.{1} M :=
  fun (M N : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.actual PUnit.unit.{1} M N

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"edge_label_card\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.edge_label_card, part := .type, path := [.body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"edge_label_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.edge_label_card, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"EdgeCardinality\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeCardinality.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionArena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionRegistration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"periodic_grid_linear_statistics\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.periodic_grid_linear_statistics, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionRegistration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.observation0 : (M N : Nat) →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] →
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature PUnit.unit.{1} M :=
  fun (M N : Nat) [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionActual PUnit.unit.{1} M N

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"periodic_grid_linear_statistics\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.periodic_grid_linear_statistics, part := .type, path := [.body, .body, .body, .body, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"periodic_grid_linear_statistics\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.periodic_grid_linear_statistics, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionRegistration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionRegistration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionRegistration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"dimensionRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.dimensionRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.arena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"flat_holonomy_constant\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_holonomy_constant, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.observation0 : {M N : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] →
    [inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
      (y : D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeLabel M N) →
        (hy : @D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.Flat M N inst inst_1 y) →
          (i : Fin M) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat
                (fun (M : Nat) =>
                  @Sigma.{0, 0} Nat fun (N : Nat) =>
                    D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeLabel M N)
                M
                (@Sigma.mk.{0, 0} Nat
                  (fun (N : Nat) => D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeLabel M N) N y)) :=
  fun {M N : Nat} [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N]
    (y : D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeLabel M N)
    (hy : @D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.Flat M N inst inst_1 y) (i : Fin M) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (M : Nat) =>
        @Sigma.{0, 0} Nat fun (N : Nat) => D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeLabel M N)
      M
      (@Sigma.mk.{0, 0} Nat (fun (N : Nat) => D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeLabel M N) N y))
    i

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"flat_holonomy_constant\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_holonomy_constant, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"flat_holonomy_constant\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_holonomy_constant, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomyConstant\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomyConstant.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.arena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"holonomy_sector_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.holonomy_sector_card, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.observation0 : (M N : Nat) →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] →
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
      (h v : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature PUnit.unit.{1} M :=
  fun (M N : Nat) [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N]
    (h v : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.actual PUnit.unit.{1} M N

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"holonomy_sector_card\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.holonomy_sector_card, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"holonomy_sector_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.holonomy_sector_card, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"HolonomySectorCard\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.HolonomySectorCard.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.arena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"anchored_vertex_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.anchored_vertex_card, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.observation0 : (M N : Nat) →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] →
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature PUnit.unit.{1} M :=
  fun (M N : Nat) [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.actual PUnit.unit.{1} M N

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"anchored_vertex_card\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.anchored_vertex_card, part := .type, path := [.body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"anchored_vertex_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.anchored_vertex_card, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"AnchoredVertexCard\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.AnchoredVertexCard.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.arena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"flat_label_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_label_card, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.observation0 : (M N : Nat) →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] →
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature PUnit.unit.{1} M :=
  fun (M N : Nat) [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.actual PUnit.unit.{1} M N

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"flat_label_card\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_label_card, part := .type, path := [.body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"flat_label_card\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_label_card, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridHolonomy\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
