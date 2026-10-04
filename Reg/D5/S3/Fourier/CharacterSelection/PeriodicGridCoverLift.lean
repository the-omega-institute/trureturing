import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
open _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
open LeanInformationAudit
open Lean Meta

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℤ → ℤ → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ → ℤ → ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (_hM : 3 ≤ M) (_hN : 3 ≤ N) (y : EdgeLabel M N) (_hy : Flat y)
      (a : ZMod 2),
    ∃! x : ℤ → ℤ → ZMod 2, IsCoverLift y a (R.readout () () x)

theorem actual_law : arena.Law actual := by
  intro M N _ _ hM hN y hy a
  simpa [actual, realize, signature] using flat_unique_cover_lift hM hN y hy a

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  let y : EdgeLabel 3 3 := seam 0 0
  have hy : Flat y := seam_flat 0 0
  obtain ⟨x, hx, _⟩ := hr (by omega : 3 ≤ 3) (by omega : 3 ≤ 3) y hy 1
  have h := hx.1
  change (0 : ZMod 2) = 1 at h
  exact (by decide : (0 : ZMod 2) ≠ 1) h

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
  refine ⟨(), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro he
  have h := congrArg (fun f : ℤ → ℤ → ZMod 2 => f 0 0) he
  change (0 : ZMod 2) = 1 at h
  exact (by decide : (0 : ZMod 2) ≠ 1) h

def registration : Registration arena
    (∀ {M N : ℕ} [NeZero M] [NeZero N]
      (_hM : 3 ≤ M) (_hN : 3 ≤ N) (y : EdgeLabel M N) (_hy : Flat y)
      (a : ZMod 2), ∃! x : ℤ → ℤ → ZMod 2, IsCoverLift y a x) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.flat_unique_cover_lift) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridCoverLift") "flat_unique_cover_lift") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
