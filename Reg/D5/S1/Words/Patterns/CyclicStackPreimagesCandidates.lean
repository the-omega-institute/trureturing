import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace OddFibreAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre

theorem dependence : ObservationalDependence OddFibre.signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [OddFibre.actual, OddFibre.signature, singleObservation, realize]
  exact _root_.Reg.Support.CyclicStackFamily.fibre_distinct_of_member
    (m := 1) (n := 3) (word := [1])
    (List.mem_filter.mpr ⟨List.mem_permutations.mpr (List.Perm.refl [1]), rfl⟩)
    (by decide)

theorem rejected_law : ¬ OddFibre.arena.Law rejected := by
  intro h
  have h := @h 1 (by decide)
  change 2 ≤ 0 at h
  omega

def registration : Registration OddFibre.arena (∀ (m : ℕ) (hm : 0 < m),
    m + 1 ≤ (fibre (2 * m + 1)).length) where
  actual := OddFibre.actual
  bridge := Iff.rfl
  variation := ⟨@oddCandidate_lower_bound, OddFibre.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.oddCandidate_lower_bound) (type_of% (realize.{0, 0, 0, 0, 0} OddFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m + 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "oddCandidate_lower_bound") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(OddFibre.arena)⟩,
  objectArena := .source ⟨(OddFibre.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (OddFibre.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} OddFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m + 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end OddFibreAudit

namespace EvenFibreAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre

theorem dependence : ObservationalDependence EvenFibre.signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [EvenFibre.actual, EvenFibre.signature, singleObservation, realize]
  exact _root_.Reg.Support.CyclicStackFamily.fibre_distinct_of_member
    (m := 0) (n := 2) (word := [])
    (List.mem_filter.mpr ⟨List.mem_permutations.mpr (List.Perm.refl []), rfl⟩)
    (by decide)

theorem rejected_law : ¬ EvenFibre.arena.Law rejected := by
  intro h
  have h := @h 1 (by decide)
  change 1 ≤ 0 at h
  omega

def registration : Registration EvenFibre.arena (∀ (m : ℕ) (hm : 0 < m),
    1 ≤ (fibre (2 * m)).length) where
  actual := EvenFibre.actual
  bridge := Iff.rfl
  variation := ⟨@evenCandidate_lower_bound, EvenFibre.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.evenCandidate_lower_bound) (type_of% (realize.{0, 0, 0, 0, 0} EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "evenCandidate_lower_bound") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(EvenFibre.arena)⟩,
  objectArena := .source ⟨(EvenFibre.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (EvenFibre.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end EvenFibreAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates
