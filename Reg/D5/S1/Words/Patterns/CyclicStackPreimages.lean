import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace FibreCountAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount

theorem dependence : ObservationalDependence EvenFibre.signature EvenFibre.actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [EvenFibre.actual, EvenFibre.signature, singleObservation, realize]
  exact _root_.Reg.Support.CyclicStackFamily.fibre_distinct_of_member
    (m := 0) (n := 2) (word := [])
    (List.mem_filter.mpr ⟨List.mem_permutations.mpr (List.Perm.refl []), rfl⟩)
    (by decide)

theorem rejected_law : ¬ FibreCount.arena.Law EvenFibre.rejected := by
  intro h
  have h := @h 2 (by decide)
  have h := h.1
  change (0 : ℕ) = 1 at h
  cases h

def registration : Registration FibreCount.arena (∀ (m : ℕ) (hm : 2 ≤ m),
    (fibre (2 * m)).length = 1 ∧ (fibre (2 * m + 1)).length = m + 1) where
  actual := EvenFibre.actual
  bridge := Iff.rfl
  variation := ⟨@zhan_bie_conjectures_3_4, EvenFibre.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.zhan_bie_conjectures_3_4) (type_of% (FibreCount.arena)) (type_of% (FibreCount.arena)) (type_of% (realize.{0, 0, 0, 0, 0} EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "zhan_bie_conjectures_3_4") "Reg.D5.S1.Words.Patterns.CyclicStackPreimages/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(FibreCount.arena)⟩,
  objectArena := ⟨(FibreCount.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (FibreCount.arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimages, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end FibreCountAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimages
