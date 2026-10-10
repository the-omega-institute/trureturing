import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.LatticeWalkNearMaximalArea
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.LatticeWalkNearMaximalArea
open _root_.D5.S3.Combinatorics.LatticeWalkNearMaximalArea

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => a029552 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n k : ℕ, k < n →
    walkCount (2 * n) ((n : ℤ) ^ 2 - k) = 2 * r.readout () () k ∧
      walkCount (2 * n + 1) ((n : ℤ) ^ 2 + n - k) = 4 * a098613 k

theorem a029552_zero : a029552 0 = 1 := by
  simp [a029552, partitionCount]

theorem a029552_one : a029552 1 = 3 := by
  norm_num [a029552, partitionCount, Finset.filter_singleton]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have original := (_root_.D5.S3.Combinatorics.LatticeWalkNearMaximalArea.result 1 0 (by decide)).1
  rw [a029552_zero] at original
  have zero := (h 1 0 (by decide)).1
  change walkCount (2 * 1) ((1 : ℤ) ^ 2 - 0) = 0 at zero
  exact (by decide : (2 : ℕ) ≠ 0) (original.symm.trans zero)

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 0, 1, ?_⟩
  change a029552 0 ≠ a029552 1
  rw [a029552_zero, a029552_one]
  decide

noncomputable def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.LatticeWalkNearMaximalArea.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.LatticeWalkNearMaximalArea.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => a029552 n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "LatticeWalkNearMaximalArea") "result") "Reg.D5.S3.Combinatorics.LatticeWalkNearMaximalArea/Reg.D5.S3.Combinatorics.LatticeWalkNearMaximalArea.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.LatticeWalkNearMaximalArea.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => a029552 n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.LatticeWalkNearMaximalArea, definition := some { owner := `D5.S3.Combinatorics.LatticeWalkNearMaximalArea, name := `D5.S3.Combinatorics.LatticeWalkNearMaximalArea.claim, path := #[] }, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.Combinatorics.LatticeWalkNearMaximalArea
