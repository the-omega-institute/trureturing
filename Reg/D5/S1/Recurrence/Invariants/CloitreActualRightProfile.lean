import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Invariants.CloitreActualRightProfile
import Reg.Support.DependentFamily

open _root_.D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ n => C n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => C n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ N i : ℕ, 3 ≤ N → X N i ∈ D N) ∧
    (∀ N : ℕ, 3 ≤ N → R.readout () () N = C (g N) + C (N - g N))

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  have he := hr.2 3 (by omega)
  have ha := actual_foundations.2 3 (by omega)
  change C 3 + 1 = C (g 3) + C (3 - g 3) at he
  omega

def registration : Registration arena
    ((∀ N i : ℕ, 3 ≤ N → X N i ∈ D N) ∧
      (∀ N : ℕ, 3 ≤ N → C N = C (g N) + C (N - g N))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_foundations, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact False.elim (hj (@Subsingleton.elim Unit _ j i))
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (1 : ℕ), (4 : ℕ), ?_⟩
    change C 1 ≠ C 4
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.actual_foundations) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => C n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Recurrence") "Invariants") "CloitreActualRightProfile") "actual_foundations") "Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile/Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => C n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end
end Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile
