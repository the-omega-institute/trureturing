import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.HartRowleyGreedyRefutation
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.HartRowleyGreedyRefutation

namespace Reg.D5.S3.FiniteGroups.HartRowleyGreedyRefutation

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := P
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role _ p => if role then invLength p else system.length p)
    (fun e => nomatch e)

def rejectLeft : Realization signature :=
  realize signature (fun role _ p => if role then invLength p else system.length p + 1)
    (fun e => nomatch e)

def rejectRight : Realization signature :=
  realize signature (fun role _ p => if role then invLength p + 1 else system.length p)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ p, r.readout false () p = r.readout true () p

private theorem rejectLeft_law : ¬ arena.Law rejectLeft := by
  intro h
  have he := h 1
  change system.length 1 + 1 = invLength 1 at he
  rw [length_eq] at he
  omega

private theorem rejectRight_law : ¬ arena.Law rejectRight := by
  intro h
  have he := h 1
  change system.length 1 = invLength 1 + 1 at he
  rw [length_eq] at he
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 1, adjacent 0, ?_⟩
  cases role
  · change system.length 1 ≠ system.length (adjacent 0)
    rw [length_eq, length_eq]
    decide
  · change invLength 1 ≠ invLength (adjacent 0)
    decide

def lengthSourceRegistration : Registration arena
    (∀ p : P, system.length p = invLength p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨length_eq, rejectLeft, rejectLeft_law⟩
  sensitivity := by
    constructor
    · intro role
      cases role
      · refine ⟨rejectLeft, ?_, rfl, rejectLeft_law⟩
        intro j hj
        cases j
        · exact False.elim (hj rfl)
        · rfl
      · refine ⟨rejectRight, ?_, rfl, rejectRight_law⟩
        intro j hj
        cases j
        · rfl
        · exact False.elim (hj rfl)
    · intro e
      exact nomatch e
  dependence := dependence

def lengthRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FiniteGroups.HartRowleyGreedyRefutation.length_eq)
      (type_of% (realize signature
        (fun role (_ : Unit) p => if role then invLength p else system.length p)
        (fun e => nomatch e)))
      P Unit := {
  unitName :=
    `D5.S3.FiniteGroups.HartRowleyGreedyRefutation.length_eq.reg.__information_unit,
  realizationName :=
    `Reg.D5.S3.FiniteGroups.HartRowleyGreedyRefutation.lengthSourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨lengthSourceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun role (_ : Unit) p => if role then invLength p else system.length p)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.HartRowleyGreedyRefutation,
    definition := none,
    coordinates := #[],
    readouts := #[
      { path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := none, booleanPredicate := false },
      { path := #["body", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.FiniteGroups.HartRowleyGreedyRefutation
