import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.XorTriangle.ReversibleSideMap
import Reg.Support.DependentFamily

/-! Source-bound registration of the full finite-row three-turn identity. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.XorTriangle.ValueOne
open _root_.D5.S3.Combinatorics.XorTriangle.ReversibleSideMap

namespace Reg.D5.S3.Combinatorics.XorTriangle.ReversibleSideMap

abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ xs => rightEdge (rightEdge (rightEdge xs)))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ xs, r.readout () () xs = xs

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h [true]
  change ([] : List Bool) = [true] at he
  cases he

def sourceRegistration : Registration arena
    (∀ xs : List Bool, rightEdge (rightEdge (rightEdge xs)) = xs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rightEdge_cube, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro ⟨⟩
    refine ⟨(), [], [true], ?_⟩
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.XorTriangle.ReversibleSideMap.rightEdge_cube)
    (type_of% (realize signature (fun _ _ xs => rightEdge (rightEdge (rightEdge xs)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.XorTriangle.ReversibleSideMap.rightEdge_cube.__information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.XorTriangle.ReversibleSideMap.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ _ xs => rightEdge (rightEdge (rightEdge xs))) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.XorTriangle.ReversibleSideMap,
    definition := none,
    coordinates := #[],
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.XorTriangle.ReversibleSideMap
