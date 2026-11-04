import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix
import Reg.Support.DependentFamily

/-! # A palette-operand audit of the exact infinite-path palette -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix
open _root_.D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ t => t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 5) (fun e => nomatch e)

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law r := Q 5 ∧ ∀ t : ℕ, Q (r.readout () () t) → 5 ≤ t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have := h.2 0 result.1
  omega

noncomputable def source_registration : Registration arena (Q 5 ∧ ∀ t : ℕ, Q t → 5 ≤ t) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    exact ⟨(), 0, 1, by decide⟩

noncomputable def registration :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix.result)
    (type_of% (realize signature (fun _ _ t => t) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str ``result "__information_unit",
  realizationName := ``source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ t => t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["arg", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix
