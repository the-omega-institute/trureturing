import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank
import Reg.Support.DependentFamily

/-! A source-bound dependent-family audit of the actual Catalan cardinality. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank

open _root_.D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentSemantics
open _root_.D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank

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
  realize signature (fun _ _ n => (avoiders n {.p101, .p201}).ncard) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, r.readout () () n = catalan n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 0
  change 0 = catalan 0 at hz
  norm_num at hz

theorem dependence : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 0, 2, ?_⟩
  change (avoiders 0 {.p101, .p201}).ncard ≠ (avoiders 2 {.p101, .p201}).ncard
  rw [card_catalan_avoiders, card_catalan_avoiders]
  norm_num [catalan_two]

noncomputable def registration : Registration arena
    (∀ n : ℕ, (avoiders n {.p101, .p201}).ncard = catalan n) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨card_catalan_avoiders, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank.card_catalan_avoiders)
      (type_of% (realize.{0,0,0,0,0} signature
        (fun _ _ n => (avoiders n {.p101, .p201}).ncard) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank.cardinality_unit,
  realizationName := `Reg.D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ _ n => (avoiders n {.p101, .p201}).ncard) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank,
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

end Reg.D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank
