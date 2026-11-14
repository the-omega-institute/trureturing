import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic

/-! The initial finite-set observation in the complete guarded-toggle law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Geometry
open _root_.D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped symmDiff

noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State P := Finset P
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => (s : Set _)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (P : Type u) [PartialOrder P] (s t : Finset P),
    (s : Set P).OrdConnected → (t : Set P).OrdConnected →
    by classical exact (∃ w : List P, w.Nodup ∧ w.toFinset = s ∆ t ∧
      w.length = (s ∆ t).card ∧
      w.foldl (fun A x => RowmotionEndpointTransport.toggle x A)
        (r.readout () P s) = (t : Set P))

abbrev sourceScope := type_of% (@exists_toggle_word.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual := Iff.rfl

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  obtain ⟨w, _, _, hl, hf⟩ := h (PUnit.{u+1}) {PUnit.unit} {PUnit.unit}
    (by simpa using (Set.ordConnected_singleton (a := (PUnit.unit : PUnit.{u+1}))))
    (by simpa using (Set.ordConnected_singleton (a := (PUnit.unit : PUnit.{u+1}))))
  have hnil : w = [] := by
    cases w with
    | nil => rfl
    | cons x w => simp [Finset.symmDiff_def] at hl
  subst w
  have he := congrArg (fun S : Set PUnit.{u+1} => PUnit.unit ∈ S) hf
  simp [rejected, realize] at he

def source_registration : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp exists_toggle_word, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨PUnit.{u+1}, ∅, {PUnit.unit}, ?_⟩
    intro he
    have hh := congrArg (fun S : Set PUnit.{u+1} => PUnit.unit ∈ S) he
    simp [actual, realize] at hh

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_toggle_word.{u}) (Realization signature.{u}) (Type u → Type u) Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic.unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ s => (s : Set _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Finset.{u})
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic
