import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Polygons.PolygonEarContraction

/-!
The source witnesses below retain the exact dependent telescopes and actual
readouts. For these targets a DependentFamily realization still requires a
source reconstruction equivalence for the full changing ZMod/Finset domain,
a lawful enrolled readout, whole-family variation and sensitivity, and actual
observational dependence. No Contract.Registration or declared_validated
status is asserted. The unfinished targets are disclosed under issue #24755.
-/

namespace Reg.D5.S3.Geometry.Polygons.PolygonEarContraction

abbrev boundary_lift_iff_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.boundary_lift_iff)
def boundary_lift_iff_source : boundary_lift_iff_scope := @_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.boundary_lift_iff

abbrev reduce_isTriangulation_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.reduce_isTriangulation)
def reduce_isTriangulation_source : reduce_isTriangulation_scope := @_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.reduce_isTriangulation

abbrev expand_isTriangulation_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.expand_isTriangulation)
def expand_isTriangulation_source : expand_isTriangulation_scope := @_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.expand_isTriangulation

abbrev expand_reduce_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.expand_reduce)
def expand_reduce_source : expand_reduce_scope := @_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.expand_reduce

abbrev reduce_expand_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.reduce_expand)
def reduce_expand_source : reduce_expand_scope := @_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.reduce_expand

abbrev compatible_card_bound_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.compatible_card_bound)
def compatible_card_bound_source : compatible_card_bound_scope := @_root_.D5.S3.Geometry.Polygons.PolygonEarContraction.compatible_card_bound

end Reg.D5.S3.Geometry.Polygons.PolygonEarContraction

namespace Reg.D5.S3.Geometry.Polygons.PolygonEarContraction.Count
open _root_.D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Actual PolygonEarContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section

abbrev signature : Signature where
  Params := {m : ℕ // 6 ≤ m}
  State p := Finset (ZMod (p.val + 1))
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def readout (b : Bool) (p : signature.Params) (P : signature.State p) : ℕ := by
  letI : NeZero p.val := ⟨by have := p.property; omega⟩
  exact if b then P.card else (reducedCenters P).card

def actual : Realization signature := realize signature readout (fun e => nomatch e)
def intervention (i : Bool) : Realization signature :=
  realize signature (fun j p P => if j = i then (if i then 2 else 1) else readout j p P)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} [NeZero m] (hm : 6 ≤ m) {P : Finset (ZMod (m + 1))},
    1 ∈ P → R.readout false ⟨m, hm⟩ P = R.readout true ⟨m, hm⟩ P - 1

private theorem intervention_law (i : Bool) : ¬ arena.Law (intervention i) := by
  intro h
  have hh := h (m := 6) (by decide) (P := {1}) (by simp)
  cases i <;> norm_num [intervention, readout, realize, reducedCenters] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨6, by decide⟩, {1}, {1, 2}, ?_⟩
  cases i <;> simp [actual, realize, readout, reducedCenters]
  all_goals decide

def source_registration : Registration arena (type_of% @reduced_centres_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reduced_centres_card, intervention false, intervention_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law i⟩
      intro j hj
      funext p P
      simp [actual, intervention, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@reduced_centres_card)
    (Realization signature) Bool Unit := {
  unitName := `Reg.D5.S3.Geometry.Polygons.PolygonEarContraction.Count.unit
  realizationName := `Reg.D5.S3.Geometry.Polygons.PolygonEarContraction.Count.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Polygons.PolygonEarContraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false}, {
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]}
end
end Reg.D5.S3.Geometry.Polygons.PolygonEarContraction.Count

namespace Reg.D5.S3.Geometry.Polygons.PolygonEarContraction.Compatibility
open _root_.D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual PolygonEarContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section

abbrev signature : Signature where
  Params := {m : ℕ // 6 ≤ m}
  State p := Finset (ZMod (p.val + 1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def readout (_ : Unit) (p : signature.Params) (P : signature.State p) : Prop := by
  letI : NeZero p.val := ⟨by have := p.property; omega⟩
  exact Compatible (reducedCenters P)

def actual : Realization signature := realize signature readout (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} [NeZero m] (hm : 6 ≤ m) {P : Finset (ZMod (m + 1))},
    Compatible P → 1 ∈ P → R.readout () ⟨m, hm⟩ P

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (m := 6) (by decide) (P := {1}) (by simp [Compatible]) (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨6, by decide⟩, {1}, {2, 3}, ?_⟩
  change Compatible (reducedCenters ({1} : Finset (ZMod 7))) ≠
    Compatible (reducedCenters ({2, 3} : Finset (ZMod 7)))
  have good : Compatible (reducedCenters ({1} : Finset (ZMod 7))) := by
    simp [reducedCenters, Compatible]
  have bad : ¬Compatible (reducedCenters ({2, 3} : Finset (ZMod 7))) := by
    have he : reducedCenters ({2, 3} : Finset (ZMod 7)) = ({1, 2} : Finset (ZMod 6)) := by decide
    rw [he]
    intro h
    exact h (by simp : (2 : ZMod 6) ∈ ({1, 2} : Finset (ZMod 6)))
      (by simp : (1 : ZMod 6) ∈ ({1, 2} : Finset (ZMod 6))) (by decide)
      (local_crossings (by decide)).1
  intro h
  exact bad (h ▸ good)

def source_registration : Registration arena (type_of% @reduced_centres_compatible) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reduced_centres_compatible, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@reduced_centres_compatible)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Polygons.PolygonEarContraction.Compatibility.unit
  realizationName := `Reg.D5.S3.Geometry.Polygons.PolygonEarContraction.Compatibility.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Polygons.PolygonEarContraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := true}]}
  continuation := .unknown
  familyRecord := none
  options := #[]}
end
end Reg.D5.S3.Geometry.Polygons.PolygonEarContraction.Compatibility
