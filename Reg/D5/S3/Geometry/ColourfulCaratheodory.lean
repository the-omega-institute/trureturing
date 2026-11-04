import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.ColourfulCaratheodory
import Reg.Support.DependentFamily

open Set
open LeanInformationAudit
open _root_.D5.S3.Geometry.ColourfulCaratheodory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Geometry.ColourfulCaratheodory
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State d := Set (EuclideanSpace ℝ (Fin d))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Set (EuclideanSpace ℝ (Fin d))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => convexHull ℝ S) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (p : EuclideanSpace ℝ (Fin d))
    (S : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d))),
    (∀ i, p ∈ R.readout () d (S i)) →
    ∃ f : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, f i ∈ S i) ∧ p ∈ convexHull ℝ (Set.range f)

theorem bridge : (type_of% (@colourful_caratheodory)) ↔ arena.Law actual := by
  constructor <;> intro h d p S hS <;> exact h p S hS

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, hf, _⟩ := h (d := 0) 0 (fun _ => ∅) (fun _ => Set.mem_univ _)
  exact hf 0

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, ∅, {0}, ?_⟩
  change convexHull ℝ (∅ : Set (EuclideanSpace ℝ (Fin 0))) ≠ convexHull ℝ {0}
  simp

def familyRegistration : Registration arena (type_of% (@colourful_caratheodory)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @colourful_caratheodory, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@colourful_caratheodory)
    (type_of% (realize signature (fun _ _ S => convexHull ℝ S) (fun a => nomatch a)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.ColourfulCaratheodory.colourful_caratheodory.hulls,
  realizationName := `Reg.D5.S3.Geometry.ColourfulCaratheodory.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ S => convexHull ℝ S) (fun a => nomatch a)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.ColourfulCaratheodory,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Geometry.ColourfulCaratheodory
