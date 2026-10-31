import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

namespace Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
open _root_.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section
universe u
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- One cardinality observation, on arbitrary finite families over any carrier. -/
abbrev signature : Signature where
  Params := Type u
  State α := Finset (Finset α)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ F => F.card) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the two rank-layer cardinalities vary; every original hypothesis remains. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [Fintype α] [DecidableEq α]
    (ω : ℕ → ℝ) (C D : Finset (Finset α)),
    4 ≤ Fintype.card α → (∀ r, 0 ≤ ω r) →
    IsUpperSet (C : Set (Finset α)) → IsUpperSet (D : Set (Finset α)) →
    (∀ s ∈ C, ∀ t ∈ D, (s ∩ t).Nonempty) →
    ω (Fintype.card α - 1) + ω (Fintype.card α) < weightedMass ω C →
    ω (Fintype.card α - 1) + ω (Fintype.card α) < weightedMass ω D →
    R.readout () α (C.slice 1) + 2 ≤ R.readout () α (C.slice (Fintype.card α - 1))

private def largeFamily : Finset (Finset (ULift.{u} (Fin 4))) :=
  univ.filter (fun s => 3 ≤ s.card)

private theorem large_upper : IsUpperSet (largeFamily.{u} : Set (Finset (ULift.{u} (Fin 4)))) := by
  intro s t hst hs
  have hs' : 3 ≤ s.card := (mem_filter.mp hs).2
  exact mem_filter.mpr ⟨mem_univ _, hs'.trans (card_le_card hst)⟩

private theorem large_cross :
    ∀ s ∈ largeFamily.{u}, ∀ t ∈ largeFamily.{u}, (s ∩ t).Nonempty := by decide

private theorem large_mass :
    (1 : ℝ) + 1 < weightedMass (fun _ => 1) largeFamily.{u} := by
  have hc : largeFamily.{u}.card = 5 := by decide
  simp [weightedMass, hc]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (α := ULift.{u} (Fin 4)) (fun _ => 1) largeFamily largeFamily
    (by decide) (fun _ => by norm_num) large_upper large_upper large_cross
    (by simpa using large_mass.{u}) (by simpa using large_mass.{u})
  change 0 + 2 ≤ (0 : ℕ) at hh
  omega

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} (Fin 1), ∅, {∅}, ?_⟩
  simp [actual, realize]

def source_registration :
    Registration arena.{u} (type_of% @weighted_cross_intersecting_layer_gap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_cross_intersecting_layer_gap.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_cross_intersecting_layer_gap.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap.unit
  realizationName := `Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
