import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope
import Reg.Support.DependentFamily

/-! Source-bound graph families observe the actual all-label independent-set hull. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope

open _root_.D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u
noncomputable section

abbrev signature : Signature where
  Params := Type u
  State V := SimpleGraph V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Set (V → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ G => stableSetPolytope G) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    R.readout () V G = edgeRegion G ↔ G.IsBipartite

private theorem bottom_bipartite (V : Type u) : (⊥ : SimpleGraph V).IsBipartite := by
  exact SimpleGraph.IsBipartite.bot V

private theorem rejected_law : ¬ (arena.{u}).Law rejected.{u} := by
  intro h
  let V := ULift.{u} Unit
  have he := (h (⊥ : SimpleGraph V)).mpr (bottom_bipartite V)
  have hz : (fun _ : V => (0 : ℝ)) ∈ edgeRegion (⊥ : SimpleGraph V) := by
    constructor
    · intro v
      norm_num
    · simp
  rw [← he] at hz
  exact hz

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  let V := ULift.{u} (Fin 2)
  let G : SimpleGraph V := SimpleGraph.comap (fun x => x.down) (⊤ : SimpleGraph (Fin 2))
  have hG : G.IsBipartite := by
    exact ⟨⟨fun x => x.down, by intro v w hvw; exact hvw⟩⟩
  refine ⟨V, (⊥ : SimpleGraph V), G, ?_⟩
  intro he
  have he' : stableSetPolytope (⊥ : SimpleGraph V) = stableSetPolytope G := he
  rw [(stableSetPolytope_eq_edgeRegion_iff _).mpr (bottom_bipartite V),
    (stableSetPolytope_eq_edgeRegion_iff G).mpr hG] at he'
  have hx : (fun _ : V => (1 : ℝ)) ∈ edgeRegion (⊥ : SimpleGraph V) := by
    constructor
    · intro v
      norm_num
    · simp
  rw [he'] at hx
  have hh := hx.2 (ULift.up 0) (ULift.up 1) (by decide)
  norm_num at hh

def source_registration :
    Registration arena.{u} (type_of% @stableSetPolytope_eq_edgeRegion_iff.{u}) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨stableSetPolytope_eq_edgeRegion_iff, rejected.{u}, rejected_law.{u}⟩
  sensitivity := ⟨fun i => ⟨rejected.{u},
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence.{u}

def registration : Contract.Registration
    (@stableSetPolytope_eq_edgeRegion_iff.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (actual.{u}).readout (actual.{u}).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope
