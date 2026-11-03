import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.GraphInvariants.FiniteGraphDominationCollapse

/-! A source-bound four-slot audit of the original graph-collapse telescope. -/

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteGraphVertexSubstitution
open _root_.D5.S3.GraphInvariants.FiniteSimplicialCollapse
open _root_.D5.S3.GraphInvariants.FiniteGraphDominationCollapse

namespace Reg.D5.S3.GraphInvariants.FiniteGraphDominationCollapse
universe u

abbrev Parameters := Σ V : Type u, Σ _a : V, Finset V

abbrev Parameters.V (p : Parameters.{u}) := p.1
abbrev Parameters.a (p : Parameters.{u}) := p.2.1
abbrev Parameters.D (p : Parameters.{u}) := p.2.2

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := SimpleGraph p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PreAbstractSimplicialComplex p.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p G => restricted G (fun x => x ∉ p.D)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (G : SimpleGraph V) (a : V) (D : Finset V),
    a ∉ D → (∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d) →
    Collapses (independenceComplex G).toPreAbstractSimplicialComplex
      (R.readout () ⟨V, a, D⟩ G)

private theorem bridge : (type_of% (@domination_collapses.{u})) ↔ arena.{u}.Law actual := by
  constructor <;> intro h V fv dv G a D ha hd
  · exact @h V fv dv G a D ha hd
  · exact @h V fv dv G a D ha hd

private theorem collapses_le {V : Type u} [DecidableEq V]
    {K L : PreAbstractSimplicialComplex V} (h : Collapses K L) : L ≤ K := by
  induction h with
  | refl => exact le_rfl
  | @tail L M _ hstep ih =>
    obtain ⟨σ, a, _, _, _, _, _, he⟩ := hstep
    exact fun τ hτ => ih ((he τ).mp hτ).1

private abbrev testParameters : Parameters.{u} :=
  ⟨ULift.{u} Bool, ⟨false⟩, ∅⟩

private abbrev edge : Finset (ULift.{u} Bool) := {⟨false⟩, ⟨true⟩}

private theorem edge_not_independent :
    ¬ (⊤ : SimpleGraph (ULift.{u} Bool)).IsIndepSet (edge : Set (ULift.{u} Bool)) := by
  intro hi
  exact hi (by simp [edge]) (by simp [edge])
    (show (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩ from fun h =>
      Bool.false_ne_true (congrArg ULift.down h))
    (by simp)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hc := @h testParameters.V inferInstance inferInstance
    ⊤ testParameters.a ∅ (by simp) (by simp)
  have hh := collapses_le hc (show edge ∈ (⊤ : PreAbstractSimplicialComplex testParameters.V)
    from by change edge.Nonempty; simp [edge])
  exact edge_not_independent hh.2

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParameters, ⊥, ⊤, ?_⟩
  intro he
  have hb : edge ∈ actual.readout i testParameters ⊥ := by
    change edge.Nonempty ∧ (⊥ : SimpleGraph (ULift.{u} Bool)).IsIndepSet
      ((edge : Finset (ULift.{u} Bool)) : Set (ULift.{u} Bool)) ∧ _
    refine ⟨by simp [edge], ?_, by simp [testParameters, Parameters.D]⟩
    intro x hx y hy hxy hadj
    exact hadj
  have ht : edge ∈ actual.readout i testParameters ⊤ := he ▸ hb
  exact edge_not_independent ht.2.1

def family : Registration arena.{u} (type_of% (@domination_collapses.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@domination_collapses.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@domination_collapses.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.GraphInvariants.FiniteGraphDominationCollapse.__information_unit
  realizationName := `Reg.D5.S3.GraphInvariants.FiniteGraphDominationCollapse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p G => restricted G (fun x => x ∉ p.D)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.GraphInvariants.FiniteGraphDominationCollapse
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.GraphInvariants.FiniteGraphDominationCollapse
