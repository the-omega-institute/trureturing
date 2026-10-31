import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow
import Reg.Support.DependentFamily

/-! Source-bound audit of the positive-weight circuit orientation criterion. -/

namespace Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow

open _root_.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Maths Maths.AdditiveTransport
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the circuit's weight in the strict positivity premise. -/
abbrev signature.{w} : Signature where
  Params := Σ ι : Type w, ι
  State q := q.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{w} : Realization signature.{w} :=
  realize signature (fun _ q weight => weight q.2) (fun e => nomatch e)

def rejected.{w} : Realization signature.{w} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena.{u, v, w} : Arena where
  signature := signature.{w}
  Law R := ∀ {V : Type u} {E : Type v} {ι : Type w}
    [Fintype E] [DecidableEq E] [Fintype ι]
    (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ)
    (weight : ι → ℝ) (base : ι → V)
    (cycle : ∀ i, (signedGraph G).Walk (base i) (base i)),
    (∀ i, 0 ≤ weight i) → (∀ i, IsSimpleCycle (cycle i)) →
    (∀ e, coefficient e = ∑ i, weight i * circuitCoefficient (cycle i) e) →
    (∀ e, coefficient (e, true) = 0) → ∀ i,
    0 < R.readout () ⟨ι, i⟩ weight → ∀ e ∈ (cycle i).edges, e.2 = false

private def loopGraph.{u, v} : EdgeGraph PUnit.{u + 1} PUnit.{v + 1} where
  source _ := ⟨⟩
  target _ := ⟨⟩

private def reverseLoop.{u, v} : (signedGraph loopGraph.{u, v}).Walk ⟨⟩ ⟨⟩ :=
  .concat .nil (⟨⟩, true) rfl

private theorem reverseLoop_simple.{u, v} : IsSimpleCycle reverseLoop.{u, v} := by
  refine ⟨by simp [reverseLoop], ?_⟩
  intro vertex before inner after he hi hout
  have hlen : 1 = before.length + inner.length + after.length := by
    calc
      1 = reverseLoop.length := rfl
      _ = reverseLoop.edges.length := (EdgeGraph.Walk.edges_length _).symm
      _ = _ := by rw [he]; simp only [List.length_append, EdgeGraph.Walk.edges_length]
  omega

theorem rejected_law.{u, v, w} : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  have hb := @h PUnit.{u + 1} PUnit.{v + 1} PUnit.{w + 1}
    inferInstance inferInstance inferInstance loopGraph (fun _ => 0) (fun _ => 0)
    (fun _ => ⟨⟩) (fun _ => reverseLoop) (fun _ => le_rfl)
    (fun _ => reverseLoop_simple) (by intro e; simp) (fun _ => rfl) ⟨⟩
    (by norm_num [rejected, realize]) (⟨⟩, true) (by simp [reverseLoop, EdgeGraph.Walk.edges])
  exact Bool.noConfusion hb

theorem dependence.{w} : ObservationalDependence signature.{w} actual := by
  intro i
  refine ⟨⟨PUnit.{w + 1}, ⟨⟩⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  exact zero_ne_one

def source_registration.{u, v, w} : Registration arena.{u, v, w}
    (type_of% @positive_coefficient_forward.{u, v, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_coefficient_forward, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u, v, w} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positive_coefficient_forward.{u, v, w}) (Realization signature.{w}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, w}⟩
  objectArena := .source ⟨arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, w} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q weight => weight q.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow
    definition := none
    coordinates := #[2, 15]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum.positive_coefficient_forward
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow
