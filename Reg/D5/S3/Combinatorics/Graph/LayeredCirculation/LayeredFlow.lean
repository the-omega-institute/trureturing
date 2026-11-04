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
abbrev signature.{u_3} : Signature where
  Params := Σ ι : Type u_3, ι
  State q := q.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u_3} : Realization signature.{u_3} :=
  realize signature (fun _ q weight => weight q.2) (fun e => nomatch e)

def rejected.{u_3} : Realization signature.{u_3} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena.{u_1, u_2, u_3} : Arena where
  signature := signature.{u_3}
  Law R := ∀ {V : Type u_1} {E : Type u_2} {ι : Type u_3}
    [Fintype E] [DecidableEq E] [Fintype ι]
    (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ)
    (weight : ι → ℝ) (base : ι → V)
    (cycle : ∀ i, (signedGraph G).Walk (base i) (base i)),
    (∀ i, 0 ≤ weight i) → (∀ i, IsSimpleCycle (cycle i)) →
    (∀ e, coefficient e = ∑ i, weight i * circuitCoefficient (cycle i) e) →
    (∀ e, coefficient (e, true) = 0) → ∀ i,
    0 < R.readout () ⟨ι, i⟩ weight → ∀ e ∈ (cycle i).edges, e.2 = false

private def loopGraph.{u_1, u_2} : EdgeGraph PUnit.{u_1 + 1} PUnit.{u_2 + 1} where
  source _ := ⟨⟩
  target _ := ⟨⟩

private def reverseLoop.{u_1, u_2} : (signedGraph loopGraph.{u_1, u_2}).Walk ⟨⟩ ⟨⟩ :=
  .concat .nil (⟨⟩, true) rfl

private theorem reverseLoop_simple.{u_1, u_2} : IsSimpleCycle reverseLoop.{u_1, u_2} := by
  refine ⟨by simp [reverseLoop], ?_⟩
  intro vertex before inner after he hi hout
  have hlen : 1 = before.length + inner.length + after.length := by
    calc
      1 = reverseLoop.length := rfl
      _ = reverseLoop.edges.length := (EdgeGraph.Walk.edges_length _).symm
      _ = _ := by rw [he]; simp only [List.length_append, EdgeGraph.Walk.edges_length]
  omega

theorem rejected_law.{u_1, u_2, u_3} : ¬ arena.{u_1, u_2, u_3}.Law rejected := by
  intro h
  have hb := @h PUnit.{u_1 + 1} PUnit.{u_2 + 1} PUnit.{u_3 + 1}
    inferInstance inferInstance inferInstance loopGraph (fun _ => 0) (fun _ => 0)
    (fun _ => ⟨⟩) (fun _ => reverseLoop) (fun _ => le_rfl)
    (fun _ => reverseLoop_simple) (by intro e; simp) (fun _ => rfl) ⟨⟩
    (by norm_num [rejected, realize]) (⟨⟩, true) (by simp [reverseLoop, EdgeGraph.Walk.edges])
  exact Bool.noConfusion hb

theorem dependence.{u_3} : ObservationalDependence signature.{u_3} actual := by
  intro i
  refine ⟨⟨PUnit.{u_3 + 1}, ⟨⟩⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  exact zero_ne_one

def source_registration.{u_1, u_2, u_3} : Registration arena.{u_1, u_2, u_3}
    (type_of% @positive_coefficient_forward.{u_1, u_2, u_3}) where
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

def registration.{u_1, u_2, u_3} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positive_coefficient_forward.{u_1, u_2, u_3}) (Realization signature.{u_3}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1, u_2, u_3}⟩
  objectArena := .source ⟨arena.{u_1, u_2, u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1, u_2, u_3} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_3}
    (fun _ q weight => weight q.2) (fun e => nomatch e))
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
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum.positive_coefficient_forward
#print axioms source_registration
#print axioms registration

namespace CyclePrefix

/-- Observe the closing edge's target in the endpoint of the final subwalk. -/
abbrev signature.{u_1, u_2} : Signature where
  Params := Σ V : Type u_1, Σ E : Type u_2, EdgeGraph V E
  State q := q.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := q.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u_1, u_2} : Realization signature.{u_1, u_2} :=
  realize signature (fun _ q edge => q.2.2.target edge) (fun e => nomatch e)

def rejected.{u_1, u_2} : Realization signature.{u_1, u_2} :=
  realize signature (fun _ q edge => q.2.2.source edge) (fun e => nomatch e)

abbrev arena.{u_1, u_2} : Arena where
  signature := signature.{u_1, u_2}
  Law R := ∀ {V : Type u_1} {E : Type u_2} {G : EdgeGraph V E} {a : V}
    (edge : E) (initial : G.Walk (G.target edge) a) (legal : G.source edge = a),
    (∀ (v : V) (before : G.Walk (G.target edge) v) (inner : G.Walk v v)
      (after : G.Walk v (R.readout () ⟨V, E, G⟩ edge)),
      (initial.concat edge legal).edges = before.edges ++ inner.edges ++ after.edges →
      0 < inner.length → 0 < before.length + after.length → False) →
    initial.visited.Nodup

private abbrev flipGraph.{u_1, u_2} : EdgeGraph (ULift.{u_1} Bool) (ULift.{u_2} Bool) where
  source e := ⟨e.down⟩
  target e := ⟨!e.down⟩

private abbrev repeatedPrefix.{u_1, u_2} :
    flipGraph.{u_1, u_2}.Walk ⟨true⟩ ⟨false⟩ := by
  let first : flipGraph.{u_1, u_2}.Walk ⟨true⟩ ⟨false⟩ :=
    .concat .nil (ULift.up true) rfl
  let second : flipGraph.{u_1, u_2}.Walk ⟨true⟩ ⟨true⟩ :=
    .concat first (ULift.up false) rfl
  exact .concat second (ULift.up true) rfl

theorem rejected_law.{u_1, u_2} : ¬ arena.{u_1, u_2}.Law rejected := by
  intro h
  have hn := h (G := flipGraph) ⟨false⟩ repeatedPrefix rfl (by
    intro v before inner after he _ _
    let joined := (before.append inner).append after
    have he' : joined.edges = (repeatedPrefix.concat ⟨false⟩ rfl).edges := by
      simpa only [joined, EdgeGraph.Walk.edges_append, List.append_assoc] using he.symm
    have hne : joined.edges ≠ [] := by
      rw [he', EdgeGraph.Walk.edges_concat]
      simp
    have hlast : joined.edges.getLast hne = (⟨false⟩ : ULift.{u_2} Bool) := by
      calc
        _ = (repeatedPrefix.concat (ULift.up false) rfl).edges.getLast
            (by simp [EdgeGraph.Walk.edges_concat]) :=
          List.getLast_congr hne _ he'
        _ = _ := by simp only [EdgeGraph.Walk.edges_concat, List.getLast_append_singleton]
    have hend := joined.target_getLast hne
    rw [hlast] at hend
    have hb : (⟨true⟩ : ULift.{u_1} Bool) = ⟨false⟩ := by
      exact hend
    exact Bool.noConfusion (congrArg ULift.down hb))
  change ([⟨true⟩, ⟨false⟩, ⟨true⟩, ⟨false⟩] : List (ULift.{u_1} Bool)).Nodup at hn
  simp at hn

theorem dependence.{u_1, u_2} : ObservationalDependence signature.{u_1, u_2} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Bool, ULift.{u_2} Bool, flipGraph⟩, ⟨false⟩, ⟨true⟩, ?_⟩
  exact fun h => Bool.noConfusion (congrArg ULift.down h)

def source_registration.{u_1, u_2} : Registration arena.{u_1, u_2}
    (type_of% @cycle_initial_visited_nodup.{u_1, u_2}) where
  actual := realize signature.{u_1, u_2}
    (fun _ q edge => q.2.2.target edge) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨cycle_initial_visited_nodup, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u_1, u_2} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cycle_initial_visited_nodup.{u_1, u_2}) (Realization signature.{u_1, u_2}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow.CyclePrefix.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow.CyclePrefix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1, u_2}⟩
  objectArena := .source ⟨arena.{u_1, u_2}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1, u_2} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1, u_2}
    (fun _ q edge => q.2.2.target edge) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain",
        "body", "body", "body", "domain", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum.cycle_initial_visited_nodup
#print axioms source_registration
#print axioms registration

end CyclePrefix

end
end Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow
