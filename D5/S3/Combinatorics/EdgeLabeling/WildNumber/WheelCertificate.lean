/- GID: D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every greedy output on the four-colored wheel has six edges. -/
/-
admission_basis: escape-witness (FiniteState.run_states)
escape_witness: FiniteState.run_states
Direct frozen dependencies: none.
H_connected: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
gamma_surjective: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
O_card: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
O_color_connecting: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
color_connecting_card_ge_five: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
all_outputs_six: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
FiniteState.run_states: proof_shape: content; escape_witness: FiniteState.run_states; Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21209
-/
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.ComponentMirror
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Subtype
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel
def Elist : List ((Fin 8) × (Fin 8)) :=
  [(0,1),(0,3),(0,4),(0,2),(0,6),(4,5),(6,7),
   (0,5),(0,7),(1,2),(1,7),(5,6),(2,3),(3,4)]
@[reducible] def H : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun u v => (u,v) ∈ Elist)
def edgeColor (e : Sym2 (Fin 8)) : (Fin 4) :=
  if e = s(0,1) ∨ e = s(0,3) ∨ e = s(0,4) then 0
  else if e = s(0,2) ∨ e = s(0,6) ∨ e = s(4,5) ∨ e = s(6,7) then 1
  else if e = s(0,5) ∨ e = s(0,7) ∨ e = s(1,2) ∨ e = s(1,7) ∨ e = s(5,6) then 2
  else 3
noncomputable def gamma : H.edgeSet → (Fin 4) := fun e => edgeColor e
theorem H_connected : H.Connected := by decide +kernel
theorem gamma_surjective : Function.Surjective gamma := by
   intro c
   fin_cases c
   · refine ⟨⟨s(0,1), ?_⟩, ?_⟩ <;> decide +kernel
   · refine ⟨⟨s(0,2), ?_⟩, ?_⟩ <;> decide +kernel
   · refine ⟨⟨s(0,5), ?_⟩, ?_⟩ <;> decide +kernel
   · refine ⟨⟨s(2,3), ?_⟩, ?_⟩ <;> decide +kernel
private def edgeSetExplicit : Set (Sym2 (Fin 8)) := {s(0,1),s(0,3),s(0,4),s(0,2),s(0,6),s(4,5),s(6,7),
  s(0,5),s(0,7),s(1,2),s(1,7),s(5,6),s(2,3),s(3,4)}
set_option maxHeartbeats 1000000 in
private theorem H_edge_set : H.edgeSet = edgeSetExplicit := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [H, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj, edgeSetExplicit, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert a b
    decide +kernel
private def edgeFinset : Finset (Sym2 (Fin 8)) := {s(0,1),s(0,3),s(0,4),s(0,2),s(0,6),s(4,5),s(6,7),
  s(0,5),s(0,7),s(1,2),s(1,7),s(5,6),s(2,3),s(3,4)}
private theorem H_edges_finset : H.edgeSet.toFinite.toFinset = edgeFinset := by
  ext e
  rw [H_edge_set]
  rw [(Set.toFinite edgeSetExplicit).mem_toFinset]
  simp [edgeFinset, edgeSetExplicit]
private def colorSet0 : Set (Sym2 (Fin 8)) := {s(0,1),s(0,3),s(0,4)}
private def colorSet1 : Set (Sym2 (Fin 8)) := {s(0,2),s(0,6),s(4,5),s(6,7)}
private def colorSet2 : Set (Sym2 (Fin 8)) := {s(0,5),s(0,7),s(1,2),s(1,7),s(5,6)}
private def colorSet3 : Set (Sym2 (Fin 8)) := {s(2,3),s(3,4)}
set_option maxHeartbeats 1000000 in
private theorem colorEdges_zero : colorEdges H gamma 0 = colorSet0 := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [colorEdges, gamma, Set.mem_ofPred_eq, exists_prop, H, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj, colorSet0, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert a b
    decide +kernel
set_option maxHeartbeats 1000000 in
private theorem colorEdges_one : colorEdges H gamma 1 = colorSet1 := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [colorEdges, gamma, Set.mem_ofPred_eq, exists_prop, H, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj, colorSet1, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert a b
    decide +kernel
set_option maxHeartbeats 1000000 in
private theorem colorEdges_two : colorEdges H gamma 2 = colorSet2 := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [colorEdges, gamma, Set.mem_ofPred_eq, exists_prop, H, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj, colorSet2, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert a b
    decide +kernel
set_option maxHeartbeats 1000000 in
private theorem colorEdges_three : colorEdges H gamma 3 = colorSet3 := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [colorEdges, gamma, Set.mem_ofPred_eq, exists_prop, H, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj, colorSet3, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert a b
    decide +kernel
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel
def O : Finset (Sym2 (Fin 8)) := {s(0,3),s(0,7),s(1,2),s(4,5),s(5,6)}
theorem O_card : O.card = 5 := by decide +kernel
private theorem O_subset : (O : Set (Sym2 (Fin 8))) ⊆ H.edgeSet := by
  intro e he
  rw [H_edge_set]
  have he' : e = s(0,3) ∨ e = s(0,7) ∨ e = s(1,2) ∨ e = s(4,5) ∨ e = s(5,6) := by simpa [O] using he
  rcases he' with rfl | rfl | rfl | rfl | rfl <;> simp [edgeSetExplicit]
private theorem O_connects_0 : (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0,?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 0 1 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 0 1 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 1 2 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 0 4 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 0 4 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 4 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 0 4 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 4 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 5 6 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet0)).Adj 0 7 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet0,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
private theorem O_connects_1 : (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0,?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 0 2 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 2 1 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 0 2 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 0 6 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 6 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 5 4 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 0 6 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 6 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 0 6 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet1)).Adj 0 7 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet1,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
private theorem O_connects_2 : (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0,?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 0 7 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 7 1 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 0 7 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 7 1 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 1 2 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 0 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 5 4 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 0 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 0 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 5 6 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet2)).Adj 0 7 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet2,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
private theorem O_connects_3 : (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0,?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 3 2 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 2 1 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 3 2 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 3 4 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 3 4 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 4 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 0 3 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 3 4 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 4 5 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 5 6 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl))))
  · exact ((show (SimpleGraph.fromEdgeSet ((O : Set (Sym2 (Fin 8))) ∪ colorSet3)).Adj 0 7 by rw [SimpleGraph.fromEdgeSet_adj]; simp only [O,colorSet3,Finset.mem_coe,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton]; decide +kernel).reachable).trans (SimpleGraph.Reachable.rfl)
theorem O_color_connecting : IsColorConnecting H gamma O := by
  refine ⟨O_subset,?_⟩
  intro c
  fin_cases c
  · change (wildColorGraph H gamma O 0).Connected
    unfold wildColorGraph
    rw [colorEdges_zero]
    exact O_connects_0
  · change (wildColorGraph H gamma O 1).Connected
    unfold wildColorGraph
    rw [colorEdges_one]
    exact O_connects_1
  · change (wildColorGraph H gamma O 2).Connected
    unfold wildColorGraph
    rw [colorEdges_two]
    exact O_connects_2
  · change (wildColorGraph H gamma O 3).Connected
    unfold wildColorGraph
    rw [colorEdges_three]
    exact O_connects_3
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.LowerBounds
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
private theorem color_connecting_edge_lower_bound (G : SimpleGraph V) (γ : G.edgeSet → C)
    (W : Finset (Sym2 V)) (hc : IsColorConnecting G γ W) (c : C)
    (S : Finset (Sym2 V)) (hS : colorEdges G γ c = (S : Set (Sym2 V))) :
    Fintype.card V ≤ W.card + S.card + 1 := by
  classical
  let K := wildColorGraph G γ W c
  have hsub : K.edgeSet ⊆ ((W ∪ S : Finset (Sym2 V)) : Set (Sym2 V)) := by
    change (wildColorGraph G γ W c).edgeSet ⊆ _
    rw [wildColorGraph, hS, ← Finset.coe_union]
    exact (SimpleGraph.le_fromEdgeSet_iff _ _).mp le_rfl
  let f : K.edgeSet → ↑(W ∪ S : Finset (Sym2 V)) := fun e => ⟨e.val,hsub e.property⟩
  have hi : Function.Injective f := by
    exact Subtype.map_injective (fun _ he => hsub he) Function.injective_id
  have hci : Nat.card K.edgeSet ≤ (W ∪ S).card := by
    have hh := Nat.card_le_card_of_injective f hi
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hh
  have hv := (hc.2 c).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at hv
  have hu := Finset.card_union_le W S
  change Fintype.card V ≤ Nat.card K.edgeSet + 1 at hv
  omega
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.LowerBounds
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel
private def S3 : Finset (Sym2 (Fin 8)) := {s(2,3),s(3,4)}
private theorem color3_finset : colorEdges H gamma 3 = (S3 : Set (Sym2 (Fin 8))) := by
  rw [colorEdges_three]
  ext e
  simp [colorSet3,S3]
theorem color_connecting_card_ge_five (W : Finset (Sym2 (Fin 8))) (hc : IsColorConnecting H gamma W) :
    5 ≤ W.card := by
  have h := D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.LowerBounds.color_connecting_edge_lower_bound H gamma W hc 3 S3 color3_finset
  have hcard : S3.card = 2 := by decide +kernel
  simp only [Fintype.card_fin,hcard] at h
  omega
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
open scoped BigOperators
private def eu : (Fin 14) → (Fin 8) := ![0,0,0,0,0,4,6,0,0,1,1,5,2,3]
private def ev : (Fin 14) → (Fin 8) := ![1,3,4,2,6,5,7,5,7,2,7,6,3,4]
private def ec : (Fin 14) → (Fin 4) := ![0,0,0,1,1,1,1,2,2,2,2,2,3,3]
private def localEdges (W : (Finset (Fin 14))) (c : (Fin 4)) : List ((Fin 8) × (Fin 8)) :=
  (List.finRange 14).filterMap (fun e => if ec e = c ∨ e ∈ W then some (eu e,ev e) else none)
private def count (W : (Finset (Fin 14))) (c : (Fin 4)) : ℕ := D5.S3.Combinatorics.EdgeLabeling.WildNumber.ComponentMirror.componentCount (localEdges W c)
private def dip (W : (Finset (Fin 14))) (e : (Fin 14)) : ℕ := ∑ c : (Fin 4), (count W c - count (insert e W) c)
private def potential (W : (Finset (Fin 14))) (e : (Fin 14)) : List ℕ :=
  ((Finset.univ : Finset (Fin 14)).val.map (dip (insert e W))).sort (· ≥ ·)
@[reducible] private def connected (W : (Finset (Fin 14))) : Prop := ∀ c : (Fin 4), count W c = 1
private def greedyStep (W : (Finset (Fin 14))) (e : (Fin 14)) : Prop :=
  ¬connected W ∧ e ∉ W ∧ (∀ f : (Fin 14), f ∉ W → dip W f ≤ dip W e) ∧
    ∀ f : (Fin 14), f ∉ W → dip W f = dip W e → ¬List.Lex (· < ·) (potential W e) (potential W f)
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
private def edge (e : (Fin 14)) : Sym2 (Fin 8) := s(eu e,ev e)
private def realize (W : (Finset (Fin 14))) : Finset (Sym2 (Fin 8)) := W.image edge
private theorem edge_injective : Function.Injective edge := by decide +kernel
private theorem edge_mem (e : (Fin 14)) : edge e ∈ D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.edgeSet := by
  fin_cases e <;> decide +kernel
private theorem edge_color (e : (Fin 14)) : D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.edgeColor (edge e) = ec e := by
  fin_cases e <;> decide +kernel
private theorem edges_realize : (Set.toFinite D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.edgeSet).toFinset = realize Finset.univ := by
  rw [D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H_edges_finset]
  decide +kernel
private theorem edge_exhaust {e : Sym2 (Fin 8)} (he : e ∈ D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.edgeSet) : ∃ i, edge i = e := by
  have hm : e ∈ (Set.toFinite D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.edgeSet).toFinset := by simpa [] using he
  rw [edges_realize] at hm
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  exact ⟨i,hi⟩
@[simp] private theorem realize_insert (W : (Finset (Fin 14))) (e : (Fin 14)) :
    realize (insert e W) = insert (edge e) (realize W) := Finset.image_insert _ _ _
@[simp] private theorem realize_mem (W : (Finset (Fin 14))) (e : (Fin 14)) : edge e ∈ realize W ↔ e ∈ W :=
  edge_injective.mem_finset_image
@[simp] private theorem realize_card (W : (Finset (Fin 14))) : (realize W).card = W.card :=
  Finset.card_image_of_injective _ edge_injective
private theorem realize_valid (W : (Finset (Fin 14))) : (realize W : Set _) ⊆ D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.edgeSet := by
  intro e he
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  exact edge_mem i
private theorem localEdges_mem (W : (Finset (Fin 14))) (c : (Fin 4)) (u v : (Fin 8)) :
    (u,v) ∈ localEdges W c ↔ ∃ e : (Fin 14), (ec e = c ∨ e ∈ W) ∧ eu e = u ∧ ev e = v := by
  simp [localEdges,List.mem_filterMap,Prod.ext_iff,eq_comm]
private theorem graph_eq (W : (Finset (Fin 14))) (c : (Fin 4)) : SimpleGraph.fromRel (fun u v => (u,v) ∈ localEdges W c) =
    wildColorGraph D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma (realize W) c := by
  ext u v
  rw [SimpleGraph.fromRel_adj,wildColorGraph,SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨huv,h | h⟩
    · obtain ⟨i,hi,rfl,rfl⟩ := (localEdges_mem W c u v).mp h
      refine ⟨?_,huv⟩
      rcases hi with hc | hw
      · exact Or.inr ⟨edge_mem i,by change D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.edgeColor (edge i) = c; rw [edge_color,hc]⟩
      · exact Or.inl (Finset.mem_image.mpr ⟨i,hw,rfl⟩)
    · obtain ⟨i,hi,rfl,rfl⟩ := (localEdges_mem W c v u).mp h
      refine ⟨?_,huv⟩
      rw [Sym2.eq_swap]
      rcases hi with hc | hw
      · exact Or.inr ⟨edge_mem i,by change D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.edgeColor (edge i) = c; rw [edge_color,hc]⟩
      · exact Or.inl (Finset.mem_image.mpr ⟨i,hw,rfl⟩)
  · rintro ⟨h,huv⟩
    refine ⟨huv,?_⟩
    have hex : ∃ i, edge i = s(u,v) ∧ (ec i = c ∨ i ∈ W) := by
      rcases h with hw | ⟨he,hc⟩
      · obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hw
        exact ⟨i,heq,Or.inr hi⟩
      · obtain ⟨i,heq⟩ := edge_exhaust he
        refine ⟨i,heq,Or.inl ?_⟩
        rw [←edge_color,heq]
        exact hc
    obtain ⟨i,heq,hi⟩ := hex
    rcases Sym2.eq_iff.mp heq with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact Or.inl ((localEdges_mem W c u v).mpr ⟨i,hi,hu,hv⟩)
    · exact Or.inr ((localEdges_mem W c v u).mpr ⟨i,hi,hu,hv⟩)
private theorem count_eq (W : (Finset (Fin 14))) (c : (Fin 4)) : count W c =
    Nat.card (wildColorGraph D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma (realize W) c).ConnectedComponent := by
  unfold count
  rw [D5.S3.Combinatorics.EdgeLabeling.WildNumber.ComponentMirror.componentCount_eq_kappa,graph_eq]
private theorem dip_eq (W : (Finset (Fin 14))) (e : (Fin 14)) : dip W e =
    D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.dip D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma (realize W) (edge e) := by
  unfold dip D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.dip
  simp only [count_eq,realize_insert]
private theorem potential_eq (W : (Finset (Fin 14))) (e : (Fin 14)) : potential W e =
    D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.potential D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma (realize W) (edge e) := by
  unfold potential D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.potential
  rw [edges_realize]
  unfold realize
  rw [Finset.image_val_of_injOn edge_injective.injOn,Multiset.map_map]
  apply congrArg (fun m : Multiset ℕ => m.sort (· ≥ ·))
  apply congrArg (fun f : (Fin 14) → ℕ => Finset.univ.val.map f)
  funext x
  change dip (insert e W) x =
    D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.dip D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma
      (insert (edge e) (realize W)) (edge x)
  rw [←realize_insert,←dip_eq]
private theorem connected_of_kappa_one (G : SimpleGraph (Fin 8)) (h : Nat.card G.ConnectedComponent = 1) : G.Connected := by
  have hs := (Nat.card_eq_one_iff_unique.mp h).1
  refine ⟨fun u v => ConnectedComponent.exact (hs.elim _ _)⟩
private theorem connected_iff (W : (Finset (Fin 14))) : connected W ↔
    IsColorConnecting D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma (realize W) := by
  constructor
  · intro h
    exact ⟨realize_valid W,fun c => connected_of_kappa_one _ ((count_eq W c) ▸ h c)⟩
  · intro h c
    rw [count_eq]
    exact D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy.kappa_connected (h.2 c)
private theorem step_reflect (W : (Finset (Fin 14))) (e : (Fin 14))
    (h : IsGreedyStep D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma (realize W) (edge e)) : greedyStep W e := by
  refine ⟨fun hc => h.1 ((connected_iff W).mp hc),?_,?_,?_⟩
  · exact fun he => (Finset.mem_sdiff.mp h.2.1).2 ((realize_mem W e).mpr he)
  · intro f hf
    have hfm : edge f ∈ (Set.toFinite D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.edgeSet).toFinset \ realize W := Finset.mem_sdiff.mpr
      ⟨by simpa [] using edge_mem f,fun hm => hf ((realize_mem W f).mp hm)⟩
    simpa only [dip_eq] using h.2.2.1 (edge f) hfm
  · intro f hf heq
    have hfm : edge f ∈ (Set.toFinite D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.edgeSet).toFinset \ realize W := Finset.mem_sdiff.mpr
      ⟨by simpa [] using edge_mem f,fun hm => hf ((realize_mem W f).mp hm)⟩
    simpa only [potential_eq] using h.2.2.2 (edge f) hfm (by simpa only [←dip_eq] using heq)
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
set_option maxHeartbeats 20000000
private theorem dips_0 : dip (∅) = ![2,3,3,2,2,3,2,3,2,3,3,3,3,2] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem pot_0_1 : potential (∅) 1 = [3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 1, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 1 (∅))) = [2, 0, 2, 1, 2, 3, 2, 3, 2, 3, 3, 3, 1, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_0_2 : potential (∅) 2 = [3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 2 (∅))) = [2, 2, 0, 1, 2, 2, 2, 2, 2, 3, 3, 2, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_0_5 : potential (∅) 5 = [3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 5 (∅))) = [2, 3, 2, 2, 2, 0, 2, 2, 2, 3, 3, 3, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_0_7 : potential (∅) 7 = [3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 7 (∅))) = [2, 3, 2, 2, 2, 2, 2, 0, 2, 3, 3, 2, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_0_9 : potential (∅) 9 = [3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 1, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 9 (∅))) = [1, 3, 3, 1, 2, 3, 2, 3, 2, 0, 2, 3, 2, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_0_10 : potential (∅) 10 = [3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 1, 1, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 10 (∅))) = [1, 3, 3, 2, 2, 3, 2, 3, 1, 2, 0, 3, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_0_11 : potential (∅) 11 = [3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 11 (∅))) = [2, 3, 2, 2, 2, 3, 2, 2, 2, 3, 3, 0, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_0_12 : potential (∅) 12 = [3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 1, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 12 (∅))) = [2, 1, 3, 1, 2, 3, 2, 3, 2, 2, 3, 3, 0, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem dips_1024 : dip ({10}) = ![1,3,3,2,2,3,2,3,1,2,0,3,3,2] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem pot_1024_1 : potential ({10}) 1 = [3, 3, 3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 1 ({10}))) = [1, 0, 2, 1, 2, 3, 2, 3, 1, 2, 0, 3, 1, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_1024_2 : potential ({10}) 2 = [3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 2 ({10}))) = [1, 2, 0, 1, 2, 2, 2, 2, 1, 2, 0, 2, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_1024_5 : potential ({10}) 5 = [3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 5 ({10}))) = [1, 3, 2, 2, 2, 0, 2, 2, 1, 2, 0, 3, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_1024_7 : potential ({10}) 7 = [3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 7 ({10}))) = [1, 3, 2, 2, 2, 2, 2, 0, 1, 2, 0, 2, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_1024_11 : potential ({10}) 11 = [3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 11 ({10}))) = [1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 0, 0, 3, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_1024_12 : potential ({10}) 12 = [3, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 12 ({10}))) = [1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 0, 3, 0, 2] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem dips_5120 : dip ({10,12}) = ![1,1,3,1,2,3,2,3,1,1,0,3,0,2] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem pot_5120_2 : potential ({10,12}) 2 = [2, 2, 2, 2, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 2 ({10,12}))) = [1, 0, 0, 0, 2, 2, 2, 2, 1, 1, 0, 2, 0, 0] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_5120_5 : potential ({10,12}) 5 = [3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 5 ({10,12}))) = [1, 1, 2, 1, 2, 0, 2, 2, 1, 1, 0, 3, 0, 1] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_5120_7 : potential ({10,12}) 7 = [2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 7 ({10,12}))) = [1, 1, 2, 1, 2, 2, 2, 0, 1, 1, 0, 2, 0, 1] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem dips_5152 : dip ({5,10,12}) = ![1,1,2,1,2,0,2,2,1,1,0,3,0,1] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem dips_7168 : dip ({10,11,12}) = ![1,1,2,1,2,3,2,2,1,1,0,0,0,1] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem dips_7200 : dip ({5,10,11,12}) = ![1,1,1,1,1,0,1,1,1,1,0,0,0,0] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem pot_7200_0 : potential ({5,10,11,12}) 0 = [1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 0 ({5,10,11,12}))) = [0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_7200_1 : potential ({5,10,11,12}) 1 = [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 1 ({5,10,11,12}))) = [1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_7200_2 : potential ({5,10,11,12}) 2 = [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 2 ({5,10,11,12}))) = [1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_7200_3 : potential ({5,10,11,12}) 3 = [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 3 ({5,10,11,12}))) = [1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_7200_4 : potential ({5,10,11,12}) 4 = [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 4 ({5,10,11,12}))) = [1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem pot_7200_7 : potential ({5,10,11,12}) 7 = [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold potential
  rw [Fin.univ_val_map]
  have hd : List.ofFn (dip (insert 7 ({5,10,11,12}))) = [1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by decide +kernel
  rw [hd]
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _) (by decide +kernel) ?_
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  exact Multiset.coe_eq_coe.mpr (by decide +kernel)
private theorem dips_7264 : dip ({5,6,10,11,12}) = ![1,1,1,1,1,0,0,1,1,0,0,0,0,0] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem dips_7456 : dip ({5,8,10,11,12}) = ![0,1,1,1,1,0,1,1,0,1,0,0,0,0] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem dips_7201 : dip ({0,5,10,11,12}) = ![0,1,1,1,1,0,1,1,0,1,0,0,0,0] := by
  funext e
  fin_cases e <;> decide +kernel
private theorem dips_7712 : dip ({5,9,10,11,12}) = ![1,1,1,1,1,0,0,1,1,0,0,0,0,0] := by
  funext e
  fin_cases e <;> decide +kernel
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
private theorem row_0 : ∀ e : (Fin 14), greedyStep (∅) e → e ∈ ({10} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · have hh := hs.2.2.1 10 (by decide +kernel)
    have hn : ¬ dip (∅) 10 ≤ dip (∅) 0 := by rw [dips_0]; decide +kernel
    exact (hn hh).elim
  · have heq : dip (∅) 10 = dip (∅) 1 := by rw [dips_0]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential (∅) 1) (potential (∅) 10) := hs.2.2.2 10 (by decide +kernel) heq
    exact (hn (by rw [pot_0_1,pot_0_10]; exact .cons (.cons (.cons (.cons (.cons (.rel (by decide +kernel)))))))).elim
  · have heq : dip (∅) 10 = dip (∅) 2 := by rw [dips_0]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential (∅) 2) (potential (∅) 10) := hs.2.2.2 10 (by decide +kernel) heq
    exact (hn (by rw [pot_0_2,pot_0_10]; exact .cons (.cons (.cons (.rel (by decide +kernel)))))).elim
  · have hh := hs.2.2.1 10 (by decide +kernel)
    have hn : ¬ dip (∅) 10 ≤ dip (∅) 3 := by rw [dips_0]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 10 (by decide +kernel)
    have hn : ¬ dip (∅) 10 ≤ dip (∅) 4 := by rw [dips_0]; decide +kernel
    exact (hn hh).elim
  · have heq : dip (∅) 10 = dip (∅) 5 := by rw [dips_0]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential (∅) 5) (potential (∅) 10) := hs.2.2.2 10 (by decide +kernel) heq
    exact (hn (by rw [pot_0_5,pot_0_10]; exact .cons (.cons (.cons (.cons (.cons (.rel (by decide +kernel)))))))).elim
  · have hh := hs.2.2.1 10 (by decide +kernel)
    have hn : ¬ dip (∅) 10 ≤ dip (∅) 6 := by rw [dips_0]; decide +kernel
    exact (hn hh).elim
  · have heq : dip (∅) 10 = dip (∅) 7 := by rw [dips_0]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential (∅) 7) (potential (∅) 10) := hs.2.2.2 10 (by decide +kernel) heq
    exact (hn (by rw [pot_0_7,pot_0_10]; exact .cons (.cons (.cons (.cons (.rel (by decide +kernel))))))).elim
  · have hh := hs.2.2.1 10 (by decide +kernel)
    have hn : ¬ dip (∅) 10 ≤ dip (∅) 8 := by rw [dips_0]; decide +kernel
    exact (hn hh).elim
  · have heq : dip (∅) 10 = dip (∅) 9 := by rw [dips_0]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential (∅) 9) (potential (∅) 10) := hs.2.2.2 10 (by decide +kernel) heq
    exact (hn (by rw [pot_0_9,pot_0_10]; exact .cons (.cons (.cons (.cons (.cons (.rel (by decide +kernel)))))))).elim
  · decide +kernel
  · have heq : dip (∅) 10 = dip (∅) 11 := by rw [dips_0]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential (∅) 11) (potential (∅) 10) := hs.2.2.2 10 (by decide +kernel) heq
    exact (hn (by rw [pot_0_11,pot_0_10]; exact .cons (.cons (.cons (.cons (.cons (.rel (by decide +kernel)))))))).elim
  · have heq : dip (∅) 10 = dip (∅) 12 := by rw [dips_0]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential (∅) 12) (potential (∅) 10) := hs.2.2.2 10 (by decide +kernel) heq
    exact (hn (by rw [pot_0_12,pot_0_10]; exact .cons (.cons (.cons (.cons (.cons (.rel (by decide +kernel)))))))).elim
  · have hh := hs.2.2.1 10 (by decide +kernel)
    have hn : ¬ dip (∅) 10 ≤ dip (∅) 13 := by rw [dips_0]; decide +kernel
    exact (hn hh).elim
private theorem row_1024 : ∀ e : (Fin 14), greedyStep ({10}) e → e ∈ ({12} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · have hh := hs.2.2.1 12 (by decide +kernel)
    have hn : ¬ dip ({10}) 12 ≤ dip ({10}) 0 := by rw [dips_1024]; decide +kernel
    exact (hn hh).elim
  · have heq : dip ({10}) 12 = dip ({10}) 1 := by rw [dips_1024]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({10}) 1) (potential ({10}) 12) := hs.2.2.2 12 (by decide +kernel) heq
    exact (hn (by rw [pot_1024_1,pot_1024_12]; exact .cons (.cons (.cons (.rel (by decide +kernel)))))).elim
  · have heq : dip ({10}) 12 = dip ({10}) 2 := by rw [dips_1024]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({10}) 2) (potential ({10}) 12) := hs.2.2.2 12 (by decide +kernel) heq
    exact (hn (by rw [pot_1024_2,pot_1024_12]; exact .cons (.rel (by decide +kernel)))).elim
  · have hh := hs.2.2.1 12 (by decide +kernel)
    have hn : ¬ dip ({10}) 12 ≤ dip ({10}) 3 := by rw [dips_1024]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 12 (by decide +kernel)
    have hn : ¬ dip ({10}) 12 ≤ dip ({10}) 4 := by rw [dips_1024]; decide +kernel
    exact (hn hh).elim
  · have heq : dip ({10}) 12 = dip ({10}) 5 := by rw [dips_1024]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({10}) 5) (potential ({10}) 12) := hs.2.2.2 12 (by decide +kernel) heq
    exact (hn (by rw [pot_1024_5,pot_1024_12]; exact .cons (.cons (.cons (.rel (by decide +kernel)))))).elim
  · have hh := hs.2.2.1 12 (by decide +kernel)
    have hn : ¬ dip ({10}) 12 ≤ dip ({10}) 6 := by rw [dips_1024]; decide +kernel
    exact (hn hh).elim
  · have heq : dip ({10}) 12 = dip ({10}) 7 := by rw [dips_1024]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({10}) 7) (potential ({10}) 12) := hs.2.2.2 12 (by decide +kernel) heq
    exact (hn (by rw [pot_1024_7,pot_1024_12]; exact .cons (.cons (.rel (by decide +kernel))))).elim
  · have hh := hs.2.2.1 12 (by decide +kernel)
    have hn : ¬ dip ({10}) 12 ≤ dip ({10}) 8 := by rw [dips_1024]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 12 (by decide +kernel)
    have hn : ¬ dip ({10}) 12 ≤ dip ({10}) 9 := by rw [dips_1024]; decide +kernel
    exact (hn hh).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · have heq : dip ({10}) 12 = dip ({10}) 11 := by rw [dips_1024]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({10}) 11) (potential ({10}) 12) := hs.2.2.2 12 (by decide +kernel) heq
    exact (hn (by rw [pot_1024_11,pot_1024_12]; exact .cons (.cons (.cons (.rel (by decide +kernel)))))).elim
  · decide +kernel
  · have hh := hs.2.2.1 12 (by decide +kernel)
    have hn : ¬ dip ({10}) 12 ≤ dip ({10}) 13 := by rw [dips_1024]; decide +kernel
    exact (hn hh).elim
private theorem row_5120 : ∀ e : (Fin 14), greedyStep ({10,12}) e → e ∈ ({5,11} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,12}) 5 ≤ dip ({10,12}) 0 := by rw [dips_5120]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,12}) 5 ≤ dip ({10,12}) 1 := by rw [dips_5120]; decide +kernel
    exact (hn hh).elim
  · have heq : dip ({10,12}) 5 = dip ({10,12}) 2 := by rw [dips_5120]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({10,12}) 2) (potential ({10,12}) 5) := hs.2.2.2 5 (by decide +kernel) heq
    exact (hn (by rw [pot_5120_2,pot_5120_5]; exact .rel (by decide +kernel))).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,12}) 5 ≤ dip ({10,12}) 3 := by rw [dips_5120]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,12}) 5 ≤ dip ({10,12}) 4 := by rw [dips_5120]; decide +kernel
    exact (hn hh).elim
  · decide +kernel
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,12}) 5 ≤ dip ({10,12}) 6 := by rw [dips_5120]; decide +kernel
    exact (hn hh).elim
  · have heq : dip ({10,12}) 5 = dip ({10,12}) 7 := by rw [dips_5120]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({10,12}) 7) (potential ({10,12}) 5) := hs.2.2.2 5 (by decide +kernel) heq
    exact (hn (by rw [pot_5120_7,pot_5120_5]; exact .rel (by decide +kernel))).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,12}) 5 ≤ dip ({10,12}) 8 := by rw [dips_5120]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,12}) 5 ≤ dip ({10,12}) 9 := by rw [dips_5120]; decide +kernel
    exact (hn hh).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,12}) 5 ≤ dip ({10,12}) 13 := by rw [dips_5120]; decide +kernel
    exact (hn hh).elim
private theorem row_5152 : ∀ e : (Fin 14), greedyStep ({5,10,12}) e → e ∈ ({11} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 0 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 1 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 2 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 3 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 4 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 6 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 7 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 8 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 9 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 11 (by decide +kernel)
    have hn : ¬ dip ({5,10,12}) 11 ≤ dip ({5,10,12}) 13 := by rw [dips_5152]; decide +kernel
    exact (hn hh).elim
private theorem row_7168 : ∀ e : (Fin 14), greedyStep ({10,11,12}) e → e ∈ ({5} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 0 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 1 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 2 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 3 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 4 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · decide +kernel
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 6 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 7 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 8 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 9 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 5 (by decide +kernel)
    have hn : ¬ dip ({10,11,12}) 5 ≤ dip ({10,11,12}) 13 := by rw [dips_7168]; decide +kernel
    exact (hn hh).elim
private theorem row_7200 : ∀ e : (Fin 14), greedyStep ({5,10,11,12}) e → e ∈ ({0,6,8,9} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · decide +kernel
  · have heq : dip ({5,10,11,12}) 0 = dip ({5,10,11,12}) 1 := by rw [dips_7200]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({5,10,11,12}) 1) (potential ({5,10,11,12}) 0) := hs.2.2.2 0 (by decide +kernel) heq
    exact (hn (by rw [pot_7200_1,pot_7200_0]; exact .cons (.cons (.cons (.cons (.rel (by decide +kernel))))))).elim
  · have heq : dip ({5,10,11,12}) 0 = dip ({5,10,11,12}) 2 := by rw [dips_7200]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({5,10,11,12}) 2) (potential ({5,10,11,12}) 0) := hs.2.2.2 0 (by decide +kernel) heq
    exact (hn (by rw [pot_7200_2,pot_7200_0]; exact .cons (.cons (.cons (.cons (.rel (by decide +kernel))))))).elim
  · have heq : dip ({5,10,11,12}) 0 = dip ({5,10,11,12}) 3 := by rw [dips_7200]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({5,10,11,12}) 3) (potential ({5,10,11,12}) 0) := hs.2.2.2 0 (by decide +kernel) heq
    exact (hn (by rw [pot_7200_3,pot_7200_0]; exact .cons (.cons (.cons (.cons (.rel (by decide +kernel))))))).elim
  · have heq : dip ({5,10,11,12}) 0 = dip ({5,10,11,12}) 4 := by rw [dips_7200]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({5,10,11,12}) 4) (potential ({5,10,11,12}) 0) := hs.2.2.2 0 (by decide +kernel) heq
    exact (hn (by rw [pot_7200_4,pot_7200_0]; exact .cons (.cons (.cons (.cons (.rel (by decide +kernel))))))).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · decide +kernel
  · have heq : dip ({5,10,11,12}) 0 = dip ({5,10,11,12}) 7 := by rw [dips_7200]; decide +kernel
    have hn : ¬List.Lex (· < ·) (potential ({5,10,11,12}) 7) (potential ({5,10,11,12}) 0) := hs.2.2.2 0 (by decide +kernel) heq
    exact (hn (by rw [pot_7200_7,pot_7200_0]; exact .cons (.cons (.cons (.cons (.rel (by decide +kernel))))))).elim
  · decide +kernel
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 0 (by decide +kernel)
    have hn : ¬ dip ({5,10,11,12}) 0 ≤ dip ({5,10,11,12}) 13 := by rw [dips_7200]; decide +kernel
    exact (hn hh).elim
private theorem row_7264 : ∀ e : (Fin 14), greedyStep ({5,6,10,11,12}) e → e ∈ ({0,1,2,3,4,7,8} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · decide +kernel
  · decide +kernel
  · have hh := hs.2.2.1 0 (by decide +kernel)
    have hn : ¬ dip ({5,6,10,11,12}) 0 ≤ dip ({5,6,10,11,12}) 9 := by rw [dips_7264]; decide +kernel
    exact (hn hh).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 0 (by decide +kernel)
    have hn : ¬ dip ({5,6,10,11,12}) 0 ≤ dip ({5,6,10,11,12}) 13 := by rw [dips_7264]; decide +kernel
    exact (hn hh).elim
private theorem row_7456 : ∀ e : (Fin 14), greedyStep ({5,8,10,11,12}) e → e ∈ ({1,2,3,4,6,7,9} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · have hh := hs.2.2.1 1 (by decide +kernel)
    have hn : ¬ dip ({5,8,10,11,12}) 1 ≤ dip ({5,8,10,11,12}) 0 := by rw [dips_7456]; decide +kernel
    exact (hn hh).elim
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · decide +kernel
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 1 (by decide +kernel)
    have hn : ¬ dip ({5,8,10,11,12}) 1 ≤ dip ({5,8,10,11,12}) 13 := by rw [dips_7456]; decide +kernel
    exact (hn hh).elim
private theorem row_7201 : ∀ e : (Fin 14), greedyStep ({0,5,10,11,12}) e → e ∈ ({1,2,3,4,6,7,9} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · exact (hs.2.1 (by decide +kernel)).elim
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · decide +kernel
  · decide +kernel
  · have hh := hs.2.2.1 1 (by decide +kernel)
    have hn : ¬ dip ({0,5,10,11,12}) 1 ≤ dip ({0,5,10,11,12}) 8 := by rw [dips_7201]; decide +kernel
    exact (hn hh).elim
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 1 (by decide +kernel)
    have hn : ¬ dip ({0,5,10,11,12}) 1 ≤ dip ({0,5,10,11,12}) 13 := by rw [dips_7201]; decide +kernel
    exact (hn hh).elim
private theorem row_7712 : ∀ e : (Fin 14), greedyStep ({5,9,10,11,12}) e → e ∈ ({0,1,2,3,4,7,8} : Finset (Fin 14)) := by
  intro e hs
  fin_cases e
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 0 (by decide +kernel)
    have hn : ¬ dip ({5,9,10,11,12}) 0 ≤ dip ({5,9,10,11,12}) 6 := by rw [dips_7712]; decide +kernel
    exact (hn hh).elim
  · decide +kernel
  · decide +kernel
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · exact (hs.2.1 (by decide +kernel)).elim
  · have hh := hs.2.2.1 0 (by decide +kernel)
    have hn : ¬ dip ({5,9,10,11,12}) 0 ≤ dip ({5,9,10,11,12}) 13 := by rw [dips_7712]; decide +kernel
    exact (hn hh).elim
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
private def states : Finset (Finset (Fin 14)) := {(∅),({10}),({10,12}),({5,10,12}),({10,11,12}),({5,10,11,12}),({0,5,10,11,12}),({0,1,5,10,11,12}),({0,2,5,10,11,12}),({0,3,5,10,11,12}),({0,4,5,10,11,12}),({5,6,10,11,12}),({0,5,6,10,11,12}),({1,5,6,10,11,12}),({2,5,6,10,11,12}),({3,5,6,10,11,12}),({4,5,6,10,11,12}),({0,5,7,10,11,12}),({5,6,7,10,11,12}),({5,8,10,11,12}),({1,5,8,10,11,12}),({2,5,8,10,11,12}),({3,5,8,10,11,12}),({4,5,8,10,11,12}),({5,6,8,10,11,12}),({5,7,8,10,11,12}),({5,9,10,11,12}),({0,5,9,10,11,12}),({1,5,9,10,11,12}),({2,5,9,10,11,12}),({3,5,9,10,11,12}),({4,5,9,10,11,12}),({5,7,9,10,11,12}),({5,8,9,10,11,12})}
private theorem terminal_info : ∀ W ∈ states, connected W ↔ W.card = 6 := by
  intro W h
  simp only [states, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private theorem closed_transitions : ∀ W ∈ states, ∀ e : (Fin 14), (W.card = 6 → False) →
  ((W = (∅) ∧ e ∈ ({10} : Finset (Fin 14))) ∨ (W = ({10}) ∧ e ∈ ({12} : Finset (Fin 14))) ∨ (W = ({10,12}) ∧ e ∈ ({5,11} : Finset (Fin 14))) ∨ (W = ({5,10,12}) ∧ e ∈ ({11} : Finset (Fin 14))) ∨ (W = ({10,11,12}) ∧ e ∈ ({5} : Finset (Fin 14))) ∨ (W = ({5,10,11,12}) ∧ e ∈ ({0,6,8,9} : Finset (Fin 14))) ∨ (W = ({5,6,10,11,12}) ∧ e ∈ ({0,1,2,3,4,7,8} : Finset (Fin 14))) ∨ (W = ({5,8,10,11,12}) ∧ e ∈ ({1,2,3,4,6,7,9} : Finset (Fin 14))) ∨ (W = ({0,5,10,11,12}) ∧ e ∈ ({1,2,3,4,6,7,9} : Finset (Fin 14))) ∨ (W = ({5,9,10,11,12}) ∧ e ∈ ({0,1,2,3,4,7,8} : Finset (Fin 14)))) → insert e W ∈ states := by
  intro W h e hn ht
  simp only [states, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hn ht e <;> decide +kernel
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
private theorem states_step (W : (Finset (Fin 14))) (hw : W ∈ states) (e : (Fin 14)) (hs : greedyStep W e) :
    insert e W ∈ states := by
  have hn : W.card ≠ 6 := fun h => hs.1 ((terminal_info W hw).mpr h)
  apply closed_transitions W hw e hn
  simp only [states,Finset.mem_insert,Finset.mem_singleton] at hw
  rcases hw with rfl | hw
  · exact Or.inl ⟨rfl,row_0 e hs⟩
  rcases hw with rfl | hw
  · exact Or.inr (Or.inl ⟨rfl,row_1024 e hs⟩)
  rcases hw with rfl | hw
  · exact Or.inr (Or.inr (Or.inl ⟨rfl,row_5120 e hs⟩))
  rcases hw with rfl | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,row_5152 e hs⟩)))
  rcases hw with rfl | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,row_7168 e hs⟩))))
  rcases hw with rfl | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,row_7200 e hs⟩)))))
  rcases hw with rfl | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,row_7201 e hs⟩))))))))
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,row_7264 e hs⟩))))))
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,row_7456 e hs⟩)))))))
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl,row_7712 e hs⟩)))))))))
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl | hw
  · exact (hn (by decide +kernel)).elim
  rcases hw with rfl
  · exact (hn (by decide +kernel)).elim
private theorem run_states {W : Finset (Sym2 (Fin 8))}
    (hr : IsGreedyRun D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma W) :
    ∃ S ∈ states, realize S = W := by
  induction hr with
  | empty => exact ⟨∅,by decide +kernel,by simp [realize]⟩
  | @step W e hr hs ih =>
    obtain ⟨S,hS,rfl⟩ := ih
    have he : e ∈ D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.edgeSet := by
      simpa [] using (Finset.mem_sdiff.mp hs.2.1).1
    obtain ⟨i,rfl⟩ := edge_exhaust he
    exact ⟨insert i S,states_step S hS i (step_reflect S i hs),realize_insert S i⟩
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel
theorem all_outputs_six (W : Finset (Sym2 (Fin 8))) (ho : IsGreedyOutput H gamma W) : W.card = 6 := by
  obtain ⟨S,hS,rfl⟩ := D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState.run_states ho.1
  rw [D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState.realize_card]
  exact (D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState.terminal_info S hS).mp
    ((D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.FiniteState.connected_iff S).mpr ho.2)
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel
