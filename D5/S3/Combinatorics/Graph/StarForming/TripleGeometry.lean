/- GID: D5/S3/Combinatorics/Graph/StarForming/TripleGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/TripleGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual balanced selected-isolate geometry of every triple-port ring. -/

import D5.S3.Combinatorics.Graph.StarForming.TripleRings

/-! The selected-isolate statement for T_r in CUBIC_TRIPLE_PORT_COMPENSATION,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
This concerns the original displayed attaining selection, not all minimal
selections and not an arbitrary equality-class classification. -/
namespace D5.S3.Combinatorics.Graph.StarForming.TripleGeometry
open StarFormingDissociationRefutation TripleRings
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

private def localIsolate (v : Fin 48) : Prop := TripleWitnesses.forming v ∧
  ∀ w : Fin 48, TripleWitnesses.forming w → ¬ TripleModule.graph.Adj v w
private instance (v : Fin 48) : Decidable (localIsolate v) :=
  by unfold localIsolate; infer_instance

set_option maxRecDepth 200000 in
private theorem local_counts : (Finset.univ.filter localIsolate).card=4 ∧
    (Finset.univ.filter (fun v => localIsolate v ∧ TripleWitnesses.color v=0)).card=2 ∧
    (Finset.univ.filter (fun v => localIsolate v ∧ TripleWitnesses.color v=1)).card=2 := by
  decide +kernel

private theorem isolate_iff (e : Equiv.Perm I) (i : I) (v : Fin 48) :
    (TripleWitnesses.forming v ∧ ∀ w : I × Fin 48,
      TripleWitnesses.forming w.2 → ¬ (graph e).Adj (i,v) w) ↔ localIsolate v := by
  constructor
  · rintro ⟨hv,h⟩
    exact ⟨hv,fun w hw he => h (i,w) hw (Or.inl ⟨rfl,he⟩)⟩
  · rintro ⟨hv,h⟩
    refine ⟨hv,?_⟩
    rintro ⟨j,w⟩ hw (⟨_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩)
    · exact h w hw he
    · exact TripleWitnesses.interface_states.2.1 (he ▸ hw)
    · exact TripleWitnesses.interface_states.1 (he ▸ hw)

/-- The original twenty-eight-per-module attaining selection has four selected
isolates per module, two in each actual bipartition side. -/
theorem isolate_counts (e : Equiv.Perm I) :
    let S : Finset (I × Fin 48) := Finset.univ.filter
      (fun x => TripleWitnesses.forming x.2)
    let Z := DegreeCapacity.isolates (graph e) S
    Z.card=4*Fintype.card I ∧
    (Z.filter (fun x => TripleWitnesses.color x.2=0)).card=2*Fintype.card I ∧
    (Z.filter (fun x => TripleWitnesses.color x.2=1)).card=2*Fintype.card I := by
  classical
  dsimp only
  let S : Finset (I × Fin 48) := Finset.univ.filter
    (fun x => TripleWitnesses.forming x.2)
  have hz : DegreeCapacity.isolates (graph e) S=
      Finset.univ.filter (fun x => localIsolate x.2) := by
    ext x
    simp only [DegreeCapacity.isolates,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [DegreeCapacity.selectedDegree,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using isolate_iff e x.1 x.2
  change (DegreeCapacity.isolates (graph e) S).card=_ ∧ _
  rw [hz]
  constructor
  · rw [TripleModule.card_fibers]
    simp [local_counts.1,Nat.mul_comm]
  constructor
  all_goals
    rw [Finset.filter_filter,TripleModule.card_fibers]
    simp [local_counts,Nat.mul_comm]

end D5.S3.Combinatorics.Graph.StarForming.TripleGeometry
