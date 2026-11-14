/- GID: D5/S3/Combinatorics/Graph/StarForming/ClosedRingGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/ClosedRingGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual balanced selected-isolate geometry of every closed-high ring. -/

import D5.S3.Combinatorics.Graph.StarForming.ClosedRings

/-! The selected-isolate statement for Z_r in CLOSED_HIGH_CYCLE_COMPENSATION,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
This concerns the original displayed attaining selection, not all minimal
selections and not an arbitrary equality-class classification. -/
namespace D5.S3.Combinatorics.Graph.StarForming.ClosedRingGeometry
open StarFormingDissociationRefutation ClosedRings
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

private def localIsolate (v : Fin 62) : Prop := ClosedRingWitnesses.forming v ∧
  ∀ w : Fin 62, ClosedRingWitnesses.forming w → ¬ ClosedModule.graph.Adj v w
private instance (v : Fin 62) : Decidable (localIsolate v) :=
  by unfold localIsolate; infer_instance

set_option maxRecDepth 200000 in
private theorem local_counts : (Finset.univ.filter localIsolate).card=6 ∧
    (Finset.univ.filter (fun v => localIsolate v ∧ ClosedRingWitnesses.color v=0)).card=3 ∧
    (Finset.univ.filter (fun v => localIsolate v ∧ ClosedRingWitnesses.color v=1)).card=3 := by
  decide +kernel

private theorem isolate_iff (e : Equiv.Perm I) (i : I) (v : Fin 62) :
    (ClosedRingWitnesses.forming v ∧ ∀ w : I × Fin 62,
      ClosedRingWitnesses.forming w.2 → ¬ (graph e).Adj (i,v) w) ↔ localIsolate v := by
  constructor
  · rintro ⟨hv,h⟩
    exact ⟨hv,fun w hw he => h (i,w) hw (Or.inl ⟨rfl,he⟩)⟩
  · rintro ⟨hv,h⟩
    refine ⟨hv,?_⟩
    rintro ⟨j,w⟩ hw (⟨_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩)
    · exact h w hw he
    · exact ClosedRingWitnesses.interface_states.2.1 (he ▸ hw)
    · exact ClosedRingWitnesses.interface_states.1 (he ▸ hw)

/-- The original thirty-six-per-module attaining selection has six selected
isolates per module, three in each actual bipartition side. -/
theorem isolate_counts (e : Equiv.Perm I) :
    let S : Finset (I × Fin 62) := Finset.univ.filter
      (fun x => ClosedRingWitnesses.forming x.2)
    let Z := DegreeCapacity.isolates (graph e) S
    Z.card=6*Fintype.card I ∧
    (Z.filter (fun x => ClosedRingWitnesses.color x.2=0)).card=3*Fintype.card I ∧
    (Z.filter (fun x => ClosedRingWitnesses.color x.2=1)).card=3*Fintype.card I := by
  classical
  dsimp only
  let S : Finset (I × Fin 62) := Finset.univ.filter
    (fun x => ClosedRingWitnesses.forming x.2)
  have hz : DegreeCapacity.isolates (graph e) S=
      Finset.univ.filter (fun x => localIsolate x.2) := by
    ext x
    simp only [DegreeCapacity.isolates,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [DegreeCapacity.selectedDegree,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using isolate_iff e x.1 x.2
  change (DegreeCapacity.isolates (graph e) S).card=_ ∧ _
  rw [hz]
  constructor
  · rw [ClosedModule.card_fibers]
    simp [local_counts.1,Nat.mul_comm]
  constructor
  all_goals
    rw [Finset.filter_filter,ClosedModule.card_fibers]
    simp [local_counts,Nat.mul_comm]

end D5.S3.Combinatorics.Graph.StarForming.ClosedRingGeometry
