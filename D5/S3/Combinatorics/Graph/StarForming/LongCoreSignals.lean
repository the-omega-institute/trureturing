/- GID: D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/LongCoreSignals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: All-length actual zero-block-deficit direct-signal obstruction. -/

import D5.S3.Combinatorics.Graph.StarForming.LongCoreRings
import D5.S3.Combinatorics.Graph.StarForming.CoverPullback

/-! The direct-signal counterexample in DIRECTIONAL_RETURN_AND_CORE_DEFICIT,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
The exact thirty-four-set and failure table are pulled back through the
actual neighborhood cover, rather than asserted from numerical deficits. -/
namespace D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals
open StarFormingDissociationRefutation
open LongCoreRings
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- The one-cell graph restores both seams. -/
def baseGraph : SimpleGraph (Fin 62) where
  Adj v w := localGraph.Adj v w ∨ forward v w ∨ forward w v
  symm := ⟨by
    intro v w h
    rcases h with h | h | h
    · exact Or.inl (localGraph.adj_symm h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h | h
    · exact localGraph.irrefl h
    all_goals rcases h with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> omega⟩
instance : DecidableRel baseGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_∨_∨_))

private theorem local_disjoint : ∀ v w : Fin 62, localGraph.Adj v w →
    ¬ forward v w ∧ ¬ forward w v := by decide +kernel
private theorem forward_unique : ∀ v a b : Fin 62,
    forward v a → forward v b → a=b := by decide +kernel
private theorem backward_unique : ∀ v a b : Fin 62,
    forward a v → forward b v → a=b := by decide +kernel
private theorem directions_disjoint : ∀ v a b : Fin 62,
    forward v a → ¬ forward b v := by decide +kernel

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Folding actual module labels is locally bijective for every index permutation. -/
theorem cover (e : Equiv.Perm I) :
    CoverPullback.NeighborhoodCover baseGraph.Adj (graph e).Adj Prod.snd where
  map_edge a b h := by
    rcases h with h | h | h
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h.2)
    · exact Or.inr (Or.inr h.2)
  neighbor_surjective a v h := by
    rcases h with h | h | h
    · exact ⟨(a.1,v),Or.inl ⟨rfl,h⟩,rfl⟩
    · exact ⟨(e a.1,v),Or.inr (Or.inl ⟨rfl,h⟩),rfl⟩
    · exact ⟨(e.symm a.1,v),Or.inr (Or.inr ⟨e.apply_symm_apply _,h⟩),rfl⟩
  neighbor_injective a b c hb hc he := by
    apply Prod.ext ?_ he
    rcases hb with hb | hb | hb <;> rcases hc with hc | hc | hc
    · exact hb.1.symm.trans hc.1
    · exact ((local_disjoint _ _ hb.2).1 (he.symm ▸ hc.2)).elim
    · exact ((local_disjoint _ _ hb.2).2 (he.symm ▸ hc.2)).elim
    · exact ((local_disjoint _ _ hc.2).1 (he ▸ hb.2)).elim
    · exact hb.1.symm.trans hc.1
    · exact (directions_disjoint _ _ _ hb.2 hc.2).elim
    · exact ((local_disjoint _ _ hc.2).2 (he ▸ hb.2)).elim
    · exact (directions_disjoint _ _ _ hc.2 hb.2).elim
    · exact e.injective (hb.1.trans hc.1.symm)

def chosen (v : Fin 62) : Prop :=
  v∈({1,2,3,4,6,8,9,10,11,12,20,23,24,25,27,29,30,31,
        35,36,37,39,41,43,44,45,49,50,51,53,55,57,58,59} : Finset (Fin 62))
instance (v : Fin 62) : Decidable (chosen v) := inferInstanceAs (Decidable (_∈_))

def failure (v : Fin 62) : Fin 62 :=
  ![0,7,7,15,5,0,6,0,14,15,16,11,12,0,0,0,0,0,0,0,
    13,0,0,33,32,25,0,26,0,29,22,21,0,0,0,42,46,47,0,39,
    0,41,0,40,34,38,0,0,0,56,60,61,0,53,0,55,0,54,48,52,0,0] v

private theorem forms : Regular.Forms baseGraph.Adj chosen := by
  unfold Regular.Forms Regular.TwoAt
  decide +kernel
private theorem failures : ∀ d : Fin 62, chosen d →
    ¬ (chosen (failure d) ∧ failure d≠d) ∧
    ¬ Regular.TwoAt baseGraph.Adj (fun v => chosen v ∧ v≠d) (failure d) := by
  unfold Regular.TwoAt
  decide +kernel
private theorem base_minimal : Regular.Minimal baseGraph.Adj chosen :=
  Subcubic.minimal_of_deletion_failures _ _ forms (fun d hd => ⟨failure d,failures d hd⟩)
private theorem proper_color : ∀ v w : Fin 62, baseGraph.Adj v w →
    ClosedRingWitnesses.color v≠ClosedRingWitnesses.color w := by decide +kernel
private theorem triangle_free : CoverPullback.TriangleFree baseGraph.Adj := by
  intro v w x hvw hwx hxv
  have h1 := proper_color v w hvw
  have h2 := proper_color w x hwx
  have h3 := proper_color x v hxv
  have hv := (ClosedRingWitnesses.color v).isLt
  have hw := (ClosedRingWitnesses.color w).isLt
  have hx := (ClosedRingWitnesses.color x).isLt
  have hn1 : (ClosedRingWitnesses.color v).val≠(ClosedRingWitnesses.color w).val :=
    fun h => h1 (Fin.ext h)
  have hn2 : (ClosedRingWitnesses.color w).val≠(ClosedRingWitnesses.color x).val :=
    fun h => h2 (Fin.ext h)
  have hn3 : (ClosedRingWitnesses.color x).val≠(ClosedRingWitnesses.color v).val :=
    fun h => h3 (Fin.ext h)
  omega

/-- The actual repeated thirty-four-set is minimal at every finite size. -/
theorem minimal (e : Equiv.Perm I) :
    Regular.Minimal (graph e).Adj (fun v => chosen v.2) :=
  CoverPullback.minimal_pullback (cover e) (fun _ => baseGraph.irrefl)
    (fun _ _ => baseGraph.adj_symm) (fun _ _ => (graph e).adj_symm)
    triangle_free base_minimal

def selection : Finset (I × Fin 62) := Finset.univ.filter (fun v => chosen v.2)

/-- Exact actual counts: thirty-four selected, ten core, eight in every block. -/
theorem counts : (selection (I := I)).card=34*Fintype.card I ∧
    (LongCoreRings.coreSet (selection (I := I))).card=10*Fintype.card I ∧
    (∀ i : I, ∀ j : Fin 3,
      (ClosedModule.blockSlice (LongCoreRings.slice (selection (I := I)) i) j).card=8) := by
  have h34 : (Finset.univ.filter chosen).card=34 := by decide +kernel
  have h10 : (Finset.univ.filter (fun v : Fin 20 => chosen (ClosedModule.core v))).card=10 :=
    by decide +kernel
  have h8 : ∀ j : Fin 3,
      (Finset.univ.filter (fun v : Fin 14 => chosen (ClosedModule.block j v))).card=8 :=
    by decide +kernel
  refine ⟨?_,?_,?_⟩
  · rw [ClosedModule.card_fibers]
    simp [selection,h34,Nat.mul_comm]
  · rw [ClosedModule.card_fibers]
    simp [LongCoreRings.coreSet,selection,h10,Nat.mul_comm]
  · intro i j
    simpa [ClosedModule.blockSlice,LongCoreRings.slice,selection] using h8 j

private theorem direct_base : ¬ chosen 13 ∧ chosen 20 ∧ baseGraph.Adj 13 20 ∧
    (∀ v : Fin 62, chosen v → baseGraph.Adj 13 v → v=20) ∧
    chosen 27 ∧ chosen 30 ∧ baseGraph.Adj 20 27 ∧ baseGraph.Adj 20 30 := by
  decide +kernel

/-- Each omitted opposite core root has exactly its selected signal port as
selected neighbor; that port has two selected internal neighbors. All blocks
still have size eight, so a positive loss cannot be assigned to each signal. -/
theorem direct_signals (e : Equiv.Perm I) (i : I) :
    (i,(13 : Fin 62))∉selection ∧ (i,(20 : Fin 62))∈selection ∧
    (graph e).Adj (i,13) (i,20) ∧
    (∀ v, v∈selection → (graph e).Adj (i,13) v → v=(i,20)) ∧
    (i,(27 : Fin 62))∈selection ∧ (i,(30 : Fin 62))∈selection ∧
    (graph e).Adj (i,20) (i,27) ∧ (graph e).Adj (i,20) (i,30) := by
  have he : ∀ v w : Fin 62, baseGraph.Adj v w →
      v≠0 → v≠5 → v≠12 → v≠17 → localGraph.Adj v w := by
    intro v w h h0 h5 h12 h17
    rcases h with h | h | h
    · exact h
    · rcases h with ⟨h,h'⟩ | ⟨h,h'⟩ <;> contradiction
    · rcases h with ⟨h',h⟩ | ⟨h',h⟩ <;> contradiction
  refine ⟨by simpa [selection] using direct_base.1,
    by simpa [selection] using direct_base.2.1,
    Or.inl ⟨rfl,he _ _ direct_base.2.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩,
    ?_,by simpa [selection] using direct_base.2.2.2.2.1,
    by simpa [selection] using direct_base.2.2.2.2.2.1,?_,?_⟩
  · intro v hv h
    have hv' : chosen v.2 := (Finset.mem_filter.mp hv).2
    have hl := direct_base.2.2.2.1 _ hv' ((cover e).map_edge _ _ h)
    apply Prod.ext ?_ hl
    rcases h with h | h | h
    · exact h.1.symm
    all_goals rcases h.2 with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> omega
  · exact Or.inl ⟨rfl,he _ _ direct_base.2.2.2.2.2.2.1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · exact Or.inl ⟨rfl,he _ _ direct_base.2.2.2.2.2.2.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

end D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals
