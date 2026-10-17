/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One mapped actual F2 cycle carries full inventory, all six marks, and retained native a/b edges. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open private relabel_selected from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport

/-- The target is the actual independently specified layer, not raw F2Domain. -/
def FrameDomain {m : ℕ} (F : SupplyFrame m 2) : Configuration m → Prop :=
  Layer F.selected.toFinset (F.terminal :: F.base : Cycle (Fin (m + 1)))

/-- Undo exactly the left relabelling used by frameDomainIso. -/
noncomputable def undoRelabel {m : ℕ} (F : SupplyFrame m 2)
    (x : Configuration m) : Configuration m := (relabel F)⁻¹ * x

private theorem up_down {m : ℕ} (F : SupplyFrame m 2) (x : Configuration m) :
    relabel F * undoRelabel F x = x := by
  simp [undoRelabel, mul_assoc]

private theorem down_up_edge {m : ℕ} (F : SupplyFrame m 2)
    (e : Sym2 (Configuration m)) :
    Sym2.map (undoRelabel F) (Sym2.map (fun x => relabel F * x) e) = e := by
  induction e using Sym2.inductionOn
  simp [Sym2.map_mk, undoRelabel, mul_assoc]

private theorem up_down_edge {m : ℕ} (F : SupplyFrame m 2)
    (e : Sym2 (Configuration m)) :
    Sym2.map (fun x => relabel F * x) (Sym2.map (undoRelabel F) e) = e := by
  induction e using Sym2.inductionOn
  simp [Sym2.map_mk, up_down]

private theorem mapped_edges {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    {x y : {v : Configuration m // F2Domain m v}}
    (w : (domainGraph (F2Domain m)).Walk x y) :
    (w.map (frameDomainIso hm F).toHom).edges.map (Sym2.map Subtype.val) =
      (w.edges.map (Sym2.map Subtype.val)).map (Sym2.map (fun z => relabel F * z)) := by
  simp only [SimpleGraph.Walk.edges_map, List.map_map]
  congr 1
  funext e
  induction e using Sym2.inductionOn
  rfl

private theorem mapped_mem {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    {x y : {v : Configuration m // F2Domain m v}}
    (w : (domainGraph (F2Domain m)).Walk x y) (e : Sym2 (Configuration m)) :
    e ∈ (w.map (frameDomainIso hm F).toHom).edges.map (Sym2.map Subtype.val) ↔
      Sym2.map (undoRelabel F) e ∈ w.edges.map (Sym2.map Subtype.val) := by
  rw [mapped_edges]
  constructor
  · intro he
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
    have hd := congrArg (Sym2.map (undoRelabel F)) hfe
    rw [down_up_edge] at hd
    exact hd ▸ hf
  · intro he
    exact List.mem_map.mpr ⟨Sym2.map (undoRelabel F) e, he, up_down_edge F e⟩

private theorem raw_a_cut_labels {m : ℕ} (hm : 5 ≤ m) (x : Configuration m)
    (hd : F2DeletedEdge m s(x, x * a m)) :
    s(x (Fin.last m), (x * a m) (Fin.last m)) = s(0, Fin.last m) := by
  rcases (native_f2_a_cut_classification (by omega : 4 ≤ m) x).mp hd with he | he
  · have h := congrArg (Sym2.map (fun z : Configuration m => z (Fin.last m))) he
    have h' : s(x (Fin.last m), (x * a m) (Fin.last m)) = s(Fin.last m, 0) := by
      simpa [Sym2.map_mk, a_apply] using h
    exact h'.trans Sym2.eq_swap
  · have h := congrArg (Sym2.map (fun z : Configuration m => z (Fin.last m))) he
    simpa [Sym2.map_mk, a_apply] using h

private theorem subtype_edge_mem {m : ℕ} (D : Configuration m → Prop)
    {base : {v : Configuration m // D v}} (w : (domainGraph D).Walk base base)
    (x y : {v : Configuration m // D v})
    (he : s(x.val, y.val) ∈ w.edges.map (Sym2.map Subtype.val)) : s(x,y) ∈ w.edges := by
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
  have heq : f = s(x,y) := (Sym2.map.injective Subtype.val_injective) hfe
  exact heq ▸ hf

/-- A single choice of canonical F2 witness is transported once to the
actual frame. That same mapped walk earns the undo-relabel full inventory,
all six marked edges and the native inventories needed by the k2 Q route. -/
theorem native_j2_frame_cycle_with_inventory {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) :
    ∃ rawBase : {v : Configuration m // F2Domain m v},
      ∃ rawWalk : (domainGraph (F2Domain m)).Walk rawBase rawBase,
      ∃ base : {v : Configuration m // FrameDomain F v},
      ∃ w : (domainGraph (FrameDomain F)).Walk base base,
        rawWalk.IsHamiltonianCycle ∧
        (∀ e : Sym2 (Configuration m),
          e ∈ rawWalk.edges.map (Sym2.map Subtype.val) ↔
            (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) ∧
        base = frameDomainIso hm F rawBase ∧
        HEq w (rawWalk.map (frameDomainIso hm F).toHom) ∧
        w.IsHamiltonianCycle ∧
        (∀ e : Sym2 (Configuration m),
          e ∈ w.edges.map (Sym2.map Subtype.val) ↔
          (F2NativeEdge m (Sym2.map (undoRelabel F) e) ∧
            ¬ F2DeletedEdge m (Sym2.map (undoRelabel F) e)) ∨
            F2Seam m (Sym2.map (undoRelabel F) e)) ∧
        (∀ p : Fin 3 × Bool,
          Sym2.map (fun z => relabel F * z) (markedEdge m p) ∈
            w.edges.map (Sym2.map Subtype.val)) ∧
        (∀ x y : {v : Configuration m // FrameDomain F v},
          y.val = x.val * a m →
          s(x.val (Fin.last m), y.val (Fin.last m)) ≠
            s(relabel F (Fin.last m), relabel F 0) → s(x,y) ∈ w.edges) ∧
        (∀ x y : {v : Configuration m // FrameDomain F v},
          y.val = x.val * b m → x.val (Fin.last m) ∉ F.selected.toFinset →
            s(x,y) ∈ w.edges) ∧
        relabel F (Fin.last m) ≠ relabel F 0 ∧
        F.selected.toFinset = {relabel F (Fin.last m), relabel F 0} := by
  classical
  obtain ⟨rawBase, rawWalk, hham, hinv, _, hmarked⟩ :=
    native_j2_hamiltonian_cycle_with_marked_edges hm
  let iso := frameDomainIso hm F
  let base : {v : Configuration m // FrameDomain F v} := iso rawBase
  let w : (domainGraph (FrameDomain F)).Walk base base := rawWalk.map iso.toHom
  have inventory (e : Sym2 (Configuration m)) :
      e ∈ w.edges.map (Sym2.map Subtype.val) ↔
      (F2NativeEdge m (Sym2.map (undoRelabel F) e) ∧
        ¬ F2DeletedEdge m (Sym2.map (undoRelabel F) e)) ∨
        F2Seam m (Sym2.map (undoRelabel F) e) :=
    (mapped_mem hm F rawWalk e).trans (hinv _)
  have rawDomain (x : {v : Configuration m // FrameDomain F v}) :
      F2Domain m (undoRelabel F x.val) := by
    apply (native_j2_frame_domain_iff hm F _).mp
    simpa only [up_down, FrameDomain] using x.property
  have retained (x : {v : Configuration m // FrameDomain F v}) (g : Configuration m)
      (hg : g = a m ∨ g = b m)
      (hd : ¬ F2DeletedEdge m s(undoRelabel F x.val, undoRelabel F x.val * g)) :
      s(x.val, x.val * g) ∈ w.edges.map (Sym2.map Subtype.val) := by
    apply (inventory _).mpr
    left
    have he : Sym2.map (undoRelabel F) s(x.val, x.val * g) =
        s(undoRelabel F x.val, undoRelabel F x.val * g) := by
      simp [Sym2.map_mk, undoRelabel, mul_assoc]
    rw [he]
    exact ⟨(native_f2_native_edge_catalog (by omega : 4 ≤ m) _).mpr
      ⟨undoRelabel F x.val, g, rawDomain x, hg, rfl⟩, hd⟩
  refine ⟨rawBase, rawWalk, base, w, hham, hinv, rfl, HEq.rfl,
    SimpleGraph.Walk.IsHamiltonianCycle.map iso.toEquiv.bijective hham, inventory, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    apply (mapped_mem hm F rawWalk _).mpr
    rw [down_up_edge]
    exact hmarked p
  · intro x y hy hlabels
    apply subtype_edge_mem (FrameDomain F) w x y
    rw [hy]
    apply retained x (a m) (Or.inl rfl)
    intro hd
    have hraw := raw_a_cut_labels hm (undoRelabel F x.val) hd
    have hmapped := congrArg (Sym2.map (relabel F)) hraw
    have hx : relabel F ((undoRelabel F x.val) (Fin.last m)) = x.val (Fin.last m) :=
      congrArg (fun z : Configuration m => z (Fin.last m)) (up_down F x.val)
    have hy' : relabel F ((undoRelabel F x.val * a m) (Fin.last m)) =
        y.val (Fin.last m) := by
      change (relabel F * (undoRelabel F x.val * a m)) (Fin.last m) = _
      rw [← mul_assoc, up_down, ← hy]
    simp only [Sym2.map_mk, hx, hy'] at hmapped
    exact hlabels (hmapped.trans Sym2.eq_swap)
  · intro x y hy ht
    apply subtype_edge_mem (FrameDomain F) w x y
    rw [hy]
    apply retained x (b m) (Or.inr rfl)
    intro hd
    rcases (native_f2_b_cut_classification (by omega : 4 ≤ m)
      (undoRelabel F x.val)).mp hd with ⟨j, _, hj⟩ | ⟨j, _, hj⟩ | ⟨j, _, hj⟩
    all_goals
      apply ht
      rw [← relabel_selected hm F]
      apply Finset.mem_image.mpr
      refine ⟨(undoRelabel F x.val) (Fin.last m), ?_, ?_⟩
      · simp [hj]
      · exact congrArg (fun z : Configuration m => z (Fin.last m)) (up_down F x.val)
  · intro he
    have hz := (relabel F).injective he
    have hv := congrArg Fin.val hz
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  · rw [← relabel_selected hm F]
    ext x
    simp [or_comm]

#print axioms native_j2_frame_cycle_with_inventory

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
