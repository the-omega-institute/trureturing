/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Six independently oriented actual components partition the entire F2 domain. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SixthComponent

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SixthComponent
open private actual_port_leaf from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel
open private actual_surviving_path_partition partition_piece_full_component
  leaf_in_path_is_endpoint from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SixthComponent
open private surviving_adj_iff from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel

/-- The six starts are specified from the original ports before choosing paths. -/
def componentStartPort (i : Fin 6) : Fin 3 × Bool × Bool :=
  match i.val with
  | 0 => (0, false, false)
  | 1 => (0, false, true)
  | 2 => (1, false, false)
  | 3 => (2, false, true)
  | 4 => (0, true, false)
  | _ => (1, false, true)

/-- The corresponding independent finishes include the residual bar L0. -/
def componentFinishPort (i : Fin 6) : Fin 3 × Bool × Bool :=
  match i.val with
  | 0 => (2, false, false)
  | 1 => (1, true, true)
  | 2 => (2, true, true)
  | 3 => (2, true, false)
  | 4 => (1, true, false)
  | _ => (0, true, true)

/-- Six actual simple paths, with independent endpoint orientations, exhaust
the full F2 domain exactly once and each retain their complete incident edges. -/
theorem native_j2_six_component_partition {m : ℕ} (hm : 5 ≤ m) :
    ∃ paths : (i : Fin 6) → (survivingGraph m).Walk
        (port m (componentStartPort i)) (port m (componentFinishPort i)),
      (∀ i, (paths i).IsPath) ∧
      (∀ i x, x ∈ (paths i).support ↔
        (survivingGraph m).Reachable (port m (componentStartPort i)) x) ∧
      (∀ i x y, (survivingGraph m).Adj x y ∧
        (survivingGraph m).Reachable (port m (componentStartPort i)) x ↔
          s(x, y) ∈ (paths i).edges) ∧
      ∀ x, F2Domain m x ↔ ∃! i, x ∈ (paths i).support := by
  classical
  have hpaths : ∀ i : Fin 6,
      ∃ w : (survivingGraph m).Walk
          (port m (componentStartPort i)) (port m (componentFinishPort i)),
        w.IsPath ∧
        (∀ x, x ∈ w.support ↔
          (survivingGraph m).Reachable (port m (componentStartPort i)) x) ∧
        ∀ x y, (survivingGraph m).Adj x y ∧
          (survivingGraph m).Reachable (port m (componentStartPort i)) x ↔
            s(x, y) ∈ w.edges := by
    intro i
    fin_cases i
    all_goals first
    | exact native_j2_sixth_full_component hm
    | have h := native_j2_word_full_component hm (0 : Fin 5)
      obtain ⟨w, hp, _, _, hv, he⟩ := h
      exact ⟨w, hp, hv, he⟩
    | have h := native_j2_word_full_component hm (1 : Fin 5)
      obtain ⟨w, hp, _, _, hv, he⟩ := h
      exact ⟨w, hp, hv, he⟩
    | have h := native_j2_word_full_component hm (2 : Fin 5)
      obtain ⟨w, hp, _, _, hv, he⟩ := h
      exact ⟨w, hp, hv, he⟩
    | have h := native_j2_word_full_component hm (3 : Fin 5)
      obtain ⟨w, hp, _, _, hv, he⟩ := h
      exact ⟨w, hp, hv, he⟩
    | have h := native_j2_word_full_component hm (4 : Fin 5)
      obtain ⟨w, hp, _, _, hv, he⟩ := h
      exact ⟨w, hp, hv, he⟩
  choose paths hpath hvertices hedges using hpaths
  have hports : ∀ q : Fin 3 × Bool × Bool,
      ∃ i : Fin 6, q = componentStartPort i ∨ q = componentFinishPort i := by decide
  have hsignature : ∀ i j : Fin 6,
      componentStartPort j = componentStartPort i ∨
        componentStartPort j = componentFinishPort i → j = i := by decide
  obtain ⟨pieces, hpiecePaths, hn, hdomain, hinventory, _, hendpoints⟩ :=
    actual_surviving_path_partition hm
  have hall : ∀ x y, (survivingGraph m).Adj x y →
      s(x, y) ∈ (pieces.flatMap fun z => z.walk.edges) := by
    intro x y hxy
    exact (hinventory _).mpr ((surviving_adj_iff m x y).mp hxy).1
  have hreach_domain (y x : Configuration m) (hy : F2Domain m y)
      (hr : (survivingGraph m).Reachable y x) : F2Domain m x := by
    obtain ⟨p, hp, hy⟩ := List.mem_flatMap.mp ((hdomain y).mpr hy)
    obtain ⟨hv, _⟩ := partition_piece_full_component pieces hn hall p hp
    have hx := (hv x).mpr (((hv y).mp hy).trans hr)
    exact (hdomain x).mp (List.mem_flatMap.mpr ⟨p, hp, hx⟩)
  refine ⟨paths, hpath, hvertices, hedges, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp ((hdomain x).mpr hx)
    obtain ⟨q, hq⟩ := (hendpoints p hp).1
    have hr : (survivingGraph m).Reachable (port m q) x := by
      rw [← hq]
      exact (p.walk.takeUntil x hxp).reachable
    obtain ⟨i, hi | hi⟩ := hports q
    all_goals
      have hix : x ∈ (paths i).support := by
        apply (hvertices i x).mpr
        first
        | simpa only [hi] using hr
        | exact (paths i).reachable.trans (by simpa only [hi] using hr)
      refine ⟨i, hix, ?_⟩
      intro j hj
      have hij : (survivingGraph m).Reachable
          (port m (componentStartPort i)) (port m (componentStartPort j)) :=
        ((hvertices i x).mp hix).trans ((hvertices j x).mp hj).symm
      have hstart := (hvertices i _).mpr hij
      rcases leaf_in_path_is_endpoint (paths i) (hpath i) hstart
          (actual_port_leaf hm (componentStartPort j)) with he | he
      · exact hsignature i j (Or.inl (native_j2_port_injective hm he))
      · exact hsignature i j (Or.inr (native_j2_port_injective hm he))
  · rintro ⟨i, hi, _⟩
    exact hreach_domain _ x (native_j2_port_domain hm (componentStartPort i))
      ((hvertices i x).mp hi)

#print axioms native_j2_six_component_partition

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components
