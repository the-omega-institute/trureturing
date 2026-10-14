/- UNCOMPILED same-cycle native J2 half-restoration consumer.
   Lift the fixed raw half-component paths into the independently defined
   domain of a supplied prior F2 cycle. The retained inventory is stated
   against that same supplied w, including the literal barred exception. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open private half_adj_iff from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration

/-- The actual half-restored paths live in the same independent domain and
retain precisely the selected prior cycle's edges minus the selected three
cuts. `hD` is a domain identification, not a target partition certificate.
The end tables remain `halfStart/halfFinish` in their original native order. -/
theorem native_actual_j2_half_paths {m : ℕ} (hm : 5 ≤ m) (side : Bool)
    (D : Configuration m → Prop) (hD : ∀ x, D x ↔ F2Domain m x)
    {base : {x : Configuration m // D x}}
    (w : (domainGraph D).Walk base base)
    (hinv : ∀ e, e ∈ w.edges.map (Sym2.map Subtype.val) ↔
      (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) :
    ∃ pieces : Fin 3 → Piece (domainGraph D),
      (∀ i, (pieces i).start.val = port m (halfStart side i) ∧
        (pieces i).finish.val = port m (halfFinish side i)) ∧
      (∀ i, (pieces i).walk.IsPath) ∧
      (∀ v : {x : Configuration m // D x}, ∃! i, v ∈ (pieces i).walk.support) ∧
      ∀ e, e ∈ (List.ofFn fun i =>
        (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten ↔
          e ∈ w.edges.map (Sym2.map Subtype.val) ∧ ¬ HalfCut m side e := by
  classical
  obtain ⟨paths, hpath, hreach, _, hcover, hflat⟩ := native_j2_half_component_partition hm side
  let ambient := SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))
  let forget : domainGraph D →g ambient := ⟨Subtype.val, fun h => h⟩
  let raw := w.map forget
  have hrawEdges : raw.edges = w.edges.map (Sym2.map Subtype.val) :=
    SimpleGraph.Walk.edges_map forget w
  have hdomadj (x y : Configuration m) (hxy : (halfGraph m side).Adj x y) : D y := by
    have he : s(x, y) ∈ raw.edges := by
      rw [hrawEdges]
      exact (hinv _).mpr ((half_adj_iff m side x y).mp hxy).1.1
    have hy := raw.snd_mem_support_of_mem_edges he
    rw [show raw.support = w.support.map Subtype.val from SimpleGraph.Walk.support_map forget w] at hy
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hy
    exact hv ▸ v.property
  have hsub : halfGraph m side ≤ ambient := by
    intro x y hxy
    apply raw.adj_of_mem_edges
    rw [hrawEdges]
    exact (hinv _).mpr ((half_adj_iff m side x y).mp hxy).1.1
  have hpreserve (x y : Configuration m) (hx : D x)
      (hr : (halfGraph m side).Reachable x y) : D y := by
    obtain ⟨q⟩ := hr
    revert hx
    induction q with
    | nil => exact fun h => h
    | @cons a b c h q ih => exact fun _ => ih (hdomadj a b h)
  have hsD (i : Fin 3) (x : Configuration m) (hx : x ∈ (paths i).support) : D x :=
    hpreserve _ x ((hD _).mpr (native_j2_port_domain hm (halfStart side i)))
      ((hreach i x).mp hx)
  let lifted (i : Fin 3) := ((paths i).mapLe hsub).induce {x | D x} (by
    intro x hx
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
    exact hsD i x hx)
  let pieces (i : Fin 3) : Piece (domainGraph D) := ⟨_, _, lifted i⟩
  have hmap (i : Fin 3) : (pieces i).walk.map forget = (paths i).mapLe hsub := by
    exact SimpleGraph.Walk.map_induce _ _
  have hsmap (i : Fin 3) : (pieces i).walk.support.map Subtype.val = (paths i).support := by
    rw [← SimpleGraph.Walk.support_map forget (pieces i).walk, hmap,
      SimpleGraph.Walk.support_mapLe_eq_support]
  have hemap (i : Fin 3) : (pieces i).walk.edges.map (Sym2.map Subtype.val) = (paths i).edges := by
    rw [← SimpleGraph.Walk.edges_map forget (pieces i).walk, hmap,
      SimpleGraph.Walk.edges_mapLe_eq_edges]
  have hsupport (i : Fin 3) (v : {x : Configuration m // D x}) :
      v ∈ (pieces i).walk.support ↔ v.val ∈ (paths i).support := by
    rw [← hsmap]
    constructor
    · intro hv
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    · intro hv
      obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
      exact (Subtype.ext huv) ▸ hu
  refine ⟨pieces, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro i
    apply SimpleGraph.Walk.IsPath.of_map (f := forget)
    rw [hmap]
    exact (hpath i).mapLe hsub
  · intro v
    obtain ⟨i, hi, huniq⟩ := (hcover v.val).mp ((hD v.val).mp v.property)
    exact ⟨i, (hsupport i v).mpr hi, fun j hj => huniq j ((hsupport j v).mp hj)⟩
  · intro e
    have heq : (List.ofFn fun i => (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten =
        (List.ofFn fun i => (paths i).edges).flatten := by
      congr 1
      exact congrArg List.ofFn (funext hemap)
    rw [heq, hflat, hinv]
    rfl

#print axioms native_actual_j2_half_paths

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths
