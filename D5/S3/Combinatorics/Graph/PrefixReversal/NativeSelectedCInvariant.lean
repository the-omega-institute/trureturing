/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classify Every Retained and New Native c Edge. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedCutRetention

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open private parentPiece childLift from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
open private right_port_terminal from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedCutRetention

private theorem c_keeps_terminal {m : ℕ} (x : Configuration m) :
    (x * c m) (Fin.last m) = x (Fin.last m) := by
  apply congrArg x
  apply Fin.ext
  rw [c_apply]
  simp only [Fin.val_last, if_neg (by omega : ¬ m < m - 1)]

private theorem left_port_terminal {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (i : ℕ) : leftPort F i (Fin.last m) = F.terminal := by
  rw [leftPort, Equiv.Perm.mul_apply, b_last, right_port_terminal hm F i]

private theorem special_port_terminal {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (p : Port k) : specialPort F p (Fin.last m) = F.terminal := by
  simp only [specialPort]
  split_ifs
  · exact right_port_terminal hm F p.1.val
  · exact left_port_terminal hm F p.1.val

private theorem c_root_label_of_endpoint {m : ℕ}
    (S : Finset (Fin (m + 1))) (y z x : Configuration m)
    (hy : y (Fin.last m) ∈ S) (he : s(y, z) = s(x, x * c m)) :
    x (Fin.last m) ∈ S := by
  rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
  · exact (congrArg (fun w => w (Fin.last m)) h) ▸ hy
  · have hl := congrArg (fun w => w (Fin.last m)) h
    rw [c_keeps_terminal] at hl
    exact hl ▸ hy

/-- Edge membership in a literal assembled route has two exhaustive
sources: a retained full piece or one actual consecutive connection. -/
private theorem chain_c_labels {m : ℕ} {V : Type*} {G : SimpleGraph V}
    (val : V → Configuration m) (S : Finset (Fin (m + 1)))
    (p : Piece G) (ps : List (Piece G))
    (hpieces : ∀ z ∈ p :: ps, ∀ e ∈ z.walk.edges, ∀ x : Configuration m,
      Sym2.map val e = s(x, x * c m) → x (Fin.last m) ∈ S)
    (hseams : ∀ (i : ℕ) (hi : i + 1 < (p :: ps).length),
      val ((p :: ps)[i]'(by omega)).finish (Fin.last m) ∈ S)
    (e : Sym2 V) (he : e ∈ chainEdges p ps) (x : Configuration m)
    (hx : Sym2.map val e = s(x, x * c m)) : x (Fin.last m) ∈ S := by
  rcases chain_edge_cases p ps e he with ⟨z, hz, hez⟩ | ⟨i, hi, he⟩
  · exact hpieces z hz e hez x hx
  · rw [he, Sym2.map_mk] at hx
    exact c_root_label_of_endpoint S _ _ x (hseams i hi) hx

/-- In the special child route, old c edges retain their previous selected
labels. Every added internal seam has supplier terminal, now newly selected.
The endpoint hypothesis is supplied by actual ordered-slice endpoint laws. -/
theorem native_special_path_c_labels {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    {base : {z : Configuration m // SpecialDomain F hB z}}
    (w : (domainGraph (SpecialDomain F hB)).Walk base base)
    (hprior : ∀ e ∈ w.edgeSet, ∀ x : Configuration m,
      Sym2.map Subtype.val e = s(x, x * c m) → x (Fin.last m) ∈ F.selected.toFinset)
    (p : Piece (domainGraph (SpecialDomain F hB)))
    (ps : List (Piece (domainGraph (SpecialDomain F hB))))
    (hinv : ∀ e, e ∈ ((p :: ps).flatMap fun z => z.walk.edges) ↔
      e ∈ w.edgeSet ∧ e ∉ specialCuts hm F hB)
    (hends : ∀ z ∈ p :: ps, ∃ r : Port k, z.finish.val = specialPort F r)
    {u v : {z : Configuration m // SpecialDomain F hB z}}
    (q : (domainGraph (SpecialDomain F hB)).Walk u v)
    (hedges : q.edges = chainEdges p ps)
    (e : Sym2 {z : Configuration m // SpecialDomain F hB z}) (he : e ∈ q.edges)
    (x : Configuration m) (hx : Sym2.map Subtype.val e = s(x, x * c m)) :
    x (Fin.last m) ∈ insert F.terminal F.selected.toFinset := by
  classical
  rw [hedges] at he
  apply chain_c_labels Subtype.val _ p ps ?_ ?_ e he x hx
  · intro z hz e hez x hxe
    have hew := ((hinv e).mp (List.mem_flatMap.mpr ⟨z, hz, hez⟩)).1
    exact Finset.mem_insert_of_mem (hprior e hew x hxe)
  · intro i hi
    obtain ⟨r, hr⟩ := hends ((p :: ps)[i]'(by omega)) (List.getElem_mem (by omega))
    change ((p :: ps)[i]'(by omega)).finish.val (Fin.last m) ∈ _
    rw [hr, special_port_terminal hm F r]
    exact Finset.mem_insert_self _ _

/-- An ordinary complement inserts no new edge. Its exact inventory
therefore transfers the prior c-label classification to the chosen path. -/
theorem native_other_path_c_labels {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (j : Fin F.base.length) (hj : 0 < j.val)
    {base : {z : Configuration m // ChildDomain (childGap F j) z}}
    (w : (domainGraph (ChildDomain (childGap F j))).Walk base base)
    (hprior : ∀ e ∈ w.edges, ∀ x : Configuration m,
      Sym2.map Subtype.val e = s(x, x * c m) → x (Fin.last m) ∈ F.selected.toFinset)
    (q : ActualChildPath F j)
    (hinv : ∀ e, e ∈ q.piece.walk.edges ↔ e ∈ w.edges ∧
      e ≠ s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj))
    (e : Sym2 {z : Configuration m // ChildDomain (childGap F j) z})
    (he : e ∈ q.piece.walk.edges) (x : Configuration m)
    (hx : Sym2.map Subtype.val e = s(x, x * c m)) :
    x (Fin.last m) ∈ F.selected.toFinset :=
  hprior e ((hinv e).mp he).1 x hx

/-- Every c edge in this actual parent cycle has a selected terminal.
The literal inventory exhausts all retained child edges and all new outer
seams; no predicate on a separately chosen cycle is substituted. -/
theorem native_parent_cycle_c_labels {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (paths : ∀ j : Fin F.base.length, ActualChildPath F j)
    (hchild : ∀ (j : Fin F.base.length) (e), e ∈ (paths j).piece.walk.edges →
      ∀ x : Configuration m, Sym2.map Subtype.val e = s(x, x * c m) →
        x (Fin.last m) ∈ insert F.terminal F.selected.toFinset)
    (pieces : Fin F.base.length → Piece (domainGraph (ParentDomain F)))
    (hpieces : ∀ j, pieces j = parentPiece F j (paths j))
    {base : {z : Configuration m // ParentDomain F z}}
    (hbase : base.val = rightPort F 0)
    (wparent : (domainGraph (ParentDomain F)).Walk base base)
    (hedges : wparent.edges = s(base, (pieces ⟨F.base.length - 1, by omega⟩).finish) ::
      (chainEdges (pieces ⟨0, by omega⟩)
        (List.ofFn fun i : Fin (F.base.length - 1) =>
          pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse)
    (x : Configuration m) (he : s(x, x * c m) ∈ wparent.edges.map (Sym2.map Subtype.val)) :
    x (Fin.last m) ∈ insert F.terminal F.selected.toFinset := by
  classical
  let p := pieces ⟨0, by omega⟩
  let ps := List.ofFn fun i : Fin (F.base.length - 1) =>
    pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩
  have hlist : p :: ps = List.ofFn pieces := by
    dsimp only [p, ps]
    apply List.ext_getElem
    · simp only [List.length_cons, List.length_ofFn]; omega
    · intro i hi hj
      cases i with
      | zero => simp only [List.getElem_cons_zero, List.getElem_ofFn]
      | succ i => simp only [List.getElem_cons_succ, List.getElem_ofFn]
  have hfinish (j : Fin F.base.length) : (pieces j).finish.val (Fin.last m) =
      F.terminal := by
    rw [hpieces j]
    change (paths j).piece.finish.val (Fin.last m) = _
    rw [(paths j).finish_eq, left_port_terminal hm F (k + j.val)]
  obtain ⟨e, he, hx⟩ := List.mem_map.mp he
  rw [hedges] at he
  rcases List.mem_cons.mp he with he | he
  · rw [he, Sym2.map_mk] at hx
    apply c_root_label_of_endpoint _ base.val _ x ?_ hx
    rw [hbase, right_port_terminal hm F 0]
    exact Finset.mem_insert_self _ _
  · have hechain : e ∈ chainEdges p ps := List.mem_reverse.mp he
    apply chain_c_labels Subtype.val _ p ps ?_ ?_ e hechain x hx
    · intro z hz e hez x hxe
      rw [hlist] at hz
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
      rw [hpieces j] at hez
      change e ∈ ((paths j).piece.walk.map (childLift F j)).edges at hez
      rw [SimpleGraph.Walk.edges_map] at hez
      obtain ⟨e', he', hmap⟩ := List.mem_map.mp hez
      have hraw : Sym2.map Subtype.val (Sym2.map (childLift F j) e') =
          Sym2.map Subtype.val e' := by
        rw [Sym2.map_map]
        rfl
      exact hchild j e' he' x (hraw.symm.trans ((congrArg (Sym2.map Subtype.val) hmap).trans hxe))
    · intro i hi
      have hz : (p :: ps)[i] ∈ List.ofFn pieces := by
        rw [← hlist]
        exact List.getElem_mem (by omega)
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hz
      rw [← hj, hfinish j]
      exact Finset.mem_insert_self _ _

#print axioms native_special_path_c_labels
#print axioms native_other_path_c_labels
#print axioms native_parent_cycle_c_labels

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
