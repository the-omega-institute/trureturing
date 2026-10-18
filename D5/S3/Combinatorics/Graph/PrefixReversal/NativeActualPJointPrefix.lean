/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualPJointPrefix
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualPJointPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Earn the Actual Native P Prefix and Retained Q Cuts. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedCutRetention
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
import D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix
open private right_port_terminal from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedCutRetention
open private frame_selected_base_disjoint frame_terminal_fresh from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansionDomains

private theorem a_not_marked {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (x y : Configuration m) (hy : y = x * a m) :
    s(x, y) ∉ markedCuts F := by
  classical
  intro he
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  change s(rightPort F i.val, leftPort F i.val) = s(x, y) at hi
  rw [hy, leftPort] at hi
  exact native_a_edge_ne_b_edge hm x (rightPort F i.val) hi.symm

private theorem b_not_marked {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (x y : Configuration m) (hy : y = x * b m)
    (hx : x (Fin.last m) ≠ F.terminal) : s(x, y) ∉ markedCuts F := by
  classical
  intro he
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  change s(rightPort F i.val, leftPort F i.val) = s(x, y) at hi
  rw [hy, leftPort] at hi
  exact native_b_edges_distinct_terminals x (rightPort F i.val)
    (by rw [right_port_terminal hm F i.val]; exact hx) hi.symm

/-- No P-prefix assumption is made. The source invariants concern the
actual old cycle w, and the old joint inventory assigns its retained
edges to actual pieces. The final supplier b is distinct from the old
marked groups because its terminal u is an unselected base label. -/
theorem native_actual_p_joint_prefix {m k : ℕ} (hm : 3 ≤ m)
    (F₀ F₁ : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F₀.base = A ++ [u]) (hterminal : F₁.terminal = F₀.terminal)
    (p q : Fin (m + 1)) (hp : p ∈ F₀.selected.toFinset) (hq : q ∈ F₀.selected.toFinset)
    (D : Configuration m → Prop)
    {base ℓ s t z : {x : Configuration m // D x}}
    (w : (domainGraph D).Walk base base)
    (hA : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ w.edges)
    (hB : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * b m →
      x.val (Fin.last m) ∉ F₀.selected.toFinset → s(x, y) ∈ w.edges)
    (d : (domainGraph D).Walk ℓ z) (rest : List (Piece (domainGraph D)))
    (hn : (d.support ++ rest.flatMap fun r => r.walk.support).Nodup)
    (K : Finset (Sym2 {x : Configuration m // D x}))
    (hK : K.image (Sym2.map Subtype.val) = markedCuts F₀ ∪ markedCuts F₁)
    (hinv : ∀ e, e ∈ ((⟨ℓ, z, d⟩ :: rest).flatMap fun r => r.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K)
    (hℓ : ℓ.val = leftPort F₀ 0)
    (hs : s.val = ℓ.val * a m) (ht : t.val = s.val * b m) :
    ∃ (hₐ : (domainGraph D).Adj ℓ s) (h_b : (domainGraph D).Adj s t)
      (tail : (domainGraph D).Walk t z),
      d = (tail.cons h_b).cons hₐ ∧ tail.IsPath ∧
      d.support = ℓ :: s :: tail.support ∧
      d.edges = s(ℓ, s) :: s(s, t) :: tail.edges := by
  classical
  have huBase : u ∈ F₀.base := by
    rw [hbase]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have huSelected : u ∉ F₀.selected.toFinset := by
    intro hu
    exact List.disjoint_left.mp (frame_selected_base_disjoint F₀) (List.mem_toFinset.mp hu) huBase
  have huTerminal : u ≠ F₀.terminal := by
    intro hu
    exact frame_terminal_fresh F₀ (List.mem_append.mpr (Or.inr (hu ▸ huBase)))
  have hℓLast : ℓ.val (Fin.last m) = F₀.terminal := by
    rw [hℓ, leftPort, Equiv.Perm.mul_apply, b_last, right_port_terminal hm F₀ 0]
  have hsPort : s.val = rightPort (outerFrame F₀ A u hbase) (m - 1) := by
    rw [hs, hℓ]
    exact (native_p_parent_cut_prefix hm F₀ A u hbase).1
  have hsLast : s.val (Fin.last m) = u := by
    rw [hsPort, right_port_terminal hm (outerFrame F₀ A u hbase) (m - 1)]
    rfl
  have htLast : t.val (Fin.last m) = u := by rw [ht, Equiv.Perm.mul_apply, b_last, hsLast]
  have hprotected : s(ℓ.val (Fin.last m), s.val (Fin.last m)) ≠ s(p, q) := by
    rw [hℓLast, hsLast]
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, huq⟩ | ⟨_, hup⟩
    · exact huSelected (huq.symm ▸ hq)
    · exact huSelected (hup.symm ▸ hp)
  have hAraw : s(ℓ.val, s.val) ∉ markedCuts F₀ ∪ markedCuts F₁ := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact a_not_marked hm F₀ ℓ.val s.val hs he
    · exact a_not_marked hm F₁ ℓ.val s.val hs he
  have hBraw : s(s.val, t.val) ∉ markedCuts F₀ ∪ markedCuts F₁ := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact b_not_marked hm F₀ s.val t.val ht (by rw [hsLast]; exact huTerminal) he
    · exact b_not_marked hm F₁ s.val t.val ht (by rw [hsLast, hterminal]; exact huTerminal) he
  have hAnot : s(ℓ, s) ∉ K := by
    intro he
    apply hAraw
    rw [← hK]
    exact Finset.mem_image.mpr ⟨s(ℓ, s), he, rfl⟩
  have hBnot : s(s, t) ∉ K := by
    intro he
    apply hBraw
    rw [← hK]
    exact Finset.mem_image.mpr ⟨s(s, t), he, rfl⟩
  have hAkeep := (hinv s(ℓ, s)).mpr ⟨hA ℓ s hs hprotected, hAnot⟩
  have hBkeep := (hinv s(s, t)).mpr ⟨hB s t ht (by rw [hsLast]; exact huSelected), hBnot⟩
  have htneq : t ≠ ℓ := by
    intro he
    have h := congrArg (fun v => v.val (Fin.last m)) he
    rw [htLast, hℓLast] at h
    exact huTerminal h
  exact actual_piece_prefix_from_retained_inventory (⟨ℓ, z, d⟩ :: rest)
    (by simpa only [List.flatMap_cons] using hn) ⟨ℓ, z, d⟩ List.mem_cons_self
    (SimpleGraph.Walk.IsPath.mk' (List.nodup_append'.mp hn).1) hAkeep hBkeep htneq

#print axioms native_actual_p_joint_prefix

/-- The two literal Q zero-cut prefix edges survive the old actual Q
joint partition. Its supplier terminal is u, while the new b has terminal
F.terminal; these labels differ because u belongs to the old base. The
protected a joins precisely those two remaining labels. Applying this
to each selected order supplies the real retained edges used by the
ordered Q slicing, without assuming their membership in a desired route. -/
theorem native_actual_q_zero_cut_retained {m k : ℕ} (hm : 3 ≤ m)
    (F G : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hGterminal : G.terminal = u)
    (p q : Fin (m + 1)) (hp : p ∈ F.selected.toFinset) (hq : q ∈ F.selected.toFinset)
    (D : Configuration m → Prop)
    {base w₀ r ℓ : {x : Configuration m // D x}}
    (w : (domainGraph D).Walk base base)
    (hA : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ w.edges)
    (hB : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * b m →
      x.val (Fin.last m) ∉ F.selected.toFinset → s(x, y) ∈ w.edges)
    (pieces : List (Piece (domainGraph D)))
    (K : Finset (Sym2 {x : Configuration m // D x}))
    (hK : K.image (Sym2.map Subtype.val) = markedCuts (outerFrame F A u hbase) ∪ markedCuts G)
    (hinv : ∀ e, e ∈ (pieces.flatMap fun z => z.walk.edges) ↔ e ∈ w.edges ∧ e ∉ K)
    (hw₀ : w₀.val = leftPort (outerFrame F A u hbase) 0)
    (hr : r.val = rightPort (nextFrame F A u hbase) 0)
    (hℓ : ℓ.val = leftPort (nextFrame F A u hbase) 0) :
    s(w₀, r) ∈ pieces.flatMap (fun z => z.walk.edges) ∧
      s(r, ℓ) ∈ pieces.flatMap (fun z => z.walk.edges) ∧ ℓ ≠ w₀ := by
  classical
  have huBase : u ∈ F.base := by
    rw [hbase]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have huTerminal : u ≠ F.terminal := fun he =>
    frame_terminal_fresh F (List.mem_append.mpr (Or.inr (he ▸ huBase)))
  have htSelected : F.terminal ∉ F.selected.toFinset := by
    simp only [List.mem_toFinset]
    exact fun h => frame_terminal_fresh F (List.mem_append.mpr (Or.inl h))
  have hwa : r.val = w₀.val * a m := by
    rw [hw₀, hr]
    exact (native_q_index_zero_prefix hm F A u hbase).1.symm
  have hrb : ℓ.val = r.val * b m := by rw [hℓ, hr]; rfl
  have hwLast : w₀.val (Fin.last m) = u := by
    rw [hw₀, leftPort, Equiv.Perm.mul_apply, b_last,
      right_port_terminal hm (outerFrame F A u hbase) 0]
    rfl
  have hrLast : r.val (Fin.last m) = F.terminal := by
    rw [hr, right_port_terminal hm (nextFrame F A u hbase) 0]
    rfl
  have hℓLast : ℓ.val (Fin.last m) = F.terminal := by
    rw [hrb, Equiv.Perm.mul_apply, b_last, hrLast]
  have hprotected : s(w₀.val (Fin.last m), r.val (Fin.last m)) ≠ s(p, q) := by
    rw [hwLast, hrLast]
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, htq⟩ | ⟨_, htp⟩
    · exact htSelected (htq.symm ▸ hq)
    · exact htSelected (htp.symm ▸ hp)
  have hAraw : s(w₀.val, r.val) ∉ markedCuts (outerFrame F A u hbase) ∪ markedCuts G := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact a_not_marked hm (outerFrame F A u hbase) w₀.val r.val hwa he
    · exact a_not_marked hm G w₀.val r.val hwa he
  have hBraw : s(r.val, ℓ.val) ∉ markedCuts (outerFrame F A u hbase) ∪ markedCuts G := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact b_not_marked hm (outerFrame F A u hbase) r.val ℓ.val hrb
        (by rw [hrLast]; exact huTerminal.symm) he
    · exact b_not_marked hm G r.val ℓ.val hrb
        (by rw [hrLast, hGterminal]; exact huTerminal.symm) he
  have hAnot : s(w₀, r) ∉ K := by
    intro he
    apply hAraw
    rw [← hK]
    exact Finset.mem_image.mpr ⟨s(w₀, r), he, rfl⟩
  have hBnot : s(r, ℓ) ∉ K := by
    intro he
    apply hBraw
    rw [← hK]
    exact Finset.mem_image.mpr ⟨s(r, ℓ), he, rfl⟩
  exact ⟨(hinv _).mpr ⟨hA w₀ r hwa hprotected, hAnot⟩,
    (hinv _).mpr ⟨hB r ℓ hrb (by rw [hrLast]; exact htSelected), hBnot⟩,
    fun h => by
      have ht := congrArg (fun x => x.val (Fin.last m)) h
      rw [hℓLast, hwLast] at ht
      exact huTerminal ht.symm⟩

#print axioms native_actual_q_zero_cut_retained

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix
