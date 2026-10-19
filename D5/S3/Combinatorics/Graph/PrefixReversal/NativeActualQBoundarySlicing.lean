/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Earn Two-Cut Q Slicing from Literal Even and Odd Routes. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQRouteSlicing
import D5.S3.Combinatorics.Graph.Walks.ActualRouteCutOrder

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQBoundarySlicing

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQRouteSlicing
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualRouteCutOrder
open private native_internal_seam_adj from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly
open private even_native_route_start even_native_route_finish
  odd_native_route_start odd_native_route_finish from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialBoundaryInstances
open private even_route_seam_step odd_route_seam_step from
  D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary

abbrev QDomain {m k : ℕ} (F : SupplyFrame m k) (A : List (Fin (m + 1)))
    (u : Fin (m + 1)) (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :=
  SpecialDomain (outerFrame F A u hbase)
    (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)

/-- The actual even native route puts the L0 boundary path at position
s+1, strictly after the initial rooted path. These concrete route positions,
together with the actual prior J state, earn the two-cut split of this Λ. -/
theorem native_actual_q_even_three_fragments {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F₀ F₁ : SupplyFrame m (2 * s + 2)) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u]) (hA : 3 ≤ A.length)
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (p q : Fin (m + 1)) (hp : p ∈ F₀.selected.toFinset) (hq : q ∈ F₀.selected.toFinset)
    {base r₀ ℓ₀ r₁ ℓ₁ : {x : Configuration m // QDomain F₀ A u hbase₀ hA x}}
    (w : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk base base)
    (hw : w.IsHamiltonianCycle)
    (hkeepA : ∀ (x y : {v : Configuration m // QDomain F₀ A u hbase₀ hA v}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ w.edges)
    (hkeepB : ∀ (x y : {v : Configuration m // QDomain F₀ A u hbase₀ hA v}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ F₀.selected.toFinset → s(x, y) ∈ w.edges)
    (joint : List (Piece (domainGraph (QDomain F₀ A u hbase₀ hA))))
    (hjointSupport : (joint.flatMap fun z => z.walk.support).Perm w.support.tail)
    (jp : Piece (domainGraph (QDomain F₀ A u hbase₀ hA))) (hjp : jp ∈ joint)
    (hjstart : jp.start.val = rightPort (outerFrame F₀ A u hbase₀) 0)
    (hjfinish : jp.finish.val = leftPort (outerFrame F₁ A u hbase₁) 0)
    (ordered : Fin (2 * s + 3) → Piece (domainGraph (QDomain F₀ A u hbase₀ hA)))
    (hend : ∀ i,
      (ordered i).start = specialVertex hm (outerFrame F₀ A u hbase₀)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)
        (evenPortRoute s ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
      (ordered i).finish = specialVertex hm (outerFrame F₀ A u hbase₀)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)
        (evenPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩))
    (Λ : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk
      (specialVertex hm (outerFrame F₀ A u hbase₀)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega) (0, 0))
      (specialVertex hm (outerFrame F₀ A u hbase₀)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)
        (Fin.last (2 * s + 2), 1)))
    (hΛ : Λ.IsHamiltonian)
    (hΛsupport : Λ.support = (List.ofFn ordered).flatMap fun z => z.walk.support)
    (K H : Finset (Sym2 {x : Configuration m // QDomain F₀ A u hbase₀ hA x}))
    (hK : K.image (Sym2.map Subtype.val) = markedCuts (outerFrame F₀ A u hbase₀))
    (hH : H.image (Sym2.map Subtype.val) = markedCuts (outerFrame F₁ A u hbase₁))
    (hjointInventory : ∀ e, e ∈ joint.flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K ∪ H)
    (hboundaryInventory : ∀ e, e ∈ (List.ofFn ordered).flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K)
    (hr₀ : r₀.val = rightPort (nextFrame F₁ A u hbase₁) 0)
    (hℓ₀ : ℓ₀.val = leftPort (nextFrame F₁ A u hbase₁) 0)
    (hr₁ : r₁.val = rightPort (nextFrame F₀ A u hbase₀) 0)
    (hℓ₁ : ℓ₁.val = leftPort (nextFrame F₀ A u hbase₀) 0) :
    ∃ q₀ : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk
        (specialVertex hm (outerFrame F₀ A u hbase₀)
          (by simp only [outerFrame, List.length_append, List.length_singleton]; omega) (0, 0)) ℓ₀,
      ∃ q₁ : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk r₀ ℓ₁,
      ∃ q₂ : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk r₁
        (specialVertex hm (outerFrame F₀ A u hbase₀)
          (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)
          (Fin.last (2 * s + 2), 1)),
      q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
      q₀.support ++ q₁.support ++ q₂.support = Λ.support ∧
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges = Λ.edges ∧
      q₀.edges ++ q₁.edges ++ q₂.edges = Λ.edges.filter
        (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  classical
  let O := outerFrame F₀ A u hbase₀
  have hB : 3 ≤ O.base.length := by
    simp only [O, outerFrame, List.length_append, List.length_singleton]
    omega
  let sv := specialVertex hm O hB
  have hstart : (ordered 0).start = sv (0, 0) := by
    exact (hend 0).1.trans (congrArg sv (even_native_route_start s))
  have hfinalRoute :
      evenPortRoute s ⟨2 * (Fin.last (2 * s + 2)).val + 1, by omega⟩ =
        (Fin.last (2 * s + 2), 1) := by
    rw [show (⟨2 * (Fin.last (2 * s + 2)).val + 1, by omega⟩ : Fin (2 * (2 * s + 3))) =
      ⟨2 * (2 * s + 3) - 1, by omega⟩ by apply Fin.ext; simp only [Fin.val_mk, Fin.val_last]; omega]
    exact even_native_route_finish s
  have hfinish : (ordered (Fin.last (2 * s + 2))).finish = sv (Fin.last (2 * s + 2), 1) :=
    (hend (Fin.last (2 * s + 2))).2.trans (congrArg sv hfinalRoute)
  have hseams (i : ℕ) (hi : i + 1 < 2 * s + 3) :
      (domainGraph (QDomain F₀ A u hbase₀ hA)).Adj
        (ordered ⟨i, by omega⟩).finish (ordered ⟨i + 1, hi⟩).start := by
    rw [(hend ⟨i, by omega⟩).2, (hend ⟨i + 1, hi⟩).1]
    apply native_internal_seam_adj hm O hB
    change internalSeam (2 * s + 2) (evenRoute s (2 * i + 1))
      (evenRoute s (2 * (i + 1)))
    simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using
      even_route_seam_step s (2 * i + 1) (by omega) (by omega)
  obtain ⟨hlink, hs, hf, _⟩ :=
    actual_ordered_path_is_join ordered Λ hstart hfinish hseams hΛsupport
  let rest := List.ofFn fun i : Fin (2 * s + 2) => ordered i.succ
  have hlist : ordered 0 :: rest = List.ofFn ordered := (List.ofFn_succ (f := ordered)).symm
  let actual := Λ.copy hs.symm hf.symm
  have hactualSupport : actual.support = (ordered 0 :: rest).flatMap fun z => z.walk.support := by
    rw [SimpleGraph.Walk.support_copy, hlist]
    exact hΛsupport
  have hbn : ((ordered 0 :: rest).flatMap fun z => z.walk.support).Nodup := by
    rw [hlist, ← hΛsupport]
    exact hΛ.isPath.support_nodup
  have hpaths : ∀ z ∈ ordered 0 :: rest, z.walk.IsPath := by
    intro z hz
    exact SimpleGraph.Walk.IsPath.mk' ((List.nodup_flatMap.mp hbn).1 z hz)
  have hjn : (joint.flatMap fun z => z.walk.support).Nodup := by
    exact hjointSupport.nodup_iff.mpr hw.isCycle.support_nodup
  have hjpath : jp.walk.IsPath := SimpleGraph.Walk.IsPath.mk'
    ((List.nodup_flatMap.mp hjn).1 jp hjp)
  have hroot : jp.start = (ordered 0).start := by
    apply Subtype.ext
    rw [hjstart, hstart]
    rfl
  have hposition : (ordered ⟨s + 1, by omega⟩).finish = sv (0, 1) :=
    (native_even_left_zero_piece_position hm s O hB ordered (fun i => (hend i).2)
      ⟨s + 1, by omega⟩).mpr rfl
  have hipos : 0 < s + 1 := by omega
  have hi : s + 1 < (ordered 0 :: rest).length := by rw [hlist, List.length_ofFn]; omega
  have hbfinish : ((ordered 0 :: rest)[s + 1]'hi).finish = sv (0, 1) := by
    simpa only [hlist, List.getElem_ofFn] using hposition
  have hboundaryInventory' : ∀ e,
      e ∈ (ordered 0 :: rest).flatMap (fun z => z.walk.edges) ↔ e ∈ w.edges ∧ e ∉ K := by
    rw [hlist]
    exact hboundaryInventory
  obtain ⟨q₀, q₁, q₂, hp₀, hp₁, hp₂, hsupport, hedges, hfiltered⟩ :=
    native_actual_q_route_three_fragments hm F₀ F₁ A u hbase₀ hbase₁ hselected
      p q hp hq (QDomain F₀ A u hbase₀ hA) w hkeepA hkeepB
      joint hjn jp hjp hjpath (ordered 0) rest hlink actual hactualSupport hbn hpaths hroot
      K H hK hH hjointInventory hboundaryInventory' hipos hi rfl hbfinish
      rfl hjfinish hr₀ hℓ₀ hr₁ hℓ₁
  refine ⟨q₀.copy hs rfl, q₁, q₂.copy rfl hf, ?_, hp₁, ?_, ?_, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.isPath_copy] using hp₀
  · simpa only [SimpleGraph.Walk.isPath_copy] using hp₂
  · simpa only [SimpleGraph.Walk.support_copy, actual] using hsupport
  · simpa only [SimpleGraph.Walk.edges_copy, actual] using hedges
  · simpa only [SimpleGraph.Walk.edges_copy, actual] using hfiltered

/-- The actual odd native route puts the L0 boundary path at position
s+1, strictly after the initial rooted path. These concrete route positions,
together with the actual prior J state, earn the two-cut split of this Λ. -/
theorem native_actual_q_odd_three_fragments {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F₀ F₁ : SupplyFrame m (2 * s + 3)) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u]) (hA : 3 ≤ A.length)
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (p q : Fin (m + 1)) (hp : p ∈ F₀.selected.toFinset) (hq : q ∈ F₀.selected.toFinset)
    {base r₀ ℓ₀ r₁ ℓ₁ : {x : Configuration m // QDomain F₀ A u hbase₀ hA x}}
    (w : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk base base)
    (hw : w.IsHamiltonianCycle)
    (hkeepA : ∀ (x y : {v : Configuration m // QDomain F₀ A u hbase₀ hA v}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ w.edges)
    (hkeepB : ∀ (x y : {v : Configuration m // QDomain F₀ A u hbase₀ hA v}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ F₀.selected.toFinset → s(x, y) ∈ w.edges)
    (joint : List (Piece (domainGraph (QDomain F₀ A u hbase₀ hA))))
    (hjointSupport : (joint.flatMap fun z => z.walk.support).Perm w.support.tail)
    (jp : Piece (domainGraph (QDomain F₀ A u hbase₀ hA))) (hjp : jp ∈ joint)
    (hjstart : jp.start.val = rightPort (outerFrame F₀ A u hbase₀) 0)
    (hjfinish : jp.finish.val = leftPort (outerFrame F₁ A u hbase₁) 0)
    (ordered : Fin (2 * s + 4) → Piece (domainGraph (QDomain F₀ A u hbase₀ hA)))
    (hend : ∀ i,
      (ordered i).start = specialVertex hm (outerFrame F₀ A u hbase₀)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)
        (oddPortRoute s ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
      (ordered i).finish = specialVertex hm (outerFrame F₀ A u hbase₀)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)
        (oddPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩))
    (Λ : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk
      (specialVertex hm (outerFrame F₀ A u hbase₀)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega) (0, 0))
      (specialVertex hm (outerFrame F₀ A u hbase₀)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)
        (Fin.last (2 * s + 3), 1)))
    (hΛ : Λ.IsHamiltonian)
    (hΛsupport : Λ.support = (List.ofFn ordered).flatMap fun z => z.walk.support)
    (K H : Finset (Sym2 {x : Configuration m // QDomain F₀ A u hbase₀ hA x}))
    (hK : K.image (Sym2.map Subtype.val) = markedCuts (outerFrame F₀ A u hbase₀))
    (hH : H.image (Sym2.map Subtype.val) = markedCuts (outerFrame F₁ A u hbase₁))
    (hjointInventory : ∀ e, e ∈ joint.flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K ∪ H)
    (hboundaryInventory : ∀ e, e ∈ (List.ofFn ordered).flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K)
    (hr₀ : r₀.val = rightPort (nextFrame F₁ A u hbase₁) 0)
    (hℓ₀ : ℓ₀.val = leftPort (nextFrame F₁ A u hbase₁) 0)
    (hr₁ : r₁.val = rightPort (nextFrame F₀ A u hbase₀) 0)
    (hℓ₁ : ℓ₁.val = leftPort (nextFrame F₀ A u hbase₀) 0) :
    ∃ q₀ : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk
        (specialVertex hm (outerFrame F₀ A u hbase₀)
          (by simp only [outerFrame, List.length_append, List.length_singleton]; omega) (0, 0)) ℓ₀,
      ∃ q₁ : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk r₀ ℓ₁,
      ∃ q₂ : (domainGraph (QDomain F₀ A u hbase₀ hA)).Walk r₁
        (specialVertex hm (outerFrame F₀ A u hbase₀)
          (by simp only [outerFrame, List.length_append, List.length_singleton]; omega)
          (Fin.last (2 * s + 3), 1)),
      q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
      q₀.support ++ q₁.support ++ q₂.support = Λ.support ∧
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges = Λ.edges ∧
      q₀.edges ++ q₁.edges ++ q₂.edges = Λ.edges.filter
        (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  classical
  let O := outerFrame F₀ A u hbase₀
  have hB : 3 ≤ O.base.length := by
    simp only [O, outerFrame, List.length_append, List.length_singleton]
    omega
  let sv := specialVertex hm O hB
  have hstart : (ordered 0).start = sv (0, 0) := by
    exact (hend 0).1.trans (congrArg sv (odd_native_route_start s))
  have hfinalRoute :
      oddPortRoute s ⟨2 * (Fin.last (2 * s + 3)).val + 1, by omega⟩ =
        (Fin.last (2 * s + 3), 1) := by
    rw [show (⟨2 * (Fin.last (2 * s + 3)).val + 1, by omega⟩ : Fin (2 * (2 * s + 4))) =
      ⟨2 * (2 * s + 4) - 1, by omega⟩ by apply Fin.ext; simp only [Fin.val_mk, Fin.val_last]; omega]
    exact odd_native_route_finish s
  have hfinish : (ordered (Fin.last (2 * s + 3))).finish = sv (Fin.last (2 * s + 3), 1) :=
    (hend (Fin.last (2 * s + 3))).2.trans (congrArg sv hfinalRoute)
  have hseams (i : ℕ) (hi : i + 1 < 2 * s + 4) :
      (domainGraph (QDomain F₀ A u hbase₀ hA)).Adj
        (ordered ⟨i, by omega⟩).finish (ordered ⟨i + 1, hi⟩).start := by
    rw [(hend ⟨i, by omega⟩).2, (hend ⟨i + 1, hi⟩).1]
    apply native_internal_seam_adj hm O hB
    change internalSeam (2 * s + 3) (oddRoute s (2 * i + 1))
      (oddRoute s (2 * (i + 1)))
    simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using
      odd_route_seam_step s (2 * i + 1) (by omega) (by omega)
  obtain ⟨hlink, hs, hf, _⟩ :=
    actual_ordered_path_is_join ordered Λ hstart hfinish hseams hΛsupport
  let rest := List.ofFn fun i : Fin (2 * s + 3) => ordered i.succ
  have hlist : ordered 0 :: rest = List.ofFn ordered := (List.ofFn_succ (f := ordered)).symm
  let actual := Λ.copy hs.symm hf.symm
  have hactualSupport : actual.support = (ordered 0 :: rest).flatMap fun z => z.walk.support := by
    rw [SimpleGraph.Walk.support_copy, hlist]
    exact hΛsupport
  have hbn : ((ordered 0 :: rest).flatMap fun z => z.walk.support).Nodup := by
    rw [hlist, ← hΛsupport]
    exact hΛ.isPath.support_nodup
  have hpaths : ∀ z ∈ ordered 0 :: rest, z.walk.IsPath := by
    intro z hz
    exact SimpleGraph.Walk.IsPath.mk' ((List.nodup_flatMap.mp hbn).1 z hz)
  have hjn : (joint.flatMap fun z => z.walk.support).Nodup := by
    exact hjointSupport.nodup_iff.mpr hw.isCycle.support_nodup
  have hjpath : jp.walk.IsPath := SimpleGraph.Walk.IsPath.mk'
    ((List.nodup_flatMap.mp hjn).1 jp hjp)
  have hroot : jp.start = (ordered 0).start := by
    apply Subtype.ext
    rw [hjstart, hstart]
    rfl
  have hposition : (ordered ⟨s + 1, by omega⟩).finish = sv (0, 1) :=
    (native_odd_left_zero_piece_position hm s O hB ordered (fun i => (hend i).2)
      ⟨s + 1, by omega⟩).mpr rfl
  have hipos : 0 < s + 1 := by omega
  have hi : s + 1 < (ordered 0 :: rest).length := by rw [hlist, List.length_ofFn]; omega
  have hbfinish : ((ordered 0 :: rest)[s + 1]'hi).finish = sv (0, 1) := by
    simpa only [hlist, List.getElem_ofFn] using hposition
  have hboundaryInventory' : ∀ e,
      e ∈ (ordered 0 :: rest).flatMap (fun z => z.walk.edges) ↔ e ∈ w.edges ∧ e ∉ K := by
    rw [hlist]
    exact hboundaryInventory
  obtain ⟨q₀, q₁, q₂, hp₀, hp₁, hp₂, hsupport, hedges, hfiltered⟩ :=
    native_actual_q_route_three_fragments hm F₀ F₁ A u hbase₀ hbase₁ hselected
      p q hp hq (QDomain F₀ A u hbase₀ hA) w hkeepA hkeepB
      joint hjn jp hjp hjpath (ordered 0) rest hlink actual hactualSupport hbn hpaths hroot
      K H hK hH hjointInventory hboundaryInventory' hipos hi rfl hbfinish
      rfl hjfinish hr₀ hℓ₀ hr₁ hℓ₁
  refine ⟨q₀.copy hs rfl, q₁, q₂.copy rfl hf, ?_, hp₁, ?_, ?_, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.isPath_copy] using hp₀
  · simpa only [SimpleGraph.Walk.isPath_copy] using hp₂
  · simpa only [SimpleGraph.Walk.support_copy, actual] using hsupport
  · simpa only [SimpleGraph.Walk.edges_copy, actual] using hedges
  · simpa only [SimpleGraph.Walk.edges_copy, actual] using hfiltered

#print axioms native_actual_q_even_three_fragments
#print axioms native_actual_q_odd_three_fragments

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQBoundarySlicing
