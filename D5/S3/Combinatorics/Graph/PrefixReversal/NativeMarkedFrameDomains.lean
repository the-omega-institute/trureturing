/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedFrameDomains
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedFrameDomains
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal native domain identifications carry the same actual cycles, partitions and retained edges between recursive frames. -/
/- exact native marked-frame domain interfaces.
   The current parent domain is exactly the next marked special domain.
   The prior P special domain is exactly the independently defined final
   outer child, so its actual walks lift to the same current parent.
   Two marked selected orders with the same label set have one domain;
   these identities do not choose replacement cycles or endpoint states. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveCycleStep
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains

open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open private p_circle_eq from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open private frame_terminal_fresh from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansionDomains
open private anchor_coordinates bc_terminal from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply

private theorem child_frame_full_perm {m k : ℕ} (F : SupplyFrame m k)
    (j : Fin F.base.length) :
    (F.selected ++ F.base.rotate j.val ++ [F.terminal]).Perm
      (F.selected ++ F.base ++ [F.terminal]) := by
  simpa only [List.append_assoc] using
    ((List.Perm.refl F.selected).append (List.rotate_perm F.base j.val)).append_right [F.terminal]

/-- Every independent outer child has its own literal prior marked
frame. Only the base circle is rotated to its actual gap; the selected
list and terminal are unchanged. This supplies an all-base induction
instance rather than assuming an unrelated cycle on that child graph. -/
def nativeChildFrame {m k : ℕ} (F : SupplyFrame m k)
    (j : Fin F.base.length) : SupplyFrame m k where
  selected := F.selected
  base := F.base.rotate j.val
  terminal := F.terminal
  selected_length := F.selected_length
  prefix_length := by
    simpa only [List.length_append, List.length_rotate] using F.prefix_length
  full_nodup := (child_frame_full_perm F j).nodup_iff.mpr F.full_nodup
  full_labels := fun x => (child_frame_full_perm F j).mem_iff.mpr (F.full_labels x)

private theorem native_child_frame_base_bound {m k : ℕ} (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) (j : Fin F.base.length) :
    3 ≤ (nativeChildFrame F j).base.length := by
  simpa only [nativeChildFrame, List.length_rotate] using hB

theorem native_child_frame_domain {m k : ℕ} (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) (j : Fin F.base.length) (x : Configuration m) :
    SpecialDomain (nativeChildFrame F j)
      (native_child_frame_base_bound F hB j) x ↔
        ChildDomain (childGap F j) x := by
  change Layer F.selected.toFinset _ x ↔ Layer F.selected.toFinset _ x
  have hc : (childGap (nativeChildFrame F j) ⟨0, by
      simpa only [nativeChildFrame, List.length_rotate] using (by omega : 0 < F.base.length)⟩).val =
      (childGap F j).val := by
    change (F.terminal :: (F.base.rotate j.val).rotate 0 : Cycle (Fin (m + 1))) =
      (F.terminal :: F.base.rotate j.val : Cycle (Fin (m + 1)))
    rw [List.rotate_zero]
  rw [hc]

def childMarkedDomainMap {m k : ℕ} (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) (j : Fin F.base.length) :
    domainGraph (SpecialDomain (nativeChildFrame F j)
      (native_child_frame_base_bound F hB j)) →g
        domainGraph (ChildDomain (childGap F j)) :=
  ⟨fun x => ⟨x.val, (native_child_frame_domain F hB j x.val).mp x.property⟩,
    fun h => h⟩

theorem child_marked_domain_map_bijective {m k : ℕ} (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) (j : Fin F.base.length) :
    Function.Bijective (childMarkedDomainMap F hB j) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.val, (native_child_frame_domain F hB j y.val).mpr y.property⟩, Subtype.ext rfl⟩

/-- A supplied prior marked cycle is converted into the specified
ordinary-child input of the parent constructor. Its remaining-b
invariant proves the actual supplier cut, and the returned child cycle
is exactly the image of this same walk, with literal raw inventories. -/
theorem native_child_frame_specified_ordinary {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (j : Fin F.base.length) (hj : 0 < j.val)
    {a : {x : Configuration m // SpecialDomain (nativeChildFrame F j)
      (native_child_frame_base_bound F hB j) x}}
    (w : (domainGraph (SpecialDomain (nativeChildFrame F j)
      (native_child_frame_base_bound F hB j))).Walk a a)
    (hw : w.IsHamiltonianCycle)
    (hkeepB : ∀ (x y : {v : Configuration m // SpecialDomain (nativeChildFrame F j)
        (native_child_frame_base_bound F hB j) v}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ F.selected.toFinset → s(x, y) ∈ w.edges) :
    ∃ C : SpecifiedOrdinaryCycle hm F hB j hj,
      ∃ hbase : C.base = childMarkedDomainMap F hB j a,
        C.walk.copy hbase hbase = w.map (childMarkedDomainMap F hB j) ∧
        C.walk.support.map Subtype.val = w.support.map Subtype.val ∧
        C.walk.edges.map (Sym2.map Subtype.val) = w.edges.map (Sym2.map Subtype.val) ∧
        (∀ hk : 2 ≤ k,
          protectedP (nativeChildFrame F j) hk = protectedP F hk ∧
            protectedQ (nativeChildFrame F j) hk = protectedQ F hk) := by
  let lift := childMarkedDomainMap F hB j
  let r := ordinaryRight hm F hB j hj
  let l := ordinaryLeft hm F hB j hj
  let r' : {v : Configuration m // SpecialDomain (nativeChildFrame F j)
      (native_child_frame_base_bound F hB j) v} :=
    ⟨r.val, (native_child_frame_domain F hB j r.val).mpr r.property⟩
  let l' : {v : Configuration m // SpecialDomain (nativeChildFrame F j)
      (native_child_frame_base_bound F hB j) v} :=
    ⟨l.val, (native_child_frame_domain F hB j l.val).mpr l.property⟩
  have hterminal : r'.val (Fin.last m) ∉ F.selected.toFinset := by
    rw [show r'.val = rightPort F (k + j.val) by rfl]
    rw [rightPort, bc_terminal (by omega : 2 ≤ m), (anchor_coordinates F).2]
    simp only [List.mem_toFinset]
    exact fun h => frame_terminal_fresh F (List.mem_append.mpr (Or.inl h))
  have hcut : s(r, l) ∈ (w.map lift).edgeSet := by
    change s(r, l) ∈ (w.map lift).edges
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(r', l'), hkeepB r' l' rfl hterminal, rfl⟩
  let C : SpecifiedOrdinaryCycle hm F hB j hj :=
    ⟨lift a, w.map lift, SimpleGraph.Walk.IsHamiltonianCycle.map
      (child_marked_domain_map_bijective F hB j) hw, hcut⟩
  refine ⟨C, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [C, SimpleGraph.Walk.support_map, List.map_map]
    rfl
  · simp only [C, SimpleGraph.Walk.edges_map, List.map_map, Function.comp_def, Sym2.map_map]
    rfl
  · intro hk
    exact native_protected_labels_same_selected F (nativeChildFrame F j) hk rfl

/-- Swapping the selected p/q order changes ports, but not the actual
native configuration domain. The base and terminal keep their literal
order; only equality of the selected label sets is used. -/
theorem native_marked_orders_same_domain {m k : ℕ}
    (F₀ F₁ : SupplyFrame m k) (hB₀ : 3 ≤ F₀.base.length) (hB₁ : 3 ≤ F₁.base.length)
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (hbase : F₀.base = F₁.base) (hterminal : F₀.terminal = F₁.terminal)
    (x : Configuration m) :
    SpecialDomain F₀ hB₀ x ↔ SpecialDomain F₁ hB₁ x := by
  change Layer F₀.selected.toFinset _ x ↔ Layer F₁.selected.toFinset _ x
  have hc₀ : (childGap F₀ ⟨0, by omega⟩).val =
      (F₀.terminal :: F₀.base : Cycle (Fin (m + 1))) := by
    change (F₀.terminal :: F₀.base.rotate 0 : Cycle (Fin (m + 1))) = _
    rw [List.rotate_zero]
  have hc₁ : (childGap F₁ ⟨0, by omega⟩).val =
      (F₁.terminal :: F₁.base : Cycle (Fin (m + 1))) := by
    change (F₁.terminal :: F₁.base.rotate 0 : Cycle (Fin (m + 1))) = _
    rw [List.rotate_zero]
  rw [hc₀, hc₁, hselected, hbase, hterminal]

/-- Reindex only the marked order, keeping every actual configuration.
This lets two orders refer to one supplied cycle instead of independently
choosing a cycle on each equal native domain. -/
def markedOrderDomainMap {m k : ℕ}
    (F₀ F₁ : SupplyFrame m k) (hB₀ : 3 ≤ F₀.base.length) (hB₁ : 3 ≤ F₁.base.length)
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (hbase : F₀.base = F₁.base) (hterminal : F₀.terminal = F₁.terminal) :
    domainGraph (SpecialDomain F₀ hB₀) →g domainGraph (SpecialDomain F₁ hB₁) :=
  ⟨fun x => ⟨x.val,
    (native_marked_orders_same_domain F₀ F₁ hB₀ hB₁ hselected hbase hterminal x.val).mp
      x.property⟩, fun h => h⟩

theorem marked_order_domain_map_bijective {m k : ℕ}
    (F₀ F₁ : SupplyFrame m k) (hB₀ : 3 ≤ F₀.base.length) (hB₁ : 3 ≤ F₁.base.length)
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (hbase : F₀.base = F₁.base) (hterminal : F₀.terminal = F₁.terminal) :
    Function.Bijective
      (markedOrderDomainMap F₀ F₁ hB₀ hB₁ hselected hbase hterminal) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.val,
      (native_marked_orders_same_domain F₀ F₁ hB₀ hB₁ hselected hbase hterminal y.val).mpr
        y.property⟩, Subtype.ext rfl⟩

/-- The two actual outer parents differ only in their selected order.
Their entire native domains agree; base order is not reversed. -/
theorem native_outer_orders_same_domain {m k : ℕ}
    (F₀ F₁ : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u])
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (hterminal : F₀.terminal = F₁.terminal) (x : Configuration m) :
    ParentDomain (outerFrame F₀ A u hbase₀) x ↔
      ParentDomain (outerFrame F₁ A u hbase₁) x := by
  change Layer (insert u F₀.selected.toFinset) (A ++ [F₀.terminal] : Cycle (Fin (m + 1))) x ↔
    Layer (insert u F₁.selected.toFinset) (A ++ [F₁.terminal] : Cycle (Fin (m + 1))) x
  rw [hselected, hterminal]

def parentOrderDomainMap {m k : ℕ}
    (F₀ F₁ : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u])
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (hterminal : F₀.terminal = F₁.terminal) :
    domainGraph (ParentDomain (outerFrame F₀ A u hbase₀)) →g
      domainGraph (ParentDomain (outerFrame F₁ A u hbase₁)) :=
  ⟨fun x => ⟨x.val,
    (native_outer_orders_same_domain F₀ F₁ A u hbase₀ hbase₁ hselected hterminal x.val).mp
      x.property⟩, fun h => h⟩

theorem parent_order_domain_map_bijective {m k : ℕ}
    (F₀ F₁ : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u])
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (hterminal : F₀.terminal = F₁.terminal) :
    Function.Bijective
      (parentOrderDomainMap F₀ F₁ A u hbase₀ hbase₁ hselected hterminal) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.val,
      (native_outer_orders_same_domain F₀ F₁ A u hbase₀ hbase₁ hselected hterminal y.val).mpr
        y.property⟩, Subtype.ext rfl⟩

/-- Literal circular rotation identifies the P old marked domain with
the final outer child. This is equality of every vertex domain, rather
than ownership only for the marked-port endpoints. -/
theorem native_p_marked_domain_eq_child {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) (x : Configuration m) :
    SpecialDomain F (by simp only [hbase, List.length_append, List.length_singleton]; omega) x ↔
      ChildDomain (childGap (outerFrame F A u hbase)
        ⟨A.length, by simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩) x := by
  change Layer F.selected.toFinset _ x ↔ Layer F.selected.toFinset _ x
  rw [p_circle_eq F A u hbase]

/-- The cycle constructed on the current outer parent is already on
the independently specified next marked domain. No new cycle is chosen
when carrying the next J/E/O state into the following induction step. -/
theorem native_next_marked_domain_eq_parent {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) (x : Configuration m) :
    SpecialDomain (nextFrame F A u hbase) (by simpa only [nextFrame] using hA) x ↔
      ParentDomain (outerFrame F A u hbase) x := by
  change Layer (u :: F.selected).toFinset
      (childGap (nextFrame F A u hbase) ⟨0, by simpa only [nextFrame] using (by omega : 0 < A.length)⟩).val x ↔
    Layer (insert u F.selected.toFinset) (A ++ [F.terminal] : Cycle (Fin (m + 1))) x
  have hc : (childGap (nextFrame F A u hbase)
      ⟨0, by simpa only [nextFrame] using (by omega : 0 < A.length)⟩).val =
      (F.terminal :: A : Cycle (Fin (m + 1))) := by
    change (F.terminal :: A.rotate 0 : Cycle (Fin (m + 1))) = _
    rw [List.rotate_zero]
  have hcircle : (F.terminal :: A : Cycle (Fin (m + 1))) = (A ++ [F.terminal] : Cycle (Fin (m + 1))) := by
    apply Cycle.coe_eq_coe.mpr
    simpa only [List.singleton_append] using
      List.isRotated_append (l := [F.terminal]) (l' := A)
  rw [hc, List.toFinset_cons, hcircle]

/-- Carry the actual current parent into its next marked domain without
changing any raw configuration, walk edge, or marked-order orientation. -/
def parentNextMarkedMap {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    domainGraph (ParentDomain (outerFrame F A u hbase)) →g
      domainGraph (SpecialDomain (nextFrame F A u hbase)
        (by simpa only [nextFrame] using hA)) :=
  ⟨fun x => ⟨x.val, (native_next_marked_domain_eq_parent F A u hbase hA x.val).mpr
    x.property⟩, fun h => h⟩

theorem parent_next_marked_map_bijective {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    Function.Bijective (parentNextMarkedMap F A u hbase hA) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.val, (native_next_marked_domain_eq_parent F A u hbase hA y.val).mp
      y.property⟩, Subtype.ext rfl⟩

/-- The supplied actual parent cycle is the next induction cycle. Its
protected-a and remaining-b edges descend to the independently specified
next marked domain, with literal raw support and edge inventories. -/
theorem native_same_parent_cycle_next_marked {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (p q : Fin (m + 1))
    {a₀ : {x : Configuration m // ParentDomain (outerFrame F A u hbase) x}}
    (c : (domainGraph (ParentDomain (outerFrame F A u hbase))).Walk a₀ a₀)
    (hc : c.IsHamiltonianCycle)
    (hkeepA : ∀ (x y : {v : Configuration m // ParentDomain (outerFrame F A u hbase) v}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ c.edges)
    (hkeepB : ∀ (x y : {v : Configuration m // ParentDomain (outerFrame F A u hbase) v}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ insert u F.selected.toFinset →
        s(x, y) ∈ c.edges) :
    let N := nextFrame F A u hbase
    let hN : 3 ≤ N.base.length := by simpa only [N, nextFrame] using hA
    let lift := parentNextMarkedMap F A u hbase hA
    let next := c.map lift
    next.IsHamiltonianCycle ∧
      next.support.map Subtype.val = c.support.map Subtype.val ∧
      next.edges.map (Sym2.map Subtype.val) = c.edges.map (Sym2.map Subtype.val) ∧
      (∀ (x y : {v : Configuration m // SpecialDomain N hN v}),
        y.val = x.val * a m →
        s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ next.edges) ∧
      (∀ (x y : {v : Configuration m // SpecialDomain N hN v}),
        y.val = x.val * b m → x.val (Fin.last m) ∉ N.selected.toFinset →
          s(x, y) ∈ next.edges) := by
  dsimp only
  have hinverse (x : {v : Configuration m // SpecialDomain (nextFrame F A u hbase)
      (by simpa only [nextFrame] using hA) v}) :
      ParentDomain (outerFrame F A u hbase) x.val :=
    (native_next_marked_domain_eq_parent F A u hbase hA x.val).mp x.property
  refine ⟨SimpleGraph.Walk.IsHamiltonianCycle.map
    (parent_next_marked_map_bijective F A u hbase hA) hc, ?_, ?_, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.support_map, List.map_map]
    rfl
  · simp only [SimpleGraph.Walk.edges_map, List.map_map, Function.comp_def, Sym2.map_map]
    rfl
  · intro x y hxy hprotected
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(⟨x.val, hinverse x⟩, ⟨y.val, hinverse y⟩),
      hkeepA _ _ hxy hprotected, rfl⟩
  · intro x y hxy hterminal
    rw [SimpleGraph.Walk.edges_map]
    have hterminal' : x.val (Fin.last m) ∉ insert u F.selected.toFinset := by
      simpa only [nextFrame, List.toFinset_cons] using hterminal
    exact List.mem_map.mpr ⟨s(⟨x.val, hinverse x⟩, ⟨y.val, hinverse y⟩),
      hkeepB _ _ hxy hterminal', rfl⟩

/-- Inclusion of the whole prior P marked domain into the actual current
parent. The map preserves each literal configuration and is injective,
so mapping prior paths keeps their actual support and edge identities. -/
def pMarkedParentLift {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    domainGraph (SpecialDomain F (by simp only [hbase, List.length_append, List.length_singleton]; omega)) →g
      domainGraph (ParentDomain (outerFrame F A u hbase)) :=
  ⟨fun x => ⟨x.val, childDomain_parent _
    ((native_p_marked_domain_eq_child F A u hbase hA x.val).mp x.property)⟩,
    fun h => h⟩

theorem p_marked_parent_lift_injective {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    Function.Injective (pMarkedParentLift F A u hbase hA) := by
  intro x y h
  have hv := congrArg Subtype.val h
  exact Subtype.ext hv

#print axioms native_marked_orders_same_domain
#print axioms native_p_marked_domain_eq_child
#print axioms native_next_marked_domain_eq_parent
#print axioms native_same_parent_cycle_next_marked
#print axioms native_child_frame_domain
#print axioms native_child_frame_specified_ordinary

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
