/- UNCOMPILED exact native marked-frame domain interfaces.
   The current parent domain is exactly the next marked special domain.
   The prior P special domain is exactly the independently defined final
   outer child, so its actual walks lift to the same current parent.
   Two marked selected orders with the same label set have one domain;
   these identities do not choose replacement cycles or endpoint states. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open private p_circle_eq from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates

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
    change (F₀.terminal :: F₀.base.rotate 0 : Cycle _) = _
    rw [List.rotate_zero]
  have hc₁ : (childGap F₁ ⟨0, by omega⟩).val =
      (F₁.terminal :: F₁.base : Cycle (Fin (m + 1))) := by
    change (F₁.terminal :: F₁.base.rotate 0 : Cycle _) = _
    rw [List.rotate_zero]
  rw [hc₀, hc₁, hselected, hbase, hterminal]

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
    change (F.terminal :: A.rotate 0 : Cycle _) = _
    rw [List.rotate_zero]
  have hcircle : (F.terminal :: A : Cycle (Fin (m + 1))) = (A ++ [F.terminal] : Cycle _) := by
    apply Cycle.coe_eq_coe.mpr
    simpa only [List.singleton_append] using
      List.isRotated_append (l := [F.terminal]) (l' := A)
  rw [hc, List.toFinset_cons, hcircle]

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
  exact Subtype.ext (congrArg Subtype.val h)

#print axioms native_marked_orders_same_domain
#print axioms native_p_marked_domain_eq_child
#print axioms native_next_marked_domain_eq_parent

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
