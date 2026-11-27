module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Preorder.Finite
import OmegaBuild.Commands

/-!
Omega original.

The size of a side of an extremal bridge in a finite poset. This is the
order-theoretic counting step for the small finite spaces in Conjecture 6.1
of Mosquera-Lois and Tanaka (https://arxiv.org/abs/2609.39615v1).
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace Omega.ExtremalBridge

variable {X : Type*} [PartialOrder X]

/-- The simple graph with an edge between each pair of strictly comparable elements. -/
def comparabilityGraph (X : Type*) [PartialOrder X] : SimpleGraph X :=
  SimpleGraph.fromRel (· < ·)

private theorem adj_iff {x y : X} : (comparabilityGraph X).Adj x y ↔ x < y ∨ y < x := by
  rw [comparabilityGraph, SimpleGraph.fromRel_adj]
  exact ⟨And.right, fun h => ⟨h.elim ne_of_lt (fun hyx => (ne_of_lt hyx).symm), h⟩⟩

/-- An up beat point has a least element strictly above it. -/
def IsUpBeatPoint (x : X) : Prop := ∃ y, IsLeast (Set.Ioi x) y

/-- A down beat point has a greatest element strictly below it. -/
def IsDownBeatPoint (x : X) : Prop := ∃ y, IsGreatest (Set.Iio x) y

private theorem beat_of_unique_neighbor {x : X}
    (h : ∃! y, (comparabilityGraph X).Adj x y) : IsUpBeatPoint x ∨ IsDownBeatPoint x := by
  obtain ⟨y, hy, unique⟩ := h
  rcases adj_iff.mp hy with hxy | hyx
  · exact Or.inl ⟨y, hxy, fun z hz => (unique z (adj_iff.mpr (Or.inl hz))).symm.le⟩
  · exact Or.inr ⟨y, hyx, fun z hz => (unique z (adj_iff.mpr (Or.inr hz))).le⟩

/-- A finite nontrivial poset whose comparability graph is a tree has two distinct
beat points, one at each of two leaves of the tree. -/
theorem exists_two_beat_points_of_isTree [Finite X] [Nontrivial X]
    (h : (comparabilityGraph X).IsTree) :
    ∃ u v : X, u ≠ v ∧ (IsUpBeatPoint u ∨ IsDownBeatPoint u) ∧
      (IsUpBeatPoint v ∨ IsDownBeatPoint v) := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨u, v, huv, hu, hv⟩ := h.exists_ne_and_degree_eq_one
  exact ⟨u, v, huv,
    beat_of_unique_neighbor (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu),
    beat_of_unique_neighbor (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv)⟩

private theorem exists_min_le [Finite X] (x : X) : ∃ p : X, IsMin p ∧ p ≤ x := by
  obtain ⟨p, hpx, hp⟩ := Finite.exists_le_minimal (p := fun y : X => y ≤ x) (le_refl x)
  exact ⟨p, fun _ h => hp.2 (h.trans hpx) h, hpx⟩

private theorem exists_two_min_lt [Finite X] {x : X} (hx : ¬ IsMin x)
    (hDown : ∀ z ≤ x, ¬ IsDownBeatPoint z) :
    ∃ p q : X, IsMin p ∧ IsMin q ∧ p ≠ q ∧ p < x ∧ q < x := by
  classical
  obtain ⟨y, hyx⟩ := not_isMin_iff.mp hx
  obtain ⟨p, hp, hpy⟩ := exists_min_le y
  have hpx := hpy.trans_lt hyx
  -- Choose a minimal point above p in the interval ending at x.
  obtain ⟨z, _, hz⟩ := Finite.exists_le_minimal (p := fun w : X => p < w ∧ w ≤ x)
    ⟨hpx, le_rfl⟩
  -- The failure of p to be greatest below z gives a second minimum below x.
  have h : ¬ ∀ w < z, w ≤ p := fun hall =>
    hDown z hz.1.2 ⟨p, hz.1.1, hall⟩
  obtain ⟨w, hw⟩ := not_forall.mp h
  obtain ⟨hwz, hwp⟩ := not_imp.mp hw
  obtain ⟨q, hq, hqw⟩ := exists_min_le w
  refine ⟨p, q, hp, hq, ?_, hpx, (hqw.trans_lt hwz).trans_le hz.1.2⟩
  rintro rfl
  exact hwz.not_ge (hz.2 ⟨lt_of_le_not_ge hqw hwp, hwz.le.trans hz.1.2⟩ hwz.le)

private theorem six_le_card_of_chain [Finite X] {a l x r : X}
    (ha : IsMin a) (hlx : l < x) (hxr : x < r)
    (hUp : ∀ z : X, IsUpBeatPoint z → z = a) (hDown : ∀ z : X, ¬ IsDownBeatPoint z) :
    6 ≤ Nat.card X := by
  classical
  obtain ⟨p, q, hp, hq, hpq, hpx, hqx⟩ :=
    exists_two_min_lt (not_isMin_iff.mpr ⟨l, hlx⟩) (fun z _ => hDown z)
  have hAbove (z : Xᵒᵈ) (hz : z ≤ OrderDual.toDual x) : ¬ IsDownBeatPoint z := by
    intro h
    have hza : OrderDual.ofDual z = a := hUp _ h
    exact ha.not_lt (show l < a from hza ▸ hlx.trans_le hz)
  obtain ⟨u, v, _, _, huvDual, hxu, hxv⟩ := exists_two_min_lt (X := Xᵒᵈ)
    (not_isMin_iff.mpr ⟨OrderDual.toDual r, hxr⟩) hAbove
  change X at u v
  have huv : u ≠ v := huvDual
  change x < u at hxu
  change x < v at hxv
  -- Use a minimum other than the distinguished endpoint.
  wlog hpa : p ≠ a generalizing p q
  · have hqa : q ≠ a := fun he => hpq ((not_not.mp hpa).trans he.symm)
    exact this q p hq hp hpq.symm hqx hpx hqa
  have h : ¬ ∀ z, p < z → x ≤ z := fun hall => hpa (hUp p ⟨x, hpx, hall⟩)
  obtain ⟨y, hy⟩ := not_forall.mp h
  obtain ⟨hpy, hxy⟩ := not_imp.mp hy
  have hyx : y ≠ x := fun e => hxy e.ge
  have hyu : y ≠ u := fun e => hxy (e.symm ▸ hxu.le)
  have hyv : y ≠ v := fun e => hxy (e.symm ▸ hxv.le)
  have hyp : y ≠ p := (ne_of_lt hpy).symm
  have hyq : y ≠ q := fun e => hq.not_lt (e ▸ hpy)
  let := Fintype.ofFinite X
  have hSix : ({y, p, q, x, u, v} : Finset X).card = 6 := by
    simp [Finset.mem_insert, Finset.mem_singleton, hyx, hyu, hyv,
      hyp, hyq, hpq, huv, hpx.ne, hqx.ne, hxu.ne, hxv.ne, (hpx.trans hxu).ne,
      (hpx.trans hxv).ne, (hqx.trans hxu).ne, (hqx.trans hxv).ne]
  rw [Nat.card_eq_fintype_card, ← hSix]
  exact Finset.card_le_univ _

/-- A finite nontrivial bridge side has at least six vertices if its only possible
beat point is an up beat point at the distinguished minimum. Acyclicity of the
comparability graph is needed only in the absence of a three-element chain. -/
theorem six_le_card_of_extremal_bridge_side [Finite X] [Nontrivial X] {a : X}
    (ha : IsMin a) (hConn : (comparabilityGraph X).Connected)
    (hAcyclic : (¬ ∃ l x r : X, l < x ∧ x < r) → (comparabilityGraph X).IsAcyclic)
    (hUp : ∀ z : X, IsUpBeatPoint z → z = a) (hDown : ∀ z : X, ¬ IsDownBeatPoint z) :
    6 ≤ Nat.card X := by
  classical
  by_cases h : ∃ l x r : X, l < x ∧ x < r
  · obtain ⟨l, x, r, hlx, hxr⟩ := h
    exact six_le_card_of_chain ha hlx hxr hUp hDown
  · obtain ⟨u, v, huv, hu, hv⟩ := exists_two_beat_points_of_isTree ⟨hConn, hAcyclic h⟩
    have atEndpoint (z : X) (hz : IsUpBeatPoint z ∨ IsDownBeatPoint z) : z = a :=
      hz.elim (hUp z) (fun hd => (hDown z hd).elim)
    exact (huv ((atEndpoint u hu).trans (atEndpoint v hv).symm)).elim

/-- Complementary bridge sides with the respective minimum and maximum as their
only possible beat points contain at least twelve vertices in total. -/
theorem twelve_le_card_of_extremal_bridge_partition [Finite X] (S : Set X)
    [Nontrivial S] [Nontrivial (Sᶜ : Set X)] {a : S} {b : (Sᶜ : Set X)}
    (ha : IsMin a) (hb : IsMax b)
    (hConnLeft : (comparabilityGraph S).Connected)
    (hConnRight : (comparabilityGraph (Sᶜ : Set X)).Connected)
    (hAcyclicLeft : (¬ ∃ l x r : S, l < x ∧ x < r) → (comparabilityGraph S).IsAcyclic)
    (hAcyclicRight : (¬ ∃ l x r : (Sᶜ : Set X), l < x ∧ x < r) →
      (comparabilityGraph (Sᶜ : Set X)).IsAcyclic)
    (hUpLeft : ∀ z : S, IsUpBeatPoint z → z = a)
    (hDownLeft : ∀ z : S, ¬ IsDownBeatPoint z)
    (hDownRight : ∀ z : (Sᶜ : Set X), IsDownBeatPoint z → z = b)
    (hUpRight : ∀ z : (Sᶜ : Set X), ¬ IsUpBeatPoint z) :
    12 ≤ Nat.card X := by
  classical
  have leftSize := six_le_card_of_extremal_bridge_side ha hConnLeft hAcyclicLeft hUpLeft hDownLeft
  have rightGraph : comparabilityGraph (Sᶜ : Set X)ᵒᵈ = comparabilityGraph (Sᶜ : Set X) := by
    apply SimpleGraph.ext
    funext x y
    have hDual := adj_iff (X := (Sᶜ : Set X)ᵒᵈ) (x := x) (y := y)
    have hOrd := adj_iff (X := (Sᶜ : Set X)) (x := OrderDual.ofDual x) (y := OrderDual.ofDual y)
    exact propext (hDual.trans (or_comm.trans hOrd.symm))
  have rightSize : 6 ≤ Nat.card (Sᶜ : Set X) := by
    apply six_le_card_of_extremal_bridge_side (X := (Sᶜ : Set X)ᵒᵈ) (a := OrderDual.toDual b)
    · exact hb
    · rwa [rightGraph]
    · intro h
      rw [rightGraph]
      apply hAcyclicRight
      rintro ⟨l, x, r, hlx, hxr⟩
      exact h ⟨OrderDual.toDual r, OrderDual.toDual x, OrderDual.toDual l, hxr, hlx⟩
    · exact hDownRight
    · exact hUpRight
  rw [← Nat.card_congr (Equiv.Set.sumCompl S), Nat.card_sum]
  exact Nat.add_le_add leftSize rightSize

/-- In a finite core, a cut crossed by exactly one strict comparison has
at least six vertices on each side if the two side graphs are connected
and any side of height one is acyclic. -/
theorem twelve_le_card_of_single_cross_comparison [Finite X] (S : Set X)
    {a : S} {b : (Sᶜ : Set X)} (hab : a.val < b.val)
    (hCross : ∀ (x : S) (y : (Sᶜ : Set X)), x.val < y.val → x = a ∧ y = b)
    (hNoReverse : ∀ (x : S) (y : (Sᶜ : Set X)), ¬ y.val < x.val)
    (hConnLeft : (comparabilityGraph S).Connected)
    (hConnRight : (comparabilityGraph (Sᶜ : Set X)).Connected)
    (hAcyclicLeft : (¬ ∃ l x r : S, l < x ∧ x < r) → (comparabilityGraph S).IsAcyclic)
    (hAcyclicRight : (¬ ∃ l x r : (Sᶜ : Set X), l < x ∧ x < r) →
      (comparabilityGraph (Sᶜ : Set X)).IsAcyclic)
    (hUp : ∀ x : X, ¬ IsUpBeatPoint x) (hDown : ∀ x : X, ¬ IsDownBeatPoint x) :
    12 ≤ Nat.card X := by
  classical
  have ha : IsMin a := by
    rw [isMin_iff_forall_not_lt]
    intro x hxa
    exact hxa.ne (hCross x b ((show x.val < a.val from hxa).trans hab)).1
  have hb : IsMax b := by
    rw [isMax_iff_forall_not_lt]
    intro y hby
    exact hby.ne (hCross a y (hab.trans (show b.val < y.val from hby))).2.symm
  have leftNontrivial : Nontrivial S := by
    by_contra h
    have only (x : S) : x = a := by
      by_contra hx
      exact h ⟨x, a, hx⟩
    apply hUp a.val
    refine ⟨b.val, hab, ?_⟩
    intro y hy
    by_cases hyS : y ∈ S
    · exact (hy.ne (congrArg Subtype.val (only ⟨y, hyS⟩)).symm).elim
    · exact (congrArg Subtype.val (hCross a ⟨y, hyS⟩ hy).2).ge
  have rightNontrivial : Nontrivial (Sᶜ : Set X) := by
    by_contra h
    have only (y : (Sᶜ : Set X)) : y = b := by
      by_contra hy
      exact h ⟨y, b, hy⟩
    apply hDown b.val
    refine ⟨a.val, hab, ?_⟩
    intro x hx
    by_cases hxS : x ∈ S
    · exact (congrArg Subtype.val (hCross ⟨x, hxS⟩ b hx).1).le
    · exact (hx.ne (congrArg Subtype.val (only ⟨x, hxS⟩))).elim
  letI := leftNontrivial
  letI := rightNontrivial
  apply twelve_le_card_of_extremal_bridge_partition S ha hb hConnLeft
    hConnRight hAcyclicLeft hAcyclicRight
  · rintro x ⟨z, hxz, hmin⟩
    by_contra hxa
    apply hUp x.val
    refine ⟨z.val, hxz, ?_⟩
    intro y hxy
    by_cases hy : y ∈ S
    · exact hmin (a := ⟨y, hy⟩) hxy
    · exact (hxa (hCross x ⟨y, hy⟩ hxy).1).elim
  · rintro x ⟨z, hzx, hmax⟩
    apply hDown x.val
    refine ⟨z.val, hzx, ?_⟩
    intro y hyx
    by_cases hy : y ∈ S
    · exact hmax (a := ⟨y, hy⟩) hyx
    · exact (hNoReverse x ⟨y, hy⟩ hyx).elim
  · rintro x ⟨z, hzx, hmax⟩
    by_contra hxb
    apply hDown x.val
    refine ⟨z.val, hzx, ?_⟩
    intro y hyx
    by_cases hy : y ∈ S
    · exact (hxb (hCross ⟨y, hy⟩ x hyx).2).elim
    · exact hmax (a := ⟨y, hy⟩) hyx
  · rintro x ⟨z, hxz, hmin⟩
    apply hUp x.val
    refine ⟨z.val, hxz, ?_⟩
    intro y hxy
    by_cases hy : y ∈ S
    · exact (hNoReverse ⟨y, hy⟩ x hxy).elim
    · exact hmin (a := ⟨y, hy⟩) hxy

end Omega.ExtremalBridge
