module

public import OmegaMath.Algebra.Refinement.FiniteTransport
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Algebra.Order.Group.DenselyOrdered
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Abel

/-!
Omega original.

Full permitted support for finite transportation over the original nonnegative
cone of a linearly ordered additive commutative group.
-/

compile_only_with_mathlib

@[expose] public section
namespace Omega.Refinement
open scoped BigOperators
universe u v w z
variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

@[simp] theorem cone_sum_coe {I : Type v} [Fintype I] (r : I → Nonneg G) :
    ((∑ i, r i : Nonneg G) : G) = ∑ i, (r i : G) :=
  map_sum (Nonneg.coeAddMonoidHom : Nonneg G →+ G) _ _

/-- All and only the cells permitted by labels and nonzero margins are nonzero. -/
def FullSupportTransport (G : Type u) [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] : Prop := by
  classical
  exact ∀ (A : Type v) (B : Type w) (Z : Type z) [Fintype A] [Fintype B]
    (f : A → Z) (g : B → Z) (p : A → Nonneg G) (q : B → Nonneg G),
    (∀ c, (∑ a, if f a = c then p a else 0) =
      ∑ b, if g b = c then q b else 0) →
    ∃ m : A → B → Nonneg G,
      (∀ a b, f a ≠ g b → m a b = 0) ∧
      (∀ a, ∑ b, m a b = p a) ∧ (∀ b, ∑ a, m a b = q b) ∧
      (∀ a b, m a b ≠ 0 ↔ f a = g b ∧ p a ≠ 0 ∧ q b ≠ 0)

/-- The original ordered-group cone is conical. -/
theorem ordered_cone_conical : Conical (Nonneg G) := by
  intro x y h
  have h' : (x : G) + y = 0 := congrArg Subtype.val h
  exact ⟨Subtype.ext (le_antisymm (by simpa [h'] using
    (le_add_of_nonneg_right y.property : (x : G) ≤ x + y)) x.property),
    Subtype.ext (le_antisymm (by simpa [h'] using
    (le_add_of_nonneg_left x.property : (y : G) ≤ x + y)) y.property)⟩

/-- Subtracting the smaller first margin constructs binary refinement. -/
theorem ordered_cone_refinement : BinaryRefinement (Nonneg G) := by
  intro a b c d h
  have h' : (a : G) + b = c + d := congrArg Subtype.val h
  rcases le_total (a : G) c with hac | hca
  · refine ⟨a, 0, ⟨c - a, sub_nonneg.mpr hac⟩, d, by simp, ?_, ?_, by simp⟩
    · apply Subtype.ext
      change (c : G) - a + d = b
      calc
        _ = ((c : G) + d) - a := by abel
        _ = b := by rw [← h']; abel
    · apply Subtype.ext
      exact add_sub_cancel _ _
  · refine ⟨c, ⟨a - c, sub_nonneg.mpr hca⟩, 0, b, ?_, by simp, by simp, ?_⟩
    · apply Subtype.ext
      exact add_sub_cancel _ _
    · apply Subtype.ext
      change (a : G) - c + b = d
      calc
        _ = ((a : G) + b) - c := by abel
        _ = d := by rw [h']; abel

open Classical in
/-- A nonnegative seed can be completed without losing any of its positive cells. -/
theorem complete_transport_seed {A : Type v} {B : Type w} {Z : Type z}
    [Fintype A] [Fintype B] (f : A → Z) (g : B → Z)
    (p : A → Nonneg G) (q : B → Nonneg G)
    (balanced : ∀ c, (∑ a, if f a = c then p a else 0) =
      ∑ b, if g b = c then q b else 0)
    (s : A → B → G) (hs : ∀ a b, 0 ≤ s a b)
    (hoff : ∀ a b, f a ≠ g b → s a b = 0)
    (hr : ∀ a, (∑ b, s a b) ≤ p a) (hc : ∀ b, (∑ a, s a b) ≤ q b) :
    ∃ m : A → B → Nonneg G,
      (∀ a b, f a ≠ g b → m a b = 0) ∧
      (∀ a, ∑ b, m a b = p a) ∧ (∀ b, ∑ a, m a b = q b) ∧
      (∀ a b, s a b ≤ (m a b : G)) := by
  classical
  let p' : A → Nonneg G := fun a => ⟨p a - ∑ b, s a b, sub_nonneg.mpr (hr a)⟩
  let q' : B → Nonneg G := fun b => ⟨q b - ∑ a, s a b, sub_nonneg.mpr (hc b)⟩
  have hbal : ∀ c, (∑ a, if f a = c then p' a else 0) =
      ∑ b, if g b = c then q' b else 0 := by
    intro c
    apply Subtype.ext
    have hb := congrArg Subtype.val (balanced c)
    simp only [cone_sum_coe, apply_ite, Nonneg.coe_zero] at hb ⊢
    have hseed : (∑ a, if f a = c then ∑ b, s a b else 0) =
        ∑ b, if g b = c then ∑ a, s a b else 0 := by
      simp only [Finset.ite_sum_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a = c <;> by_cases hb : g b = c
      · simp [ha, hb]
      · have hz := hoff a b (fun e => hb (e ▸ ha))
        simp [ha, hb, hz]
      · have hz := hoff a b (fun e => ha (e.symm ▸ hb))
        simp [ha, hb, hz]
      · simp [ha, hb]
    have hexpand (x y : G) (P : Prop) [Decidable P] :
        (if P then x - y else 0) = (if P then x else 0) - (if P then y else 0) := by
      split_ifs <;> simp
    simp only [p', q', hexpand, Finset.sum_sub_distrib]
    rw [hb, hseed]
  obtain ⟨t, ht, htr, htc⟩ := finite_fiber_transport
    (ordered_cone_conical (G := G)) (ordered_cone_refinement (G := G))
    A B Z f g p' q' hbal
  refine ⟨fun a b => ⟨s a b + t a b, add_nonneg (hs a b) (t a b).property⟩,
    ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    simp [hoff a b hab, ht a b hab]
  · intro a
    apply Subtype.ext
    have h := congrArg Subtype.val (htr a)
    simp only [cone_sum_coe] at h
    simp only [cone_sum_coe, Finset.sum_add_distrib]
    change (∑ b, s a b) + (∑ b, (t a b : G)) = p a
    rw [h]
    exact add_sub_cancel _ _
  · intro b
    apply Subtype.ext
    have h := congrArg Subtype.val (htc b)
    simp only [cone_sum_coe] at h
    simp only [cone_sum_coe, Finset.sum_add_distrib]
    change (∑ a, s a b) + (∑ a, (t a b : G)) = q b
    rw [h]
    exact add_sub_cancel _ _
  · intro a b
    exact le_add_of_nonneg_right (t a b).property

/-- Density supplies a uniformly small positive seed on all permitted cells. -/
theorem full_support_transport_of_dense [DenselyOrdered G] :
    FullSupportTransport.{u,v,w,z} G := by
  classical
  intro A B Z _ _ f g p q balanced
  let S : Finset G := ((Finset.univ.image (fun a => (p a : G))) ∪
    (Finset.univ.image (fun b => (q b : G)))).filter (0 < ·)
  let n := Fintype.card A + Fintype.card B
  have ep : ∃ e : G, 0 ≤ e ∧ (∀ x ∈ S, n • e < x) ∧ (S.Nonempty → 0 < e) := by
    by_cases hS : S.Nonempty
    · have hpos : 0 < S.min' hS := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
      obtain ⟨e, he, hsmall⟩ := exists_nsmul_lt_of_pos hpos n
      exact ⟨e, he.le, fun x hx => hsmall.trans_le (Finset.min'_le S x hx), fun _ => he⟩
    · refine ⟨0, le_rfl, ?_, ?_⟩
      · intro x hx
        exact (hS ⟨x, hx⟩).elim
      · exact fun h => (hS h).elim
  obtain ⟨e, he, hsmall, hepos⟩ := ep
  have pmem (a : A) (ha : p a ≠ 0) : (p a : G) ∈ S := by
    have hne : (p a : G) ≠ 0 := fun h => ha (Subtype.ext h)
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩),
      lt_of_le_of_ne (p a).property (Ne.symm hne)⟩
  have qmem (b : B) (hb : q b ≠ 0) : (q b : G) ∈ S := by
    have hne : (q b : G) ≠ 0 := fun h => hb (Subtype.ext h)
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩),
      lt_of_le_of_ne (q b).property (Ne.symm hne)⟩
  let s : A → B → G := fun a b =>
    if f a = g b ∧ p a ≠ 0 ∧ q b ≠ 0 then e else 0
  have hs (a : A) (b : B) : 0 ≤ s a b := by dsimp [s]; split_ifs <;> first | exact he | exact le_rfl
  have hle (a : A) (b : B) : s a b ≤ e := by dsimp [s]; split_ifs <;> first | exact he | exact le_rfl
  have hoff (a : A) (b : B) (h : f a ≠ g b) : s a b = 0 := by simp [s, h]
  have hr (a : A) : (∑ b, s a b) ≤ p a := by
    by_cases ha : p a = 0
    · simp [s, ha]
    · calc
        _ ≤ Fintype.card B • e := Finset.sum_le_card_nsmul _ _ _ (fun b _ => hle a b)
        _ ≤ n • e := nsmul_le_nsmul_left he (Nat.le_add_left _ _)
        _ ≤ (p a : G) := (hsmall _ (pmem a ha)).le
  have hc (b : B) : (∑ a, s a b) ≤ q b := by
    by_cases hb : q b = 0
    · simp [s, hb]
    · calc
        _ ≤ Fintype.card A • e := Finset.sum_le_card_nsmul _ _ _ (fun a _ => hle a b)
        _ ≤ n • e := nsmul_le_nsmul_left he (Nat.le_add_right _ _)
        _ ≤ (q b : G) := (hsmall _ (qmem b hb)).le
  obtain ⟨m, hmoff, hmrow, hmcol, hmseed⟩ :=
    complete_transport_seed f g p q balanced s hs hoff hr hc
  refine ⟨m, hmoff, hmrow, hmcol, ?_⟩
  intro a b
  constructor
  · intro h
    refine ⟨by_contra fun hn => h (hmoff a b hn), ?_, ?_⟩
    · intro hp
      exact h (term_eq_zero_of_sum_eq_zero (ordered_cone_conical (G := G))
        Finset.univ (m a) ((hmrow a).trans hp) b (Finset.mem_univ b))
    · intro hq
      exact h (term_eq_zero_of_sum_eq_zero (ordered_cone_conical (G := G))
        Finset.univ (fun a => m a b) ((hmcol b).trans hq) a (Finset.mem_univ a))
  · intro hab hzero
    have hpos := hepos ⟨p a, pmem a hab.2.1⟩
    have hl := hmseed a b
    simp only [s, ite_eq_left hab, hzero, Nonneg.coe_zero] at hl
    exact (not_lt_of_ge hl) hpos

/-- Binary full support splits every positive element, at independent universes. -/
theorem dense_of_full_support_transport (h : FullSupportTransport.{u,v,w,z} G) :
    DenselyOrdered G := by
  classical
  have sumBool {K : Type u} [AddCommMonoid K] (r : ULift.{v} Bool → K) :
      (∑ i, r i) = r ⟨true⟩ + r ⟨false⟩ :=
    (Fintype.sum_equiv Equiv.ulift r (fun i => r ⟨i⟩) (fun _ => rfl)).trans
      (Fintype.sum_bool _)
  have sumBoolW (r : ULift.{w} Bool → Nonneg G) :
      (∑ i, r i) = r ⟨true⟩ + r ⟨false⟩ :=
    (Fintype.sum_equiv Equiv.ulift r (fun i => r ⟨i⟩) (fun _ => rfl)).trans
      (Fintype.sum_bool _)
  constructor
  intro a b hab
  let x : Nonneg G := ⟨b - a, (sub_pos.mpr hab).le⟩
  have hx : x ≠ 0 := fun he => (ne_of_gt (sub_pos.mpr hab)) (congrArg Subtype.val he)
  obtain ⟨m, _, hr, _, hs⟩ := h (ULift.{v} Bool) (ULift.{w} Bool) (ULift.{z} Unit)
    (fun _ => ⟨()⟩) (fun _ => ⟨()⟩) (fun _ => x) (fun _ => x) (by
      intro c
      rcases c with ⟨⟨⟩⟩
      simp only [↓reduceIte, sumBool, sumBoolW])
  have h₀ := (hs ⟨true⟩ ⟨true⟩).mpr ⟨rfl, hx, hx⟩
  have h₁ := (hs ⟨true⟩ ⟨false⟩).mpr ⟨rfl, hx, hx⟩
  have pos (y : Nonneg G) (hy : y ≠ 0) : 0 < (y : G) :=
    lt_of_le_of_ne y.property (Ne.symm (fun he => hy (Subtype.ext he)))
  have heq : (m ⟨true⟩ ⟨true⟩ : G) + m ⟨true⟩ ⟨false⟩ = b - a := by
    have hh := congrArg Subtype.val (hr ⟨true⟩)
    simpa only [sumBoolW, Nonneg.coe_add] using hh
  refine ⟨a + m ⟨true⟩ ⟨true⟩, lt_add_of_pos_right a (pos _ h₀), ?_⟩
  have hlt : (m ⟨true⟩ ⟨true⟩ : G) < b - a := by
    rw [← heq]
    exact lt_add_of_pos_right _ (pos _ h₁)
  simpa only [add_comm] using (lt_sub_iff_add_lt.mp hlt)

/-- Exact full permitted-support transportation characterizes order density. -/
theorem densely_ordered_iff_full_support_transport :
    DenselyOrdered G ↔ FullSupportTransport.{u,v,w,z} G :=
  ⟨fun h => @full_support_transport_of_dense G _ _ _ h,
    dense_of_full_support_transport⟩

end Omega.Refinement
