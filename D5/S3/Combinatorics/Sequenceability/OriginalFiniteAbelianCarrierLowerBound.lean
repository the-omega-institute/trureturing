/- GID: D5/S3/Combinatorics/Sequenceability/OriginalFiniteAbelianCarrierLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalFiniteAbelianCarrierLowerBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.Coset.Card, mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: Complete original zero supports force twice the pair count in the distinguished quotient. -/

import D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound

/-!
In the quotient by the distinguished label, the original pair labels are
nonzero, occupy distinct negation orbits, and admit no signed zero triple
from three distinct indices. If none is self-negative, their positive and
negative copies already give twice the pair count. Otherwise quotient by
one selected element of order two: the pair labels remain injective there,
again forcing twice the pair count in the original quotient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

namespace D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound

open scoped Classical BigOperators
open OriginalFiniteOrderSharpness (Index Coordinate q a b triple)
open OriginalSharpnessCarrierLowerBound
  (pair_sum label_not_mem_zmultiples difference_not_mem_zmultiples
    sum_not_mem_zmultiples carrier_card_lower_bound)
open OriginalCyclicFiveCarrierLowerBound (signed_triple_not_mem_zmultiples)

private lemma signed_classes_card_lower_bound
    {K : Type*} [AddCommGroup K] [Finite K]
    (m : ℕ) (A : Index m → K)
    (hA0 : ∀ i, A i ≠ 0) (hAA : Function.Injective A)
    (hAN : ∀ i j, i ≠ j → A i ≠ -A j)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → A i - A j - A k ≠ 0) :
    2 * (m - 1) ≤ Nat.card K := by
  classical
  by_cases hself : ∃ o, A o = -A o
  · obtain ⟨o, ho⟩ := hself
    have hdouble : A o + A o = 0 := by
      calc
        A o + A o = -A o + A o := congrArg (fun x => x + A o) ho
        _ = 0 := neg_add_cancel _
    have htwo : (2 : ℕ) • A o = 0 := by simpa only [two_nsmul] using hdouble
    have hord : addOrderOf (A o) = 2 := by
      have hdvd : addOrderOf (A o) ∣ 2 :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo_order
      · exact (hA0 o (AddMonoid.addOrderOf_eq_one_iff.mp hone)).elim
      · exact htwo_order
    let J := AddSubgroup.zmultiples (A o)
    have hJ : Nat.card J = 2 := by
      dsimp only [J]
      rw [Nat.card_zmultiples, hord]
    have hmem_cases {x : K} (hx : x ∈ J) : x = 0 ∨ x = A o := by
      have hx' : x ∈ (Finset.range (addOrderOf (A o))).image
          (fun t : ℕ => t • A o) :=
        mem_zmultiples_iff_mem_range_addOrderOf.mp hx
      rw [hord] at hx'
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hx'
      have ht2 : t < 2 := Finset.mem_range.mp ht
      rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
      · exact Or.inl (by simpa only [zero_nsmul] using he.symm)
      · exact Or.inr (by simpa only [one_nsmul] using he.symm)
    let c : Index m → K ⧸ J := fun i => (A i : K ⧸ J)
    have hc : Function.Injective c := by
      intro i j heq
      by_contra hij
      have hmem : A i - A j ∈ J := QuotientAddGroup.eq_iff_sub_mem.mp heq
      rcases hmem_cases hmem with hz | hd
      · exact hij (hAA (sub_eq_zero.mp hz))
      have he : A i = A o + A j := sub_eq_iff_eq_add.mp hd
      by_cases hio : i = o
      · subst i
        have he' : A o + A j = A o + 0 := by
          simpa only [add_zero] using he.symm
        exact hA0 j (add_left_cancel he')
      by_cases hjo : j = o
      · subst j
        exact hA0 i (he.trans hdouble)
      apply htriple i j o hij hio hjo
      rw [hd, sub_self]
    have hquot : m - 1 ≤ Nat.card (K ⧸ J) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
        Nat.card_le_card_of_injective c hc
    calc
      2 * (m - 1) = (m - 1) * 2 := Nat.mul_comm _ _
      _ ≤ Nat.card (K ⧸ J) * Nat.card J := by
        rw [hJ]
        exact Nat.mul_le_mul_right 2 hquot
      _ = Nat.card K :=
        (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup J).symm
  · have hANall (i j : Index m) : A i ≠ -A j := by
      by_cases hij : i = j
      · subst j
        exact fun h => hself ⟨i, h⟩
      · exact hAN i j hij
    let c : Bool × Index m → K := fun z => if z.1 then -A z.2 else A z.2
    have hc : Function.Injective c := by
      rintro ⟨s, i⟩ ⟨t, j⟩ h
      cases s <;> cases t
      · have hij : i = j := hAA (by simpa only [c, Bool.false_eq_true, ↓reduceIte] using h)
        subst j
        rfl
      · exact (hANall i j (by simpa only [c, Bool.false_eq_true, ↓reduceIte] using h)).elim
      · exact (hANall j i (by simpa only [c, Bool.false_eq_true, ↓reduceIte] using h.symm)).elim
      · have he : -A i = -A j := by simpa only [c, ↓reduceIte] using h
        have hij : i = j := hAA (neg_injective he)
        subst j
        rfl
    have hdom : Nat.card (Bool × Index m) = 2 * (m - 1) := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool,
        Fintype.card_fin]
    simpa only [hdom] using Nat.card_le_card_of_injective c hc

/-- Every finite abelian carrier with the full original zero-support family
and distinguished label of exact order `m ≥ 3` has at least `2*m*(m-1)` elements. -/
theorem finite_abelian_carrier_card_lower_bound
    {G : Type u} [AddCommGroup G] [Finite G]
    (m : ℕ) (hm : 3 ≤ m) (f : Coordinate m → G)
    (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j) :
    2 * m * (m - 1) ≤ Nat.card G := by
  classical
  by_cases hm3 : m = 3
  · simpa [hm3] using carrier_card_lower_bound m (by omega) f hq hzero
  have hm4 : 4 ≤ m := by omega
  let H := AddSubgroup.zmultiples (f (q m))
  let A : Index m → G ⧸ H := fun i => (f (a m i) : G ⧸ H)
  have hA0 (i : Index m) : A i ≠ 0 := by
    intro h
    have heq : (f (a m i) : G ⧸ H) = ((0 : G) : G ⧸ H) := h
    exact label_not_mem_zmultiples (by omega) hq hzero i
      (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hAA : Function.Injective A := by
    intro i j heq
    by_contra hij
    exact difference_not_mem_zmultiples (by omega) hq hzero i j hij
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hAN (i j : Index m) (hij : i ≠ j) : A i ≠ -A j := by
    intro heq
    have heq' : (f (a m i) : G ⧸ H) = ((-f (a m j) : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_neg] using heq
    exact sum_not_mem_zmultiples (by omega) hq hzero i j hij
      (by simpa only [sub_neg_eq_add] using QuotientAddGroup.eq_iff_sub_mem.mp heq')
  have hq0 : (f (q m) : G ⧸ H) = 0 := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [sub_zero] using AddSubgroup.mem_zmultiples (f (q m))
  have hmate (i : Index m) : (f (b m i) : G ⧸ H) = -A i := by
    have hp := congrArg (fun x : G => (x : G ⧸ H)) (pair_sum hzero i)
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_neg, hq0, neg_zero] at hp
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hp)
  have htriple (i j k : Index m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      A i - A j - A k ≠ 0 := by
    intro hz
    have heq : ((f (a m i) + f (b m j) + f (b m k) : G) : G ⧸ H) =
        ((0 : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_add, QuotientAddGroup.mk_zero,
        hmate, sub_eq_add_neg] using hz
    have hnot := signed_triple_not_mem_zmultiples hm4 hq hzero
      i j k hij hik hjk false true true
    change f (a m i) + f (b m j) + f (b m k) ∉ H at hnot
    exact hnot (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hquot : 2 * (m - 1) ≤ Nat.card (G ⧸ H) :=
    signed_classes_card_lower_bound m A hA0 hAA hAN htriple
  have hH : Nat.card H = m := by
    dsimp only [H]
    rw [Nat.card_zmultiples, hq]
  calc
    2 * m * (m - 1) = (2 * (m - 1)) * m := by ring
    _ ≤ Nat.card (G ⧸ H) * Nat.card H := by
      rw [hH]
      exact Nat.mul_le_mul_right m hquot
    _ = Nat.card G :=
      (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H).symm

end D5.S3.Combinatorics.Sequenceability.OriginalFiniteAbelianCarrierLowerBound
