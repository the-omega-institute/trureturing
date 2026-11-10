/- GID: D5/S3/Combinatorics/Sequenceability/OriginalTranslatedQuotientCarrierLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalTranslatedQuotientCarrierLowerBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup, mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: A translated signed-label set gives quadratic cyclic and odd-abelian carrier bounds. -/

import D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.Data.Finset.Card

/-!
In T = {0} union {±A_i}, a collision
x in T intersect (A_o + T) either repeats an index or violates a full signed
triple exclusion. The repeated-index case 2*x = A_o is retained explicitly.
The root fiber injects into the two-torsion subgroup. No optimality claim
or stronger 4*r-2 bound is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open scoped Classical BigOperators

namespace D5.S3.Combinatorics.Sequenceability.OriginalTranslatedQuotientCarrierLowerBound

open OriginalFiniteOrderSharpness (Index Coordinate q a b triple)
open OriginalSharpnessCarrierLowerBound
  (pair_sum label_not_mem_zmultiples difference_not_mem_zmultiples sum_not_mem_zmultiples)
open OriginalCyclicFiveCarrierLowerBound (signed_triple_not_mem_zmultiples)

private def signed {K : Type*} [AddGroup K] (s : Bool) (x : K) : K :=
  if s then -x else x

private lemma signed_not {K : Type*} [AddGroup K] (s : Bool) (x : K) :
    signed (!s) x = -signed s x := by
  cases s <;> simp [signed]

section Counting
variable {K : Type*} [AddCommGroup K] [Fintype K]
variable {m : ℕ} (A : Index m → K)

private def positive : Finset K := by classical exact Finset.univ.image A
private def negative : Finset K := by classical exact Finset.univ.image (fun i => -A i)
private def support : Finset K := by classical exact insert 0 (positive A ∪ negative A)
private def roots (a : K) : Finset K := by classical exact Finset.univ.filter (fun x => 2 • x = a)
private def translated (a : K) : Finset K := by
  classical
  exact (support A).image (fun x => a + x)

private lemma mem_roots {a x : K} : x ∈ roots a ↔ 2 • x = a := by
  classical
  simp [roots]

private lemma mem_support {x : K} :
    x ∈ support A ↔ x = 0 ∨ ∃ i s, x = signed s (A i) := by
  classical
  simp only [support, Finset.mem_insert, Finset.mem_union, positive, negative,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨i, hi⟩ | ⟨i, hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, false, by simpa [signed] using hi.symm⟩
    · exact Or.inr ⟨i, true, by simpa [signed] using hi.symm⟩
  · rintro (h | ⟨i, s, hs⟩)
    · exact Or.inl h
    · cases s
      · exact Or.inr (Or.inl ⟨i, by simpa [signed] using hs.symm⟩)
      · exact Or.inr (Or.inr ⟨i, by simpa [signed] using hs.symm⟩)

/-- Every nonempty doubling fiber injects into the zero fiber by translation. -/
private lemma roots_card_le (a : K) : (roots a).card ≤ (roots (0 : K)).card := by
  classical
  rcases (roots a).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · simp [he]
  · apply Finset.card_le_card_of_injOn (fun x => x - x₀)
    · intro x hx
      apply mem_roots.mpr
      rw [nsmul_sub, mem_roots.mp hx, mem_roots.mp hx₀, sub_self]
    · intro x _ y _ heq
      simpa only [sub_add_cancel] using congrArg (fun z : K => z + x₀) heq

/-- The complete collision list. The final alternative is essential. -/
private lemma translated_collision
    (hA0 : ∀ i, A i ≠ 0)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ s t u,
      signed s (A i) + signed t (A j) + signed u (A k) ≠ 0)
    (o : Index m) {x : K} (hx : x ∈ support A) (hy : x - A o ∈ support A) :
    x = 0 ∨ x = A o ∨ x = -A o ∨ x = 2 • A o ∨ 2 • x = A o := by
  rcases (mem_support A).mp hx with hx | ⟨i, s, hx⟩
  · exact Or.inl hx
  rcases (mem_support A).mp hy with hy | ⟨j, t, hy⟩
  · exact Or.inr (Or.inl (sub_eq_zero.mp hy))
  by_cases hio : i = o
  · subst i
    cases s
    · exact Or.inr (Or.inl (by simpa [signed] using hx))
    · exact Or.inr (Or.inr (Or.inl (by simpa [signed] using hx)))
  by_cases hjo : j = o
  · subst j
    cases t
    · right; right; right; left
      have he : x - A o = A o := by simpa [signed] using hy
      simpa only [two_nsmul] using sub_eq_iff_eq_add.mp he
    · left
      have he : x - A o = -A o := by simpa [signed] using hy
      exact (sub_eq_iff_eq_add.mp he).trans (neg_add_cancel _)
  by_cases hij : i = j
  · subst j
    have he : x - A o = x ∨ x - A o = -x := by
      cases s <;> cases t <;> simp_all [signed]
    rcases he with he | he
    · have hz : A o = 0 := by
        calc
          A o = x - (x - A o) := by abel
          _ = 0 := by rw [he, sub_self]
      exact (hA0 o hz).elim
    · right; right; right; right
      have hd : x + x = A o := by
        calc
          x + x = x - (x - A o) := by rw [he]; abel
          _ = A o := by abel
      simpa only [two_nsmul] using hd
  · exfalso
    apply htriple i j o hij hio hjo s (!t) true
    rw [signed_not]
    change signed s (A i) + -signed t (A j) + -A o = 0
    rw [← hx, ← hy]
    abel

private lemma intersection_card_le
    (hA0 : ∀ i, A i ≠ 0)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ s t u,
      signed s (A i) + signed t (A j) + signed u (A k) ≠ 0)
    (o : Index m) :
    (support A ∩ translated A (A o)).card ≤
      ({0, A o, -A o, 2 • A o} : Finset K).card + (roots (0 : K)).card := by
  classical
  have hsub : support A ∩ translated A (A o) ⊆
      ({0, A o, -A o, 2 • A o} : Finset K) ∪ roots (A o) := by
    intro x hx
    obtain ⟨hx, ht⟩ := Finset.mem_inter.mp hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp ht
    have hy' : x - A o ∈ support A := by
      have he' : x - A o = y := by rw [← he]; abel
      rwa [he']
    rcases translated_collision A hA0 htriple o hx hy' with h | h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · simp [h]
    · exact Finset.mem_union_right _ (mem_roots.mpr h)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (roots_card_le (A o)) _))

/-- Count T through the overlap of positive and negative copies. Its overlap,
with zero adjoined, embeds in the zero doubling fiber. -/
private lemma support_counts
    (hA0 : ∀ i, A i ≠ 0) (hAA : Function.Injective A)
    (hAN : ∀ i j, i ≠ j → A i ≠ -A j) :
    (support A).card + (positive A ∩ negative A).card = 2 * (m - 1) + 1 ∧
      (positive A ∩ negative A).card + 1 ≤ (roots (0 : K)).card := by
  classical
  have hp : (positive A).card = m - 1 := by
    rw [positive, Finset.card_image_of_injective _ hAA, Finset.card_univ]
    exact Fintype.card_fin _
  have hn : (negative A).card = m - 1 := by
    rw [negative, Finset.card_image_of_injective _ (fun i j h => hAA (neg_injective h)),
      Finset.card_univ]
    exact Fintype.card_fin _
  have h0 : (0 : K) ∉ positive A ∪ negative A := by
    simp [positive, negative, hA0]
  have ht : (support A).card = (positive A ∪ negative A).card + 1 :=
    Finset.card_insert_of_notMem h0
  have hu := Finset.card_union_add_card_inter (positive A) (negative A)
  have hz : (0 : K) ∉ positive A ∩ negative A := by
    intro h
    exact h0 (Finset.mem_union_left _ (Finset.mem_inter.mp h).1)
  have hsub : insert 0 (positive A ∩ negative A) ⊆ roots (0 : K) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      simp [roots]
    · obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
      have he : A i = -A j := hi.trans hj.symm
      have hij : i = j := by
        by_contra hij
        exact hAN i j hij he
      subst j
      have hs : x = -x := hi.symm.trans (he.trans (congrArg Neg.neg hi))
      apply mem_roots.mpr
      calc
        2 • x = x + x := two_nsmul x
        _ = -x + x := congrArg (fun z => z + x) hs
        _ = 0 := neg_add_cancel _
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hz] at hc
  exact ⟨by omega, hc⟩

private lemma support_card_no_self
    (hA0 : ∀ i, A i ≠ 0) (hAA : Function.Injective A)
    (hAN : ∀ i j, i ≠ j → A i ≠ -A j)
    (hself : ¬ ∃ i, A i = -A i) : (support A).card = 2 * (m - 1) + 1 := by
  classical
  have he : positive A ∩ negative A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
    have h : A i = -A j := hi.trans hj.symm
    have hij : i = j := by
      by_contra hij
      exact hAN i j hij h
    subst j
    exact hself ⟨i, h⟩
  have hc := (support_counts A hA0 hAA hAN).1
  simpa [he] using hc

private lemma union_bound (o : Index m) :
    2 * (support A).card ≤ Nat.card K + (support A ∩ translated A (A o)).card := by
  classical
  have ht : (translated A (A o)).card = (support A).card :=
    Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)
  have he := Finset.card_union_add_card_inter (support A) (translated A (A o))
  have hu : (support A ∪ translated A (A o)).card ≤ Nat.card K := by
    simpa only [Nat.card_eq_fintype_card] using
      Finset.card_le_univ (support A ∪ translated A (A o))
  omega

private lemma bounded_two_torsion_bound (hm : 2 ≤ m)
    (hA0 : ∀ i, A i ≠ 0) (hAA : Function.Injective A)
    (hAN : ∀ i j, i ≠ j → A i ≠ -A j)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ s t u,
      signed s (A i) + signed t (A j) + signed u (A k) ≠ 0)
    (hk : (roots (0 : K)).card ≤ 2) :
    4 * (m - 1) ≤ Nat.card K + 4 := by
  classical
  by_cases hself : ∃ o, A o = -A o
  · obtain ⟨o, ho⟩ := hself
    have hd : 2 • A o = 0 := by
      rw [two_nsmul]
      calc A o + A o = -A o + A o := congrArg (fun x => x + A o) ho
           _ = 0 := neg_add_cancel _
    have hex : ({0, A o, -A o, 2 • A o} : Finset K).card ≤ 2 := by
      simpa [← ho, hd, Finset.insert_comm] using
        (Finset.card_le_two (a := A o) (b := (0 : K)))
    have hi := intersection_card_le A hA0 htriple o
    have ht := support_counts A hA0 hAA hAN
    have hu := union_bound A o
    omega
  · let o : Index m := ⟨0, by omega⟩
    have ht := support_card_no_self A hA0 hAA hAN hself
    have hi := intersection_card_le A hA0 htriple o
    have hex : ({0, A o, -A o, 2 • A o} : Finset K).card ≤ 4 := Finset.card_le_four
    have hu := union_bound A o
    omega

private lemma odd_two_torsion_bound (hodd : Odd (Nat.card K)) :
    (roots (0 : K)).card ≤ 1 := by
  classical
  have hsub : roots (0 : K) ⊆ {0} := by
    intro x hx
    have hdvd : addOrderOf x ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (mem_roots.mp hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exact Finset.mem_singleton.mpr (AddMonoid.addOrderOf_eq_one_iff.mp hone)
    · have hd : 2 ∣ Nat.card K := by simpa only [htwo] using addOrderOf_dvd_natCard x
      exact (hodd.not_two_dvd_nat hd).elim
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma odd_quotient_bound (hm : 2 ≤ m)
    (hA0 : ∀ i, A i ≠ 0) (hAA : Function.Injective A)
    (hAN : ∀ i j, i ≠ j → A i ≠ -A j)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ s t u,
      signed s (A i) + signed t (A j) + signed u (A k) ≠ 0)
    (hodd : Odd (Nat.card K)) : 4 * (m - 1) ≤ Nat.card K + 3 := by
  classical
  let o : Index m := ⟨0, by omega⟩
  have hk := odd_two_torsion_bound hodd
  have ht := support_counts A hA0 hAA hAN
  have hi := intersection_card_le A hA0 htriple o
  have hex : ({0, A o, -A o, 2 • A o} : Finset K).card ≤ 4 := Finset.card_le_four
  have hu := union_bound A o
  omega
end Counting

private def chosen (m : ℕ) (i : Index m) (s : Bool) : Coordinate m :=
  if s then b m i else a m i

/-- Reuse the original complete-support separation and the full all-signs
triple theorem. The two signs of the translated members are not restricted. -/
lemma quotient_data {G : Type*} [AddCommGroup G] [Finite G]
    (m : ℕ) (hm : 4 ≤ m) (f : Coordinate m → G)
    (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ i : Index m, C = triple m i) :
    let H := AddSubgroup.zmultiples (f (q m))
    let A : Index m → G ⧸ H := fun i => (f (a m i) : G ⧸ H)
    (∀ i, A i ≠ 0) ∧ Function.Injective A ∧
    (∀ i j, i ≠ j → A i ≠ -A j) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ s t u,
      signed s (A i) + signed t (A j) + signed u (A k) ≠ 0) := by
  classical
  let H := AddSubgroup.zmultiples (f (q m))
  let A : Index m → G ⧸ H := fun i => (f (a m i) : G ⧸ H)
  have hq0 : (f (q m) : G ⧸ H) = 0 := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [sub_zero] using AddSubgroup.mem_zmultiples (f (q m))
  have hmate (i : Index m) : (f (b m i) : G ⧸ H) = -A i := by
    have hp := congrArg (fun x : G => (x : G ⧸ H)) (pair_sum hzero i)
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_neg, hq0, neg_zero] at hp
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hp)
  have hchosen (i : Index m) (s : Bool) :
      (f (chosen m i s) : G ⧸ H) = signed s (A i) := by
    cases s
    · rfl
    · exact hmate i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hz
    have heq : (f (a m i) : G ⧸ H) = ((0 : G) : G ⧸ H) := hz
    exact label_not_mem_zmultiples (by omega) hq hzero i
      (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  · intro i j heq
    by_contra hij
    exact difference_not_mem_zmultiples (by omega) hq hzero i j hij
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
  · intro i j hij heq
    have heq' : (f (a m i) : G ⧸ H) = ((-f (a m j) : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_neg] using heq
    exact sum_not_mem_zmultiples (by omega) hq hzero i j hij
      (by simpa only [sub_neg_eq_add] using QuotientAddGroup.eq_iff_sub_mem.mp heq')
  · intro i j k hij hik hjk s t u hz
    have heq : ((f (chosen m i s) + f (chosen m j t) + f (chosen m k u) : G) :
        G ⧸ H) = ((0 : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_add, QuotientAddGroup.mk_zero, hchosen] using hz
    have hnot := signed_triple_not_mem_zmultiples hm hq hzero i j k hij hik hjk s t u
    change f (chosen m i s) + f (chosen m j t) + f (chosen m k u) ∉ H at hnot
    exact hnot (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)

/-- Every finite cyclic original-support carrier at order m>=3 has at least
4*m*(m-2) elements. This is a lower bound, with no optimality assertion. -/
theorem cyclic_carrier_card_lower_bound {G : Type u} [AddCommGroup G] [Finite G]
    [IsAddCyclic G] (m : ℕ) (hm : 3 ≤ m) (f : Coordinate m → G)
    (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ i : Index m, C = triple m i) :
    4 * m * (m - 2) ≤ Nat.card G := by
  classical
  by_cases hm3 : m = 3
  · subst m
    have h := OriginalSharpnessCarrierLowerBound.cyclic_carrier_card_lower_bound
      3 (by decide) f hq hzero
    norm_num at h ⊢
    omega
  have hm4 : 4 ≤ m := by omega
  let H := AddSubgroup.zmultiples (f (q m))
  let A : Index m → G ⧸ H := fun i => (f (a m i) : G ⧸ H)
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  letI : IsAddCyclic (G ⧸ H) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' H) (QuotientAddGroup.mk'_surjective H)
  have hd := quotient_data m hm4 f hq hzero
  have hk : (roots (0 : G ⧸ H)).card ≤ 2 := by
    have hc := IsAddCyclic.card_nsmul_eq_zero_le
      (α := G ⧸ H) (n := 2) (by decide)
    convert hc using 1
    congr 1
    ext x
    simp [roots]
  have hquot := bounded_two_torsion_bound A (by omega) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 hk
  have hbound : 4 * (m - 2) ≤ Nat.card (G ⧸ H) := by omega
  have hH : Nat.card H = m := by dsimp only [H]; rw [Nat.card_zmultiples, hq]
  calc
    4 * m * (m - 2) = (4 * (m - 2)) * m := by ring
    _ ≤ Nat.card (G ⧸ H) * Nat.card H := by
      rw [hH]
      exact Nat.mul_le_mul_right m hbound
    _ = Nat.card G := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H).symm

/-- In every finite odd-order abelian original-support carrier at order m>=3,
the translated-set argument gives m*(4*m-7) elements. Cyclicity is unnecessary. -/
theorem odd_carrier_card_lower_bound {G : Type u} [AddCommGroup G] [Finite G]
    (m : ℕ) (hm : 3 ≤ m) (f : Coordinate m → G)
    (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ i : Index m, C = triple m i)
    (hodd : Odd (Nat.card G)) : m * (4 * m - 7) ≤ Nat.card G := by
  classical
  by_cases hm3 : m = 3
  · subst m
    have h := OriginalSharpnessCarrierLowerBound.odd_carrier_card_lower_bound
      3 (by decide) f hq hzero hodd
    norm_num at h ⊢
    omega
  have hm4 : 4 ≤ m := by omega
  let H := AddSubgroup.zmultiples (f (q m))
  let A : Index m → G ⧸ H := fun i => (f (a m i) : G ⧸ H)
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hoddK : Odd (Nat.card (G ⧸ H)) := by
    have hp : Odd (Nat.card (G ⧸ H) * Nat.card H) := by
      rw [← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H]
      exact hodd
    exact (Nat.odd_mul.mp hp).1
  have hd := quotient_data m hm4 f hq hzero
  have hquot := odd_quotient_bound A (by omega) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 hoddK
  have hbound : 4 * m - 7 ≤ Nat.card (G ⧸ H) := by omega
  have hH : Nat.card H = m := by dsimp only [H]; rw [Nat.card_zmultiples, hq]
  calc
    m * (4 * m - 7) = (4 * m - 7) * m := Nat.mul_comm _ _
    _ ≤ Nat.card (G ⧸ H) * Nat.card H := by
      rw [hH]
      exact Nat.mul_le_mul_right m hbound
    _ = Nat.card G := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H).symm

end D5.S3.Combinatorics.Sequenceability.OriginalTranslatedQuotientCarrierLowerBound
