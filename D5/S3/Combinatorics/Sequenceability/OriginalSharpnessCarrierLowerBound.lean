/- GID: D5/S3/Combinatorics/Sequenceability/OriginalSharpnessCarrierLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalSharpnessCarrierLowerBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.Coset.Card, mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Sequenceability/OriginalSharpnessCarrierLowerBound.cyclic_five_carrier_card_lower_bound; premises=D5/S3/Combinatorics/Sequenceability/OriginalSharpnessCarrierLowerBound.cyclic_carrier_card_lower_bound
   digest: Complete original zero-support classification forces at least m times m plus one carrier elements. -/

import D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound

open scoped Classical BigOperators
open OriginalFiniteOrderSharpness (Index Coordinate q p a b full triple)

variable {G : Type*} [AddCommGroup G] [Finite G]
variable {m : ℕ} {f : Coordinate m → G}

private def paired (m : ℕ) (K : Finset (Index m)) : Finset (Coordinate m) :=
  K.image (a m) ∪ K.image (b m)

private lemma pair_sum
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i : Index m) : f (a m i) + f (b m i) = -f (q m) := by
  classical
  have hz := ((hzero (triple m i)).mpr ⟨i, rfl⟩).2
  have ht : f (q m) + f (a m i) + f (b m i) = 0 := by
    simpa [triple, q, a, b, add_assoc] using hz
  calc
    f (a m i) + f (b m i) =
        (f (q m) + f (a m i) + f (b m i)) - f (q m) := by abel
    _ = -f (q m) := by simp only [ht, zero_sub]

private lemma paired_sum
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (K : Finset (Index m)) :
    (∑ x ∈ paired m K, f x) = -(K.card • f (q m)) := by
  classical
  have ha : Function.Injective (a m) := by
    intro i j h
    simpa [a] using h
  have hb : Function.Injective (b m) := by
    intro i j h
    simpa [b] using h
  have hd : Disjoint (K.image (a m)) (K.image (b m)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simpa [a, b] using hy
  calc
    (∑ x ∈ paired m K, f x) =
        (∑ i ∈ K, f (a m i)) + ∑ i ∈ K, f (b m i) := by
      rw [paired, Finset.sum_union hd]
      congr 1
      · exact Finset.sum_image (fun i _ j _ hij => ha hij)
      · exact Finset.sum_image (fun i _ j _ hij => hb hij)
    _ = ∑ i ∈ K, (f (a m i) + f (b m i)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ _i ∈ K, -f (q m) := by
      apply Finset.sum_congr rfl
      intro i _
      exact pair_sum hzero i
    _ = -(K.card • f (q m)) := by simp

private lemma forbidden_sum
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i : Index m) (C : Finset (Coordinate m))
    (ha : a m i ∈ C) (hb : b m i ∉ C) :
    (∑ x ∈ C, f x) ≠ 0 := by
  classical
  intro hz
  obtain ⟨j, hC⟩ := (hzero C).mp ⟨⟨a m i, ha⟩, hz⟩
  have hij : i = j := by
    have hmem : a m i ∈ triple m j := hC ▸ ha
    simpa [triple, q, a, b] using hmem
  apply hb
  rw [hC, hij]
  simp [triple]

private lemma single_completion_ne_zero
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i : Index m) (K : Finset (Index m)) (hi : i ∉ K) :
    (f (a m i) - K.card • f (q m) ≠ 0) ∧
      (f (q m) + f (a m i) - K.card • f (q m) ≠ 0) := by
  classical
  let C := insert (a m i) (paired m K)
  have hai : a m i ∉ paired m K := by simp [paired, a, b, hi]
  have ha : a m i ∈ C := by simp [C]
  have hb : b m i ∉ C := by simp [C, paired, a, b, hi]
  have hqC : q m ∉ C := by simp [C, paired, q, a, b]
  have hs : (∑ x ∈ C, f x) = f (a m i) - K.card • f (q m) := by
    dsimp [C]
    simp only [Finset.sum_insert hai, paired_sum hzero K, sub_eq_add_neg]
  have hs' : (∑ x ∈ insert (q m) C, f x) =
      f (q m) + f (a m i) - K.card • f (q m) := by
    rw [Finset.sum_insert hqC, hs]
    abel
  constructor
  · rw [← hs]
    exact forbidden_sum hzero i C ha hb
  · rw [← hs']
    apply forbidden_sum hzero i (insert (q m) C)
    · exact Finset.mem_insert_of_mem ha
    · simpa [q, b] using hb

private lemma mixed_completion_ne_zero
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i j : Index m) (hij : i ≠ j)
    (K : Finset (Index m)) (hi : i ∉ K) (hj : j ∉ K) :
    (f (a m i) + f (b m j) - K.card • f (q m) ≠ 0) ∧
      (f (q m) + f (a m i) + f (b m j) - K.card • f (q m) ≠ 0) := by
  classical
  let C := insert (a m i) (insert (b m j) (paired m K))
  have hbj : b m j ∉ paired m K := by simp [paired, a, b, hj]
  have hai : a m i ∉ insert (b m j) (paired m K) := by
    simp [paired, a, b, hi]
  have ha : a m i ∈ C := by simp [C]
  have hb : b m i ∉ C := by simp [C, paired, a, b, hi, hij]
  have hqC : q m ∉ C := by simp [C, paired, q, a, b]
  have hs : (∑ x ∈ C, f x) =
      f (a m i) + f (b m j) - K.card • f (q m) := by
    dsimp [C]
    rw [Finset.sum_insert hai, Finset.sum_insert hbj, paired_sum hzero K]
    abel
  have hs' : (∑ x ∈ insert (q m) C, f x) =
      f (q m) + f (a m i) + f (b m j) - K.card • f (q m) := by
    rw [Finset.sum_insert hqC, hs]
    abel
  constructor
  · rw [← hs]
    exact forbidden_sum hzero i C ha hb
  · rw [← hs']
    apply forbidden_sum hzero i (insert (q m) C)
    · exact Finset.mem_insert_of_mem ha
    · simpa [q, b] using hb

private lemma residue_of_mem_zmultiples
    (hq : addOrderOf (f (q m)) = m) {x : G}
    (hx : x ∈ AddSubgroup.zmultiples (f (q m))) :
    ∃ t : ℕ, t < m ∧ t • f (q m) = x := by
  classical
  have hx' : x ∈ (Finset.range (addOrderOf (f (q m)))).image
      (fun t : ℕ => t • f (q m)) :=
    mem_zmultiples_iff_mem_range_addOrderOf.mp hx
  rw [hq] at hx'
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hx'
  exact ⟨t, Finset.mem_range.mp ht, he⟩

private lemma label_not_mem_zmultiples
    (hm : 2 ≤ m) (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i : Index m) : f (a m i) ∉ AddSubgroup.zmultiples (f (q m)) := by
  classical
  intro hmem
  obtain ⟨t, ht, he⟩ := residue_of_mem_zmultiples hq hmem
  have hord : m • f (q m) = 0 := by
    simpa only [hq] using addOrderOf_nsmul_eq_zero (f (q m))
  by_cases hlast : t = m - 1
  · have hne := (single_completion_ne_zero hzero i ∅ (by simp)).2
    apply hne
    simp only [Finset.card_empty, zero_nsmul, sub_zero]
    calc
      f (q m) + f (a m i) = f (q m) + t • f (q m) := by rw [he]
      _ = (t + 1) • f (q m) := by rw [add_nsmul, one_nsmul]; abel
      _ = m • f (q m) := by congr 1; omega
      _ = 0 := hord
  · have hcard : ((Finset.univ : Finset (Index m)).erase i).card = m - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      omega
    have hbound : t ≤ ((Finset.univ : Finset (Index m)).erase i).card := by
      rw [hcard]
      omega
    obtain ⟨K, hK, hKcard⟩ := Finset.exists_subset_card_eq hbound
    have hi : i ∉ K := by
      intro hi
      have h := hK hi
      simpa using h
    have hne := (single_completion_ne_zero hzero i K hi).1
    apply hne
    rw [hKcard, he, sub_self]

private lemma difference_eq_neg_of_mem
    (hm : 2 ≤ m) (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i j : Index m) (hij : i ≠ j)
    (hmem : f (a m i) - f (a m j) ∈ AddSubgroup.zmultiples (f (q m))) :
    f (a m i) - f (a m j) = -f (q m) := by
  classical
  have hm3 : 3 ≤ m := by
    by_contra h
    have hi := i.isLt
    have hj := j.isLt
    apply hij
    apply Fin.ext
    omega
  obtain ⟨t, ht, he⟩ := residue_of_mem_zmultiples hq hmem
  have hpj := pair_sum hzero j
  have hlast : t = m - 1 := by
    by_contra hnlast
    by_cases ht0 : t = 0
    · have hne := (mixed_completion_ne_zero hzero i j hij ∅ (by simp) (by simp)).2
      apply hne
      simp only [Finset.card_empty, zero_nsmul, sub_zero]
      have he0 : f (a m i) = f (a m j) := by
        apply sub_eq_zero.mp
        simpa only [ht0, zero_nsmul] using he.symm
      rw [he0]
      calc
        f (q m) + f (a m j) + f (b m j) =
            f (q m) + (f (a m j) + f (b m j)) := by abel
        _ = 0 := by rw [hpj]; simp
    · have hjmem : j ∈ (Finset.univ : Finset (Index m)).erase i := by
        simp [hij, Ne.symm hij]
      have hcard : (((Finset.univ : Finset (Index m)).erase i).erase j).card =
          m - 3 := by
        rw [Finset.card_erase_of_mem hjmem,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
        omega
      have hbound : t - 1 ≤
          (((Finset.univ : Finset (Index m)).erase i).erase j).card := by
        rw [hcard]
        omega
      obtain ⟨K, hK, hKcard⟩ := Finset.exists_subset_card_eq hbound
      have hi : i ∉ K := by
        intro hi
        have h := hK hi
        simpa using h
      have hj : j ∉ K := by
        intro hj
        have h := hK hj
        simpa using h
      have hsplit : t • f (q m) = (t - 1) • f (q m) + f (q m) := by
        calc
          t • f (q m) = ((t - 1) + 1) • f (q m) := by congr 1; omega
          _ = (t - 1) • f (q m) + f (q m) := by rw [add_nsmul, one_nsmul]
      have hsum : f (a m i) + f (b m j) = (t - 1) • f (q m) := by
        calc
          f (a m i) + f (b m j) =
              (f (a m i) - f (a m j)) + (f (a m j) + f (b m j)) := by abel
          _ = t • f (q m) + -f (q m) := by rw [← he, hpj]
          _ = (t - 1) • f (q m) := by rw [hsplit]; abel
      have hne := (mixed_completion_ne_zero hzero i j hij K hi hj).1
      apply hne
      rw [hKcard, hsum, sub_self]
  have hord : m • f (q m) = 0 := by
    simpa only [hq] using addOrderOf_nsmul_eq_zero (f (q m))
  have hsplit : (m - 1) • f (q m) + f (q m) = 0 := by
    calc
      (m - 1) • f (q m) + f (q m) = ((m - 1) + 1) • f (q m) := by
        rw [add_nsmul, one_nsmul]
      _ = m • f (q m) := by congr 1; omega
      _ = 0 := hord
  calc
    f (a m i) - f (a m j) = (m - 1) • f (q m) := by rw [← he, hlast]
    _ = ((m - 1) • f (q m) + f (q m)) - f (q m) := by abel
    _ = -f (q m) := by simp only [hsplit, zero_sub]

private lemma difference_not_mem_zmultiples
    (hm : 2 ≤ m) (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i j : Index m) (hij : i ≠ j) :
    f (a m i) - f (a m j) ∉ AddSubgroup.zmultiples (f (q m)) := by
  classical
  intro hmem
  have hm3 : 3 ≤ m := by
    by_contra h
    have hi := i.isLt
    have hj := j.isLt
    apply hij
    apply Fin.ext
    omega
  have hrev : f (a m j) - f (a m i) ∈ AddSubgroup.zmultiples (f (q m)) := by
    simpa only [neg_sub] using (AddSubgroup.zmultiples (f (q m))).neg_mem hmem
  have he := difference_eq_neg_of_mem hm hq hzero i j hij hmem
  have he' := difference_eq_neg_of_mem hm hq hzero j i (Ne.symm hij) hrev
  have hneg : -(f (q m) + f (q m)) = 0 := by
    calc
      -(f (q m) + f (q m)) =
          (f (a m i) - f (a m j)) + (f (a m j) - f (a m i)) := by
        rw [he, he']
        abel
      _ = 0 := by abel
  have htwo : (2 : ℕ) • f (q m) = 0 := by
    simpa only [two_nsmul] using neg_eq_zero.mp hneg
  have hle := addOrderOf_le_of_nsmul_eq_zero (by decide : 0 < (2 : ℕ)) htwo
  rw [hq] at hle
  omega

private lemma sentinel_not_mem_zmultiples
    (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j) :
    f (p m) ∉ AddSubgroup.zmultiples (f (q m)) := by
  classical
  intro hmem
  obtain ⟨t, ht, he⟩ := residue_of_mem_zmultiples hq hmem
  have hbound : t ≤ (Finset.univ : Finset (Index m)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨K, _, hKcard⟩ := Finset.exists_subset_card_eq hbound
  let C := insert (p m) (paired m K)
  have hp : p m ∉ paired m K := by simp [paired, p, a, b]
  have hpC : p m ∈ C := by simp [C]
  have hz : (∑ x ∈ C, f x) = 0 := by
    dsimp only [C]
    simp only [Finset.sum_insert hp, paired_sum hzero K, hKcard, he, add_neg_cancel]
  obtain ⟨j, hC⟩ := (hzero C).mp ⟨⟨p m, hpC⟩, hz⟩
  have hpT : p m ∈ triple m j := hC ▸ hpC
  simpa [triple, p, q, a, b] using hpT

private lemma sentinel_difference_not_mem_zmultiples
    (hm : 2 ≤ m) (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i : Index m) :
    f (p m) - f (a m i) ∉ AddSubgroup.zmultiples (f (q m)) := by
  classical
  intro hmem
  obtain ⟨t, ht, he⟩ := residue_of_mem_zmultiples hq hmem
  have hforbid (D : Finset (Coordinate m)) (hpD : p m ∈ D) :
      (∑ x ∈ D, f x) ≠ 0 := by
    intro hz
    obtain ⟨j, hD⟩ := (hzero D).mp ⟨⟨p m, hpD⟩, hz⟩
    have hpT : p m ∈ triple m j := hD ▸ hpD
    simpa [triple, p, q, a, b] using hpT
  have hcard : ((Finset.univ : Finset (Index m)).erase i).card = m - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hbound : t - 1 ≤ ((Finset.univ : Finset (Index m)).erase i).card := by
    rw [hcard]
    omega
  obtain ⟨K, hK, hKcard⟩ := Finset.exists_subset_card_eq hbound
  have hi : i ∉ K := by
    intro hi
    have h := hK hi
    simpa using h
  let C := insert (p m) (insert (b m i) (paired m K))
  have hbi : b m i ∉ paired m K := by simp [paired, a, b, hi]
  have hp : p m ∉ insert (b m i) (paired m K) := by simp [paired, p, a, b]
  have hpC : p m ∈ C := by simp [C]
  have hs : (∑ x ∈ C, f x) =
      f (p m) + f (b m i) - (t - 1) • f (q m) := by
    dsimp only [C]
    rw [Finset.sum_insert hp, Finset.sum_insert hbi, paired_sum hzero K, hKcard]
    abel
  by_cases ht0 : t = 0
  · have hqC : q m ∉ C := by simp [C, paired, q, p, a, b]
    have he0 : f (p m) = f (a m i) := by
      apply sub_eq_zero.mp
      simpa only [ht0, zero_nsmul] using he.symm
    apply hforbid (insert (q m) C) (Finset.mem_insert_of_mem hpC)
    rw [Finset.sum_insert hqC, hs]
    simp only [ht0, Nat.zero_sub, zero_nsmul, sub_zero, he0,
      pair_sum hzero i, add_neg_cancel]
  · have hsplit : t • f (q m) = (t - 1) • f (q m) + f (q m) := by
      calc
        t • f (q m) = ((t - 1) + 1) • f (q m) := by congr 1; omega
        _ = (t - 1) • f (q m) + f (q m) := by rw [add_nsmul, one_nsmul]
    have hsum : f (p m) + f (b m i) = (t - 1) • f (q m) := by
      calc
        f (p m) + f (b m i) =
            (f (p m) - f (a m i)) + (f (a m i) + f (b m i)) := by abel
        _ = t • f (q m) + -f (q m) := by rw [← he, pair_sum hzero i]
        _ = (t - 1) • f (q m) := by rw [hsplit]; abel
    apply hforbid C hpC
    rw [hs, hsum, sub_self]

theorem carrier_card_lower_bound {G : Type*} [AddCommGroup G] [Finite G]
    (m : ℕ) (hm : 2 ≤ m) (f : Coordinate m → G)
    (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j) :
    m * (m + 1) ≤ Nat.card G := by
  classical
  let H := AddSubgroup.zmultiples (f (q m))
  let c : Option (Option (Index m)) → G ⧸ H
    | none => 0
    | some none => (f (p m) : G ⧸ H)
    | some (some i) => (f (a m i) : G ⧸ H)
  have hP0 : (f (p m) : G ⧸ H) ≠ 0 := by
    intro h
    have heq : (f (p m) : G ⧸ H) = ((0 : G) : G ⧸ H) := h
    have hmem : f (p m) ∈ H := by
      simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq
    exact sentinel_not_mem_zmultiples hq hzero hmem
  have hPA (i : Index m) : (f (p m) : G ⧸ H) ≠ (f (a m i) : G ⧸ H) := by
    intro heq
    exact sentinel_difference_not_mem_zmultiples hm hq hzero i
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hc : Function.Injective c := by
    intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some j =>
        cases j with
        | none =>
          change (0 : G ⧸ H) = (f (p m) : G ⧸ H) at huv
          exact (hP0 huv.symm).elim
        | some j =>
          change (0 : G ⧸ H) = (f (a m j) : G ⧸ H) at huv
          have heq : (f (a m j) : G ⧸ H) = ((0 : G) : G ⧸ H) := huv.symm
          have hj : f (a m j) ∈ H := by
            simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq
          exact (label_not_mem_zmultiples hm hq hzero j hj).elim
    | some i =>
      cases v with
      | none =>
        cases i with
        | none =>
          change (f (p m) : G ⧸ H) = (0 : G ⧸ H) at huv
          exact (hP0 huv).elim
        | some i =>
          change (f (a m i) : G ⧸ H) = (0 : G ⧸ H) at huv
          have heq : (f (a m i) : G ⧸ H) = ((0 : G) : G ⧸ H) := huv
          have hi : f (a m i) ∈ H := by
            simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq
          exact (label_not_mem_zmultiples hm hq hzero i hi).elim
      | some j =>
        cases i with
        | none =>
          cases j with
          | none => rfl
          | some j =>
            change (f (p m) : G ⧸ H) = (f (a m j) : G ⧸ H) at huv
            exact (hPA j huv).elim
        | some i =>
          cases j with
          | none =>
            change (f (a m i) : G ⧸ H) = (f (p m) : G ⧸ H) at huv
            exact (hPA i huv.symm).elim
          | some j =>
            change (f (a m i) : G ⧸ H) = (f (a m j) : G ⧸ H) at huv
            by_cases hij : i = j
            · exact congrArg (fun k : Index m => some (some k)) hij
            · have hmem : f (a m i) - f (a m j) ∈ H :=
                QuotientAddGroup.eq_iff_sub_mem.mp huv
              exact (difference_not_mem_zmultiples hm hq hzero i j hij hmem).elim
  have hdom : Nat.card (Option (Option (Index m))) = m + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]
    omega
  have hquot : m + 1 ≤ Nat.card (G ⧸ H) := by
    simpa only [hdom] using Nat.card_le_card_of_injective c hc
  have hH : Nat.card H = m := by
    dsimp [H]
    rw [Nat.card_zmultiples, hq]
  calc
    m * (m + 1) = (m + 1) * m := Nat.mul_comm m (m + 1)
    _ ≤ Nat.card (G ⧸ H) * Nat.card H := by
      rw [hH]
      exact Nat.mul_le_mul_right m hquot
    _ = Nat.card G :=
      (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H).symm


private lemma sentinel_plus_not_mem_zmultiples
    (hm : 2 ≤ m) (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i : Index m) :
    f (p m) + f (a m i) ∉ AddSubgroup.zmultiples (f (q m)) := by
  classical
  intro hmem
  obtain ⟨t, ht, he⟩ := residue_of_mem_zmultiples hq hmem
  have hforbid (C : Finset (Coordinate m)) (hpC : p m ∈ C) :
      (∑ x ∈ C, f x) ≠ 0 := by
    intro hz
    obtain ⟨j, hC⟩ := (hzero C).mp ⟨⟨p m, hpC⟩, hz⟩
    have hpT : p m ∈ triple m j := hC ▸ hpC
    simpa [triple, p, q, a, b] using hpT
  by_cases hlast : t = m - 1
  · have hord : m • f (q m) = 0 := by
      simpa only [hq] using addOrderOf_nsmul_eq_zero (f (q m))
    apply hforbid {q m, p m, a m i} (by simp)
    have hs : (∑ x ∈ ({q m, p m, a m i} : Finset (Coordinate m)), f x) =
        f (q m) + (f (p m) + f (a m i)) := by
      simp [q, p, a, add_assoc]
    rw [hs, ← he]
    calc
      f (q m) + t • f (q m) = (t + 1) • f (q m) := by
        rw [add_nsmul, one_nsmul]; abel
      _ = m • f (q m) := by congr 1; omega
      _ = 0 := hord
  · have hcard : ((Finset.univ : Finset (Index m)).erase i).card = m - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      omega
    have hbound : t ≤ ((Finset.univ : Finset (Index m)).erase i).card := by
      rw [hcard]
      omega
    obtain ⟨K, hK, hKcard⟩ := Finset.exists_subset_card_eq hbound
    have hi : i ∉ K := by
      intro hi
      have h := hK hi
      simpa using h
    let C := insert (p m) (insert (a m i) (paired m K))
    have hai : a m i ∉ paired m K := by simp [paired, a, b, hi]
    have hp : p m ∉ insert (a m i) (paired m K) := by simp [paired, p, a, b]
    apply hforbid C (by simp [C])
    dsimp only [C]
    rw [Finset.sum_insert hp, Finset.sum_insert hai, paired_sum hzero K, hKcard]
    rw [he]
    abel

private lemma sum_not_mem_zmultiples
    (hm : 2 ≤ m) (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (i j : Index m) (hij : i ≠ j) :
    f (a m i) + f (a m j) ∉ AddSubgroup.zmultiples (f (q m)) := by
  classical
  intro hmem
  have hm3 : 3 ≤ m := by
    by_contra h
    have hi := i.isLt
    have hj := j.isLt
    apply hij
    apply Fin.ext
    omega
  obtain ⟨t, ht, he⟩ := residue_of_mem_zmultiples hq hmem
  have hord : m • f (q m) = 0 := by
    simpa only [hq] using addOrderOf_nsmul_eq_zero (f (q m))
  by_cases hlast : t = m - 1
  · let C : Finset (Coordinate m) := {q m, a m i, a m j}
    have hs : (∑ x ∈ C, f x) =
        f (q m) + (f (a m i) + f (a m j)) := by
      simp [C, q, a, hij, add_assoc]
    apply forbidden_sum hzero i C (by simp [C]) (by simp [C, q, a, b])
    rw [hs, ← he]
    calc
      f (q m) + t • f (q m) = (t + 1) • f (q m) := by
        rw [add_nsmul, one_nsmul]; abel
      _ = m • f (q m) := by congr 1; omega
      _ = 0 := hord
  · by_cases hpenult : t = m - 2
    · have hsplit : t • f (q m) + f (q m) + f (q m) = m • f (q m) := by
        calc
          t • f (q m) + f (q m) + f (q m) = ((t + 1) + 1) • f (q m) := by
            simp only [add_nsmul, one_nsmul]
          _ = m • f (q m) := by congr 1; omega
      have hsum : f (b m i) + f (b m j) = 0 := by
        calc
          f (b m i) + f (b m j) =
              (f (a m i) + f (b m i)) + (f (a m j) + f (b m j)) -
                (f (a m i) + f (a m j)) := by abel
          _ = -f (q m) + -f (q m) - t • f (q m) := by
            rw [pair_sum hzero i, pair_sum hzero j, ← he]
          _ = -(t • f (q m) + f (q m) + f (q m)) := by abel
          _ = 0 := by rw [hsplit, hord, neg_zero]
      let C : Finset (Coordinate m) := {b m i, b m j}
      have hz : (∑ x ∈ C, f x) = 0 := by
        simpa [C, b, hij] using hsum
      obtain ⟨k, hC⟩ := (hzero C).mp ⟨by simp [C], hz⟩
      have hqC : q m ∈ C := hC ▸ (by simp [triple])
      simpa [C, q, b] using hqC
    · have hjmem : j ∈ (Finset.univ : Finset (Index m)).erase i := by
        simp [hij, Ne.symm hij]
      have hcard : (((Finset.univ : Finset (Index m)).erase i).erase j).card =
          m - 3 := by
        rw [Finset.card_erase_of_mem hjmem,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
        omega
      have hbound : t ≤ (((Finset.univ : Finset (Index m)).erase i).erase j).card := by
        rw [hcard]
        omega
      obtain ⟨K, hK, hKcard⟩ := Finset.exists_subset_card_eq hbound
      have hi : i ∉ K := by
        intro hi
        have h := hK hi
        simpa using h
      have hj : j ∉ K := by
        intro hj
        have h := hK hj
        simpa using h
      let C := insert (a m i) (insert (a m j) (paired m K))
      have haj : a m j ∉ paired m K := by simp [paired, a, b, hj]
      have hai : a m i ∉ insert (a m j) (paired m K) := by
        simp [paired, a, b, hi, hij]
      apply forbidden_sum hzero i C (by simp [C]) (by simp [C, paired, a, b, hi])
      dsimp only [C]
      rw [Finset.sum_insert hai, Finset.sum_insert haj, paired_sum hzero K, hKcard]
      rw [he]
      abel

private lemma signed_classes_card_bound
    {K : Type*} [AddCommGroup K] [Finite K] [IsAddCyclic K]
    (m : ℕ) (hm : 2 ≤ m) (A : Index m → K) (P : K)
    (hA0 : ∀ i, A i ≠ 0) (hAA : Function.Injective A)
    (hAN : ∀ i j, i ≠ j → A i ≠ -A j)
    (hP0 : P ≠ 0) (hPA : ∀ i, P ≠ A i) (hPN : ∀ i, P ≠ -A i) :
    2 * m ≤ Nat.card K := by
  classical
  letI := Fintype.ofFinite K
  let e : K ≃+ ZMod (Nat.card K) := (zmodAddCyclicAddEquiv (G := K) inferInstance).symm
  let T := (Finset.univ : Finset (Index m)).image A
  let U := (Finset.univ : Finset (Index m)).image (fun i => -A i)
  have hT : T.card = m - 1 := by
    rw [Finset.card_image_of_injective _ hAA, Finset.card_univ, Fintype.card_fin]
  have hU : U.card = m - 1 := by
    have hnegA : Function.Injective (fun i => -A i) :=
      fun _ _ h => hAA (neg_injective h)
    rw [Finset.card_image_of_injective _ hnegA, Finset.card_univ, Fintype.card_fin]
  have hself (x : K) (hx : x ∈ T ∩ U) : x = -x ∧ x ≠ 0 := by
    obtain ⟨hxT, hxU⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxT
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hxU
    have hij : i = j := by
      by_contra hij
      exact hAN i j hij he.symm
    subst j
    exact ⟨he.symm, hA0 i⟩
  have hval (x : K) (hx : x ∈ T ∩ U) : 2 * (e x).val = Nat.card K := by
    have hs := hself x hx
    have he : -(e x) = e x := by simpa using congrArg e hs.1.symm
    have hn : e x ≠ 0 := by
      intro hz
      apply hs.2
      exact e.injective (by simpa using hz)
    exact ((ZMod.neg_eq_self_iff (e x)).mp he).resolve_left hn
  have hinter : (T ∩ U).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply e.injective
    apply ZMod.val_injective
    have hxv := hval x hx
    have hyv := hval y hy
    omega
  have h0 : (0 : K) ∉ T ∪ U := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact hA0 i hi
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact hA0 i (neg_eq_zero.mp hi)
  have hP : P ∉ T ∪ U := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact hPA i hi.symm
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact hPN i hi.symm
  have hS : (T ∪ U).card + 2 ≤ Nat.card K := by
    have hcard := Finset.card_le_univ (insert (0 : K) (insert P (T ∪ U)))
    rw [Finset.card_insert_of_notMem (by simp [h0, hP0.symm]),
      Finset.card_insert_of_notMem hP] at hcard
    simpa only [Nat.card_eq_fintype_card, Nat.add_assoc] using hcard
  have hunion := Finset.card_union_add_card_inter T U
  by_cases hodd : Odd (Nat.card K)
  · have hempty : T ∩ U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hs := hself x hx
      have hn : e x ≠ 0 := by
        intro hz
        exact hs.2 (e.injective (by simpa using hz))
      exact ZMod.ne_neg_self hodd hn (by simpa using congrArg e hs.1)
    rw [hempty, Finset.card_empty, hT, hU] at hunion
    omega
  · have heven : Nat.card K % 2 = 0 := Nat.not_odd_iff.mp hodd
    rw [hT, hU] at hunion
    omega

theorem cyclic_carrier_card_lower_bound {G : Type*} [AddCommGroup G] [Finite G]
    [IsAddCyclic G] (m : ℕ) (hm : 2 ≤ m) (f : Coordinate m → G)
    (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j) :
    2 * m * m ≤ Nat.card G := by
  classical
  let H := AddSubgroup.zmultiples (f (q m))
  letI : IsAddCyclic (G ⧸ H) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' H) (QuotientAddGroup.mk'_surjective H)
  let A : Index m → G ⧸ H := fun i => (f (a m i) : G ⧸ H)
  let P : G ⧸ H := (f (p m) : G ⧸ H)
  have hA0 (i : Index m) : A i ≠ 0 := by
    intro h
    have heq : (f (a m i) : G ⧸ H) = ((0 : G) : G ⧸ H) := h
    exact label_not_mem_zmultiples hm hq hzero i
      (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hAA : Function.Injective A := by
    intro i j heq
    by_contra hij
    exact difference_not_mem_zmultiples hm hq hzero i j hij
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hAN (i j : Index m) (hij : i ≠ j) : A i ≠ -A j := by
    intro heq
    have heq' : (f (a m i) : G ⧸ H) = ((-f (a m j) : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_neg] using heq
    exact sum_not_mem_zmultiples hm hq hzero i j hij
      (by simpa only [sub_neg_eq_add] using QuotientAddGroup.eq_iff_sub_mem.mp heq')
  have hP0 : P ≠ 0 := by
    intro h
    have heq : (f (p m) : G ⧸ H) = ((0 : G) : G ⧸ H) := h
    exact sentinel_not_mem_zmultiples hq hzero
      (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hPA (i : Index m) : P ≠ A i := by
    intro heq
    exact sentinel_difference_not_mem_zmultiples hm hq hzero i
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hPN (i : Index m) : P ≠ -A i := by
    intro heq
    have heq' : (f (p m) : G ⧸ H) = ((-f (a m i) : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_neg] using heq
    exact sentinel_plus_not_mem_zmultiples hm hq hzero i
      (by simpa only [sub_neg_eq_add] using QuotientAddGroup.eq_iff_sub_mem.mp heq')
  have hquot : 2 * m ≤ Nat.card (G ⧸ H) :=
    signed_classes_card_bound m hm A P hA0 hAA hAN hP0 hPA hPN
  have hH : Nat.card H = m := by
    dsimp [H]
    rw [Nat.card_zmultiples, hq]
  calc
    2 * m * m ≤ Nat.card (G ⧸ H) * Nat.card H := by
      rw [hH]
      exact Nat.mul_le_mul_right m hquot
    _ = Nat.card G :=
      (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H).symm

/-- Odd finite abelian carriers satisfying the complete original zero-support
classification have at least `m * (2 * m + 1)` elements. -/
theorem odd_carrier_card_lower_bound {G : Type*} [AddCommGroup G] [Finite G]
    (m : ℕ) (hm : 2 ≤ m) (f : Coordinate m → G)
    (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔
        ∃ j : Index m, C = triple m j)
    (hodd : Odd (Nat.card G)) :
    m * (2 * m + 1) ≤ Nat.card G := by
  classical
  let H := AddSubgroup.zmultiples (f (q m))
  let A : Index m → G ⧸ H := fun i => (f (a m i) : G ⧸ H)
  let P : G ⧸ H := (f (p m) : G ⧸ H)
  have hquot_odd : Odd (Nat.card (G ⧸ H)) := by
    have hprod : Odd (Nat.card (G ⧸ H) * Nat.card H) := by
      rw [← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H]
      exact hodd
    exact (Nat.odd_mul.mp hprod).1
  have hA0 (i : Index m) : A i ≠ 0 := by
    intro h
    have heq : (f (a m i) : G ⧸ H) = ((0 : G) : G ⧸ H) := h
    exact label_not_mem_zmultiples hm hq hzero i
      (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hAA : Function.Injective A := by
    intro i j heq
    by_contra hij
    exact difference_not_mem_zmultiples hm hq hzero i j hij
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hAN (i j : Index m) : A i ≠ -A j := by
    by_cases hij : i = j
    · subst j
      intro heq
      have htwo : (2 : ℕ) • A i = 0 := by
        rw [two_nsmul]
        calc
          A i + A i = -A i + A i := congrArg (fun x => x + A i) heq
          _ = 0 := neg_add_cancel (A i)
      have hdvd : addOrderOf (A i) ∣ 2 :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo_order
      · exact hA0 i (AddMonoid.addOrderOf_eq_one_iff.mp hone)
      · have hcard : 2 ∣ Nat.card (G ⧸ H) := by
          simpa only [htwo_order] using addOrderOf_dvd_natCard (A i)
        exact hquot_odd.not_two_dvd_nat hcard
    · intro heq
      have heq' : (f (a m i) : G ⧸ H) = ((-f (a m j) : G) : G ⧸ H) := by
        simpa only [QuotientAddGroup.mk_neg] using heq
      exact sum_not_mem_zmultiples hm hq hzero i j hij
        (by simpa only [sub_neg_eq_add] using QuotientAddGroup.eq_iff_sub_mem.mp heq')
  have hP0 : P ≠ 0 := by
    intro h
    have heq : (f (p m) : G ⧸ H) = ((0 : G) : G ⧸ H) := h
    exact sentinel_not_mem_zmultiples hq hzero
      (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hPA (i : Index m) : P ≠ A i := by
    intro heq
    exact sentinel_difference_not_mem_zmultiples hm hq hzero i
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hPN (i : Index m) : P ≠ -A i := by
    intro heq
    have heq' : (f (p m) : G ⧸ H) = ((-f (a m i) : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_neg] using heq
    exact sentinel_plus_not_mem_zmultiples hm hq hzero i
      (by simpa only [sub_neg_eq_add] using QuotientAddGroup.eq_iff_sub_mem.mp heq')
  letI := Fintype.ofFinite (G ⧸ H)
  let T := (Finset.univ : Finset (Index m)).image A
  let U := (Finset.univ : Finset (Index m)).image (fun i => -A i)
  have hT : T.card = m - 1 := by
    rw [Finset.card_image_of_injective _ hAA, Finset.card_univ, Fintype.card_fin]
  have hU : U.card = m - 1 := by
    have hnegA : Function.Injective (fun i => -A i) :=
      fun _ _ h => hAA (neg_injective h)
    rw [Finset.card_image_of_injective _ hnegA, Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxU
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxT
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hxU
    exact hAN i j heq.symm
  have h0 : (0 : G ⧸ H) ∉ T ∪ U := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact hA0 i hi
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact hA0 i (neg_eq_zero.mp hi)
  have hP : P ∉ T ∪ U := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact hPA i hi.symm
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact hPN i hi.symm
  have hS : (T ∪ U).card + 2 ≤ Nat.card (G ⧸ H) := by
    have hcard := Finset.card_le_univ (insert (0 : G ⧸ H) (insert P (T ∪ U)))
    rw [Finset.card_insert_of_notMem (by simp [h0, hP0.symm]),
      Finset.card_insert_of_notMem hP] at hcard
    simpa only [Nat.card_eq_fintype_card, Nat.add_assoc] using hcard
  have hunion : (T ∪ U).card = T.card + U.card :=
    Finset.card_union_of_disjoint hdisj
  have hquot : 2 * m + 1 ≤ Nat.card (G ⧸ H) := by
    have hparity := Nat.odd_iff.mp hquot_odd
    rw [hT, hU] at hunion
    omega
  have hH : Nat.card H = m := by
    dsimp [H]
    rw [Nat.card_zmultiples, hq]
  calc
    m * (2 * m + 1) = (2 * m + 1) * m := Nat.mul_comm m (2 * m + 1)
    _ ≤ Nat.card (G ⧸ H) * Nat.card H := by
      rw [hH]
      exact Nat.mul_le_mul_right m hquot
    _ = Nat.card G :=
      (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H).symm

private def signedCoordinate (m : ℕ) (i : Index m) (s : Bool) : Coordinate m :=
  if s then b m i else a m i

private lemma signed_pair_sum
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ j : Index m, C = triple m j)
    (i : Index m) (s : Bool) :
    f (signedCoordinate m i s) + f (signedCoordinate m i (!s)) = -f (q m) := by
  cases s <;> simpa [signedCoordinate, add_comm] using pair_sum hzero i

private lemma signed_forbidden_sum
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ j : Index m, C = triple m j)
    (i : Index m) (s : Bool) (C : Finset (Coordinate m))
    (ha : signedCoordinate m i s ∈ C) (hb : signedCoordinate m i (!s) ∉ C) :
    (∑ x ∈ C, f x) ≠ 0 := by
  classical
  intro hz
  obtain ⟨j, hC⟩ := (hzero C).mp ⟨⟨signedCoordinate m i s, ha⟩, hz⟩
  have hij : i = j := by
    have hmem := hC ▸ ha
    cases s <;> simpa [signedCoordinate, triple, q, a, b] using hmem
  apply hb
  rw [hC, hij]
  cases s <;> simp [signedCoordinate, triple]

private lemma signed_triple_completion_ne_zero
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ j : Index m, C = triple m j)
    (i j k : Index m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t u : Bool) (K : Finset (Index m))
    (hi : i ∉ K) (hj : j ∉ K) (hk : k ∉ K) :
    (f (signedCoordinate m i s) + f (signedCoordinate m j t) +
        f (signedCoordinate m k u) - K.card • f (q m) ≠ 0) ∧
    (f (q m) + f (signedCoordinate m i s) + f (signedCoordinate m j t) +
        f (signedCoordinate m k u) - K.card • f (q m) ≠ 0) := by
  classical
  let C := insert (signedCoordinate m i s)
    (insert (signedCoordinate m j t) (insert (signedCoordinate m k u) (paired m K)))
  have hku : signedCoordinate m k u ∉ paired m K := by
    cases u <;> simp [signedCoordinate, paired, a, b, hk]
  have hjt : signedCoordinate m j t ∉ insert (signedCoordinate m k u) (paired m K) := by
    cases t <;> cases u <;> simp [signedCoordinate, paired, a, b, hj, hjk]
  have his : signedCoordinate m i s ∉
      insert (signedCoordinate m j t) (insert (signedCoordinate m k u) (paired m K)) := by
    cases s <;> cases t <;> cases u <;>
      simp [signedCoordinate, paired, a, b, hi, hij, hik]
  have ha : signedCoordinate m i s ∈ C := by simp [C]
  have hb : signedCoordinate m i (!s) ∉ C := by
    cases s <;> cases t <;> cases u <;>
      simp [C, signedCoordinate, paired, a, b, hi, hij, hik]
  have hqC : q m ∉ C := by
    cases s <;> cases t <;> cases u <;> simp [C, signedCoordinate, paired, q, a, b]
  have hs : (∑ x ∈ C, f x) = f (signedCoordinate m i s) +
      f (signedCoordinate m j t) + f (signedCoordinate m k u) - K.card • f (q m) := by
    dsimp only [C]
    rw [Finset.sum_insert his, Finset.sum_insert hjt, Finset.sum_insert hku,
      paired_sum hzero K]
    abel
  have hs' : (∑ x ∈ insert (q m) C, f x) = f (q m) +
      f (signedCoordinate m i s) + f (signedCoordinate m j t) +
      f (signedCoordinate m k u) - K.card • f (q m) := by
    rw [Finset.sum_insert hqC, hs]
    abel
  constructor
  · rw [← hs]
    exact signed_forbidden_sum hzero i s C ha hb
  · rw [← hs']
    apply signed_forbidden_sum hzero i s (insert (q m) C)
    · exact Finset.mem_insert_of_mem ha
    · cases s <;> simpa [signedCoordinate, q, a, b] using hb

/-- Three labels from distinct pairs, with either coordinate chosen in each pair,
never sum to a multiple of the distinguished label. -/
private lemma signed_triple_not_mem_zmultiples
    (hm : 4 ≤ m) (hq : addOrderOf (f (q m)) = m)
    (hzero : ∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ j : Index m, C = triple m j)
    (i j k : Index m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t u : Bool) :
    f (signedCoordinate m i s) + f (signedCoordinate m j t) +
      f (signedCoordinate m k u) ∉ AddSubgroup.zmultiples (f (q m)) := by
  classical
  intro hmem
  obtain ⟨r, hr, he⟩ := residue_of_mem_zmultiples hq hmem
  let S := f (signedCoordinate m i s) + f (signedCoordinate m j t) +
    f (signedCoordinate m k u)
  have hord : m • f (q m) = 0 := by
    simpa only [hq] using addOrderOf_nsmul_eq_zero (f (q m))
  by_cases hsmall : r ≤ m - 4
  · have hcard : ((((Finset.univ : Finset (Index m)).erase i).erase j).erase k).card =
        m - 4 := by
      rw [Finset.card_erase_of_mem (by simp [Ne.symm hik, Ne.symm hjk]),
        Finset.card_erase_of_mem (by simp [Ne.symm hij]),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    have hbound : r ≤ ((((Finset.univ : Finset (Index m)).erase i).erase j).erase k).card := by
      rw [hcard]
      exact hsmall
    obtain ⟨K, hK, hKcard⟩ := Finset.exists_subset_card_eq hbound
    have hi : i ∉ K := by intro h; have := hK h; simp at this
    have hj : j ∉ K := by intro h; have := hK h; simp at this
    have hk : k ∉ K := by intro h; have := hK h; simp at this
    have hne := (signed_triple_completion_ne_zero hzero i j k hij hik hjk s t u K hi hj hk).1
    apply hne
    rw [hKcard, he, sub_self]
  · have hempty := signed_triple_completion_ne_zero hzero i j k hij hik hjk
      s t u ∅ (by simp) (by simp) (by simp)
    by_cases hlast : r = m - 1
    · apply hempty.2
      simp only [Finset.card_empty, zero_nsmul, sub_zero]
      calc
        f (q m) + f (signedCoordinate m i s) + f (signedCoordinate m j t) +
            f (signedCoordinate m k u) = f (q m) + S := by dsimp [S]; abel
        _ = (r + 1) • f (q m) := by dsimp only [S]; rw [← he, add_nsmul, one_nsmul]; abel
        _ = m • f (q m) := by congr 1; omega
        _ = 0 := hord
    · have hmate (l : Index m) (v : Bool) :
          f (signedCoordinate m l (!v)) = -f (q m) - f (signedCoordinate m l v) := by
        have hp := signed_pair_sum hzero l v
        calc
          f (signedCoordinate m l (!v)) =
              (f (signedCoordinate m l v) + f (signedCoordinate m l (!v))) -
                f (signedCoordinate m l v) := by abel
          _ = -f (q m) - f (signedCoordinate m l v) := by rw [hp]
      have hmates : f (signedCoordinate m i (!s)) + f (signedCoordinate m j (!t)) +
          f (signedCoordinate m k (!u)) = -((3 + r) • f (q m)) := by
        rw [hmate i s, hmate j t, hmate k u, add_nsmul, he]
        simp only [succ_nsmul, zero_nsmul, zero_add]
        abel
      have hne := signed_triple_completion_ne_zero hzero i j k hij hik hjk
        (!s) (!t) (!u) ∅ (by simp) (by simp) (by simp)
      rcases (show r = m - 3 ∨ r = m - 2 by omega) with hr3 | hr2
      · apply hne.1
        simp only [Finset.card_empty, zero_nsmul, sub_zero]
        rw [hmates, show 3 + r = m by omega, hord, neg_zero]
      · apply hne.2
        simp only [Finset.card_empty, zero_nsmul, sub_zero]
        calc
          f (q m) + f (signedCoordinate m i (!s)) + f (signedCoordinate m j (!t)) +
              f (signedCoordinate m k (!u)) = f (q m) - ((3 + r) • f (q m)) := by
                simpa only [sub_eq_add_neg, add_assoc] using
                  congrArg (fun x : G => f (q m) + x) hmates
          _ = 0 := by rw [show 3 + r = m + 1 by omega, add_nsmul, hord, one_nsmul]; simp

private def signedValue {K : Type*} [AddGroup K] (s : Bool) (x : K) : K :=
  if s then -x else x

private lemma signedValue_signedValue {K : Type*} [AddGroup K]
    (s t : Bool) (x : K) :
    signedValue s (signedValue t x) = signedValue (Bool.xor s t) x := by
  cases s <;> cases t <;> simp [signedValue]

set_option maxHeartbeats 2000000 in
-- The unsorted residue orders require a larger Presburger proof term.
/-- The small interval leaves no four distinct positive absolute residues without
an additive relation on three different residues. -/
private lemma four_small_residues_impossible (n : ℕ) (hn : 10 ≤ n) (hn' : n ≤ 13)
    (r : Fin 4 → ℕ) (hpos : ∀ i, 0 < r i) (hbound : ∀ i, 2 * r i ≤ n)
    (hinj : Function.Injective r)
    (hadd : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → r i + r j ≠ r k)
    (hsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → r i + r j + r k ≠ n) : False := by
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2; have h3 := hpos 3
  have b0 := hbound 0; have b1 := hbound 1; have b2 := hbound 2; have b3 := hbound 3
  have d01 : r 0 ≠ r 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) (hinj h)
  have d02 : r 0 ≠ r 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hinj h)
  have d03 : r 0 ≠ r 3 := fun h => (by decide : (0 : Fin 4) ≠ 3) (hinj h)
  have d12 : r 1 ≠ r 2 := fun h => (by decide : (1 : Fin 4) ≠ 2) (hinj h)
  have d13 : r 1 ≠ r 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hinj h)
  have d23 : r 2 ≠ r 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (hinj h)
  have a012 := hadd 0 1 2 (by decide) (by decide) (by decide)
  have a021 := hadd 0 2 1 (by decide) (by decide) (by decide)
  have a120 := hadd 1 2 0 (by decide) (by decide) (by decide)
  have a013 := hadd 0 1 3 (by decide) (by decide) (by decide)
  have a031 := hadd 0 3 1 (by decide) (by decide) (by decide)
  have a130 := hadd 1 3 0 (by decide) (by decide) (by decide)
  have a023 := hadd 0 2 3 (by decide) (by decide) (by decide)
  have a032 := hadd 0 3 2 (by decide) (by decide) (by decide)
  have a230 := hadd 2 3 0 (by decide) (by decide) (by decide)
  have a123 := hadd 1 2 3 (by decide) (by decide) (by decide)
  have a132 := hadd 1 3 2 (by decide) (by decide) (by decide)
  have a231 := hadd 2 3 1 (by decide) (by decide) (by decide)
  have s012 := hsum 0 1 2 (by decide) (by decide) (by decide)
  have s013 := hsum 0 1 3 (by decide) (by decide) (by decide)
  have s023 := hsum 0 2 3 (by decide) (by decide) (by decide)
  have s123 := hsum 1 2 3 (by decide) (by decide) (by decide)
  omega

private lemma four_signed_classes_card_bound
    {K : Type*} [AddCommGroup K] [Finite K] [IsAddCyclic K]
    (hn : 10 ≤ Nat.card K) (A : Fin 4 → K)
    (hA0 : ∀ i, A i ≠ 0) (hAA : Function.Injective A)
    (hAN : ∀ i j, i ≠ j → A i ≠ -A j)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ s t u : Bool,
      signedValue s (A i) + signedValue t (A j) + signedValue u (A k) ≠ 0) :
    14 ≤ Nat.card K := by
  classical
  by_contra hcard
  let n := Nat.card K
  have hn' : n ≤ 13 := by dsimp [n]; omega
  have hn0 : 0 < n := by dsimp [n]; omega
  letI : NeZero n := ⟨by omega⟩
  let e : K ≃+ ZMod n := (zmodAddCyclicAddEquiv (G := K) inferInstance).symm
  let B : Fin 4 → ZMod n := fun i => e (A i)
  have hB0 (i) : B i ≠ 0 := by
    intro h; exact hA0 i (e.injective (by simpa [B] using h))
  have hrepr (i : Fin 4) : ∃ s : Bool, ∃ v : ℕ,
      0 < v ∧ 2 * v ≤ n ∧ (v : ZMod n) = signedValue s (B i) := by
    have hv : (B i).val < n := ZMod.val_lt _
    have hv0 : 0 < (B i).val := (ZMod.val_pos).mpr (hB0 i)
    by_cases hsmall : 2 * (B i).val ≤ n
    · exact ⟨false, (B i).val, hv0, hsmall, by simp [signedValue]⟩
    · refine ⟨true, n - (B i).val, by omega, by omega, ?_⟩
      dsimp only [signedValue]
      rw [Nat.cast_sub (Nat.le_of_lt hv), ZMod.natCast_self, ZMod.natCast_zmod_val,
        zero_sub]
      rfl
  choose signs r hpos hbound hrepr using hrepr
  have horbit (i j : Fin 4) (h : r i = r j) : A i = A j ∨ A i = -A j := by
    have heq : signedValue (signs i) (B i) = signedValue (signs j) (B j) := by
      rw [← hrepr i, ← hrepr j, h]
    cases hi : signs i <;> cases hj : signs j <;>
      simp only [hi, hj, signedValue, Bool.false_eq_true, ↓reduceIte] at heq
    · exact Or.inl (e.injective heq)
    · exact Or.inr (e.injective (by simpa [B] using heq))
    · exact Or.inr (e.injective (by simpa [B] using (congrArg Neg.neg heq)))
    · exact Or.inl (e.injective (neg_injective heq))
  have hinj : Function.Injective r := by
    intro i j h
    rcases horbit i j h with he | he
    · exact hAA he
    · by_contra hij
      exact hAN i j hij he
  have hrepTriple (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (s t u : Bool) : signedValue s (r i : ZMod n) + signedValue t (r j : ZMod n) +
        signedValue u (r k : ZMod n) ≠ 0 := by
    rw [hrepr i, hrepr j, hrepr k, signedValue_signedValue, signedValue_signedValue,
      signedValue_signedValue]
    intro hz
    apply htriple i j k hij hik hjk (Bool.xor s (signs i))
      (Bool.xor t (signs j)) (Bool.xor u (signs k))
    apply e.injective
    simpa only [map_add, map_zero, signedValue, apply_ite, map_neg, B] using hz
  apply four_small_residues_impossible n hn hn' r hpos hbound hinj
  · intro i j k hij hik hjk heq
    apply hrepTriple i j k hij hik hjk false false true
    have hc := congrArg (fun v : ℕ => (v : ZMod n)) heq
    simp only [Nat.cast_add] at hc
    simpa only [signedValue, Bool.false_eq_true, ↓reduceIte, hc, add_neg_cancel]
  · intro i j k hij hik hjk heq
    apply hrepTriple i j k hij hik hjk false false false
    have hc := congrArg (fun v : ℕ => (v : ZMod n)) heq
    simpa only [Nat.cast_add, ZMod.natCast_self, signedValue, Bool.false_eq_true,
      ↓reduceIte] using hc

/-- The complete original support pattern for four pairs in a finite cyclic
carrier requires at least seventy carrier elements. -/
theorem cyclic_five_carrier_card_lower_bound {G : Type*} [AddCommGroup G] [Finite G]
    [IsAddCyclic G] (f : Coordinate 5 → G)
    (hq : addOrderOf (f (q 5)) = 5)
    (hzero : ∀ C : Finset (Coordinate 5),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ j : Index 5, C = triple 5 j) :
    70 ≤ Nat.card G := by
  classical
  let H := AddSubgroup.zmultiples (f (q 5))
  letI : IsAddCyclic (G ⧸ H) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' H) (QuotientAddGroup.mk'_surjective H)
  let A : Fin 4 → G ⧸ H := fun i => (f (a 5 i) : G ⧸ H)
  have hA0 (i : Fin 4) : A i ≠ 0 := by
    intro h
    have heq : (f (a 5 i) : G ⧸ H) = ((0 : G) : G ⧸ H) := h
    exact label_not_mem_zmultiples (by decide) hq hzero i
      (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hAA : Function.Injective A := by
    intro i j heq
    by_contra hij
    exact difference_not_mem_zmultiples (by decide) hq hzero i j hij
      (QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hAN (i j : Fin 4) (hij : i ≠ j) : A i ≠ -A j := by
    intro heq
    have heq' : (f (a 5 i) : G ⧸ H) = ((-f (a 5 j) : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_neg] using heq
    exact sum_not_mem_zmultiples (by decide) hq hzero i j hij
      (by simpa only [sub_neg_eq_add] using QuotientAddGroup.eq_iff_sub_mem.mp heq')
  have hq0 : (f (q 5) : G ⧸ H) = 0 := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [sub_zero] using AddSubgroup.mem_zmultiples (f (q 5))
  have hchosen (i : Fin 4) (s : Bool) :
      (f (signedCoordinate 5 i s) : G ⧸ H) = signedValue s (A i) := by
    cases s
    · rfl
    · have hp := congrArg (fun x : G => (x : G ⧸ H)) (pair_sum hzero i)
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_neg, hq0, neg_zero] at hp
      dsimp only [signedCoordinate, signedValue]
      simp only [↓reduceIte]
      change (f (b 5 i) : G ⧸ H) = -A i
      have hz : A i + (f (b 5 i) : G ⧸ H) = 0 := hp
      exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hz)
  have htriple (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (s t u : Bool) : signedValue s (A i) + signedValue t (A j) +
        signedValue u (A k) ≠ 0 := by
    intro hz
    have heq : ((f (signedCoordinate 5 i s) + f (signedCoordinate 5 j t) +
        f (signedCoordinate 5 k u) : G) : G ⧸ H) = ((0 : G) : G ⧸ H) := by
      simpa only [QuotientAddGroup.mk_add, QuotientAddGroup.mk_zero, hchosen] using hz
    exact signed_triple_not_mem_zmultiples (by decide) hq hzero i j k hij hik hjk s t u
      (by simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp heq)
  have hH : Nat.card H = 5 := by
    dsimp [H]
    rw [Nat.card_zmultiples, hq]
  have hG : Nat.card G = Nat.card (G ⧸ H) * 5 := by
    simpa only [hH] using AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hten : 10 ≤ Nat.card (G ⧸ H) := by
    have hbase := cyclic_carrier_card_lower_bound 5 (by decide) f hq hzero
    rw [hG] at hbase
    omega
  have hfourteen := four_signed_classes_card_bound hten A hA0 hAA hAN htriple
  rw [hG]
  omega
end D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound
