/- GID: D5/S3/Combinatorics/Sequenceability/OriginalCyclicFiveCarrierLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalCyclicFiveCarrierLowerBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.Coset.Card, mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Sequenceability/OriginalCyclicFiveCarrierLowerBound.cyclic_five_carrier_card_lower_bound; premises=D5/S3/Combinatorics/Sequenceability/OriginalSharpnessCarrierLowerBound.cyclic_carrier_card_lower_bound
   digest: The complete original support pattern at order five requires seventy cyclic carrier elements. -/

import D5.S3.Combinatorics.Sequenceability.OriginalSharpnessCarrierLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u_2

namespace D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound

open scoped Classical BigOperators
open OriginalFiniteOrderSharpness (Index Coordinate q p a b full triple)
open OriginalSharpnessCarrierLowerBound
  (paired pair_sum paired_sum residue_of_mem_zmultiples label_not_mem_zmultiples
    difference_not_mem_zmultiples sum_not_mem_zmultiples cyclic_carrier_card_lower_bound)

variable {G : Type*} [AddCommGroup G] [Finite G]
variable {m : ℕ} {f : Coordinate m → G}

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
lemma signed_triple_not_mem_zmultiples
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
theorem cyclic_five_carrier_card_lower_bound {G : Type u_2} [AddCommGroup G] [Finite G]
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
end D5.S3.Combinatorics.Sequenceability.OriginalCyclicFiveCarrierLowerBound
