/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined
   mirror-E: none(waiver:refined-enumeration-of-the-arrow-pattern-32-1-to-3)
   anchors: []
   utility: none
   digest: The last-cycle bijection gives the Catalan refined counts and the exact integer recurrence for the avoider series. -/

import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection
import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeLastCycle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeRefined

open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeCatalan
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection
open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeGapCode
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeLastCycle

noncomputable section

/-- For a fixed set of earlier letters in the last cycle, its allowed orders
ending at the selected maximum are counted by one Catalan number. -/
theorem final_cycle_word_count (t : Finset ℕ) (b : ℕ)
    (hb : ∀ x ∈ t, x < b) :
    {w : List ℕ | w.Perm (t.toList ++ [b]) ∧
      w.getLast? = some b ∧ ¬ Has132 w}.ncard = catalan t.card := by
  have hset :
      {w : List ℕ | w.Perm (t.toList ++ [b]) ∧
        w.getLast? = some b ∧ ¬ Has132 w} =
      (fun u : List ℕ => u ++ [b]) ''
        {u : List ℕ | u.Perm t.toList ∧ ¬ Has132 u} := by
    ext w
    constructor
    · rintro ⟨hperm, hlast, h132⟩
      let u := w.dropLast
      have hmem : b ∈ w.getLast? := by simp [hlast]
      have heq : u ++ [b] = w :=
        List.dropLast_append_getLast? (l := w) b hmem
      have hu : u.Perm t.toList :=
        (List.perm_append_right_iff [b]).mp (by simpa [heq] using hperm)
      have hbu : ∀ x ∈ u, x < b := by
        intro x hx
        exact hb x (Finset.mem_toList.mp (hu.mem_iff.mp hx))
      refine ⟨u, ⟨hu, ?_⟩, heq⟩
      intro h
      exact h132 (by rw [← heq]; exact (has132_append_max_iff u b hbu).mpr h)
    · rintro ⟨u, ⟨hu, h132⟩, rfl⟩
      have hbu : ∀ x ∈ u, x < b := by
        intro x hx
        exact hb x (Finset.mem_toList.mp (hu.mem_iff.mp hx))
      refine ⟨hu.append_right [b], by simp, ?_⟩
      intro h
      exact h132 ((has132_append_max_iff u b hbu).mp h)
  rw [hset, Set.ncard_image_of_injective _ (fun _ _ h => List.append_cancel_right h)]
  exact ncard_avoid132 t

/-- A positive last-cycle stratum is a Catalan order times independent gap words. -/
theorem stratum_card_positive (n k : ℕ) (hk : k + 1 ≤ n) :
    (Nat.card (Stratum n (k + 1)) : ℤ) = (catalan k : ℤ) *
      PowerSeries.coeff (n - (k + 1)) (series ^ (k + 2)) := by
  classical
  have horders (d : GapData n (k + 1)) : Nat.card (CycleOrders d.val.1) = catalan k := by
    let S := d.val.1
    have hlen : S.length = k + 1 := d.property.2.1
    have hsort : S.Pairwise (· < ·) := d.property.1
    have hnd : S.Nodup := (d.property.2.2.1.nodup_iff.mpr List.nodup_range').of_append_right
    have hne : S ≠ [] := by intro h; simp [h] at hlen
    let b := S.getLast hne
    let t := S.dropLast.toFinset
    have hlast : S.getLast? = some b := List.getLast?_eq_some_getLast hne
    have hsplit : S.dropLast ++ [b] = S :=
      List.dropLast_append_getLast? (l := S) b (by simp [hlast])
    have hsmall : ∀ x ∈ S.dropLast, x < b := by
      intro x hx
      have hsort' : (S.dropLast ++ [b]).Pairwise (· < ·) := hsplit.symm ▸ hsort
      exact (List.pairwise_append.mp hsort').2.2 x hx b (by simp)
    have hbound : ∀ x ∈ S, x ≤ b := by
      intro x hx
      rw [← hsplit] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hsmall x hx).le
      · have : x = b := by simpa using hx
        omega
    have hdropnd : S.dropLast.Nodup := hnd.sublist (List.dropLast_sublist S)
    have htperm : t.toList.Perm S.dropLast := List.toFinset_toList hdropnd
    have hbase : (t.toList ++ [b]).Perm S := by
      simpa only [hsplit] using htperm.append_right [b]
    have htcard : t.card = k := by
      dsimp [t]
      rw [List.card_toFinset, List.dedup_eq_self.mpr hdropnd, List.length_dropLast, hlen]
      omega
    have hset : {w : List ℕ | w.Perm S ∧ (∀ x ∈ w, x ≤ w.getLastD 0) ∧ ¬ Has132 w} =
        {w : List ℕ | w.Perm (t.toList ++ [b]) ∧ w.getLast? = some b ∧ ¬ Has132 w} := by
      ext w
      constructor
      · rintro ⟨hw, hmax, h132⟩
        have hwne : w ≠ [] := by intro h; have hh := hw.length_eq; simp [h, hlen] at hh
        let c := w.getLast hwne
        have hclast : w.getLast? = some c := List.getLast?_eq_some_getLast hwne
        have hcw : c ∈ w := List.getLast_mem hwne
        have hcle : c ≤ b := hbound c (hw.mem_iff.mp hcw)
        have hbw : b ∈ w := hw.mem_iff.mpr (List.getLast_mem hne)
        have hbcle : b ≤ c := by simpa [hclast] using hmax b hbw
        have hcb : c = b := by omega
        exact ⟨hw.trans hbase.symm, by simpa [hcb] using hclast, h132⟩
      · rintro ⟨hw, hlastw, h132⟩
        have hwS : w.Perm S := hw.trans hbase
        refine ⟨hwS, ?_, h132⟩
        intro x hx
        simpa [hlastw] using hbound x (hwS.mem_iff.mp hx)
    change {w : List ℕ | w.Perm S ∧ (∀ x ∈ w, x ≤ w.getLastD 0) ∧ ¬ Has132 w}.ncard = _
    rw [hset, final_cycle_word_count t b
      (fun x hx => hsmall x (List.mem_toFinset.mp hx)), htcard]
  have : Finite (GapData n (k + 1)) := by
    let Perms := {p : List ℕ // p.Perm (List.range' 1 n)}
    have hfinite : {p : List ℕ | p.Perm (List.range' 1 n)}.Finite := by
      apply (List.permutations (List.range' 1 n)).finite_toSet.subset
      intro p hp
      exact List.mem_permutations.mpr hp
    have : Finite Perms := hfinite.to_subtype
    let f : GapData n (k + 1) → Perms := fun d => ⟨d.val.2 ++ d.val.1, d.property.2.2.1⟩
    apply Finite.of_injective f
    intro a b hab
    have hlen (d : GapData n (k + 1)) : d.val.2.length = n - (k + 1) := by
      have h := d.property.2.2.1.length_eq
      simp only [List.length_append, List.length_range', d.property.2.1] at h
      omega
    have hw : a.val.2 ++ a.val.1 = b.val.2 ++ b.val.1 := congrArg Subtype.val hab
    have hpre : a.val.2 = b.val.2 := by
      have h := congrArg (List.take (n - (k + 1))) hw
      simpa [hlen] using h
    have hsel : a.val.1 = b.val.1 := by
      rw [hpre] at hw
      exact List.append_cancel_left hw
    exact Subtype.ext (Prod.ext hsel hpre)
  have (d : GapData n (k + 1)) : Finite (CycleOrders d.val.1) := by
    have hfinite : {w : List ℕ | w.Perm d.val.1 ∧
        (∀ x ∈ w, x ≤ w.getLastD 0) ∧ ¬ Has132 w}.Finite := by
      apply (List.permutations d.val.1).finite_toSet.subset
      intro w hw
      exact List.mem_permutations.mpr hw.1
    exact hfinite.to_subtype
  let : Fintype (GapData n (k + 1)) := Fintype.ofFinite _
  have hcard : Nat.card (Stratum n (k + 1)) = catalan k * Nat.card (GapData n (k + 1)) := by
    rw [← Nat.card_congr (Equiv.ofBijective (joinLastCycle n k) (joinLastCycle_bijective n k)),
      Nat.card_sigma]
    simp_rw [horders]
    simp [← Nat.card_eq_fintype_card, mul_comm]
  have hg := gapData_card (n - (k + 1)) (k + 1)
  rw [Nat.sub_add_cancel hk] at hg
  rw [hcard, Nat.cast_mul, hg]

/-- Partitioning by the final-cycle length gives precisely the recurrence used
by the formal-series algebra module. -/
theorem count_recurrence : ∀ n, 1 ≤ n → (count n : ℤ) = (count (n - 1) : ℤ) +
    ∑ k ∈ Finset.Icc 1 (n - 1), (catalan (k - 1) : ℤ) *
      PowerSeries.coeff (n - 1 - k) (series ^ (k + 1)) := by
  classical
  intro N hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  simp only [Nat.succ_sub_one]
  have hfinite (m : ℕ) : (avoiders m [3, 2] [(1, 3)] 3).Finite := by
    apply (List.permutations (List.range' 1 m)).finite_toSet.subset
    intro p hp
    exact List.mem_permutations.mpr hp.1
  have (k : ℕ) : Finite (Stratum n k) := by
    have : Finite (avoiders (n + 1) [3, 2] [(1, 3)] 3) := (hfinite _).to_subtype
    exact Finite.of_injective (fun p : Stratum n k =>
      (⟨p.val, p.property.1⟩ : avoiders (n + 1) [3, 2] [(1, 3)] 3))
      (fun _ _ h => Subtype.ext (congrArg
        (fun p : avoiders (n + 1) [3, 2] [(1, 3)] 3 => p.val) h))
  let f : (Σ k : Fin (n + 1), Stratum n k.val) →
      avoiders (n + 1) [3, 2] [(1, 3)] 3 := fun z => ⟨z.2.val, z.2.property.1⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, p⟩ ⟨j, q⟩ h
      have hpq : p.val = q.val := congrArg Subtype.val h
      have hi := p.property.2
      have hj := q.property.2
      rw [hpq] at hi
      have hij : i = j := Fin.ext (by omega)
      subst j
      have hpq' : p = q := Subtype.ext hpq
      subst q
      rfl
    · rintro ⟨p, hp⟩
      have hm : n + 1 ∈ p := hp.1.mem_iff.mpr (by
        apply List.mem_range'.mpr; exact ⟨n, by omega, by omega⟩)
      have hidx : p.idxOf (n + 1) < n + 1 := by
        have hh := List.idxOf_lt_length_of_mem hm
        have hlen : p.length = n + 1 := by simpa using hp.1.length_eq
        omega
      let i : Fin (n + 1) := ⟨n - p.idxOf (n + 1), by omega⟩
      refine ⟨⟨i, ⟨p, hp, by dsimp [i]; omega⟩⟩, rfl⟩
  have htotal : count (n + 1) = ∑ k : Fin (n + 1), Nat.card (Stratum n k.val) := by
    have h := Nat.card_congr (Equiv.ofBijective f hf)
    rw [Nat.card_sigma, Nat.card_coe_set_eq] at h
    exact h.symm
  have hzero : Nat.card (Stratum n 0) = count n := by
    have hset : {p : List ℕ | p ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 ∧
        p.idxOf (n + 1) + 0 = n} =
        {p : List ℕ | p ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 ∧ p.getLast? = some (n + 1)} := by
      ext p
      constructor
      · rintro ⟨hp, hi⟩
        have hlen : p.length = n + 1 := by simpa using hp.1.length_eq
        have hm : n + 1 ∈ p := hp.1.mem_iff.mpr (by
          apply List.mem_range'.mpr; exact ⟨n, by omega, by omega⟩)
        have hidx := List.idxOf_lt_length_of_mem hm
        refine ⟨hp, ?_⟩
        rw [List.getLast?_eq_getElem?, hlen]
        have hn : n + 1 - 1 = n := by omega
        rw [hn, List.getElem?_eq_getElem (by omega)]
        congr 1
        have hi' : p.idxOf (n + 1) = n := by omega
        simpa [hi'] using List.getElem_idxOf hidx
      · rintro ⟨hp, hlast⟩
        have hlen : p.length = n + 1 := by simpa using hp.1.length_eq
        have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
        have hget : p[n]'(by omega) = n + 1 := by
          rw [List.getLast?_eq_getElem?, hlen] at hlast
          have hn : n + 1 - 1 = n := by omega
          rw [hn, List.getElem?_eq_getElem (by omega)] at hlast
          exact Option.some.inj hlast
        refine ⟨hp, ?_⟩
        rw [← hget, hnd.idxOf_getElem n (by omega)]
        omega
    change {p : List ℕ | p ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 ∧
      p.idxOf (n + 1) + 0 = n}.ncard = _
    rw [hset, singleton_final_cycle_count]
  have hsum : (count (n + 1) : ℤ) = (count n : ℤ) +
      ∑ k ∈ Finset.Icc 1 n, (Nat.card (Stratum n k) : ℤ) := by
    rw [htotal, Nat.cast_sum, Fin.sum_univ_eq_sum_range
      (f := fun k => (Nat.card (Stratum n k) : ℤ))]
    have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hrange, Finset.sum_insert (by simp), hzero]
  exact hsum.trans (congrArg ((count n : ℤ) + ·) (by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hjpos, hjle⟩ := Finset.mem_Icc.mp hj
    have h := stratum_card_positive n (j - 1) (by omega)
    have hjEq : j - 1 + 1 = j := by omega
    simpa only [hjEq, show j - 1 + 2 = j + 1 by omega, Nat.succ_sub_one] using h))

end
end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeRefined

#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeRefined.stratum_card_positive
