/- GID: D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Identity and transposition classes lead tensor high-temperature degrees. -/

import D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity
import D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture

/-! Formal reading of the all-ones and transposition leading classes in (7.21). -/

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses

open Finset
open D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity (onesPartition)
open D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture (partition126 partition126_parts)

set_option autoImplicit false

noncomputable section

/-- The degree in equation (7.21), summed over tuples of distinct partition parts. -/
def degree (s : ℕ) {n : ℕ} (p : Nat.Partition n) : ℚ :=
  ∑ t : Fin s → p.parts.toFinset,
    (∏ j, ((t j : ℕ) * p.parts.count (t j : ℕ) : ℚ)) /
      ((Finset.lcm (Finset.univ.image (fun j => (t j : ℕ))) id : ℕ) : ℚ)

/-- The partition `[2,1^(n-2)]` when `n ≥ 2`, with a total extension below that range. -/
def transpositionClass (n : ℕ) : Nat.Partition n :=
  if h : 2 ≤ n then
    partition126 n 1 0 (by simpa using h)
  else Nat.Partition.indiscrete n

/-- The formal reading of the O'Connor--Ramgoolam leading-class assertion. -/
def claim : Prop :=
  ∀ n ≥ 2, ∀ s ≥ 1,
    degree s (onesPartition n) = (n : ℚ) ^ s ∧
      degree s (transpositionClass n) =
        ((n : ℚ) ^ s + ((n - 2 : ℕ) : ℚ) ^ s) / 2 ∧
      degree s (transpositionClass n) < degree s (onesPartition n) ∧
      ∀ p : Nat.Partition n,
        p ≠ onesPartition n → p ≠ transpositionClass n →
          degree s p < degree s (transpositionClass n)

private theorem transposition_parts (n : ℕ) (hn : 2 ≤ n) :
    (transpositionClass n).parts = 2 ::ₘ Multiset.replicate (n - 2) 1 := by
  rw [transpositionClass, dite_eq_left hn]
  rw [partition126_parts]
  simp only [Nat.mul_one, Nat.mul_zero, Nat.sub_zero, Nat.add_zero,
    Multiset.replicate_zero, Multiset.replicate_one, Multiset.add_zero]
  change Multiset.replicate (n - 2) 1 + {2} = _
  rw [Multiset.add_comm, Multiset.singleton_add]

private theorem total_weight (s : ℕ) {n : ℕ} (p : Nat.Partition n) :
    (∑ t : Fin s → p.parts.toFinset,
      ∏ j, ((t j : ℕ) * p.parts.count (t j : ℕ) : ℚ)) = (n : ℚ) ^ s := by
  let f : p.parts.toFinset → ℚ :=
    fun a => ((a : ℕ) * p.parts.count (a : ℕ) : ℚ)
  have hsum : (∑ a : p.parts.toFinset, f a) = n := by
    change (∑ a : p.parts.toFinset,
      ((a : ℕ) * p.parts.count (a : ℕ) : ℚ)) = n
    have h := Finset.sum_multiset_count p.parts
    rw [p.parts_sum] at h
    have hqNat : n = ∑ m ∈ p.parts.toFinset, p.parts.count m * m := by
      simpa [nsmul_eq_mul] using h
    have hq : (∑ m ∈ p.parts.toFinset, (p.parts.count m : ℚ) * m) = n := by
      exact_mod_cast hqNat.symm
    rw [← Finset.sum_subtype p.parts.toFinset (by simp)
      (fun a => ((a : ℕ) * p.parts.count a : ℚ))]
    simpa [mul_comm] using hq
  change (∑ t : Fin s → p.parts.toFinset, ∏ j, f (t j)) = (n : ℚ) ^ s
  rw [← Fintype.sum_pow, hsum]

private theorem one_weight (s : ℕ) {n : ℕ} (p : Nat.Partition n) (hs : 1 ≤ s) :
    (∑ t ∈ (Finset.univ : Finset (Fin s → p.parts.toFinset)).filter
        (fun t => ∀ j, (t j : ℕ) = 1),
      ∏ j, ((t j : ℕ) * p.parts.count (t j : ℕ) : ℚ)) =
        (p.parts.count 1 : ℚ) ^ s := by
  let T := Fin s → p.parts.toFinset
  let one : T → Prop := fun t => ∀ j, (t j : ℕ) = 1
  let w : T → ℚ := fun t => ∏ j, ((t j : ℕ) * p.parts.count (t j : ℕ) : ℚ)
  change (∑ t ∈ (Finset.univ : Finset T).filter one, w t) = _
  by_cases h1 : 1 ∈ p.parts
  · let u : T := fun _ => ⟨1, Multiset.mem_toFinset.mpr h1⟩
    have hfilter : (Finset.univ : Finset T).filter one = {u} := by
      simpa only [T, one, u, Finset.mem_univ, ite_true, funext_iff, Subtype.ext_iff] using
        (Finset.filter_eq' (Finset.univ : Finset T) u)
    rw [hfilter]
    simp [w, u]
  · have hfilter : (Finset.univ : Finset T).filter one = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro t _ htone
      have hj0 : Fin s := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hs⟩
      exact h1 (htone hj0 ▸ Multiset.mem_toFinset.mp (t hj0).property)
    rw [hfilter]
    simp [Multiset.count_eq_zero.mpr h1, Nat.ne_of_gt hs]

private theorem degree_le_from_one_count (s : ℕ) {n : ℕ} (p : Nat.Partition n)
    (hs : 1 ≤ s) :
    degree s p ≤ ((n : ℚ) ^ s + (p.parts.count 1 : ℚ) ^ s) / 2 := by
  let T := Fin s → p.parts.toFinset
  let one : T → Prop := fun t => ∀ j, (t j : ℕ) = 1
  let w : T → ℚ := fun t => ∏ j, ((t j : ℕ) * p.parts.count (t j : ℕ) : ℚ)
  let l : T → ℕ := fun t =>
    Finset.lcm (Finset.univ.image (fun j => (t j : ℕ))) id
  have hne : (Finset.univ : Finset (Fin s)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hs)
  have hlpos (t : T) : 0 < l t := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact (p.parts_pos (Multiset.mem_toFinset.mp (t j).property)).ne'
  have hpoint (t : T) :
      w t / (l t : ℚ) ≤ if one t then w t else w t / 2 := by
    by_cases ht : one t
    · have hconst : (fun j => (t j : ℕ)) = (fun _ : Fin s => 1) := funext ht
      have hlone : l t = 1 := by
        dsimp [l]
        rw [hconst, Finset.image_const hne]
        simp
      simp [ht, hlone]
    · have hsome : ∃ j, (t j : ℕ) ≠ 1 := not_forall.mp ht
      obtain ⟨j, hj⟩ := hsome
      have hjge : 2 ≤ (t j : ℕ) := by
        have hjpos := p.parts_pos (Multiset.mem_toFinset.mp (t j).property)
        exact (Nat.two_le_iff _).mpr ⟨hjpos.ne', hj⟩
      have hjmem : (t j : ℕ) ∈ Finset.univ.image (fun j => (t j : ℕ)) := by
        exact Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      have hjdvd : (t j : ℕ) ∣ l t := Finset.dvd_lcm hjmem
      have hlge : 2 ≤ l t := hjge.trans (Nat.le_of_dvd (hlpos t) hjdvd)
      have hlgeQ : (2 : ℚ) ≤ (l t : ℚ) := by exact_mod_cast hlge
      have hw : 0 ≤ w t := by
        dsimp [w]
        apply Finset.prod_nonneg
        intro k _
        positivity
      simp only [ht, ite_false]
      exact div_le_div_of_nonneg_left hw (by norm_num) hlgeQ
  have hpoint_sum :
      degree s p ≤ ∑ t : T, if one t then w t else w t / 2 := by
    change (∑ t : T, w t / (l t : ℚ)) ≤ _
    exact Finset.sum_le_sum fun t _ => hpoint t
  have hone :
      (∑ t ∈ (Finset.univ : Finset T).filter one, w t) =
        (p.parts.count 1 : ℚ) ^ s := one_weight s p hs
  have htotal : (∑ t : T, w t) = (n : ℚ) ^ s := by
    simpa [T, w] using total_weight s p
  have hnot :
      (∑ t ∈ (Finset.univ : Finset T).filter one, w t) +
          ∑ t ∈ (Finset.univ : Finset T).filter (fun t => ¬one t), w t =
        ∑ t : T, w t := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hnot' :
      (∑ t ∈ (Finset.univ : Finset T).filter (fun t => ¬one t), w t) =
        (n : ℚ) ^ s - (p.parts.count 1 : ℚ) ^ s := by
    linarith [hnot, htotal, hone]
  calc
    degree s p ≤ ∑ t : T, if one t then w t else w t / 2 := hpoint_sum
    _ = (p.parts.count 1 : ℚ) ^ s +
          (∑ t ∈ (Finset.univ : Finset T).filter (fun t => ¬one t), w t) / 2 := by
      rw [Finset.sum_ite, hone]
      congr 1
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = ((n : ℚ) ^ s + (p.parts.count 1 : ℚ) ^ s) / 2 := by
      rw [hnot']
      linarith

private theorem identity_degree (s n : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) :
    degree s (onesPartition n) = (n : ℚ) ^ s := by
  have hparts : (onesPartition n).parts = Multiset.replicate n 1 := rfl
  have hn0 : n ≠ 0 := by omega
  have hset : (Multiset.replicate n 1).toFinset = {1} := by
    simp [Multiset.toFinset_replicate, hn0]
  rw [degree, hparts, hset]
  simp only [univ_unique, Pi.default_def, sum_singleton, default_singleton, Nat.cast_one,
    Multiset.count_replicate_self, one_mul, prod_const, card_univ, Fintype.card_fin]
  have hne : (Finset.univ : Finset (Fin s)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hs)
  rw [Finset.image_const hne]
  simp

private theorem transposition_degree (s n : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) :
    degree s (transpositionClass n) =
      ((n : ℚ) ^ s + ((n - 2 : ℕ) : ℚ) ^ s) / 2 := by
  have hparts : (transpositionClass n).parts = 2 ::ₘ Multiset.replicate (n - 2) 1 := by
    exact transposition_parts n hn
  let T := Fin s → (transpositionClass n).parts.toFinset
  let one : T → Prop := fun t => ∀ j, (t j : ℕ) = 1
  let w : T → ℚ := fun t =>
    ∏ j, ((t j : ℕ) * (transpositionClass n).parts.count (t j : ℕ) : ℚ)
  let l : T → ℕ := fun t =>
    Finset.lcm (Finset.univ.image (fun j => (t j : ℕ))) id
  have hne : (Finset.univ : Finset (Fin s)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hs)
  have hval (t : T) (j : Fin s) : (t j : ℕ) = 1 ∨ (t j : ℕ) = 2 := by
    have hm : (t j : ℕ) ∈ (transpositionClass n).parts :=
      Multiset.mem_toFinset.mp (t j).property
    have hm' : (t j : ℕ) ∈ 2 ::ₘ Multiset.replicate (n - 2) 1 := hparts ▸ hm
    rcases Multiset.mem_cons.mp hm' with h | h
    · exact Or.inr h
    · exact Or.inl (Multiset.mem_replicate.mp h).2
  have hpoint (t : T) :
      w t / (l t : ℚ) = if one t then w t else w t / 2 := by
    by_cases ht : one t
    · have hconst : (fun j => (t j : ℕ)) = (fun _ : Fin s => 1) := funext ht
      have hlone : l t = 1 := by
        dsimp [l]
        rw [hconst, Finset.image_const hne]
        simp
      simp [ht, hlone]
    · have hsome : ∃ j, (t j : ℕ) ≠ 1 := not_forall.mp ht
      obtain ⟨j, hj⟩ := hsome
      have hjtwo : (t j : ℕ) = 2 := (hval t j).resolve_left hj
      have hjmem : (t j : ℕ) ∈ Finset.univ.image (fun j => (t j : ℕ)) := by
        exact Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      have h2dvd : 2 ∣ l t := by
        rw [← hjtwo]
        exact Finset.dvd_lcm hjmem
      have hldiv : l t ∣ 2 := by
        dsimp [l]
        apply Finset.lcm_dvd
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨j', -, rfl⟩
        rcases hval t j' with h | h
        · rw [h]
          norm_num
        · rw [h]
          exact dvd_refl 2
      have hltwo : l t = 2 := Nat.dvd_antisymm hldiv h2dvd
      simp [ht, hltwo]
  have hsumEq :
      degree s (transpositionClass n) = ∑ t : T, if one t then w t else w t / 2 := by
    change (∑ t : T, w t / (l t : ℚ)) = _
    apply Finset.sum_congr rfl
    intro t _
    exact hpoint t
  have hone :
      (∑ t ∈ (Finset.univ : Finset T).filter one, w t) =
        ((n - 2 : ℕ) : ℚ) ^ s := by
    have hcount : (transpositionClass n).parts.count 1 = n - 2 := by
      simp [hparts]
    simpa only [hcount] using one_weight s (transpositionClass n) hs
  have htotal : (∑ t : T, w t) = (n : ℚ) ^ s := by
    simpa [T, w] using total_weight s (transpositionClass n)
  have hnot :
      (∑ t ∈ (Finset.univ : Finset T).filter one, w t) +
          ∑ t ∈ (Finset.univ : Finset T).filter (fun t => ¬one t), w t =
        ∑ t : T, w t := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hnot' :
      (∑ t ∈ (Finset.univ : Finset T).filter (fun t => ¬one t), w t) =
        (n : ℚ) ^ s - ((n - 2 : ℕ) : ℚ) ^ s := by
    linarith [hnot, htotal, hone]
  calc
    degree s (transpositionClass n) = ∑ t : T, if one t then w t else w t / 2 := hsumEq
    _ = ((n - 2 : ℕ) : ℚ) ^ s +
          (∑ t ∈ (Finset.univ : Finset T).filter (fun t => ¬one t), w t) / 2 := by
      rw [Finset.sum_ite, hone]
      congr 1
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = ((n : ℚ) ^ s + ((n - 2 : ℕ) : ℚ) ^ s) / 2 := by
      rw [hnot']
      linarith

private theorem transposition_lt_identity (s n : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) :
    degree s (transpositionClass n) < degree s (onesPartition n) := by
  rw [transposition_degree s n hn hs, identity_degree s n hn hs]
  have hbase : n - 2 < n :=
    Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 2) hn) (by decide)
  have hpow : (n - 2) ^ s < n ^ s := Nat.pow_lt_pow_left hbase (by omega)
  have hpowQ : ((n - 2 : ℕ) : ℚ) ^ s < (n : ℚ) ^ s := by
    exact_mod_cast hpow
  linarith

private theorem one_count_le_two_sub {n : ℕ} (p : Nat.Partition n)
    (hp : p ≠ onesPartition n) :
    p.parts.count 1 ≤ n - 2 := by
  let nonunits := p.parts.filter (fun a => a ≠ 1)
  let units := p.parts.filter (fun a => ¬a ≠ 1)
  have hsplit : nonunits + units = p.parts := by
    exact Multiset.filter_add_not (fun a : ℕ => a ≠ 1) p.parts
  have hcount : units.card = p.parts.count 1 := by
    simpa only [units, not_not, eq_comm] using
      (Multiset.count_eq_card_filter_eq p.parts 1).symm
  have hunit : units = Multiset.replicate units.card 1 := by
    rw [hcount]
    simpa only [units, not_not] using Multiset.filter_eq' p.parts 1
  have hnon : nonunits ≠ 0 := by
    intro hzero
    apply hp
    apply Nat.Partition.ext
    have hparts : p.parts = units := by rw [← hsplit, hzero, zero_add]
    rw [hparts, hunit]
    have hcard : units.card = n := by
      have hsump := p.parts_sum
      rw [hparts, hunit, Multiset.sum_replicate] at hsump
      simpa using hsump
    rw [hcard]
    have hidentity : (onesPartition n).parts = Multiset.replicate n 1 := rfl
    exact hidentity.symm
  have hnon_sum : 2 ≤ nonunits.sum := by
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hnon
    have hapos := p.parts_pos (Multiset.mem_of_mem_filter ha)
    have hane := (Multiset.mem_filter.mp ha).2
    exact ((Nat.two_le_iff a).mpr ⟨hapos.ne', hane⟩).trans (Multiset.le_sum_of_mem ha)
  have hsum : nonunits.sum + units.sum = n := by
    calc
      nonunits.sum + units.sum = (nonunits + units).sum :=
        (Multiset.sum_add _ _).symm
      _ = p.parts.sum := by rw [hsplit]
      _ = n := p.parts_sum
  rw [hunit] at hsum
  simp only [Multiset.sum_replicate, nsmul_eq_mul, mul_one] at hsum
  have hsum' : nonunits.sum + p.parts.count 1 = n := by
    simpa [hcount] using hsum
  apply Nat.le_sub_of_add_le
  omega

private theorem one_count_eq_two_sub_iff {n : ℕ} (p : Nat.Partition n) (hn : 2 ≤ n) :
    p.parts.count 1 = n - 2 ↔ p = transpositionClass n := by
  let nonunits := p.parts.filter (fun a => a ≠ 1)
  let units := p.parts.filter (fun a => ¬a ≠ 1)
  have hsplit : nonunits + units = p.parts := by
    exact Multiset.filter_add_not (fun a : ℕ => a ≠ 1) p.parts
  have hcount : units.card = p.parts.count 1 := by
    simpa only [units, not_not, eq_comm] using
      (Multiset.count_eq_card_filter_eq p.parts 1).symm
  have hunit : units = Multiset.replicate units.card 1 := by
    rw [hcount]
    simpa only [units, not_not] using Multiset.filter_eq' p.parts 1
  constructor
  · intro hcountp
    have hsum : nonunits.sum + units.sum = n := by
      calc
        nonunits.sum + units.sum = (nonunits + units).sum :=
          (Multiset.sum_add _ _).symm
        _ = p.parts.sum := by rw [hsplit]
        _ = n := p.parts_sum
    rw [hunit] at hsum
    simp only [Multiset.sum_replicate, nsmul_eq_mul, mul_one] at hsum
    have hsum' : nonunits.sum + p.parts.count 1 = n := by
      simpa [hcount] using hsum
    have hnon_sum : nonunits.sum = 2 := by omega
    have hnonmem : ∀ a ∈ nonunits, 2 ≤ a := by
      intro a ha
      have hapos := p.parts_pos (Multiset.mem_of_mem_filter ha)
      have hane := (Multiset.mem_filter.mp ha).2
      exact (Nat.two_le_iff a).mpr ⟨hapos.ne', hane⟩
    have hcard_le : 2 * nonunits.card ≤ nonunits.sum := by
      have hh := Multiset.card_nsmul_le_sum (s := nonunits) (a := 2) hnonmem
      simpa [nsmul_eq_mul, Nat.mul_comm] using hh
    have hcard : nonunits.card = 1 := by
      have hpos : 0 < nonunits.card := Multiset.card_pos.mpr (by
        intro hzero
        have : nonunits.sum = 0 := by simp [hzero]
        omega)
      omega
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
    have hasum : a = 2 := by
      have hsum_a := congrArg Multiset.sum ha
      simpa [hnon_sum] using hsum_a.symm
    have hparts : p.parts = 2 ::ₘ Multiset.replicate (n - 2) 1 := by
      calc
        p.parts = nonunits + units := hsplit.symm
        _ = {a} + units := by rw [ha]
        _ = {a} + Multiset.replicate units.card 1 := by
          exact congrArg (fun m => {a} + m) hunit
        _ = 2 ::ₘ Multiset.replicate (n - 2) 1 := by
          rw [hasum, hcount, hcountp]
          simp
    apply Nat.Partition.ext
    have htrans : (transpositionClass n).parts = 2 ::ₘ Multiset.replicate (n - 2) 1 := by
      exact transposition_parts n hn
    exact hparts.trans htrans.symm
  · intro hptrans
    rw [hptrans, transposition_parts n hn]
    simp

private theorem other_degree_lt (s n : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (p : Nat.Partition n) (hp₁ : p ≠ onesPartition n)
    (hp₂ : p ≠ transpositionClass n) :
    degree s p < degree s (transpositionClass n) := by
  have hbound := degree_le_from_one_count s p hs
  have hcountle := one_count_le_two_sub p hp₁
  have hcountlt : p.parts.count 1 < n - 2 := by
    apply Nat.lt_of_le_of_ne hcountle
    intro heq
    exact hp₂ ((one_count_eq_two_sub_iff p hn).mp heq)
  have hpow : p.parts.count 1 ^ s < (n - 2) ^ s :=
    Nat.pow_lt_pow_left hcountlt (by omega)
  have hpowQ : (p.parts.count 1 : ℚ) ^ s < ((n - 2 : ℕ) : ℚ) ^ s := by
    exact_mod_cast hpow
  rw [transposition_degree s n hn hs]
  linarith

theorem result : claim := by
  intro n hn s hs
  have hid := identity_degree s n hn hs
  have htr := transposition_degree s n hn hs
  have hlt := transposition_lt_identity s n hn hs
  refine ⟨hid, htr, hlt, ?_⟩
  intro p hp₁ hp₂
  exact other_degree_lt s n hn hs p hp₁ hp₂

end
end D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses
