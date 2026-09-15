/- GID: D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit
   generality: I
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The total distinct-cycle-size weight is asymptotic to n times n factorial. -/

import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-
The local partition-counting proof below adapts the exact predecessor:
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/notes/tauceti2026classsizes.md.
Modified in trureturing: specialize to Fin n, localize the adapted facts inside
result, and use them in the weighted distinct-cycle-size asymptotic proof.
Authors: The Tau Ceti contributors.
TauCetiProject/TauCeti, revision d7ac608e0c97f71e9e0dc210d26a470d974368d7,
RepresentationTheory/Symmetric/{Partitions,ClassSize}.lean.
The classical class-size formula is due to Cauchy (Flajolet--Sedgewick,
Analytic Combinatorics, 2009, p.188). The inclusion-exclusion formulas in
OEIS A293211 and A122974 are credited to Dennis P. Walsh; no such formula
is an assumption here.
-/

open scoped BigOperators
open Finset Filter

namespace D5.S0.Asymptotics.WeightedProbability.DistinctCycleSizeLimit

noncomputable def DistinctCycleSizes {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  σ.partition.parts.toFinset

noncomputable def CycleSizeSum (n : ℕ) : ℕ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ k ∈ DistinctCycleSizes σ, k

theorem result :
  Filter.Tendsto
    (fun n : ℕ => (CycleSizeSum n : ℝ) /
      ((n : ℝ) * (Nat.factorial n : ℝ)))
    Filter.atTop (nhds (1 : ℝ)) := by
  classical
  let z : Multiset ℕ → ℕ := fun m =>
    ∏ i ∈ m.toFinset, i ^ m.count i * (m.count i).factorial
  have hz_prod : ∀ (m : Multiset ℕ) (s : Finset ℕ), m.toFinset ⊆ s →
      z m = ∏ i ∈ s, i ^ m.count i * (m.count i).factorial := by
    intro m s hs
    refine Finset.prod_subset hs ?_
    intro i _ hi
    rw [Multiset.count_eq_zero_of_notMem (by simpa using hi)]
    simp
  have hz_pos : ∀ {n : ℕ} (p : n.Partition), 0 < z p.parts := by
    intro n p
    apply Finset.prod_pos
    intro i hi
    have hi' := p.parts_pos (Multiset.mem_toFinset.mp hi)
    positivity
  have hz_perm : ∀ n (σ : Equiv.Perm (Fin n)),
      z σ.partition.parts =
        (n - σ.cycleType.sum).factorial * σ.cycleType.prod *
          ∏ i ∈ σ.cycleType.toFinset, (σ.cycleType.count i).factorial := by
    intro n σ
    let m := σ.cycleType
    let k := n - σ.support.card
    have hparts : σ.partition.parts = m + Multiset.replicate k 1 := by
      simp only [Equiv.Perm.parts_partition, Fintype.card_fin, m, k]
    have h1 : (1 : ℕ) ∉ m := fun h => by
      simpa using Equiv.Perm.two_le_of_mem_cycleType h
    have hsub : σ.partition.parts.toFinset ⊆ insert 1 m.toFinset := by
      intro i hi
      rw [Multiset.mem_toFinset, hparts, Multiset.mem_add] at hi
      rcases hi with h | h
      · exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr h)
      · exact Finset.mem_insert.mpr (Or.inl (Multiset.eq_of_mem_replicate h))
    have hcount : ∀ i ∈ m.toFinset, σ.partition.parts.count i = m.count i := by
      intro i hi
      have hne : (1 : ℕ) ≠ i := fun h => h1 (h ▸ Multiset.mem_toFinset.mp hi)
      rw [hparts, Multiset.count_add, Multiset.count_replicate, if_neg hne, add_zero]
    have hcount_one : σ.partition.parts.count 1 = k := by
      rw [hparts, Multiset.count_add, Multiset.count_eq_zero_of_notMem h1,
        Multiset.count_replicate_self, zero_add]
    rw [hz_prod _ _ hsub, Finset.prod_insert (by simpa using h1), hcount_one,
      Finset.prod_congr rfl (fun i hi => by rw [hcount i hi]), Finset.prod_mul_distrib,
      ← Finset.prod_multiset_count, one_pow, one_mul]
    dsimp [m, k]
    rw [Equiv.Perm.sum_cycleType]
    ring
  have hexists : ∀ n (p : n.Partition),
      ∃ σ : Equiv.Perm (Fin n), σ.partition.parts = p.parts := by
    intro n p
    let largeParts := p.parts.filter fun a => 2 ≤ a
    let unitParts := p.parts.filter fun a => ¬2 ≤ a
    have hsplit : largeParts + unitParts = p.parts :=
      Multiset.filter_add_not (p := fun a : ℕ => 2 ≤ a) p.parts
    have hunit : unitParts = Multiset.replicate unitParts.card 1 := by
      apply Multiset.eq_replicate_card.mpr
      intro a ha
      have ha' := Multiset.mem_filter.mp ha
      have hpos := p.parts_pos ha'.1
      omega
    have hunitSum : unitParts.sum = unitParts.card := by
      rw [hunit, Multiset.sum_replicate]
      simp
    have hsum : largeParts.sum + unitParts.card = n := by
      rw [← p.parts_sum, ← hsplit, Multiset.sum_add, hunitSum]
    obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin n)).mpr
      ⟨by simpa using (show largeParts.sum ≤ n by omega),
        fun a ha => (Multiset.mem_filter.mp ha).2⟩
    refine ⟨σ, ?_⟩
    have hsupport : σ.support.card = largeParts.sum := by
      rw [← Equiv.Perm.sum_cycleType, hσ]
    have hremaining : n - largeParts.sum = unitParts.card := by omega
    rw [Equiv.Perm.parts_partition, Fintype.card_fin, hσ, hsupport,
      hremaining, ← hunit, hsplit]
  have hclass : ∀ n (p : n.Partition),
      Nat.card {σ : Equiv.Perm (Fin n) // σ.partition.parts = p.parts} * z p.parts =
        n.factorial := by
    intro n p
    obtain ⟨g, hg⟩ := hexists n p
    have hcongr : Nat.card {σ : Equiv.Perm (Fin n) // σ.partition.parts = p.parts} =
        Nat.card {σ : Equiv.Perm (Fin n) | IsConj g σ} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight fun σ => by
        rw [Set.mem_ofPred_eq, Equiv.Perm.partition_eq_of_isConj,
          Nat.Partition.ext_iff, hg, eq_comm]
    rw [hcongr, ← hg, hz_perm]
    simpa using Equiv.Perm.card_isConj_mul_eq g
  let part : (n : ℕ) → Equiv.Perm (Fin n) → n.Partition := fun n σ =>
    ⟨σ.partition.parts, σ.partition.parts_pos, by simpa using σ.partition.parts_sum⟩
  have htransfer : ∀ n (f : n.Partition → ℝ),
      (∑ σ : Equiv.Perm (Fin n), f (part n σ)) =
        (n.factorial : ℝ) * ∑ p : n.Partition, f p / z p.parts := by
    intro n f
    have hc : ∀ p : n.Partition,
        (Fintype.card {σ : Equiv.Perm (Fin n) // part n σ = p} : ℝ) =
          (n.factorial : ℝ) / z p.parts := by
      intro p
      apply (eq_div_iff (by exact_mod_cast (hz_pos p).ne')).mpr
      have hh := hclass n p
      have he : {σ : Equiv.Perm (Fin n) // part n σ = p} =
          {σ : Equiv.Perm (Fin n) // σ.partition.parts = p.parts} := by
        congr 1 with σ
        exact Nat.Partition.ext_iff
      rw [← Nat.card_eq_fintype_card, he]
      exact_mod_cast hh
    calc
      (∑ σ : Equiv.Perm (Fin n), f (part n σ)) =
          ∑ p : n.Partition,
            (Fintype.card {σ : Equiv.Perm (Fin n) // part n σ = p} : ℝ) * f p := by
        simpa using (Fintype.sum_fiberwise' (part n) f).symm
      _ = (n.factorial : ℝ) * ∑ p : n.Partition, f p / z p.parts := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [hc]
        ring
  have hnorm : ∀ n : ℕ, (∑ p : n.Partition, (1 : ℝ) / z p.parts) = 1 := by
    intro n
    have h := htransfer n (fun _ => 1)
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    exact (mul_left_cancel₀ hn (by simpa using h.symm))
  have hz_cons : ∀ (m : Multiset ℕ) k,
      z (k ::ₘ m) = k * (m.count k + 1) * z m := by
    intro m k
    let s := insert k m.toFinset
    have hs : m.toFinset ⊆ s := Finset.subset_insert _ _
    have hs' : (k ::ₘ m).toFinset ⊆ s := by simp [s]
    rw [hz_prod _ s hs', hz_prod _ s hs]
    have hf : ∀ i ∈ s,
        i ^ (k ::ₘ m).count i * ((k ::ₘ m).count i).factorial =
          (if i = k then k * (m.count k + 1) else 1) *
            (i ^ m.count i * (m.count i).factorial) := by
      intro i hi
      by_cases h : i = k
      · subst i
        simp only [Multiset.count_cons_self, if_true, pow_succ, Nat.factorial_succ]
        ring
      · rw [Multiset.count_cons_of_ne h, if_neg h, one_mul]
    rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib]
    simp [s]
  have htwo : ∀ (m : Multiset ℕ) k, 2 ≤ m.count k →
      k ::ₘ k ::ₘ (m.erase k).erase k = m := by
    intro m k hk
    have h1 : k ∈ m := Multiset.count_pos.mp (by omega)
    have h2 : k ∈ m.erase k := Multiset.count_pos.mp (by
      rw [Multiset.count_erase_self]
      omega)
    rw [Multiset.cons_erase h2, Multiset.cons_erase h1]
  have hmoment : ∀ (n k : ℕ), 0 < k →
      (∑ p : n.Partition,
        ((p.parts.count k * (p.parts.count k - 1) : ℕ) : ℝ) / z p.parts) ≤
        1 / (k : ℝ)^2 := by
    intro n k hk
    let P := {p : n.Partition // 2 ≤ p.parts.count k}
    let strip : P → (n - 2*k).Partition := fun p => by
      have hfirst : k ∈ p.val.parts := Multiset.count_pos.mp (by have := p.property; omega)
      have hsum := congrArg Multiset.sum (htwo p.val.parts k p.property)
      simp only [Multiset.sum_cons, p.val.parts_sum] at hsum
      let q := Nat.Partition.partitionWithPartEquiv hk
        (p.val.le_of_mem_parts hfirst) ⟨p.val, hfirst⟩
      have hsecond : k ∈ q.parts := by
        change k ∈ p.val.parts.erase k
        apply Multiset.count_pos.mp
        rw [Multiset.count_erase_self]
        have := p.property
        omega
      let r := Nat.Partition.partitionWithPartEquiv hk
        (show k ≤ n - k by omega) ⟨q, hsecond⟩
      exact ⟨r.parts, r.parts_pos, by
        simpa only [Nat.sub_sub, two_mul] using r.parts_sum⟩
    have hs : ∀ p : P, k ::ₘ k ::ₘ (strip p).parts = p.val.parts := by
      intro p
      exact htwo p.val.parts k p.property
    have hinj : Function.Injective strip := by
      intro p q h
      apply Subtype.ext
      apply Nat.Partition.ext
      rw [← hs p, ← hs q, h]
    have hweight : ∀ p : P,
        ((p.val.parts.count k * (p.val.parts.count k - 1) : ℕ) : ℝ) / z p.val.parts =
          (1 / (k : ℝ)^2) * (1 / z (strip p).parts) := by
      intro p
      have hpz : z p.val.parts = k * k * ((strip p).parts.count k + 2) *
          ((strip p).parts.count k + 1) * z (strip p).parts := by
        rw [← hs p, hz_cons, hz_cons, Multiset.count_cons_self]
        ring
      have hpc : p.val.parts.count k = (strip p).parts.count k + 2 := by
        rw [← hs p, Multiset.count_cons_self, Multiset.count_cons_self]
      have hm : (strip p).parts.count k + 2 - 1 = (strip p).parts.count k + 1 := by omega
      have hkR : (k : ℝ) ≠ 0 := by positivity
      have hzR : (z (strip p).parts : ℝ) ≠ 0 := by exact_mod_cast (hz_pos (strip p)).ne'
      have hd1 : ((strip p).parts.count k : ℝ) + 1 ≠ 0 := by positivity
      have hd2 : ((strip p).parts.count k : ℝ) + 2 ≠ 0 := by positivity
      rw [hpz, hpc, hm]
      push_cast
      field_simp
    have hrestrict :
        (∑ p : n.Partition,
          ((p.parts.count k * (p.parts.count k - 1) : ℕ) : ℝ) / z p.parts) =
        ∑ p : P,
          ((p.val.parts.count k * (p.val.parts.count k - 1) : ℕ) : ℝ) / z p.val.parts := by
      symm
      apply Fintype.sum_of_injective (fun p : P => p.val) Subtype.val_injective
      · intro p hp
        have hc : p.parts.count k ≤ 1 := by
          by_contra h
          exact hp ⟨⟨p, by omega⟩, rfl⟩
        have hm : p.parts.count k - 1 = 0 := by omega
        simp [hm]
      · intro p
        rfl
    have hsum : (∑ p : P, (1 : ℝ) / z (strip p).parts) ≤ 1 := by
      calc
        (∑ p : P, (1 : ℝ) / z (strip p).parts) =
            ∑ q ∈ Finset.univ.image strip, (1 : ℝ) / z q.parts := by
          rw [Finset.sum_image]
          exact fun a _ b _ h => hinj h
        _ ≤ ∑ q : (n - 2*k).Partition, (1 : ℝ) / z q.parts := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro q _ _
          positivity
        _ = 1 := hnorm _
    rw [hrestrict, Finset.sum_congr rfl (fun p _ => hweight p), ← Finset.mul_sum]
    simpa using mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1 / (k : ℝ)^2)
  let D : (n : ℕ) → n.Partition → ℝ := fun _ p => ∑ k ∈ p.parts.toFinset, (k : ℝ)
  let M : ℕ → ℝ := fun n => ∑ p : n.Partition, D n p / z p.parts
  have hsource : ∀ n, (CycleSizeSum n : ℝ) = (n.factorial : ℝ) * M n := by
    intro n
    simpa [CycleSizeSum, DistinctCycleSizes, part, D, M] using htransfer n (D n)
  have hdeficit : ∀ (n : ℕ) (p : n.Partition),
      0 ≤ (n : ℝ) - D n p ∧
      (n : ℝ) - D n p ≤
        ∑ k ∈ Finset.Icc 1 n,
          (k : ℝ) * ((p.parts.count k * (p.parts.count k - 1) : ℕ) : ℝ) := by
    intro n p
    have hmass : (n : ℝ) = ∑ k ∈ p.parts.toFinset, (p.parts.count k : ℝ) * k := by
      have h := Finset.sum_multiset_count p.parts
      rw [p.parts_sum] at h
      exact_mod_cast h
    have hsub : p.parts.toFinset ⊆ Finset.Icc 1 n := by
      intro k hk
      have hm := Multiset.mem_toFinset.mp hk
      exact Finset.mem_Icc.mpr ⟨p.parts_pos hm, p.le_of_mem_parts hm⟩
    have hterm : ∀ k ∈ p.parts.toFinset,
        0 ≤ (p.parts.count k : ℝ) * k - k ∧
        (p.parts.count k : ℝ) * k - k ≤
          (k : ℝ) * ((p.parts.count k * (p.parts.count k - 1) : ℕ) : ℝ) := by
      intro k hk
      have hc : 1 ≤ p.parts.count k :=
        Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hk)
      have hcR : (1 : ℝ) ≤ p.parts.count k := by exact_mod_cast hc
      have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      rw [Nat.cast_mul, Nat.cast_sub hc, Nat.cast_one]
      have hsq : 0 ≤ ((p.parts.count k : ℝ) - 1)^2 := sq_nonneg _
      constructor
      · nlinarith
      · have hh := mul_nonneg h0 hsq
        nlinarith
    have he : (n : ℝ) - D n p =
        ∑ k ∈ p.parts.toFinset, ((p.parts.count k : ℝ) * k - k) := by
      rw [hmass, Finset.sum_sub_distrib]
    rw [he]
    constructor
    · exact Finset.sum_nonneg fun k hk => (hterm k hk).1
    · calc
        _ ≤ ∑ k ∈ p.parts.toFinset,
            (k : ℝ) * ((p.parts.count k * (p.parts.count k - 1) : ℕ) : ℝ) :=
          Finset.sum_le_sum fun k hk => (hterm k hk).2
        _ ≤ ∑ k ∈ Finset.Icc 1 n,
            (k : ℝ) * ((p.parts.count k * (p.parts.count k - 1) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro k _ _
          positivity
  have hbound : ∀ n : ℕ, 0 ≤ (n : ℝ) - M n ∧
      (n : ℝ) - M n ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
    intro n
    have he : (n : ℝ) - M n =
        ∑ p : n.Partition, ((n : ℝ) - D n p) / z p.parts := by
      simp only [sub_div, Finset.sum_sub_distrib, M]
      congr 1
      calc
        (n : ℝ) = n * ∑ p : n.Partition, (1 : ℝ) / z p.parts := by rw [hnorm, mul_one]
        _ = ∑ p : n.Partition, (n : ℝ) / z p.parts := by
          rw [Finset.mul_sum]
          congr 1
          ext p
          ring
    rw [he]
    constructor
    · apply Finset.sum_nonneg
      intro p _
      exact div_nonneg (hdeficit n p).1 (by positivity)
    · calc
        _ ≤ ∑ p : n.Partition, (∑ k ∈ Finset.Icc 1 n,
            (k : ℝ) * ((p.parts.count k * (p.parts.count k - 1) : ℕ) : ℝ)) / z p.parts := by
          apply Finset.sum_le_sum
          intro p _
          exact div_le_div_of_nonneg_right (hdeficit n p).2 (by positivity)
        _ = ∑ k ∈ Finset.Icc 1 n, (k : ℝ) *
            ∑ p : n.Partition, ((p.parts.count k * (p.parts.count k - 1) : ℕ) : ℝ) / z p.parts := by
          simp_rw [Finset.sum_div, mul_div_assoc]
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
        _ ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * (1 / (k : ℝ)^2) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (hmoment n k (Finset.mem_Icc.mp hk).1) (by positivity)
        _ = ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
          apply Finset.sum_congr rfl
          intro k hk
          have h : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hk).1)
          field_simp
  have haverage : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k)
      atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).cesaro
    convert h using 1
    ext n
    congr 1
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  have herr : Tendsto (fun n : ℕ => ((n : ℝ) - M n) / n) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact div_nonneg (hbound n).1 (Nat.cast_nonneg _)
    · intro n
      simpa [div_eq_mul_inv, mul_comm] using
        div_le_div_of_nonneg_right (hbound n).2 (Nat.cast_nonneg n)
    · simpa only [one_div] using haverage
  have ht : Tendsto (fun n : ℕ => 1 - ((n : ℝ) - M n) / n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub herr
  apply ht.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hfR : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [hsource]
  field_simp
  ring

end D5.S0.Asymptotics.WeightedProbability.DistinctCycleSizeLimit
