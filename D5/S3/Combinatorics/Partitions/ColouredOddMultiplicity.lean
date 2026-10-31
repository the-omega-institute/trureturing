/- GID: D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/ColouredOddMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Sym.Card, mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.GenFun]
   utility: none
   digest: Coloured odd occupations have the independent multichoose partition count. -/

import D5.S3.Combinatorics.Partitions.ColouredOddOccupation
import Mathlib.Data.Sym.Card
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-! # Odd partitions with independently allocated colours

For each occurring odd part, a weak composition allocates its multiplicity
among the colours. Reconstructing occupations from these allocations proves
the weighted partition count, including empty colour and grade sets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity
open D5.S3.Combinatorics.Partitions.ColouredOddOccupation

abbrev Allocation (r m : ℕ) := {u : Fin r → ℕ // ∑ i, u i = m}

instance allocationFintype (r m : ℕ) : Fintype (Allocation r m) :=
  Fintype.ofEquiv (Sym (Fin r) m) (Sym.equivNatSumOfFintype (Fin r) m)

abbrev PartAllocation (r k m : ℕ) := Allocation r m × PLift (Odd k)

abbrev Colouring (r : ℕ) {N : ℕ} (p : Nat.Partition N) :=
  (k : ↥p.parts.toFinset) → PartAllocation r k.1 (p.parts.count k.1)

abbrev PartitionData (r N : ℕ) := Σ p : Nat.Partition N, Colouring r p

private theorem weight_sum (r : ℕ) (d : (Fin r × ℕ) →₀ ℕ) :
    (d.toMultiset.map (fun x => 2 * x.2 + 1)).sum = colouredEnergy (Fin r) d := by
  rw [Finsupp.toMultiset_apply, Finsupp.multiset_map_sum, Finsupp.multiset_sum_sum]
  simp only [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton,
    Multiset.sum_singleton]
  rfl

def occupationPartition (r N : ℕ) (d : ColouredOddFiber (Fin r) N) :
    Nat.Partition N where
  parts := d.1.toMultiset.map (fun x => 2 * x.2 + 1)
  parts_pos := by
    intro k hk
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hk
    omega
  parts_sum := (weight_sum r d.1).trans d.2

private theorem count_odd (r : ℕ) (d : (Fin r × ℕ) →₀ ℕ) (n : ℕ) :
    (d.toMultiset.map (fun x => 2 * x.2 + 1)).count (2 * n + 1) =
      ∑ i : Fin r, d (i,n) := by
  classical
  induction d using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | single_add x a d hx ha ih =>
    rcases x with ⟨i,m⟩
    simp only [Finsupp.toMultiset_add, Multiset.map_add, Multiset.count_add,
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.map_singleton,
      Multiset.count_nsmul, Multiset.count_singleton, ih, Finsupp.add_apply,
      Finset.sum_add_distrib]
    congr 1
    by_cases h : m = n
    · subst m
      simp [Finsupp.single_apply]
    · have hw : 2 * n + 1 ≠ 2 * m + 1 := by omega
      simp [Finsupp.single_apply, h, Ne.symm h, hw]

private theorem part_odd (r N : ℕ) (d : ColouredOddFiber (Fin r) N)
    (k : ℕ) (hk : k ∈ (occupationPartition r N d).parts) : Odd k := by
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hk
  exact ⟨x.2, by omega⟩

private theorem odd_recover (k : ℕ) (h : Odd k) : 2 * (k / 2) + 1 = k := by
  obtain ⟨n, hn⟩ := h
  omega

def occupationColouring (r N : ℕ) (d : ColouredOddFiber (Fin r) N) :
    Colouring r (occupationPartition r N d) := by
  intro k
  have hk := part_odd r N d k (Multiset.mem_toFinset.mp k.2)
  refine ⟨⟨fun i => d.1 (i, k.1 / 2), ?_⟩, ⟨hk⟩⟩
  change (∑ i, d.1 (i, k.1 / 2)) =
    (d.1.toMultiset.map (fun x => 2 * x.2 + 1)).count k.1
  rw [← count_odd, odd_recover k.1 hk]

def encode (r N : ℕ) (d : ColouredOddFiber (Fin r) N) : PartitionData r N :=
  ⟨occupationPartition r N d, occupationColouring r N d⟩

def decodeOccupation (r : ℕ) {N : ℕ} (p : Nat.Partition N) (c : Colouring r p) :
    (Fin r × ℕ) →₀ ℕ :=
  ∑ k : ↥p.parts.toFinset, ∑ i : Fin r,
    Finsupp.single (i, k.1 / 2) ((c k).1.1 i)

private theorem decode_at (r : ℕ) {N : ℕ} (p : Nat.Partition N)
    (c : Colouring r p) (k : ↥p.parts.toFinset) (i : Fin r) :
    decodeOccupation r p c (i, k.1 / 2) = (c k).1.1 i := by
  classical
  unfold decodeOccupation
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single k]
  · simp [Finsupp.single_apply]
  · intro j hj hne
    have hn : j.1 / 2 ≠ k.1 / 2 := by
      intro he
      have hjodd := odd_recover j.1 (c j).2.down
      have hkodd := odd_recover k.1 (c k).2.down
      exact hne (Subtype.ext (by omega))
    simp [Finsupp.single_apply, hn]
  · simp

private theorem decode_outside (r : ℕ) {N : ℕ} (p : Nat.Partition N)
    (c : Colouring r p) (i : Fin r) (n : ℕ) (hn : 2 * n + 1 ∉ p.parts) :
    decodeOccupation r p c (i,n) = 0 := by
  classical
  unfold decodeOccupation
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hne : k.1 / 2 ≠ n := by
    intro he
    have hodd := odd_recover k.1 (c k).2.down
    have heq : 2*n+1 = k.1 := by omega
    exact hn (by rw [heq]; exact Multiset.mem_toFinset.mp k.2)
  simp [Finsupp.single_apply, hne]

private theorem decode_weight (r : ℕ) {N : ℕ} (p : Nat.Partition N)
    (c : Colouring r p) : colouredEnergy (Fin r) (decodeOccupation r p c) = N := by
  classical
  change Finsupp.weight (fun x : Fin r × ℕ => oddWeight x.2) (decodeOccupation r p c) = N
  unfold decodeOccupation
  simp only [map_sum, Finsupp.weight_single, nsmul_eq_mul]
  have hsum : (∑ k : ↥p.parts.toFinset,
      ∑ i : Fin r, (c k).1.1 i * oddWeight (k.1 / 2)) =
      ∑ k : ↥p.parts.toFinset, p.parts.count k.1 * k.1 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_mul, (c k).1.2]
    rw [oddWeight, odd_recover k.1 (c k).2.down]
  change (∑ k : ↥p.parts.toFinset,
    ∑ i : Fin r, (c k).1.1 i * oddWeight (k.1 / 2)) = N
  rw [hsum]
  calc
    _ = ∑ k ∈ p.parts.toFinset, p.parts.count k * k :=
      Finset.sum_coe_sort p.parts.toFinset (fun k => p.parts.count k * k)
    _ = N := by
      simpa only [nsmul_eq_mul, Nat.cast_id, p.parts_sum] using
        (Finset.sum_multiset_count p.parts).symm


def decode (r N : ℕ) (s : PartitionData r N) : ColouredOddFiber (Fin r) N :=
  ⟨decodeOccupation r s.1 s.2, decode_weight r s.1 s.2⟩

private theorem decode_encode (r N : ℕ) (d : ColouredOddFiber (Fin r) N) :
    decode r N (encode r N d) = d := by
  classical
  apply Subtype.ext
  ext x
  rcases x with ⟨i,n⟩
  by_cases hk : 2 * n + 1 ∈ (occupationPartition r N d).parts
  · let k : ↥(occupationPartition r N d).parts.toFinset :=
      ⟨2*n+1, Multiset.mem_toFinset.mpr hk⟩
    have h := decode_at r (occupationPartition r N d) (occupationColouring r N d) k i
    have hn : (2 * n + 1) / 2 = n := by omega
    simpa only [decode, encode, occupationColouring, k, hn] using h
  · have hout := decode_outside r (occupationPartition r N d)
      (occupationColouring r N d) i n hk
    have hsum : (∑ j : Fin r, d.1 (j,n)) = 0 := by
      rw [← count_odd]
      exact Multiset.count_eq_zero.mpr hk
    have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) =>
      Nat.zero_le (d.1 (j,n))) (Finset.mem_univ i)
    have hi : d.1 (i,n) = 0 := by omega
    exact hout.trans hi.symm

private theorem partition_decode (r N : ℕ) (p : Nat.Partition N) (c : Colouring r p) :
    occupationPartition r N (decode r N ⟨p,c⟩) = p := by
  classical
  apply Nat.Partition.ext
  apply Multiset.ext.mpr
  intro k
  by_cases hk : k ∈ p.parts
  · let l : ↥p.parts.toFinset := ⟨k, Multiset.mem_toFinset.mpr hk⟩
    have hodd : Odd k := (c l).2.down
    have hr := odd_recover k hodd
    change ((decodeOccupation r p c).toMultiset.map (fun x => 2*x.2+1)).count k = _
    calc
      _ = ((decodeOccupation r p c).toMultiset.map (fun x => 2*x.2+1)).count
          (2*(k/2)+1) := by rw [hr]
      _ = ∑ i : Fin r, decodeOccupation r p c (i,k/2) := count_odd _ _ _
      _ = ∑ i : Fin r, (c l).1.1 i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact decode_at r p c l i
      _ = _ := (c l).1.2
  · rw [Multiset.count_eq_zero.mpr hk]
    by_cases ho : Odd k
    · have hr := odd_recover k ho
      change ((decodeOccupation r p c).toMultiset.map (fun x => 2*x.2+1)).count k = 0
      rw [← hr, count_odd]
      apply Finset.sum_eq_zero
      intro i hi
      exact decode_outside r p c i (k/2) (by rwa [hr])
    · exact Multiset.count_eq_zero.mpr
        (fun h => ho (part_odd r N (decode r N ⟨p,c⟩) k h))

private theorem allocation_heq (r : ℕ) {k l m t : ℕ}
    (a : PartAllocation r k m) (b : PartAllocation r l t)
    (hkl : k = l) (hab : ∀ i, a.1.1 i = b.1.1 i) : HEq a b := by
  subst l
  have hmt : m = t := by
    rw [← a.1.2, ← b.1.2]
    exact Finset.sum_congr rfl (fun i hi => hab i)
  subst t
  apply heq_of_eq
  apply Prod.ext
  · exact Subtype.ext (funext hab)
  · exact Subsingleton.elim _ _

private theorem encode_decode (r N : ℕ) (s : PartitionData r N) :
    encode r N (decode r N s) = s := by
  classical
  rcases s with ⟨p,c⟩
  have hp := partition_decode r N p c
  apply Sigma.ext hp
  apply Function.hfunext (congrArg (fun q : Nat.Partition N => ↥q.parts.toFinset) hp)
  intro k l hkl
  have hval : k.1 = l.1 :=
    (Subtype.heq_iff_coe_eq (by intro x; rw [hp])).mp hkl
  apply allocation_heq r _ _ hval
  intro i
  change decodeOccupation r p c (i,k.1/2) = (c l).1.1 i
  rw [hval]
  exact decode_at r p c l i

/-- The exact occupation fibre is the dependent family of odd-part colour allocations. -/
def colouredMultiplicityEquiv (r N : ℕ) :
    ColouredOddFiber (Fin r) N ≃ PartitionData r N where
  toFun := encode r N
  invFun := decode r N
  left_inv := decode_encode r N
  right_inv := encode_decode r N

def oddColourFactor (r k m : ℕ) : ℕ := if Odd k then Nat.multichoose r m else 0

def partitionCount (r N : ℕ) : ℕ :=
  ∑ p : Nat.Partition N,
    ∏ k ∈ p.parts.toFinset, oddColourFactor r k (p.parts.count k)

def onesPartition (N : ℕ) : Nat.Partition N where
  parts := Multiset.replicate N 1
  parts_pos := by
    intro k hk
    have hk1 : k = 1 := (Multiset.mem_replicate.mp hk).2
    omega
  parts_sum := by simp

/-- The boundary grades of the same independent finite count. -/
theorem partitionCount_small (r : ℕ) :
    partitionCount r 0 = 1 ∧ partitionCount r 1 = r ∧
      partitionCount r 2 = Nat.multichoose r 2 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [partitionCount]
  · simp [partitionCount, oddColourFactor]
  · unfold partitionCount
    rw [Finset.sum_eq_single (onesPartition 2)]
    · norm_num [onesPartition, oddColourFactor]
    · intro p hp hne
      have htwo : 2 ∈ p.parts := by
        by_contra hnot
        have he : ∀ k ∈ p.parts, k = 1 := by
          intro k hk
          have hl := Multiset.le_sum_of_mem hk
          have hpos := p.parts_pos hk
          rw [p.parts_sum] at hl
          have hne2 : k ≠ 2 := fun h => hnot (h ▸ hk)
          omega
        have hrepl := Multiset.eq_replicate_card.mpr he
        have hc : p.parts.card = 2 := by
          have hs := p.parts_sum
          rw [hrepl] at hs
          simpa using hs
        apply hne
        apply Nat.Partition.ext
        simpa [onesPartition, hc] using hrepl
      exact Finset.prod_eq_zero (Multiset.mem_toFinset.mpr htwo)
        (by norm_num [oddColourFactor])
    · simp

private theorem allocation_card (r k m : ℕ) :
    Fintype.card (PartAllocation r k m) = oddColourFactor r k m := by
  classical
  have hc : Fintype.card (Allocation r m) = Nat.multichoose r m := by
    rw [← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin r) m)]
    exact Sym.card_sym_fin_eq_multichoose r m
  rw [Fintype.card_prod, hc]
  by_cases h : Odd k <;> simp [oddColourFactor, h]

/-- A genuine finite partition count; neither side is defined by a formal product. -/
theorem card_colouredFiber (r N : ℕ) :
    Nat.card (ColouredOddFiber (Fin r) N) = partitionCount r N := by
  classical
  rw [Nat.card_congr (colouredMultiplicityEquiv r N), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  unfold partitionCount
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fintype.card_pi, allocation_card]
  exact Finset.prod_coe_sort p.parts.toFinset
    (fun k => oddColourFactor r k (p.parts.count k))

section Series
open scoped PowerSeries.WithPiTopology

/-- The independent partition count is the existing weighted partition generating function. -/
theorem colouredFiberSeries_eq_genFun (R : Type*) [CommSemiring R] (r : ℕ) :
    colouredFiberSeries R (Fin r) =
      Nat.Partition.genFun (fun k m => (oddColourFactor r k m : R)) := by
  classical
  ext N
  rw [colouredFiberSeries, PowerSeries.coeff_mk, card_colouredFiber,
    Nat.Partition.coeff_genFun]
  simp [partitionCount, Finsupp.prod, Multiset.toFinsupp_support,
    Multiset.toFinsupp_apply]

private theorem multichoose_series (r : ℕ) :
    PowerSeries.mk (fun m => (Nat.multichoose r m : ℂ)) =
      (PowerSeries.mk (fun _ : ℕ => (1 : ℂ))) ^ r := by
  cases r with
  | zero =>
    ext n
    cases n <;> simp [Nat.multichoose_zero_succ]
  | succ r =>
    change _ = (PowerSeries.mk (1 : ℕ → ℂ)) ^ (r+1)
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add ℂ r]
    ext n
    simp only [PowerSeries.coeff_mk, Nat.multichoose_eq]
    congr 1
    rw [show r + 1 + n - 1 = r + n by omega, Nat.choose_symm_add]

private theorem expanded_geometric (k : ℕ) (hk : k ≠ 0) :
    PowerSeries.expand k hk (PowerSeries.mk (fun _ : ℕ => (1 : ℂ))) =
      ((1 : PowerSeries ℂ) - PowerSeries.X ^ k)⁻¹ := by
  change PowerSeries.expand k hk (PowerSeries.mk (1 : ℕ → ℂ)) = _
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hk])).2
  have h := congrArg (PowerSeries.expand k hk)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simpa only [map_mul, map_sub, map_one, PowerSeries.expand_X, Pi.one_apply] using h

/-- All local geometric-power coefficients, including the degree-zero and rank-zero cases. -/
theorem local_geometric_power_coeff (r k : ℕ) (hk : k ≠ 0) (N : ℕ) :
    PowerSeries.coeff N ((((1 : PowerSeries ℂ) - PowerSeries.X ^ k)⁻¹) ^ r) =
      if k ∣ N then (Nat.multichoose r (N / k) : ℂ) else 0 := by
  have he : (((1 : PowerSeries ℂ) - PowerSeries.X ^ k)⁻¹) ^ r =
      PowerSeries.expand k hk (PowerSeries.mk (fun m => (Nat.multichoose r m : ℂ))) := by
    rw [multichoose_series, map_pow, expanded_geometric]
  rw [he, PowerSeries.coeff_expand]
  simp only [PowerSeries.coeff_mk]

private theorem local_factor (r k : ℕ) (hk : k ≠ 0) :
    (1 : PowerSeries ℂ) + ∑' j : ℕ,
        (Nat.multichoose r (j+1) : ℂ) • PowerSeries.X ^ (k*(j+1)) =
      (((1 : PowerSeries ℂ) - PowerSeries.X ^ k)⁻¹) ^ r := by
  ext N
  rw [local_geometric_power_coeff r k hk]
  rw [map_add, (Nat.Partition.summable_genFun_term'
    (fun _ m => (Nat.multichoose r m : ℂ)) hk).map_tsum _
      (PowerSeries.WithPiTopology.continuous_coeff _ _)]
  simp only [map_smul, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hn : N = 0
  · subst N
    simp [hk, Nat.mul_ne_zero hk (Nat.succ_ne_zero _)]
  · by_cases hd : k ∣ N
    · rw [if_pos hd]
      have hq : 0 < N / k := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
        (Nat.pos_of_ne_zero hk)
      have hmul : k * (N / k - 1 + 1) = N := by
        rw [Nat.sub_add_cancel hq, Nat.mul_div_cancel' hd]
      rw [tsum_eq_single (N / k - 1)]
      · simp [hn, hmul, Nat.sub_add_cancel hq, Nat.mul_div_cancel' hd]
      · intro j hj
        have hne : N ≠ k * (j+1) := by
          intro heq
          have he : N/k = j+1 := by rw [heq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)]
          omega
        simp [hne]
    · rw [if_neg hd]
      have hz (j : ℕ) : N ≠ k * (j+1) := fun h => hd ⟨j+1,h⟩
      simp [hn, hz]

/-- Correct positive-part and positive-multiplicity factors for the independent count. -/
theorem hasProd_partitionGenFun (r : ℕ) :
    HasProd (fun n : ℕ =>
      (((1 : PowerSeries ℂ) - PowerSeries.X ^ (2*n+1))⁻¹) ^ r)
      (Nat.Partition.genFun (fun k m => (oddColourFactor r k m : ℂ))) := by
  classical
  let F : ℕ → PowerSeries ℂ := fun i =>
    1 + ∑' j : ℕ, (oddColourFactor r (i+1) (j+1) : ℂ) •
      PowerSeries.X ^ ((i+1)*(j+1))
  have hF : HasProd F
      (Nat.Partition.genFun (fun k m => (oddColourFactor r k m : ℂ))) :=
    Nat.Partition.hasProd_genFun (fun k m => (oddColourFactor r k m : ℂ))
  have hinj : Function.Injective (fun n : ℕ => 2*n) := by
    intro a b h
    change 2*a = 2*b at h
    omega
  have hout : ∀ i : ℕ, i ∉ Set.range (fun n : ℕ => 2*n) → F i = 1 := by
    intro i hi
    have hnot : ¬ Even i := by
      rintro ⟨j,hj⟩
      exact hi ⟨j,by dsimp; omega⟩
    have heven : ¬ Odd (i+1) := by
      have hm := Nat.not_even_iff.mp hnot
      intro ⟨j,hj⟩
      omega
    simp [F, oddColourFactor, heven]
  have hsub : HasProd (F ∘ (fun n : ℕ => 2*n))
      (Nat.Partition.genFun (fun k m => (oddColourFactor r k m : ℂ))) :=
    (hinj.hasProd_iff hout).2 hF
  apply hsub.congr_fun
  intro n
  have ho : Odd (2*n+1) := ⟨n,by omega⟩
  simpa only [Function.comp_apply, F, oddColourFactor, if_pos ho, Nat.cast_id] using
    (local_factor r (2*n+1) (by omega)).symm

end Series

end D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity
