/- GID: D5/S3/Combinatorics/Partitions/ColouredOccupation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/ColouredOccupation
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Ordinary positive-mode occupations are the existing coloured partitions. -/

import D5.S3.Combinatorics.Partitions.ColouredEulerLedger
import D5.S3.VertexAlgebra.PolynomialFockCharacter

/-!
SOURCE ONLY UNCOMPILED. Frequencies here are k+1, including every positive
integer. The one-colour partition map is reused, not proved again. The
allocation carrier and its finite instance are reused from the odd-mode
module; no oddness condition or odd-mode weight is used here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.Combinatorics.Partitions.ColouredOccupation

open ColouredEulerLedger
open ColouredOddMultiplicity (Allocation)
open D5.S3.VertexAlgebra.PolynomialFockCharacter (energyFiberEquivPartition)
open D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum (energy EnergyFiber)

/-- All ordinary positive modes, with finitely many occupied colour/mode pairs. -/
abbrev OccupationFiber (r N : ℕ) :=
  {d : (Fin r × ℕ) →₀ ℕ // Finsupp.weight (fun x => x.2 + 1) d = N}

private def forgetColours (r : ℕ) (d : (Fin r × ℕ) →₀ ℕ) : ℕ →₀ ℕ :=
  (d.toMultiset.map Prod.snd).toFinsupp

private theorem weight_sum (r : ℕ) (d : (Fin r × ℕ) →₀ ℕ) :
    (d.toMultiset.map (fun x => x.2 + 1)).sum =
      Finsupp.weight (fun x => x.2 + 1) d := by
  rw [Finsupp.toMultiset_apply, Finsupp.multiset_map_sum, Finsupp.multiset_sum_sum]
  simp only [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton,
    Multiset.sum_singleton]
  rfl

private theorem forgetColours_energy (r : ℕ) (d : (Fin r × ℕ) →₀ ℕ) :
    energy (forgetColours r d) = Finsupp.weight (fun x => x.2 + 1) d := by
  have hs (a : ℕ →₀ ℕ) : (a.toMultiset.map Nat.succ).sum = energy a := by
    rw [Finsupp.toMultiset_apply, Finsupp.multiset_map_sum,
      Finsupp.multiset_sum_sum]
    simp [energy, Finsupp.sum, Multiset.map_nsmul, Multiset.sum_nsmul,
      Multiset.map_singleton, Multiset.sum_singleton, Nat.succ_eq_add_one, mul_comm]
  rw [← hs, forgetColours, Multiset.toFinsupp_toMultiset, Multiset.map_map]
  exact weight_sum r d

private def occupationPartition (r N : ℕ) (d : OccupationFiber r N) :
    Nat.Partition N :=
  energyFiberEquivPartition N
    ⟨forgetColours r d.val, (forgetColours_energy r d.val).trans d.property⟩

private theorem occupationPartition_parts (r N : ℕ) (d : OccupationFiber r N) :
    (occupationPartition r N d).parts = d.val.toMultiset.map (fun x => x.2 + 1) := by
  change ((forgetColours r d.val).toMultiset.map Nat.succ) = _
  rw [forgetColours, Multiset.toFinsupp_toMultiset, Multiset.map_map]
  rfl

private theorem count_mode (r : ℕ) (d : (Fin r × ℕ) →₀ ℕ) (n : ℕ) :
    (d.toMultiset.map (fun x => x.2 + 1)).count (n + 1) =
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
    · have hw : n + 1 ≠ m + 1 := by omega
      simp [Finsupp.single_apply, h, Ne.symm h, hw]

private abbrev Colouring (r : ℕ) {N : ℕ} (p : Nat.Partition N) :=
  (k : ↥p.parts.toFinset) → Allocation r (p.parts.count k.val)

private abbrev PartitionData (r N : ℕ) := Σ p : Nat.Partition N, Colouring r p

private def occupationColouring (r N : ℕ) (d : OccupationFiber r N) :
    Colouring r (occupationPartition r N d) := by
  intro k
  refine ⟨fun i => d.val (i, k.val - 1), ?_⟩
  have hk : 0 < k.val := (occupationPartition r N d).parts_pos
    (Multiset.mem_toFinset.mp k.property)
  calc
    _ = (d.val.toMultiset.map (fun x => x.2 + 1)).count (k.val - 1 + 1) :=
      (count_mode r d.val (k.val - 1)).symm
    _ = (d.val.toMultiset.map (fun x => x.2 + 1)).count k.val := by
      rw [Nat.sub_add_cancel hk]
    _ = _ := congrArg (Multiset.count k.val) (occupationPartition_parts r N d).symm

private def encode (r N : ℕ) (d : OccupationFiber r N) : PartitionData r N :=
  ⟨occupationPartition r N d, occupationColouring r N d⟩

private def decodeOccupation (r : ℕ) {N : ℕ} (p : Nat.Partition N)
    (c : Colouring r p) : (Fin r × ℕ) →₀ ℕ :=
  ∑ k : ↥p.parts.toFinset, ∑ i : Fin r,
    Finsupp.single (i, k.val - 1) ((c k).val i)

private theorem decode_at (r : ℕ) {N : ℕ} (p : Nat.Partition N)
    (c : Colouring r p) (k : ↥p.parts.toFinset) (i : Fin r) :
    decodeOccupation r p c (i, k.val - 1) = (c k).val i := by
  classical
  unfold decodeOccupation
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single k]
  · simp [Finsupp.single_apply]
  · intro j hj hne
    have hn : j.val - 1 ≠ k.val - 1 := by
      intro he
      have hjpos := p.parts_pos (Multiset.mem_toFinset.mp j.property)
      have hkpos := p.parts_pos (Multiset.mem_toFinset.mp k.property)
      exact hne (Subtype.ext (by omega))
    simp [Finsupp.single_apply, hn]
  · simp

private theorem decode_outside (r : ℕ) {N : ℕ} (p : Nat.Partition N)
    (c : Colouring r p) (i : Fin r) (n : ℕ) (hn : n + 1 ∉ p.parts) :
    decodeOccupation r p c (i,n) = 0 := by
  classical
  unfold decodeOccupation
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hne : k.val - 1 ≠ n := by
    intro he
    have hpos := p.parts_pos (Multiset.mem_toFinset.mp k.property)
    have heq : n + 1 = k.val := by omega
    exact hn (by rw [heq]; exact Multiset.mem_toFinset.mp k.property)
  simp [Finsupp.single_apply, hne]

private theorem decode_weight (r : ℕ) {N : ℕ} (p : Nat.Partition N)
    (c : Colouring r p) :
    Finsupp.weight (fun x : Fin r × ℕ => x.2 + 1) (decodeOccupation r p c) = N := by
  classical
  unfold decodeOccupation
  simp only [map_sum, Finsupp.weight_single, nsmul_eq_mul]
  have hsum : (∑ k : ↥p.parts.toFinset,
      ∑ i : Fin r, (c k).val i * (k.val - 1 + 1)) =
      ∑ k : ↥p.parts.toFinset, p.parts.count k.val * k.val := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_mul, (c k).property]
    have hpos := p.parts_pos (Multiset.mem_toFinset.mp k.property)
    rw [Nat.sub_add_cancel hpos]
  change (∑ k : ↥p.parts.toFinset,
    ∑ i : Fin r, (c k).val i * (k.val - 1 + 1)) = N
  rw [hsum]
  calc
    _ = ∑ k ∈ p.parts.toFinset, p.parts.count k * k :=
      Finset.sum_coe_sort p.parts.toFinset (fun k => p.parts.count k * k)
    _ = N := by
      simpa only [nsmul_eq_mul, Nat.cast_id, p.parts_sum] using
        (Finset.sum_multiset_count p.parts).symm

private def decode (r N : ℕ) (s : PartitionData r N) : OccupationFiber r N :=
  ⟨decodeOccupation r s.1 s.2, decode_weight r s.1 s.2⟩

private theorem decode_encode (r N : ℕ) (d : OccupationFiber r N) :
    decode r N (encode r N d) = d := by
  classical
  apply Subtype.ext
  ext x
  rcases x with ⟨i,n⟩
  by_cases hk : n + 1 ∈ (occupationPartition r N d).parts
  · let k : ↥(occupationPartition r N d).parts.toFinset :=
      ⟨n+1, Multiset.mem_toFinset.mpr hk⟩
    have h := decode_at r (occupationPartition r N d) (occupationColouring r N d) k i
    simpa only [decode, encode, occupationColouring, k, Nat.add_sub_cancel] using h
  · have hout := decode_outside r (occupationPartition r N d)
      (occupationColouring r N d) i n hk
    have hsum : (∑ j : Fin r, d.val (j,n)) = 0 := by
      rw [← count_mode]
      exact Multiset.count_eq_zero.mpr (by rwa [← occupationPartition_parts])
    have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) =>
      Nat.zero_le (d.val (j,n))) (Finset.mem_univ i)
    have hi : d.val (i,n) = 0 := by omega
    exact hout.trans hi.symm

private theorem partition_decode (r N : ℕ) (p : Nat.Partition N) (c : Colouring r p) :
    occupationPartition r N (decode r N ⟨p,c⟩) = p := by
  classical
  apply Nat.Partition.ext
  apply Multiset.ext.mpr
  intro k
  rw [occupationPartition_parts]
  by_cases hk : k ∈ p.parts
  · let l : ↥p.parts.toFinset := ⟨k, Multiset.mem_toFinset.mpr hk⟩
    have hr : k - 1 + 1 = k := Nat.sub_add_cancel (p.parts_pos hk)
    change ((decodeOccupation r p c).toMultiset.map (fun x => x.2+1)).count k = _
    calc
      _ = ((decodeOccupation r p c).toMultiset.map (fun x => x.2+1)).count
          (k-1+1) := by rw [hr]
      _ = ∑ i : Fin r, decodeOccupation r p c (i,k-1) := count_mode _ _ _
      _ = ∑ i : Fin r, (c l).val i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact decode_at r p c l i
      _ = _ := (c l).property
  · rw [Multiset.count_eq_zero.mpr hk]
    by_cases hpos : 0 < k
    · have hr : k - 1 + 1 = k := Nat.sub_add_cancel hpos
      change ((decodeOccupation r p c).toMultiset.map (fun x => x.2+1)).count k = 0
      rw [← hr, count_mode]
      apply Finset.sum_eq_zero
      intro i hi
      exact decode_outside r p c i (k-1) (by rwa [hr])
    · have hk0 : k = 0 := by omega
      subst k
      apply Multiset.count_eq_zero.mpr
      intro hm
      obtain ⟨x,hx,he⟩ := Multiset.mem_map.mp hm
      omega

private theorem allocation_heq (r : ℕ) {m n : ℕ}
    (a : Allocation r m) (b : Allocation r n) (hab : ∀ i, a.val i = b.val i) :
    HEq a b := by
  have hmn : m = n := by
    rw [← a.property, ← b.property]
    exact Finset.sum_congr rfl (fun i hi => hab i)
  subst n
  exact heq_of_eq (Subtype.ext (funext hab))

private theorem encode_decode (r N : ℕ) (s : PartitionData r N) :
    encode r N (decode r N s) = s := by
  classical
  rcases s with ⟨p,c⟩
  have hp := partition_decode r N p c
  apply Sigma.ext hp
  apply Function.hfunext (congrArg (fun q : Nat.Partition N => ↥q.parts.toFinset) hp)
  intro k l hkl
  have hval : k.val = l.val :=
    (Subtype.heq_iff_coe_eq (by intro x; rw [hp])).mp hkl
  apply allocation_heq r
  intro i
  dsimp only [encode, occupationColouring]
  change decodeOccupation r p c (i,k.val-1) = (c l).val i
  rw [hval]
  exact decode_at r p c l i

/-- Explicit inverse: convert each colour multiset to its allocation, then
sum single (i,k-1) with the allocated multiplicity over all occurring parts.
Both dependent sigma identities hold for every r,N, including zero. -/
def occupationPartitionEquiv (r N : ℕ) :
    OccupationFiber r N ≃ ColouredPartition (fun _ => r) N :=
  (show OccupationFiber r N ≃ PartitionData r N from
    { toFun := encode r N
      invFun := decode r N
      left_inv := decode_encode r N
      right_inv := encode_decode r N }).trans
    (Equiv.sigmaCongrRight (fun p => Equiv.piCongrRight (fun k =>
      (Sym.equivNatSumOfFintype (Fin r) (p.parts.count k.val)).symm)))

end D5.S3.Combinatorics.Partitions.ColouredOccupation
