/- GID: D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maximal indices in a prime-power group coset partition have p-divisible multiplicity. -/

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Exact-name searches on current `origin/dev` found no declaration named
     `maximalIndex`, `maximalIndexPositions`, `prime_dvd_card_maximalIndex`, or
     `prime_le_card_maximalIndex` under `D5`.
   * Conclusion-shape searches found only unrelated subgroup-index cardinality
     computations in Fourier and seat-combinatorics modules.
   * The generated in-flight module and atom inventories contained none of the
     target names or atom hashes.
   * Pinned Mathlib contains the unrelated Marica--Schonheim inequality, but no
     Herzog--Schonheim coset-partition multiplicity result; direct `exact?`
     trials against both target conclusions found no closing declaration. -/

open scoped BigOperators Pointwise
open Function

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.FiniteCosetPartitionMaximalIndexMultiplicity

variable {G : Type*} [Group G] [Finite G]

/-- The largest subgroup index in a finite indexed family. -/
noncomputable def maximalIndex {r : ℕ} (H : Fin r → Subgroup G) : ℕ :=
  Finset.univ.sup fun i ↦ (H i).index

/-- The positions at which the largest subgroup index is attained. -/
noncomputable def maximalIndexPositions {r : ℕ}
    (H : Fin r → Subgroup G) : Finset (Fin r) :=
  Finset.univ.filter fun i ↦ (H i).index = maximalIndex H

private theorem card_eq_sum_subgroup_card_of_leftCoset_partition
    {r : ℕ} (H : Fin r → Subgroup G) (g : Fin r → G)
    (hdisj : Pairwise (Disjoint on fun i ↦ g i • (H i : Set G)))
    (hcover : (⋃ i, g i • (H i : Set G)) = Set.univ) :
    Nat.card G = ∑ i, Nat.card (H i) := by
  calc
    Nat.card G = (Set.univ : Set G).ncard := by simp
    _ = (⋃ i, g i • (H i : Set G)).ncard := by rw [hcover]
    _ = ∑ᶠ i : Fin r, (g i • (H i : Set G)).ncard :=
      Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hdisj
    _ = ∑ i, Nat.card (H i) := by
      rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.univ) (by simp)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq]
      rfl

omit [Finite G] in
private theorem index_le_maximalIndex {r : ℕ}
    (H : Fin r → Subgroup G) (i : Fin r) :
    (H i).index ≤ maximalIndex H := by
  exact Finset.le_sup (f := fun j ↦ (H j).index) (Finset.mem_univ i)

omit [Finite G] in
private theorem exists_index_eq_maximalIndex {r : ℕ} (hr : 0 < r)
    (H : Fin r → Subgroup G) : ∃ i, (H i).index = maximalIndex H := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin r))
    ⟨⟨0, hr⟩, Finset.mem_univ _⟩ (fun j ↦ (H j).index)
  exact ⟨i, hi.symm⟩

omit [Finite G] in
private theorem index_dvd_maximalIndex_of_card_eq_prime_pow
    {r p N : ℕ} (hr : 0 < r) (hp : p.Prime) (hcard : Nat.card G = p ^ N)
    (H : Fin r → Subgroup G) (i : Fin r) :
    (H i).index ∣ maximalIndex H := by
  obtain ⟨j, hj⟩ := exists_index_eq_maximalIndex hr H
  obtain ⟨ei, -, hei⟩ := (Nat.dvd_prime_pow hp).mp (hcard ▸ (H i).index_dvd_card)
  obtain ⟨ej, -, hej⟩ := (Nat.dvd_prime_pow hp).mp (hcard ▸ (H j).index_dvd_card)
  rw [hei, ← hj, hej]
  apply Nat.pow_dvd_pow
  apply (Nat.pow_le_pow_iff_right hp.two_le).mp
  calc
    p ^ ei = (H i).index := hei.symm
    _ ≤ maximalIndex H := index_le_maximalIndex H i
    _ = (H j).index := hj.symm
    _ = p ^ ej := hej

private theorem maximalIndex_eq_sum_div_index
    {r p N : ℕ} (hr : 0 < r) (hp : p.Prime) (hcard : Nat.card G = p ^ N)
    (H : Fin r → Subgroup G) (g : Fin r → G)
    (hdisj : Pairwise (Disjoint on fun i ↦ g i • (H i : Set G)))
    (hcover : (⋃ i, g i • (H i : Set G)) = Set.univ) :
    maximalIndex H = ∑ i, maximalIndex H / (H i).index := by
  let d := maximalIndex H
  let q := Nat.card G / d
  obtain ⟨j, hj⟩ := exists_index_eq_maximalIndex hr H
  have hdvdcard : d ∣ Nat.card G := by
    dsimp [d]
    rw [← hj]
    exact (H j).index_dvd_card
  have hdpos : 0 < d := by
    dsimp [d]
    rw [← hj]
    exact Nat.pos_of_ne_zero (H j).index_ne_zero_of_finite
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd Nat.card_pos hdvdcard) hdpos
  have hterm : ∀ i, Nat.card (H i) = q * (d / (H i).index) := by
    intro i
    have hid : (H i).index ∣ d :=
      index_dvd_maximalIndex_of_card_eq_prime_pow hr hp hcard H i
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (H i).index_ne_zero_of_finite)
    calc
      (H i).index * Nat.card (H i) = Nat.card G := (H i).index_mul_card
      _ = q * d := (Nat.div_mul_cancel hdvdcard).symm
      _ = q * ((H i).index * (d / (H i).index)) :=
        congrArg (q * ·) (Nat.mul_div_cancel' hid).symm
      _ = (H i).index * (q * (d / (H i).index)) := by ac_rfl
  apply Nat.eq_of_mul_eq_mul_left hqpos
  calc
    q * d = Nat.card G := Nat.div_mul_cancel hdvdcard
    _ = ∑ i, Nat.card (H i) :=
      card_eq_sum_subgroup_card_of_leftCoset_partition H g hdisj hcover
    _ = ∑ i, q * (d / (H i).index) := Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = q * ∑ i, d / (H i).index := (Finset.mul_sum ..).symm

private theorem prime_dvd_div_of_dvd_prime_pow
    {p N a d : ℕ} (hp : p.Prime) (had : a ∣ d) (hd : d ∣ p ^ N) (hne : a ≠ d) :
    p ∣ d / a := by
  have hquot_dvd : d / a ∣ p ^ N := (Nat.div_dvd_of_dvd had).trans hd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hquot_dvd
  have hk0 : k ≠ 0 := by
    intro hkzero
    apply hne
    have hquot_one : d / a = 1 := by simpa [hkzero] using hk
    calc
      a = a * 1 := by simp
      _ = a * (d / a) := by rw [hquot_one]
      _ = d := Nat.mul_div_cancel' had
  rw [hk]
  exact dvd_pow_self p hk0

private theorem prime_dvd_maximalIndex
    {r p N : ℕ} (hr : 2 ≤ r) (hp : p.Prime) (hcard : Nat.card G = p ^ N)
    (H : Fin r → Subgroup G) (g : Fin r → G)
    (hdisj : Pairwise (Disjoint on fun i ↦ g i • (H i : Set G)))
    (hcover : (⋃ i, g i • (H i : Set G)) = Set.univ) :
    p ∣ maximalIndex H := by
  let d := maximalIndex H
  change p ∣ d
  have hrpos : 0 < r := by omega
  obtain ⟨j, hj⟩ := exists_index_eq_maximalIndex hrpos H
  have hdvd : d ∣ p ^ N := by
    have hmaxdvd : maximalIndex H ∣ Nat.card G := by
      rw [← hj]
      exact (H j).index_dvd_card
    simpa only [d] using (hcard ▸ hmaxdvd)
  have hdne : d ≠ 1 := by
    intro hd1
    have hratio : d = ∑ i, d / (H i).index := by
      simpa only [d] using
        maximalIndex_eq_sum_div_index hrpos hp hcard H g hdisj hcover
    have hidx : ∀ i, (H i).index = 1 := by
      intro i
      exact Nat.dvd_one.mp (hd1 ▸ index_dvd_maximalIndex_of_card_eq_prime_pow
        hrpos hp hcard H i)
    have hdr : d = r := by simpa [hidx, hd1] using hratio
    omega
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hk0 : k ≠ 0 := by
    intro hkzero
    apply hdne
    simpa [hkzero] using hk
  rw [hk]
  exact dvd_pow_self p hk0

private theorem sum_index_ratios_modEq_maximal_count
    {r p N : ℕ} (hr : 0 < r) (hp : p.Prime) (hcard : Nat.card G = p ^ N)
    (H : Fin r → Subgroup G) :
    (∑ i, maximalIndex H / (H i).index) ≡
      (maximalIndexPositions H).card [MOD p] := by
  let d := maximalIndex H
  obtain ⟨j, hj⟩ := exists_index_eq_maximalIndex hr H
  have hdvd : d ∣ p ^ N := by
    have hmaxdvd : maximalIndex H ∣ Nat.card G := by
      rw [← hj]
      exact (H j).index_dvd_card
    simpa only [d] using (hcard ▸ hmaxdvd)
  have hdnezero : d ≠ 0 := by
    dsimp [d]
    rw [← hj]
    exact (H j).index_ne_zero_of_finite
  have hterms : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      d / (H i).index ≡ (if (H i).index = d then 1 else 0) [MOD p] := by
    intro i _
    by_cases hi : (H i).index = d
    · simpa [hi, Nat.div_self (Nat.pos_of_ne_zero hdnezero)] using
        (Nat.ModEq.refl (n := p) 1)
    · rw [if_neg hi]
      exact Nat.modEq_zero_iff_dvd.mpr <|
        prime_dvd_div_of_dvd_prime_pow hp
          (index_dvd_maximalIndex_of_card_eq_prime_pow hr hp hcard H i) hdvd hi
  simpa [d, maximalIndexPositions] using Nat.ModEq.sum hterms

/-- In a finite group of order `p ^ N`, `p` divides the number of maximal-index
cosets in every nontrivial pairwise-disjoint left-coset partition. -/
theorem prime_dvd_card_maximalIndex
    {r p N : ℕ} (hr : 2 ≤ r) (hp : p.Prime) (hcard : Nat.card G = p ^ N)
    (H : Fin r → Subgroup G) (g : Fin r → G)
    (hdisj : Pairwise (Disjoint on fun i ↦ g i • (H i : Set G)))
    (hcover : (⋃ i, g i • (H i : Set G)) = Set.univ) :
    p ∣ (maximalIndexPositions H).card := by
  have hrpos : 0 < r := by omega
  have hratios := maximalIndex_eq_sum_div_index hrpos hp hcard H g hdisj hcover
  have hreduce := sum_index_ratios_modEq_maximal_count hrpos hp hcard H
  have hmaxzero : maximalIndex H ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr <| prime_dvd_maximalIndex hr hp hcard H g hdisj hcover
  apply Nat.modEq_zero_iff_dvd.mp
  have hratios_to_max :
      (∑ i, maximalIndex H / (H i).index) ≡ maximalIndex H [MOD p] := by
    rw [← hratios]
  exact hreduce.symm.trans (hratios_to_max.trans hmaxzero)

/-- The maximal index occurs at least `p` times, and consequently two distinct
positions have equal subgroup index: the prime-power-group Herzog--Schonheim conclusion. -/
theorem prime_le_card_maximalIndex
    {r p N : ℕ} (hr : 2 ≤ r) (hp : p.Prime) (hcard : Nat.card G = p ^ N)
    (H : Fin r → Subgroup G) (g : Fin r → G)
    (hdisj : Pairwise (Disjoint on fun i ↦ g i • (H i : Set G)))
    (hcover : (⋃ i, g i • (H i : Set G)) = Set.univ) :
    p ≤ (maximalIndexPositions H).card ∧
      ∃ i j : Fin r, i ≠ j ∧ (H i).index = (H j).index := by
  have hrpos : 0 < r := by omega
  obtain ⟨i, hi⟩ := exists_index_eq_maximalIndex hrpos H
  have hlower : p ≤ (maximalIndexPositions H).card := by
    apply Nat.le_of_dvd
    · exact Finset.card_pos.mpr ⟨i, by simpa [maximalIndexPositions] using hi⟩
    · exact prime_dvd_card_maximalIndex hr hp hcard H g hdisj hcover
  refine ⟨hlower, ?_⟩
  have htwo : 1 < (maximalIndexPositions H).card :=
    lt_of_lt_of_le hp.one_lt hlower
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htwo
  refine ⟨i, j, hij, ?_⟩
  have hii : (H i).index = maximalIndex H := by
    simpa [maximalIndexPositions] using hi
  have hjj : (H j).index = maximalIndex H := by
    simpa [maximalIndexPositions] using hj
  exact hii.trans hjj.symm

section FidelityWitnesses

example :
    ∃ (H : Fin 2 → Subgroup (Multiplicative (ZMod 2)))
      (g : Fin 2 → Multiplicative (ZMod 2)),
      Pairwise (Disjoint on fun i ↦ g i • (H i : Set (Multiplicative (ZMod 2)))) ∧
      (⋃ i, g i • (H i : Set (Multiplicative (ZMod 2)))) = Set.univ ∧
      2 ∣ (maximalIndexPositions H).card := by
  let e : Fin 2 ≃ Multiplicative (ZMod 2) :=
    Equiv.ofBijective (fun i ↦ Multiplicative.ofAdd (i : ZMod 2)) (by decide)
  let H : Fin 2 → Subgroup (Multiplicative (ZMod 2)) := fun _ ↦ ⊥
  let g : Fin 2 → Multiplicative (ZMod 2) := e
  have hcoset : ∀ i, g i • (H i : Set (Multiplicative (ZMod 2))) = {g i} := by
    intro i
    ext x
    simp [H]
  have hdisj : Pairwise
      (Disjoint on fun i ↦ g i • (H i : Set (Multiplicative (ZMod 2)))) := by
    intro i j hij
    change Disjoint
      (g i • (H i : Set (Multiplicative (ZMod 2))))
      (g j • (H j : Set (Multiplicative (ZMod 2))))
    rw [hcoset i, hcoset j]
    exact Set.disjoint_singleton.mpr (e.injective.ne hij)
  have hcover :
      (⋃ i, g i • (H i : Set (Multiplicative (ZMod 2)))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, rfl⟩ := e.surjective x
    exact Set.mem_iUnion.mpr ⟨i, by
      rw [hcoset i]
      exact Set.mem_singleton (g i)⟩
  refine ⟨H, g, hdisj, hcover, ?_⟩
  exact prime_dvd_card_maximalIndex (G := Multiplicative (ZMod 2))
    (r := 2) (p := 2) (N := 1) (by omega) Nat.prime_two (by simp)
    H g hdisj hcover

end FidelityWitnesses

#print axioms prime_dvd_card_maximalIndex
#print axioms prime_le_card_maximalIndex

end D5.S3.Factorization.PrimePowers.FiniteCosetPartitionMaximalIndexMultiplicity
