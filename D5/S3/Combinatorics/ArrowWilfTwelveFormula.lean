/- GID: D5/S3/Combinatorics/ArrowWilfTwelveFormula
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfTwelveFormula
   mirror-E: none(waiver:finite-cardinality-formula-for-the-twelve-arrow-pattern)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: The twelve avoidance class is counted by largest fixed-point decorated fibers. -/

import D5.S3.Combinatorics.ArrowWilfTwelveSurject
import D5.S3.Combinatorics.ArrowWilfTwelveCard
import D5.S3.Combinatorics.ArrowWilfPartition
import D5.S3.Combinatorics.ArrowWilfSums
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfTwelveFormula

noncomputable section

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCountingCore
open D5.S3.Combinatorics.ArrowWilfTwelveCount
open D5.S3.Combinatorics.ArrowWilfTwelveInverse
open D5.S3.Combinatorics.ArrowWilfTwelveSurject
open D5.S3.Combinatorics.ArrowWilfTwelveCard
open D5.S3.Combinatorics.ArrowWilfPartition

private abbrev TwelveP (n : ℕ) (p : Word (fullSupport n)) : Prop :=
  ¬ Contains [1, 2] [(3, 3)] 3 p.1

/-- A largest-fixed-point fiber is exactly the decorated family over all moving-set sizes. -/
def twelveFiberEquiv (n : ℕ) (m : ↑(fullSupport n)) :
    (Σ k : Fin (n - m.1 + 1), TwelveData n m.1 k.1) ≃
      MaxFixedFiber (fullSupport n) (TwelveP n) m := by
  have hm : 1 ≤ m.1 := by
    have hmem := m.2
    simp only [fullSupport, List.mem_toFinset, List.mem_range', one_mul] at hmem
    rcases hmem with ⟨i, hi, heq⟩
    omega
  have hmn : m.1 ≤ n := by
    have hmem := m.2
    simp only [fullSupport, List.mem_toFinset, List.mem_range', one_mul] at hmem
    rcases hmem with ⟨i, hi, heq⟩
    omega
  let f : (Σ k : Fin (n - m.1 + 1), TwelveData n m.1 k.1) →
      MaxFixedFiber (fullSupport n) (TwelveP n) m := fun ⟨_, d⟩ => by
    refine ⟨twelveWord hm hmn d, twelveList_avoids hm hmn d,
      twelveList_fixed_m hm hmn d, ?_⟩
    intro g hg hmg
    have hgH : g ∈ upperSupport n m.1 := by
      simp only [upperSupport, List.mem_toFinset, List.mem_range', one_mul]
      have hgf : g ∈ List.range' 1 n := by
        simpa [fullSupport] using hg
      simp only [List.mem_range', one_mul] at hgf
      rcases hgf with ⟨i, hi, heq⟩
      refine ⟨g - (m.1 + 1), ?_, ?_⟩ <;> omega
    exact twelveList_no_upper_fixed hm hmn d hgH
  refine Equiv.ofBijective f ?_
  constructor
  · intro ⟨k, d⟩ ⟨l, e⟩ heq
    have hlist : twelveList d = twelveList e := by
      exact congrArg (fun p => p.1.1) heq
    have hK := twelveList_K_eq hlist
    have hk : k.1 = l.1 := by
      have hdc := (Finset.mem_powersetCard.mp d.K.2).2
      have hec := (Finset.mem_powersetCard.mp e.K.2).2
      calc
        k.1 = d.K.1.card := hdc.symm
        _ = e.K.1.card := congrArg Finset.card hK
        _ = l.1 := hec
    have hkl : k = l := Fin.ext hk
    cases hkl
    have hde : d = e := twelveList_injective hlist
    cases hde
    rfl
  · intro p
    have hno : ∀ g ∈ upperSupport n m.1, hat p.1.1 g ≠ g := by
      intro g hg
      have hmg : m.1 < g := by
        simp only [upperSupport, List.mem_toFinset, List.mem_range', one_mul] at hg
        rcases hg with ⟨i, hi, heq⟩
        omega
      have hgf : g ∈ fullSupport n := by
        simp only [fullSupport, List.mem_toFinset, List.mem_range', one_mul]
        simp only [upperSupport, List.mem_toFinset, List.mem_range', one_mul] at hg
        rcases hg with ⟨i, hi, heq⟩
        exact ⟨m.1 + i, by omega, by omega⟩
      exact p.2.2.2 g hgf hmg
    obtain ⟨k, d, hd⟩ :=
      exists_twelveData_of_largest_fixed hm hmn p.1 p.2.1 p.2.2.1 hno
    have hk : k < n - m.1 + 1 := by
      have hKsub := (Finset.mem_powersetCard.mp d.K.2).1
      have hKcard := (Finset.mem_powersetCard.mp d.K.2).2
      have hHcard : (upperSupport n m.1).card = n - m.1 := by
        simp [upperSupport, List.toFinset_card_of_nodup List.nodup_range']
      have := Finset.card_le_card hKsub
      omega
    refine ⟨⟨⟨k, hk⟩, d⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hd

/-- The first avoidance class has Zhou--Yu's finite decorated-object count. -/
theorem card_twelve_avoiders (n : ℕ) (hn : 1 ≤ n) :
    (avoiders n [1, 2] [(3, 3)] 3).ncard =
      D5.S3.Combinatorics.ArrowWilfSums.F1 n := by
  classical
  let s := fullSupport n
  let P := TwelveP n
  have hword : ∀ p : List ℕ, p.Perm (List.range' 1 n) ↔ p ∈ words s := by
    intro p
    rw [words, List.mem_toFinset, List.mem_permutations]
    have hr : (List.range' 1 n).Perm s.toList := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact List.nodup_range'
      · exact s.nodup_toList
      · simp [s, fullSupport]
    exact ⟨fun hp => hp.trans hr, fun hp => hp.trans hr.symm⟩
  have havFinite : (avoiders n [1, 2] [(3, 3)] 3).Finite := by
    apply (words s).finite_toSet.subset
    intro p hp
    exact (hword p).mp hp.1
  letI : Fintype (avoiders n [1, 2] [(3, 3)] 3) := havFinite.fintype
  have hset : Avoiding s P ≃ (avoiders n [1, 2] [(3, 3)] 3) := {
    toFun p := ⟨p.1.1, ⟨(hword p.1.1).mpr p.1.2, p.2⟩⟩
    invFun p := ⟨⟨p.1, (hword p.1).mp p.2.1⟩, p.2.2⟩
    left_inv := by intro p; cases p; rfl
    right_inv := by intro p; cases p; rfl }
  have hP0 : ∀ p : Word s, (∀ f ∈ s, hat p.1 f ≠ f) → P p := by
    intro p h0 hc
    obtain ⟨a, b, f, hab, hbf, ha, hb, hf, hsub, hfix⟩ :=
      (D5.S3.Combinatorics.ArrowWilfCharacterization.contains_twelve_iff _).mp hc
    have hp : p.1.Perm s.toList := by
      simpa [words, List.mem_permutations] using p.2
    exact h0 f (Finset.mem_toList.mp (hp.mem_iff.mp hf)) hfix
  have hcardS : s.card = n := by
    simp [s, fullSupport, List.toFinset_card_of_nodup List.nodup_range']
  have hmSum : (∑ m : ↑s, Fintype.card (MaxFixedFiber s P m)) =
      ∑ m ∈ Finset.Icc 1 n,
        ∑ k ∈ Finset.range (n - m + 1),
          (n - m).choose k * (m + k - 1).choose (n - m) *
            numDerangements k := by
    have hsupport : s = Finset.Icc 1 n := by
      ext x
      simp only [s, fullSupport, List.mem_toFinset, List.mem_range', one_mul,
        Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi, rfl⟩
        omega
      · rintro ⟨h1, hn'⟩
        exact ⟨x - 1, by omega, by omega⟩
    have hpoint : ∀ m : ↑s,
        Fintype.card (MaxFixedFiber s P m) =
          ∑ k ∈ Finset.range (n - m.1 + 1),
            (n - m.1).choose k * (m.1 + k - 1).choose (n - m.1) *
              numDerangements k := by
      intro m
      have hm : 1 ≤ m.1 := by
        have hmem := m.2
        simp only [s, fullSupport, List.mem_toFinset, List.mem_range', one_mul] at hmem
        rcases hmem with ⟨i, hi, heq⟩
        omega
      have hEq := twelveFiberEquiv n m
      rw [← Fintype.card_congr hEq, Fintype.card_sigma]
      rw [Fin.sum_univ_eq_sum_range
        (fun k : ℕ => Fintype.card (TwelveData n m.1 k)) (n - m.1 + 1)]
      apply Finset.sum_congr rfl
      intro k hk
      have hcard := card_twelveData (n := n) (m := m.1) (k := k) hm
      rw [hcard]
      ring
    calc
      (∑ m : ↑s, Fintype.card (MaxFixedFiber s P m)) =
          ∑ m : ↑s, ∑ k ∈ Finset.range (n - m.1 + 1),
            (n - m.1).choose k * (m.1 + k - 1).choose (n - m.1) *
              numDerangements k := by simp_rw [hpoint]
      _ = ∑ m ∈ s, ∑ k ∈ Finset.range (n - m + 1),
            (n - m).choose k * (m + k - 1).choose (n - m) *
              numDerangements k := by
          let f : ℕ → ℕ := fun m =>
            ∑ k ∈ Finset.range (n - m + 1),
              (n - m).choose k * (m + k - 1).choose (n - m) *
                numDerangements k
          change (∑ m : ↑s, f m.1) = ∑ m ∈ s, f m
          rw [← Finset.sum_attach s f, Finset.attach_eq_univ]
      _ = _ := by rw [hsupport]
  calc
    (avoiders n [1, 2] [(3, 3)] 3).ncard = Fintype.card (Avoiding s P) := by
      rw [← Set.fintypeCard_eq_ncard]
      exact (Fintype.card_congr hset).symm
    _ = Fintype.card (NoFixed s) +
        ∑ m : ↑s, Fintype.card (MaxFixedFiber s P m) := by
      rw [Fintype.card_congr (maxFixedPartitionEquiv s P hP0),
        Fintype.card_sum, Fintype.card_sigma]
    _ = D5.S3.Combinatorics.ArrowWilfSums.F1 n := by
      rw [card_noFixed s, hcardS, hmSum]
      rfl

end

end D5.S3.Combinatorics.ArrowWilfTwelveFormula
