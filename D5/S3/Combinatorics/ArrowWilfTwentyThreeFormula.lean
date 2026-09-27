/- GID: D5/S3/Combinatorics/ArrowWilfTwentyThreeFormula
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfTwentyThreeFormula
   mirror-E: none(waiver:finite-cardinality-formula-for-the-twenty-three-arrow-pattern)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: The smallest-fixed-point partition gives Theorem 5.5's cardinality formula. -/

import D5.S3.Combinatorics.ArrowWilfTwentyThreeInverse
import D5.S3.Combinatorics.ArrowWilfPartition
import D5.S3.Combinatorics.ArrowWilfSums
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfTwentyThreeFormula

noncomputable section

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowWilfCountingCore
open D5.S3.Combinatorics.ArrowWilfTwelveCount
open D5.S3.Combinatorics.ArrowWilfTwentyThreeCount
open D5.S3.Combinatorics.ArrowWilfTwentyThreeInverse
open D5.S3.Combinatorics.ArrowWilfPartition

/-- Convert the fixed public avoidance set into words on the standard support. -/
def avoiderWordEquiv (n : ℕ) :
    ↑(avoiders n [2, 3] [(1, 1)] 3) ≃
      Avoiding (fullSupport n)
        (fun p => ¬ Contains [2, 3] [(1, 1)] 3 p.1) where
  toFun p := by
    refine ⟨⟨p.1, ?_⟩, p.2.2⟩
    change p.1 ∈ words (fullSupport n)
    rw [words, List.mem_toFinset, List.mem_permutations]
    apply p.2.1.trans
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_range'
    · exact (fullSupport n).nodup_toList
    · simp [fullSupport]
  invFun p := ⟨p.1.1, by
    constructor
    · have hp : p.1.1.Perm (fullSupport n).toList := by
        simpa [words, List.mem_permutations] using p.1.2
      apply hp.trans
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact (fullSupport n).nodup_toList
      · exact List.nodup_range'
      · simp [fullSupport]
    · exact p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p with | mk p hp => cases p; rfl

noncomputable instance (n : ℕ) :
    Fintype (Avoiding (fullSupport n)
      (fun p => ¬ Contains [2, 3] [(1, 1)] 3 p.1)) := by
  classical exact inferInstance

noncomputable instance (n : ℕ) : Fintype ↑(avoiders n [2, 3] [(1, 1)] 3) :=
  Fintype.ofEquiv _ (avoiderWordEquiv n).symm

/-- Theorem 5.5 for the fixed public avoidance set. -/
theorem card_twentyThree_avoiders (n : ℕ) (hn : 1 ≤ n) :
    (avoiders n [2, 3] [(1, 1)] 3).ncard =
      D5.S3.Combinatorics.ArrowWilfSums.F2 n := by
  classical
  let P : Word (fullSupport n) → Prop :=
    fun p => ¬ Contains [2, 3] [(1, 1)] 3 p.1
  have hP0 : ∀ p : Word (fullSupport n),
      (∀ f ∈ fullSupport n, hat p.1 f ≠ f) → P p := by
    intro p h0
    change ¬ Contains [2, 3] [(1, 1)] 3 p.1
    rw [contains_twenty_three_iff]
    rintro ⟨f, a, b, hfa, hab, hf, ha, hb, hsub, hfix⟩
    have hp : p.1.Perm (fullSupport n).toList := by
      simpa [words, List.mem_permutations] using p.2
    exact h0 f (Finset.mem_toList.mp (hp.mem_iff.mp hf)) hfix
  have hcount : Fintype.card (Avoiding (fullSupport n) P) =
      Fintype.card (NoFixed (fullSupport n)) +
        ∑ m : ↑(fullSupport n),
          Fintype.card (MinFixedFiber (fullSupport n) P m) := by
    rw [Fintype.card_congr (minFixedPartitionEquiv (fullSupport n) P hP0),
      Fintype.card_sum, Fintype.card_sigma]
  have hfullcard : (fullSupport n).card = n := by
    simp [fullSupport, List.toFinset_card_of_nodup List.nodup_range']
  have htop : Fintype.card (MinFixedFiber (fullSupport n) P
      ⟨n, by
        simp [fullSupport, List.mem_range']
        exact ⟨n - 1, by omega, by omega⟩⟩) = numDerangements (n - 1) := by
    change Fintype.card (TopAvoiders n) = _
    rw [Fintype.card_congr (topAvoidersEquiv n hn)]
    have hsub : ({n} : Finset ℕ) ⊆ fullSupport n := by
      intro g hg
      simp only [Finset.mem_singleton] at hg
      subst g
      simp [fullSupport, List.mem_range']
      exact ⟨n - 1, by omega, by omega⟩
    rw [card_exactFixed hsub, hfullcard]
    simp
  have hmiddle : ∀ m : ℕ, 1 ≤ m → m < n →
      Fintype.card (MinAvoiders n m) =
        ∑ r ∈ Finset.range m,
          (m - 1).choose r * (n - m + r - 1).choose r *
            r.factorial * numDerangements (m - 1 - r) := by
    intro m hm hmn
    rw [Fintype.card_congr (twentyThreeFamilyEquiv hm hmn).symm,
      Fintype.card_sigma]
    simp_rw [card_twentyThreeData]
    simpa using (Fin.sum_univ_eq_sum_range
      (fun r => (m - 1).choose r * (n - m + r - 1).choose r *
        r.factorial * numDerangements (m - 1 - r)) m)
  let inner (m : ℕ) : ℕ :=
    ∑ r ∈ Finset.range m,
      (m - 1).choose r * (n - m + r - 1).choose r *
        r.factorial * numDerangements (m - 1 - r)
  let f (m : ℕ) : ℕ := if m = n then numDerangements (n - 1) else inner m
  have hpoint (m : ℕ) (hm : m ∈ fullSupport n) :
      Fintype.card (MinFixedFiber (fullSupport n) P ⟨m, hm⟩) = f m := by
    have hm_bounds : 1 ≤ m ∧ m ≤ n := by
      simp only [fullSupport, List.mem_toFinset, List.mem_range', one_mul] at hm
      rcases hm with ⟨i, hi, heq⟩
      omega
    by_cases hmn : m = n
    · subst m
      simpa [f] using htop
    · have hlt : m < n := lt_of_le_of_ne hm_bounds.2 hmn
      change Fintype.card (MinAvoiders n m) = f m
      simpa [f, hmn, inner] using hmiddle m hm_bounds.1 hlt
  have hsupport : fullSupport n = Finset.Icc 1 n := by
    ext m
    simp only [fullSupport, List.mem_toFinset, List.mem_range', one_mul,
      Finset.mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · rintro ⟨hm, hmn⟩
      exact ⟨m - 1, by omega, by omega⟩
  have hsum :
      (∑ m : ↑(fullSupport n),
        Fintype.card (MinFixedFiber (fullSupport n) P m)) =
        numDerangements (n - 1) +
          ∑ m ∈ Finset.Icc 1 (n - 1), inner m := by
    calc
      (∑ m : ↑(fullSupport n),
          Fintype.card (MinFixedFiber (fullSupport n) P m)) =
          ∑ m ∈ (fullSupport n).attach, f m.1 := by
        rw [Finset.attach_eq_univ]
        apply Finset.sum_congr rfl
        intro m _
        exact hpoint m.1 m.2
      _ = ∑ m ∈ fullSupport n, f m := Finset.sum_attach _ _
      _ = ∑ m ∈ Finset.Icc 1 n, f m := by rw [hsupport]
      _ = (∑ m ∈ Finset.Icc 1 (n - 1), f m) + f n := by
        have hsplit := Finset.sum_Icc_succ_top
          (a := 1) (b := n - 1) (by omega : 1 ≤ n - 1 + 1) f
        have hn_eq : n - 1 + 1 = n := by omega
        rw [hn_eq] at hsplit
        exact hsplit
      _ = numDerangements (n - 1) +
          ∑ m ∈ Finset.Icc 1 (n - 1), inner m := by
        have hsmall : (∑ m ∈ Finset.Icc 1 (n - 1), f m) =
            ∑ m ∈ Finset.Icc 1 (n - 1), inner m := by
          apply Finset.sum_congr rfl
          intro m hm
          have hlt : m < n := by
            have := (Finset.mem_Icc.mp hm).2
            omega
          simp [f, ne_of_lt hlt]
        rw [hsmall]
        simp [f, add_comm]
  have hnc : Fintype.card (NoFixed (fullSupport n)) = numDerangements n := by
    rw [card_noFixed, hfullcard]
  calc
    (avoiders n [2, 3] [(1, 1)] 3).ncard =
        Fintype.card (Avoiding (fullSupport n) P) := by
      rw [← Set.fintypeCard_eq_ncard]
      exact Fintype.card_congr (avoiderWordEquiv n)
    _ = numDerangements n +
        (numDerangements (n - 1) +
          ∑ m ∈ Finset.Icc 1 (n - 1), inner m) := by
      rw [hcount, hnc, hsum]
    _ = D5.S3.Combinatorics.ArrowWilfSums.F2 n := by
      simp only [D5.S3.Combinatorics.ArrowWilfSums.F2, inner]
      omega

end

end D5.S3.Combinatorics.ArrowWilfTwentyThreeFormula
