/- GID: D5/S3/FiniteGroups/Aliabadi/AbelianZeroSumPartition
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Aliabadi/AbelianZeroSumPartition
   mirror-E: none(waiver:pure-finite-abelian-theorem)
   anchors: []
   utility: none
   digest: Finite abelian EGZ extraction and exact zero-sum partitions retain the original labels. -/

import D5.S3.FiniteGroups.GordonFullSet
import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

universe u v w

namespace D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition

private def HasEGZ (G : Type u) [AddCommGroup G] : Prop :=
  ∀ {I : Type v} (a : I → G) (s : Finset I),
    2 * Nat.card G - 1 ≤ s.card →
      ∃ t ⊆ s, t.card = Nat.card G ∧ ∑ i ∈ t, a i = 0

/-- Greedy extraction is performed on the exact unused original support. -/
private theorem zero_sum_batches {A : Type u} [AddCommGroup A] {I : Type v}
    (n : ℕ) (hn : 0 < n) (a : I → A)
    (extract : ∀ s : Finset I, 2 * n - 1 ≤ s.card →
      ∃ t ⊆ s, t.card = n ∧ ∑ i ∈ t, a i = 0)
    (k : ℕ) (s : Finset I) (hs : (k + 1) * n - 1 ≤ s.card) :
    ∃ F : Finset (Finset I), F.card = k ∧
      (F : Set (Finset I)).Pairwise Disjoint ∧
      ∀ t ∈ F, t ⊆ s ∧ t.card = n ∧ ∑ i ∈ t, a i = 0 := by
  classical
  induction k generalizing s with
  | zero => exact ⟨∅, by simp⟩
  | succ k ih =>
    have htwo : 2 * n - 1 ≤ s.card := by
      have hle := Nat.mul_le_mul_right n (show 2 ≤ k + 1 + 1 by omega)
      omega
    obtain ⟨t, hts, htcard, htsum⟩ := extract s htwo
    have hrem : (s \ t).card = s.card - n := by
      rw [card_sdiff hts, htcard]
    have hbudget : (k + 1) * n - 1 ≤ (s \ t).card := by
      rw [hrem]
      rw [Nat.succ_mul] at hs
      have := card_le_card hts
      omega
    obtain ⟨F, hFcard, hFdisj, hF⟩ := ih (s \ t) hbudget
    have hdisj : ∀ b ∈ F, Disjoint t b := by
      intro b hb
      exact disjoint_sdiff.mono_right (hF b hb).1
    have hnot : t ∉ F := by
      intro ht
      have he : t = ∅ := disjoint_self.mp (hdisj t ht)
      rw [he, card_empty] at htcard
      omega
    refine ⟨insert t F, by rw [card_insert_of_notMem hnot, hFcard], ?_, ?_⟩
    · simp only [coe_insert, Set.pairwise_insert_of_symm, mem_coe, ne_eq]
      exact ⟨hFdisj, fun b hb _ => hdisj b hb⟩
    · intro b hb
      rcases mem_insert.mp hb with rfl | hb
      · exact ⟨hts, htcard, htsum⟩
      · exact ⟨(hF b hb).1.trans sdiff_subset, (hF b hb).2⟩

/-- The factor extractions act on one common family of disjoint labeled blocks. -/
private theorem product_extraction {A : Type u} {B : Type w}
    [AddCommGroup A] [Finite A] [AddCommGroup B] [Finite B]
    (hA : HasEGZ.{u,v} A) (hB : HasEGZ.{w,v} B) : HasEGZ.{max u w,v} (A × B) := by
  classical
  intro I a s hs
  have hn : 0 < Nat.card A := Nat.card_pos
  have hq : 0 < Nat.card B := Nat.card_pos
  rw [Nat.card_prod] at hs ⊢
  have hbudget : ((2 * Nat.card B - 1) + 1) * Nat.card A - 1 ≤ s.card := by
    have he : 2 * Nat.card B - 1 + 1 = 2 * Nat.card B := by omega
    rw [he]
    nlinarith
  obtain ⟨F, hFcard, hFdisj, hF⟩ := zero_sum_batches (Nat.card A) hn
    (fun i => (a i).1) (fun t ht => hA _ t ht) (2 * Nat.card B - 1) s hbudget
  obtain ⟨C, hCF, hCcard, hCsum⟩ := hB
    (fun t : Finset I => ∑ i ∈ t, (a i).2) F (by omega)
  have hCdisj := hFdisj.mono hCF
  refine ⟨C.biUnion id, biUnion_subset.mpr (fun t ht => (hF t (hCF ht)).1), ?_, ?_⟩
  · rw [card_biUnion hCdisj, sum_const_nat (fun t ht => (hF t (hCF ht)).2.1), hCcard]
    exact Nat.mul_comm _ _
  · apply Prod.ext
    · simp only [Prod.fst_sum, Prod.fst_zero]
      rw [sum_biUnion hCdisj]
      exact sum_eq_zero (fun t ht => (hF t (hCF ht)).2.2)
    · simp only [Prod.snd_sum, Prod.snd_zero]
      rw [sum_biUnion hCdisj]
      exact hCsum

private theorem chain_extraction (cs : List Gordon.CyclicFactor) :
    HasEGZ.{0,v} (Gordon.Chain cs) := by
  classical
  induction cs with
  | nil =>
    intro I a s hs
    have hs' : 1 ≤ s.card := by simpa [Gordon.Chain, Nat.card_eq_fintype_card] using hs
    obtain ⟨t, hts, ht⟩ := exists_subset_card_eq hs'
    exact ⟨t, hts, by simpa [Gordon.Chain, Nat.card_eq_fintype_card] using ht,
      Subsingleton.elim _ _⟩
  | cons c cs ih =>
    apply product_extraction (B := Gordon.Chain cs) ?_ ih
    intro I a s hs
    have hc : Nat.card (ZMod c.modulus) = c.modulus := by
      rw [Nat.card_eq_fintype_card, ZMod.card]
    simpa only [hc] using ZMod.erdos_ginzburg_ziv a (by simpa only [hc] using hs)

/-- Among at least `2 |G| - 1` labeled entries in a finite abelian group,
there are `|G|` original labels whose values sum to zero. Values may repeat. -/
theorem exists_zero_sum_card {G : Type u} [AddCommGroup G] [Finite G]
    {I : Type v} (a : I → G) (s : Finset I)
    (hs : 2 * Nat.card G - 1 ≤ s.card) :
    ∃ t ⊆ s, t.card = Nat.card G ∧ ∑ i ∈ t, a i = 0 := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨cs, ⟨e⟩⟩ := Gordon.finite_abelian_presentation G
  have hc := Nat.card_congr e.toEquiv
  obtain ⟨t, hts, htcard, htsum⟩ := chain_extraction cs (fun i => e (a i)) s (by omega)
  refine ⟨t, hts, htcard.trans hc.symm, e.injective ?_⟩
  simpa only [map_sum, map_zero] using htsum

/-- A zero-sum support of size `m |G|` splits into exactly `m` disjoint
zero-sum blocks of size `|G|`, indexed by `Fin m`, in the same label type. -/
theorem exists_zero_sum_partition {G : Type u} [AddCommGroup G] [Finite G]
    {I : Type v} (a : I → G) (s : Finset I) (m : ℕ)
    (hcard : s.card = m * Nat.card G) (hsum : ∑ i ∈ s, a i = 0) :
    ∃ B : Fin m → Finset I,
      (∀ j, B j ⊆ s) ∧ Pairwise (fun j k => Disjoint (B j) (B k)) ∧
      (Finset.univ.biUnion B = s) ∧
      (∀ j, (B j).card = Nat.card G) ∧ (∀ j, ∑ i ∈ B j, a i = 0) := by
  classical
  have hn : 0 < Nat.card G := Nat.card_pos
  induction m generalizing s with
  | zero =>
    have hs : s = ∅ := card_eq_zero.mp (by simpa using hcard)
    subst s
    exact ⟨Fin.elim0, by simp [Pairwise]⟩
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      refine ⟨fun _ => s, by simp, ?_, by simp, ?_, fun _ => hsum⟩
      · intro j k hjk
        exact (hjk (Subsingleton.elim _ _)).elim
      · intro j
        simpa using hcard
    · have hlarge : 2 * Nat.card G - 1 ≤ s.card := by
        rw [hcard, Nat.succ_mul]
        have hle := Nat.mul_le_mul_right (Nat.card G) (show 1 ≤ m by omega)
        omega
      obtain ⟨t, hts, htcard, htsum⟩ := exists_zero_sum_card a s hlarge
      have hremcard : (s \ t).card = m * Nat.card G := by
        rw [card_sdiff hts, htcard, hcard, Nat.succ_mul]
        omega
      have hremsum : ∑ i ∈ s \ t, a i = 0 := by
        have he := sum_sdiff hts (f := a)
        rw [hsum, htsum, add_zero] at he
        exact he
      obtain ⟨B, hBs, hBdisj, hBunion, hBcard, hBsum⟩ := ih (s \ t) hremcard hremsum
      refine ⟨Fin.cons t B, ?_, ?_, ?_, ?_, ?_⟩
      · intro j
        refine Fin.cases hts (fun k => (hBs k).trans sdiff_subset) j
      · intro j k
        refine Fin.cases ?_ (fun j => ?_) j
        · refine Fin.cases ?_ (fun k => ?_) k
          · intro hjk; exact (hjk rfl).elim
          · intro _; exact disjoint_sdiff.mono_right (hBs k)
        · refine Fin.cases ?_ (fun k => ?_) k
          · intro _; exact (disjoint_sdiff.mono_right (hBs j)).symm
          · intro hjk; exact hBdisj (fun he => hjk (congrArg Fin.succ he))
      · ext i
        simp only [mem_biUnion, mem_univ, true_and]
        constructor
        · rintro ⟨j, hj⟩
          exact Fin.cases (fun ht => hts ht)
            (fun k hk => sdiff_subset (hBs k hk)) j hj
        · intro hi
          by_cases hit : i ∈ t
          · exact ⟨0, hit⟩
          · have hir : i ∈ Finset.univ.biUnion B := by rw [hBunion]; exact mem_sdiff.mpr ⟨hi, hit⟩
            obtain ⟨j, _, hj⟩ := mem_biUnion.mp hir
            exact ⟨j.succ, hj⟩
      · intro j
        exact Fin.cases htcard hBcard j
      · intro j
        exact Fin.cases htsum hBsum j

end D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition
