/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Exchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed paired prime exchanges and fixed-grid lower counts. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy
import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)

private lemma mem_selected_union {J : Type*} [Fintype J]
    {P f : J → Finset ℕ} (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hf : ∀ j, f j ⊆ P j) {j : J} {p : ℕ} (hp : p ∈ P j) :
    p ∈ univ.biUnion f ↔ p ∈ f j := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    by_cases hij : i = j
    · simpa [hij] using hi
    · exact ((disjoint_left.mp (hd hij)) (hf i hi) hp).elim
  · intro h
    exact mem_biUnion.mpr ⟨j, mem_univ _, h⟩

/-- On one prime base, removing and adding the same prescribed number in
each paired bin realizes the full independent product of choices. -/
theorem paired_exchange {J : Type*} [Fintype J] [DecidableEq J]
    (base : Finset ℕ) (D R : J → Finset ℕ) (h : J → ℕ)
    (lo hi : J → ℝ) (x : ℝ)
    (hbase : ∀ p ∈ base, Nat.Prime p)
    (hD : ∀ j, D j ⊆ base) (hR : ∀ j, Disjoint (R j) base)
    (hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hRdisj : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hprime : ∀ j, ∀ p ∈ R j, Nat.Prime p)
    (hlo : ∀ j, ∀ p ∈ D j, lo j ≤ log (p : ℝ))
    (hhi : ∀ j, ∀ p ∈ R j, log (p : ℝ) ≤ hi j)
    (hx : 0 < x)
    (hslack : (∑ p ∈ base, log (p : ℝ)) + ∑ j, (h j : ℝ) * (hi j - lo j) < log x) :
    ∃ outputs : Finset ℕ,
      outputs.card = (∏ j, (D j).card.choose (h j) * (R j).card.choose (h j)) ∧
      ∀ n ∈ outputs, 0 < n ∧ Squarefree n ∧ ArithmeticFunction.cardDistinctFactors n =
        base.card ∧ (n : ℝ) < x := by
  classical
  let C := Fintype.piFinset (fun j => (D j).powersetCard (h j)) ×ˢ
    Fintype.piFinset (fun j => (R j).powersetCard (h j))
  let removed := fun f : (J → Finset ℕ) × (J → Finset ℕ) => univ.biUnion f.1
  let added := fun f : (J → Finset ℕ) × (J → Finset ℕ) => univ.biUnion f.2
  let support := fun f => (base \ removed f) ∪ added f
  let output := fun f => ∏ p ∈ support f, p
  have hdf {f} (hf : f ∈ C) (j : J) : f.1 j ⊆ D j ∧ (f.1 j).card = h j :=
    mem_powersetCard.mp (Fintype.mem_piFinset.mp (mem_product.mp hf).1 j)
  have hrf {f} (hf : f ∈ C) (j : J) : f.2 j ⊆ R j ∧ (f.2 j).card = h j :=
    mem_powersetCard.mp (Fintype.mem_piFinset.mp (mem_product.mp hf).2 j)
  have hrem {f} (hf : f ∈ C) : removed f ⊆ base := by
    intro p hp
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hp
    exact hD j ((hdf hf j).1 hj)
  have hadd {f} (hf : f ∈ C) : Disjoint (added f) base := by
    apply disjoint_left.mpr
    intro p hp hb
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hp
    exact disjoint_left.mp (hR j) ((hrf hf j).1 hj) hb
  have hunion {f} (hf : f ∈ C) : Disjoint (base \ removed f) (added f) :=
    (hadd hf).symm.mono_left sdiff_subset
  have hDpair {f} (hf : f ∈ C) : (univ : Finset J : Set J).PairwiseDisjoint f.1 :=
    fun i _ j _ hij => (hDdisj hij).mono (hdf hf i).1 (hdf hf j).1
  have hRpair {f} (hf : f ∈ C) : (univ : Finset J : Set J).PairwiseDisjoint f.2 :=
    fun i _ j _ hij => (hRdisj hij).mono (hrf hf i).1 (hrf hf j).1
  have hsupport {f} (hf : f ∈ C) : ∀ p ∈ support f, Nat.Prime p := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hbase p (mem_sdiff.mp hp).1
    · obtain ⟨j, _, hj⟩ := mem_biUnion.mp hp
      exact hprime j p ((hrf hf j).1 hj)
  have hrecover {f} (hf : f ∈ C) (j : J) :
      D j \ support f = f.1 j ∧ support f ∩ R j = f.2 j := by
    constructor
    · ext p
      constructor
      · intro hp
        obtain ⟨hd, hs⟩ := mem_sdiff.mp hp
        apply (mem_selected_union hDdisj (fun j => (hdf hf j).1) hd).mp
        exact not_not.mp fun hm => hs (mem_union_left _ (mem_sdiff.mpr ⟨hD j hd, hm⟩))
      · intro hp
        have hd := (hdf hf j).1 hp
        refine mem_sdiff.mpr ⟨hd, ?_⟩
        intro hs
        rcases mem_union.mp hs with hs | hs
        · exact (mem_sdiff.mp hs).2
            ((mem_selected_union hDdisj (fun j => (hdf hf j).1) hd).mpr hp)
        · exact disjoint_left.mp (hadd hf) hs (hD j hd)
    · ext p
      constructor
      · intro hp
        obtain ⟨hs, hr⟩ := mem_inter.mp hp
        apply (mem_selected_union hRdisj (fun j => (hrf hf j).1) hr).mp
        rcases mem_union.mp hs with hs | hs
        · exact (disjoint_left.mp (hR j) hr (mem_sdiff.mp hs).1).elim
        · exact hs
      · intro hp
        have hr := (hrf hf j).1 hp
        exact mem_inter.mpr ⟨mem_union_right _
          ((mem_selected_union hRdisj (fun j => (hrf hf j).1) hr).mpr hp), hr⟩
  have hinj : Set.InjOn output (C : Set ((J → Finset ℕ) × (J → Finset ℕ))) := by
    intro f hf g hg he
    have hs : support f = support g := by
      simpa only [output, Nat.primeFactors_prod (hsupport hf),
        Nat.primeFactors_prod (hsupport hg)] using congrArg Nat.primeFactors he
    exact Prod.ext (funext fun j => by rw [← (hrecover hf j).1, hs, (hrecover hg j).1])
      (funext fun j => by rw [← (hrecover hf j).2, hs, (hrecover hg j).2])
  refine ⟨C.image output, ?_, ?_⟩
  · simp only [card_image_of_injOn hinj, C, card_product, Fintype.card_piFinset,
      card_powersetCard, prod_mul_distrib]
  · intro n hn
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hn
    have hcard : (support f).card = base.card := by
      have hDcard : (removed f).card = ∑ j, h j := by
        rw [show removed f = univ.biUnion f.1 from rfl, card_biUnion (hDpair hf)]
        exact sum_congr rfl fun j _ => (hdf hf j).2
      have hRcard : (added f).card = ∑ j, h j := by
        rw [show added f = univ.biUnion f.2 from rfl, card_biUnion (hRpair hf)]
        exact sum_congr rfl fun j _ => (hrf hf j).2
      rw [show support f = (base \ removed f) ∪ added f from rfl,
        card_union_of_disjoint (hunion hf), card_sdiff_of_subset (hrem hf),
        hRcard, ← hDcard, Nat.sub_add_cancel (card_le_card (hrem hf))]
    have hlog :
        log (output f : ℝ) = (∑ p ∈ base, log (p : ℝ)) -
          (∑ j, ∑ p ∈ f.1 j, log (p : ℝ)) + (∑ j, ∑ p ∈ f.2 j, log (p : ℝ)) := by
      dsimp only [output]
      rw [Nat.cast_prod, log_prod (fun p hp => by exact_mod_cast (hsupport hf p hp).ne_zero)]
      dsimp only [support]
      rw [sum_union (hunion hf), sum_sdiff (hrem hf)]
      simp only [removed, added, sum_biUnion (hDpair hf), sum_biUnion (hRpair hf)]
    have hdonor : (∑ j, (h j : ℝ) * lo j) ≤ ∑ j, ∑ p ∈ f.1 j, log (p : ℝ) := by
      apply sum_le_sum
      intro j _
      calc
        (h j : ℝ) * lo j = ∑ _p ∈ f.1 j, lo j := by simp [(hdf hf j).2]
        _ ≤ _ := sum_le_sum fun p hp => hlo j p ((hdf hf j).1 hp)
    have hrecipient : (∑ j, ∑ p ∈ f.2 j, log (p : ℝ)) ≤ ∑ j, (h j : ℝ) * hi j := by
      apply sum_le_sum
      intro j _
      calc
        (∑ p ∈ f.2 j, log (p : ℝ)) ≤ ∑ _p ∈ f.2 j, hi j :=
          sum_le_sum fun p hp => hhi j p ((hrf hf j).1 hp)
        _ = _ := by simp [(hrf hf j).2]
    have hnpos : 0 < output f := prod_pos fun p hp => (hsupport hf p hp).pos
    refine ⟨hnpos, ?_, ?_, (log_lt_log_iff (by exact_mod_cast hnpos) hx).mp ?_⟩
    · apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        exact (hsupport hf p hp).irreducible.isRelPrime_iff_not_dvd.mpr
          (fun hd => hpq (((Nat.prime_dvd_prime_iff_eq (hsupport hf p hp)
            (hsupport hf q hq))).mp hd))
      · exact fun p hp => (hsupport hf p hp).squarefree
    · rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
        Nat.toFinset_factors, show output f = ∏ p ∈ support f, p from rfl,
        Nat.primeFactors_prod (hsupport hf), hcard]
    · rw [hlog]
      simp only [mul_sub, sum_sub_distrib] at hslack
      linarith

end D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
