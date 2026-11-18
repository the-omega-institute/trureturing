/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Lower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Lower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Injective squarefree prime selection and finite lower bounds for distinct-prime tails. -/

import D5.S3.Arith.Robin.Analytic.OmegaTailUpper
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper

private lemma prime_product_injective {S T : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (h : ∏ p ∈ S, p = ∏ p ∈ T, p) : S = T := by
  simpa only [Nat.primeFactors_prod hS, Nat.primeFactors_prod hT] using
    congrArg Nat.primeFactors h

private lemma omega_prime_product {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    ArithmeticFunction.cardDistinctFactors (∏ p ∈ S, p) = S.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors, Nat.primeFactors_prod hS]

/-- A family of distinct prime subsets with the required logarithmic cost gives
an injective family of integers in the literal distinct-prime tail. -/
private theorem prime_family_bound (lambda x : ℝ) (C : Finset (Finset ℕ))
    (hprime : ∀ S ∈ C, ∀ p ∈ S, Nat.Prime p)
    (hsize : ∀ S ∈ C, threshold lambda x < (S.card : ℝ))
    (hcost : ∀ S ∈ C, ∑ p ∈ S, log (p : ℝ) ≤ log x)
    (hx : 0 < x) : C.card ≤ tailCount lambda x := by
  classical
  let f : Finset ℕ → ℕ := fun S => ∏ p ∈ S, p
  have hinj : Set.InjOn f (C : Set (Finset ℕ)) := by
    intro S hS T hT h
    exact prime_product_injective (hprime S hS) (hprime T hT) h
  have hsub : C.image f ⊆ (Icc 1 ⌊x⌋₊).filter
      (fun n => threshold lambda x < (ArithmeticFunction.cardDistinctFactors n : ℝ)) := by
    intro n hn
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hn
    have hnpos : 0 < f S := prod_pos (fun p hp => (hprime S hS p hp).pos)
    have hnrpos : 0 < (f S : ℝ) := by exact_mod_cast hnpos
    have hlog : log (f S : ℝ) = ∑ p ∈ S, log (p : ℝ) := by
      dsimp [f]
      rw [Nat.cast_prod, log_prod]
      intro p hp
      exact_mod_cast (hprime S hS p hp).ne_zero
    have hnx : (f S : ℝ) ≤ x := (log_le_log_iff hnrpos hx).mp (by
      rw [hlog]
      exact hcost S hS)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hnpos, (Nat.le_floor_iff hx.le).mpr hnx⟩, ?_⟩
    simpa only [f, omega_prime_product (hprime S hS)] using hsize S hS
  simpa only [card_image_of_injOn hinj, tailCount] using card_le_card hsub

private lemma bin_union_inter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P f : ι → Finset ℕ) (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hf : ∀ j, f j ⊆ P j) (j : ι) :
    (univ.biUnion f) ∩ P j = f j := by
  ext p
  simp only [mem_inter, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hj⟩
    by_cases hij : i = j
    · simpa [hij] using hi
    · exact False.elim ((disjoint_left.mp (hP hij)) (hf i hi) hj)
  · intro hp
    exact ⟨⟨j, hp⟩, hf j hp⟩

/-- Independent selections of prescribed sizes from disjoint prime bins give a
product of binomial coefficients as a lower bound for the original tail count. -/
theorem multibox_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (k : ι → ℕ) (B : ι → ℝ) (lambda x : ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hprime : ∀ j, ∀ p ∈ P j, Nat.Prime p)
    (hB : ∀ j, 0 < B j) (hcap : ∀ j, ∀ p ∈ P j, (p : ℝ) ≤ B j)
    (hsize : threshold lambda x < ((∑ j, k j : ℕ) : ℝ))
    (hcost : ∑ j, (k j : ℝ) * log (B j) ≤ log x)
    (hx : 0 < x) :
    (∏ j, (P j).card.choose (k j)) ≤ tailCount lambda x := by
  classical
  let C := Fintype.piFinset (fun j => (P j).powersetCard (k j))
  let U : (ι → Finset ℕ) → Finset ℕ := fun f => univ.biUnion f
  have hsel {f : ι → Finset ℕ} (hf : f ∈ C) (j : ι) :
      f j ⊆ P j ∧ (f j).card = k j :=
    mem_powersetCard.mp (Fintype.mem_piFinset.mp hf j)
  have hpair {f : ι → Finset ℕ} (hf : f ∈ C) :
      Set.PairwiseDisjoint (univ : Finset ι) f := by
    intro i _ j _ hij
    exact (hdisj hij).mono (hsel hf i).1 (hsel hf j).1
  have hinj : Set.InjOn U (C : Set (ι → Finset ℕ)) := by
    intro f hf g hg hfg
    funext j
    calc
      f j = U f ∩ P j := (bin_union_inter P f hdisj (fun j => (hsel hf j).1) j).symm
      _ = U g ∩ P j := by rw [hfg]
      _ = g j := bin_union_inter P g hdisj (fun j => (hsel hg j).1) j
  have hcard {f : ι → Finset ℕ} (hf : f ∈ C) : (U f).card = ∑ j, k j := by
    dsimp [U]
    rw [card_biUnion (hpair hf)]
    exact sum_congr rfl (fun j _ => (hsel hf j).2)
  have hb := prime_family_bound lambda x (C.image U) ?_ ?_ ?_ hx
  · simpa only [card_image_of_injOn hinj, C, Fintype.card_piFinset,
      card_powersetCard] using hb
  · intro S hS p hp
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hS
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hp
    exact hprime j p ((hsel hf j).1 hj)
  · intro S hS
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hS
    simpa only [hcard hf] using hsize
  · intro S hS
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hS
    calc
      ∑ p ∈ U f, log (p : ℝ) = ∑ j, ∑ p ∈ f j, log (p : ℝ) :=
        sum_biUnion (hpair hf)
      _ ≤ ∑ j, (k j : ℝ) * log (B j) := by
        apply sum_le_sum
        intro j _
        calc
          ∑ p ∈ f j, log (p : ℝ) ≤ ∑ _p ∈ f j, log (B j) := by
            apply sum_le_sum
            intro p hp
            exact log_le_log (by exact_mod_cast (hprime j p ((hsel hf j).1 hp)).pos)
              (hcap j p ((hsel hf j).1 hp))
          _ = _ := by simp [(hsel hf j).2]
      _ ≤ log x := hcost

end D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
