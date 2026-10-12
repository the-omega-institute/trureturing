/- GID: D5/S1/Words/Palindromes/ScatteredPalindromeMatching
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/ScatteredPalindromeMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convex endpoint matching bounds the sum of inner gaps. -/

/-
proof_shape: content
escape_witness: matching_bound
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15593
Audit targets: nestSum_succ and matching_bound.
Template gap: DependentFamily.realize lacks ArenaRef, original-statement
Implementation, Correspondence, VariationEvidence, Sensitivity and SourceSelection.
DTR reading: DTR-Unregistered (Observe) for nestSum_succ and matching_bound.
Direct frozen dependencies: none.
convex_shift: proof_shape: content;
  escape_witness: convex_shift
  consumers: convex_two
  Direct frozen dependencies: none.
convex_two: proof_shape: content;
  escape_witness: convex_two
  consumers: uncross_cost
  Direct frozen dependencies: none.
matchValid: proof_shape: definition;
  escape_witness: none
  consumers: shrink_valid, exchange_valid, matching_bound, word_match_valid
  Direct frozen dependencies: none.
nestSum: proof_shape: definition;
  escape_witness: none
  consumers: nestSum_succ, matching_bound, maxSP_telescoping, sp_residue_bound
  Direct frozen dependencies: none.
nestSum_succ: proof_shape: bind-only;
  escape_witness: none
  consumers: matching_bound, maxSP_telescoping
  Direct frozen dependencies: none.
uncross_cost: proof_shape: content;
  escape_witness: uncross_cost
  consumers: matching_bound
  Direct frozen dependencies: none.
shrink_valid: proof_shape: bind-only;
  escape_witness: none
  consumers: matching_bound
  Direct frozen dependencies: none.
exchange_valid: proof_shape: bind-only;
  escape_witness: none
  consumers: matching_bound
  Direct frozen dependencies: none.
matching_bound: proof_shape: content;
  escape_witness: matching_bound
  consumers: sp_residue_bound
  Direct frozen dependencies: none.
-/

import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace D5.S1.Words.Palindromes.ScatteredPalindromeMatching
open Finset

private theorem convex_shift (f : ℕ → ℕ) (hm : Monotone f)
    (hc : Monotone (fun n => f (n + 1) - f n)) {a b : ℕ} (hab : a ≤ b) (k : ℕ) :
    f (a + k) + f b ≤ f a + f (b + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hd := hc (Nat.add_le_add_right hab k)
    have ha := hm (Nat.le_succ (a + k))
    have hb := hm (Nat.le_succ (b + k))
    simp only [Nat.add_succ, Nat.add_zero] at *
    omega

private theorem convex_two (f : ℕ → ℕ) (hm : Monotone f)
    (hc : Monotone (fun n => f (n + 1) - f n)) {a b c d : ℕ}
    (hac : a ≤ c) (hbc : b ≤ c) (hs : a + b ≤ c + d) :
    f a + f b ≤ f c + f d := by
  by_cases hsum : a + b ≤ c
  · have h := convex_shift f hm hc (Nat.zero_le a) b
    simp only [Nat.zero_add] at h
    have h0 := hm (Nat.zero_le d)
    have h1 := hm hsum
    omega
  · have hsmall : a + b - c ≤ a := by omega
    have h := convex_shift f hm hc hsmall (c - a)
    have he1 : a + b - c + (c - a)=b := by omega
    have he2 : a + (c - a)=c := by omega
    rw [he1, he2] at h
    have hdd := hm (show a + b - c≤d by omega)
    omega

def matchValid {ι : Type*} (s : Finset ι) (l h : ι → ℕ) (n : ℕ) : Prop :=
  (∀ i ∈ s, l i < h i ∧ h i < n) ∧
  (∀ i ∈ s, ∀ j ∈ s, (l i = l j → i = j) ∧ (h i = h j → i = j) ∧ l i ≠ h j)

def nestSum (f : ℕ → ℕ) (n r : ℕ) : ℕ := ∑ i ∈ range r, f (n - 2 * (i + 1))

theorem nestSum_succ (f : ℕ → ℕ) (n r : ℕ) :
    nestSum f n (r + 1) = f (n - 2) + nestSum f (n - 2) r := by
  unfold nestSum
  rw [Finset.sum_range_succ', Nat.add_comm]
  simp only [Nat.zero_add, Nat.mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  omega

private theorem uncross_cost (f : ℕ → ℕ) (hm : Monotone f)
    (hc : Monotone (fun n => f (n + 1) - f n))
    {lo x y hi : ℕ} (hlx : lo < x) (hly : lo < y) (hxh : x < hi)
    (hyh : y < hi) :
    f (x - lo - 1) + f (hi - y - 1) ≤
      f (hi - lo - 1) + f (max x y - min x y - 1) := by
  apply convex_two f hm hc <;> omega

private theorem shrink_valid {ι : Type*} (s : Finset ι) (l h : ι → ℕ) (n : ℕ)
    (hv : matchValid s l h n)
    (hb : ∀ i ∈ s, 0 < l i ∧ h i + 1 < n) :
    matchValid s (fun i => l i - 1) (fun i => h i - 1) (n - 2) := by
  dsimp [matchValid]
  constructor
  · intro i hi
    obtain ⟨hli, hhi⟩ := hv.1 i hi
    obtain ⟨hlpos, hhbound⟩ := hb i hi
    constructor <;> omega
  · intro i hi j hj
    obtain ⟨hi0, hi1⟩ := hb i hi
    obtain ⟨hj0, hj1⟩ := hb j hj
    obtain ⟨hli, hhi⟩ := hv.1 i hi
    obtain ⟨hlj, hhj⟩ := hv.1 j hj
    obtain ⟨hll, hhh, hlh⟩ := hv.2 i hi j hj
    refine ⟨?_, ?_, ?_⟩
    · intro he; apply hll; omega
    · intro he; apply hhh; omega
    · intro he; apply hlh; omega

private theorem exchange_valid {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (l h : ι → ℕ) (n : ℕ) {a b : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hv : matchValid s l h n)
    (hmin : ∀ i ∈ s, l a ≤ l i) (hmax : ∀ i ∈ s, h i ≤ h b) :
    let L := fun i => if i = b then min (h a) (l b) else l i
    let H := fun i => if i = b then max (h a) (l b) else h i
    matchValid (s.erase a) L H n ∧
      ∀ i ∈ s.erase a, 0 < L i ∧ H i + 1 < n := by
  dsimp
  obtain ⟨haal, haah⟩ := hv.1 a ha
  obtain ⟨hbbl, hbbh⟩ := hv.1 b hb
  have hne : h a ≠ l b := (hv.2 b hb a ha).2.2.symm
  have hla : l a < l b := by
    have := hmin b hb
    have hne : l a ≠ l b := fun he => hab ((hv.2 a ha b hb).1 he)
    omega
  have hhb : h a < h b := by
    have := hmax a ha
    have hne : h a ≠ h b := fun he => hab ((hv.2 a ha b hb).2.1 he)
    omega
  have hstrict : ∀ i ∈ s.erase a, i ≠ b → l a < l i ∧ h i < h b := by
    intro i hi hib
    obtain ⟨hia, his⟩ := mem_erase.mp hi
    have hm := hmin i his
    have hx := hmax i his
    have hn1 : l a ≠ l i := fun he => hia ((hv.2 a ha i his).1 he).symm
    have hn2 : h i ≠ h b := fun he => hib ((hv.2 i his b hb).2.1 he)
    constructor <;> omega
  constructor
  · constructor
    · intro i hi
      obtain ⟨hia, his⟩ := mem_erase.mp hi
      by_cases hib : i = b
      · subst i; simp only [ite_true]; constructor <;> omega
      · simp only [if_neg hib]
        exact hv.1 i his
    · intro i hi j hj
      obtain ⟨hia, his⟩ := mem_erase.mp hi
      obtain ⟨hja, hjs⟩ := mem_erase.mp hj
      have disj : ∀ k ∈ s, k ≠ a → k ≠ b →
          l k ≠ h a ∧ h k ≠ h a ∧ l k ≠ l b ∧ h k ≠ l b := by
        intro k hk hka hkb
        refine ⟨(hv.2 k hk a ha).2.2, ?_, ?_, (hv.2 b hb k hk).2.2.symm⟩
        · exact fun he => hka ((hv.2 k hk a ha).2.1 he)
        · exact fun he => hkb ((hv.2 k hk b hb).1 he)
      by_cases hib : i = b <;> by_cases hjb : j = b
      · subst i; subst j
        simp only [ite_true]
        exact ⟨fun _ => trivial, fun _ => trivial, by omega⟩
      · subst i
        simp only [ite_true, if_neg hjb]
        obtain ⟨h1, h2, h3, h4⟩ := disj j hjs hja hjb
        refine ⟨?_, ?_, ?_⟩ <;> intro he <;> omega
      · subst j
        simp only [ite_true, if_neg hib]
        obtain ⟨h1, h2, h3, h4⟩ := disj i his hia hib
        refine ⟨?_, ?_, ?_⟩ <;> intro he <;> omega
      · simp only [if_neg hib, if_neg hjb]
        exact hv.2 i his j hjs
  · intro i hi
    by_cases hib : i = b
    · subst i; simp only [ite_true]; constructor <;> omega
    · simp only [if_neg hib]
      have hs := hstrict i hi hib
      constructor <;> omega

theorem matching_bound {ι : Type*} [DecidableEq ι]
    (f : ℕ → ℕ) (hm : Monotone f)
    (hc : Monotone (fun n => f (n + 1) - f n))
    (s : Finset ι) (l h : ι → ℕ) (n : ℕ)
    (hv : matchValid s l h n) :
    ∑ i ∈ s, f (h i - l i - 1) ≤ nestSum f n s.card := by
  induction s using Finset.strongInductionOn generalizing l h n with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image s l hs
      obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image s h hs
      have hsize : 2 ≤ n := by have := hv.1 a ha; omega
      have hcard : (s.erase a).card + 1=s.card := Finset.card_erase_add_one ha
      have hss : s.erase a ⊂ s := Finset.erase_ssubset ha
      rw [← hcard, nestSum_succ]
      by_cases hab : a = b
      · subst b
        have hbnd : ∀ i ∈ s.erase a, 0 < l i ∧ h i + 1<n := by
          intro i hi
          obtain ⟨hia, his⟩ := mem_erase.mp hi
          have hm := hmin i his
          have hx := hmax i his
          obtain ⟨hal, hah⟩ := hv.1 a ha
          have hn1 : l a ≠ l i := fun he => hia ((hv.2 a ha i his).1 he).symm
          have hn2 : h i ≠ h a := fun he => hia ((hv.2 i his a ha).2.1 he)
          constructor <;> omega
        have hve : matchValid (s.erase a) l h n := by
          exact ⟨fun i hi => hv.1 i (mem_of_mem_erase hi),
            fun i hi j hj => hv.2 i (mem_of_mem_erase hi) j (mem_of_mem_erase hj)⟩
        have hr := ih (s.erase a) hss (fun i => l i - 1) (fun i => h i - 1) (n - 2)
          (shrink_valid _ _ _ _ hve hbnd)
        have heq : (∑ i ∈ s.erase a, f ((h i - 1) - (l i - 1) - 1)) =
            ∑ i ∈ s.erase a, f (h i - l i - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have := hbnd i hi
          congr 1
          omega
        rw [heq] at hr
        have hterm := hm (show h a - l a - 1≤n - 2 by have := hv.1 a ha; omega)
        have he := Finset.sum_erase_add s (fun i => f (h i - l i - 1)) ha
        omega
      · let L := fun i => if i = b then min (h a) (l b) else l i
        let H := fun i => if i = b then max (h a) (l b) else h i
        obtain ⟨hve, hbnd⟩ := exchange_valid s l h n ha hb hab hv hmin hmax
        change matchValid (s.erase a) L H n at hve
        change (∀ i ∈ s.erase a, 0 < L i ∧ H i + 1 < n) at hbnd
        have hr := ih (s.erase a) hss (fun i => L i - 1) (fun i => H i - 1) (n - 2)
          (shrink_valid _ _ _ _ hve hbnd)
        have heq : (∑ i ∈ s.erase a, f ((H i - 1) - (L i - 1) - 1)) =
            ∑ i ∈ s.erase a, f (H i - L i - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have := hbnd i hi
          congr 1
          omega
        rw [heq] at hr
        have hla : l a<l b := by
          have hm := hmin b hb
          have hn : l a≠l b := fun he => hab ((hv.2 a ha b hb).1 he)
          omega
        have hhb : h a<h b := by
          have hx := hmax a ha
          have hn : h a≠h b := fun he => hab ((hv.2 a ha b hb).2.1 he)
          omega
        have hx := uncross_cost f hm hc (hv.1 a ha).1 hla hhb (hv.1 b hb).1
        have hterm := hm (show h b - l a - 1≤n - 2 by have := hv.1 b hb; omega)
        have hb' : b ∈ s.erase a := mem_erase.mpr ⟨Ne.symm hab, hb⟩
        have hs0 := Finset.sum_erase_add s (fun i => f (h i - l i - 1)) ha
        have hs1 := Finset.sum_erase_add (s.erase a) (fun i => f (h i - l i - 1)) hb'
        have hs2 := Finset.sum_erase_add (s.erase a) (fun i => f (H i - L i - 1)) hb'
        have heqrest : (∑ i ∈ (s.erase a).erase b, f (H i - L i - 1)) =
            ∑ i ∈ (s.erase a).erase b, f (h i - l i - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hib := (mem_erase.mp hi).1
          simp [L,H,hib]
        rw [heqrest] at hs2
        have hbval : f (H b - L b - 1) = f (max (h a) (l b) - min (h a) (l b) - 1) := by simp [L,H]
        rw [hbval] at hs2
        omega
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simp [nestSum]

end D5.S1.Words.Palindromes.ScatteredPalindromeMatching
