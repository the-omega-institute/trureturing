/- GID: D5/S3/Combinatorics/SubsetSpectrum/EvenBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/EvenBridge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Powerset]
   utility: none
   digest: Even subset spectra determine total and full spectra in odd length. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubsetSpectrum

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- The index subsets of even cardinality. -/
def evenSubsets (s : Finset α) : Finset (Finset α) :=
  s.powerset.filter (fun t => Even t.card)

/-- The index subsets of odd cardinality. -/
def oddSubsets (s : Finset α) : Finset (Finset α) :=
  s.powerset.filter (fun t => Odd t.card)

/-- Every even index subset contributes one occurrence, even when values coincide. -/
def evenSubsetSums (s : Finset α) (b : α → ℝ) : Multiset ℝ :=
  (evenSubsets s).val.map (fun t => ∑ i ∈ t, b i)

/-- Every odd index subset contributes one occurrence. -/
def oddSubsetSums (s : Finset α) (b : α → ℝ) : Multiset ℝ :=
  (oddSubsets s).val.map (fun t => ∑ i ∈ t, b i)

/-- The occurrence spectrum over all index subsets. -/
def fullSubsetSums (s : Finset α) (b : α → ℝ) : Multiset ℝ :=
  s.powerset.val.map (fun t => ∑ i ∈ t, b i)

private lemma even_insert_sum (s : Finset α) (a : α) (ha : a ∉ s)
    (f : Finset α → ℝ) :
    (∑ t ∈ evenSubsets (insert a s), f t) =
      (∑ t ∈ evenSubsets s, f t) + (∑ t ∈ oddSubsets s, f (insert a t)) := by
  simp only [evenSubsets, oddSubsets, Finset.sum_filter]
  rw [Finset.sum_powerset_insert ha]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
  simp only [Finset.card_insert_of_notMem hat, Nat.even_add_one, Nat.not_even_iff_odd]

private lemma odd_insert_sum (s : Finset α) (a : α) (ha : a ∉ s)
    (f : Finset α → ℝ) :
    (∑ t ∈ oddSubsets (insert a s), f t) =
      (∑ t ∈ oddSubsets s, f t) + (∑ t ∈ evenSubsets s, f (insert a t)) := by
  simp only [evenSubsets, oddSubsets, Finset.sum_filter]
  rw [Finset.sum_powerset_insert ha]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
  simp only [Finset.card_insert_of_notMem hat, Nat.odd_add_one, Nat.not_odd_iff_even]

omit [DecidableEq α] in
private lemma parity_counts (s : Finset α) (hs : s.Nonempty) :
    (∑ _t ∈ evenSubsets s, (1 : ℝ)) = 2 ^ (s.card - 1) ∧
      (∑ _t ∈ oddSubsets s, (1 : ℝ)) = 2 ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    by_cases h : s = ∅
    · subst s
      have hp : ({a} : Finset α).powerset = {∅, {a}} := by
        simpa using (Finset.powerset_insert (∅ : Finset α) a)
      simp [evenSubsets, oddSubsets, hp, Finset.filter_insert, Finset.filter_singleton]
    · have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
      obtain ⟨he, ho⟩ := ih (Finset.nonempty_iff_ne_empty.mpr h)
      rw [even_insert_sum s a ha, odd_insert_sum s a ha]
      simp only [he, ho, Finset.card_insert_of_notMem ha]
      have hc : s.card + 1 - 1 = (s.card - 1) + 1 := by omega
      rw [hc, pow_succ]
      constructor <;> ring

omit [DecidableEq α] in
/-- The even incidence first moment counts each coordinate exactly 2^(|s|-2) times. -/
theorem even_first_moment (s : Finset α) (b : α → ℝ) (hs : 2 ≤ s.card) :
    (evenSubsetSums s b).sum = (2 : ℝ) ^ (s.card - 2) * ∑ i ∈ s, b i := by
  classical
  have moments : ∀ s : Finset α, 2 ≤ s.card →
      (∑ t ∈ evenSubsets s, ∑ i ∈ t, b i) =
        (2 : ℝ) ^ (s.card - 2) * ∑ i ∈ s, b i ∧
      (∑ t ∈ oddSubsets s, ∑ i ∈ t, b i) =
        (2 : ℝ) ^ (s.card - 2) * ∑ i ∈ s, b i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      intro hcard
      have hpos : s.Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_insert_of_notMem ha] at hcard
        omega)
      obtain ⟨hec, hoc⟩ := parity_counts s hpos
      have hinsert : ∀ t ∈ s.powerset, (∑ i ∈ insert a t, b i) = b a + ∑ i ∈ t, b i := by
        intro t ht
        exact Finset.sum_insert (fun h => ha (Finset.mem_powerset.mp ht h))
      have he : (∑ t ∈ evenSubsets (insert a s), ∑ i ∈ t, b i) =
          (∑ t ∈ evenSubsets s, ∑ i ∈ t, b i) +
            (∑ t ∈ oddSubsets s, ∑ i ∈ t, b i) + 2 ^ (s.card - 1) * b a := by
        rw [even_insert_sum s a ha]
        have hh : (∑ t ∈ oddSubsets s, ∑ i ∈ insert a t, b i) =
            (∑ t ∈ oddSubsets s, (b a + ∑ i ∈ t, b i)) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact hinsert t (Finset.mem_filter.mp ht).1
        rw [hh, Finset.sum_add_distrib]
        have hc : (∑ _t ∈ oddSubsets s, b a) = 2 ^ (s.card - 1) * b a := by
          simpa using congrArg (fun x : ℝ => x * b a) hoc
        rw [hc]
        ring
      have ho : (∑ t ∈ oddSubsets (insert a s), ∑ i ∈ t, b i) =
          (∑ t ∈ oddSubsets s, ∑ i ∈ t, b i) +
            (∑ t ∈ evenSubsets s, ∑ i ∈ t, b i) + 2 ^ (s.card - 1) * b a := by
        rw [odd_insert_sum s a ha]
        have hh : (∑ t ∈ evenSubsets s, ∑ i ∈ insert a t, b i) =
            (∑ t ∈ evenSubsets s, (b a + ∑ i ∈ t, b i)) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact hinsert t (Finset.mem_filter.mp ht).1
        rw [hh, Finset.sum_add_distrib]
        have hc : (∑ _t ∈ evenSubsets s, b a) = 2 ^ (s.card - 1) * b a := by
          simpa using congrArg (fun x : ℝ => x * b a) hec
        rw [hc]
        ring
      rw [he, ho, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      by_cases htwo : 2 ≤ s.card
      · obtain ⟨he', ho'⟩ := ih htwo
        rw [he', ho']
        have hpow : s.card - 1 = (s.card - 2) + 1 := by omega
        have hpow' : s.card + 1 - 2 = s.card - 1 := by omega
        rw [hpow', hpow, pow_succ]
        constructor <;> ring
      · have hc : s.card = 1 := by
          have := Finset.card_pos.mpr hpos
          omega
        obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
        have hp : ({x} : Finset α).powerset = {∅, {x}} := by
          simpa using (Finset.powerset_insert (∅ : Finset α) x)
        simp [evenSubsets, oddSubsets, hp, Finset.filter_insert, Finset.filter_singleton, add_comm]
  exact (moments s hs).1

omit [DecidableEq α] in
/-- Odd-length complementation identifies odd sums with reflected even sums,
with every occurrence retained. -/
theorem odd_spectrum_reflection [Fintype α] (b : α → ℝ)
    (hodd : Odd (Fintype.card α)) :
    oddSubsetSums Finset.univ b =
      (evenSubsetSums Finset.univ b).map (fun x => (∑ i, b i) - x) := by
  classical
  let e : Finset α ↪ Finset α := ⟨fun t => tᶜ, compl_injective⟩
  have hpar : ∀ t : Finset α, Even t.card ↔ Odd tᶜ.card := by
    intro t
    rw [Finset.card_compl, Nat.odd_sub (Finset.card_le_univ t)]
    simp [hodd]
  have hmap : (evenSubsets (Finset.univ : Finset α)).map e = oddSubsets Finset.univ := by
    ext t
    simp only [Finset.mem_map, evenSubsets, oddSubsets, Finset.mem_filter,
      Finset.mem_powerset, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hpar u).mp hu
    · intro ht
      refine ⟨tᶜ, ?_, by simp [e]⟩
      exact (hpar tᶜ).mpr (by simpa using ht)
  unfold oddSubsetSums evenSubsetSums
  rw [← hmap, Finset.map_val, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro t _
  dsimp [e]
  exact eq_sub_iff_add_eq.mpr (Finset.sum_compl_add_sum t b)

omit [DecidableEq α] in
private lemma even_odd_partition (s : Finset α) (b : α → ℝ) :
    fullSubsetSums s b = evenSubsetSums s b + oddSubsetSums s b := by
  unfold fullSubsetSums evenSubsetSums oddSubsetSums evenSubsets oddSubsets
  rw [← Multiset.map_add]
  congr 1
  change s.powerset.val = s.powerset.val.filter (fun t => Even t.card) +
    s.powerset.val.filter (fun t => Odd t.card)
  simpa only [Nat.not_even_iff_odd] using
    (Multiset.filter_add_not (fun t : Finset α => Even t.card) s.powerset.val).symm

/-- For odd length at least three, an even spectrum determines the coefficient
sum and the full occurrence spectrum. -/
theorem even_spectrum_determines_full {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m)
    (b c : Fin m → ℝ)
    (h : evenSubsetSums Finset.univ b = evenSubsetSums Finset.univ c) :
    (∑ i, b i) = (∑ i, c i) ∧
      fullSubsetSums Finset.univ b = fullSubsetSums Finset.univ c := by
  have hm' : 2 ≤ (Finset.univ : Finset (Fin m)).card := by simp; omega
  have hsum := congrArg Multiset.sum h
  rw [even_first_moment _ b hm', even_first_moment _ c hm'] at hsum
  have htotal : (∑ i, b i) = (∑ i, c i) :=
    mul_left_cancel₀ (by positivity : (2 : ℝ) ^
      ((Finset.univ : Finset (Fin m)).card - 2) ≠ 0) hsum
  refine ⟨htotal, ?_⟩
  rw [even_odd_partition, even_odd_partition, odd_spectrum_reflection b (by simpa),
    odd_spectrum_reflection c (by simpa), h, htotal]

end D5.S3.Combinatorics.SubsetSpectrum
