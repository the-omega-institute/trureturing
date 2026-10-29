/- GID: D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The largest strongly complementary permutation family has size two to the valuation. -/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! The matrix convention is `σ.permMatrix ℕ i j = 1 ↔ σ i = j`.
The definitions are Definitions 4.1 and 4.3 of Rajchel–Gąsiorowski–Życzkowski,
arXiv:1804.10715v2. Only the maximum-cardinality question is addressed.
Admission basis: external open-problem resolution, preregistration #23851. -/

namespace StronglyComplementaryPermutationMaximum

/-- Complementarity, with all four indices quantified as in Definition 4.1. -/
def IsComplementary {α : Type*} (p q : Matrix α α ℕ) : Prop :=
  ∀ i j h k, p i j = 1 → p h k = 1 → q i k = 1 → q h j = 1

/-- Complementarity together with disjoint support, as in Definition 4.3. -/
def IsStronglyComplementary {α : Type*} (p q : Matrix α α ℕ) : Prop :=
  IsComplementary p q ∧ ∀ i j, p i j = 1 → q i j = 0

/-- A matrix arising from a permutation of its indices. -/
def IsPermutationMatrix {α : Type*} [DecidableEq α] (p : Matrix α α ℕ) : Prop :=
  ∃ σ : Equiv.Perm α, p = σ.permMatrix ℕ

/-- The supremum of the attained cardinalities of finite, pairwise strongly
complementary sets of permutation matrices. -/
noncomputable def maxStronglyComplementary (n : ℕ) : ℕ :=
  sSup {k | ∃ s : Finset (Matrix (Fin n) (Fin n) ℕ),
    (∀ p ∈ s, IsPermutationMatrix p) ∧ s.Pairwise IsStronglyComplementary ∧ s.card = k}

/-- The cardinality clause of the question in arXiv:1804.10715v2. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → maxStronglyComplementary n = 2 ^ padicValNat 2 n

private lemma entry_one {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (i j : α) :
    σ.permMatrix ℕ i j = 1 ↔ σ i = j := by
  sorry

private lemma entry_zero {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (i j : α) :
    σ.permMatrix ℕ i j = 0 ↔ σ i ≠ j := by
  sorry

private lemma matrix_injective {α : Type*} [DecidableEq α] :
    Function.Injective (fun σ : Equiv.Perm α => σ.permMatrix ℕ) := by
  sorry

private lemma complementary_iff {α : Type*} [DecidableEq α] (σ τ : Equiv.Perm α) :
    IsComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ) ↔
      Function.Involutive (σ⁻¹ * τ) := by
  sorry

private lemma strong_iff {α : Type*} [DecidableEq α] (σ τ : Equiv.Perm α) :
    IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ) ↔
      Function.Involutive (σ⁻¹ * τ) ∧ ∀ x, (σ⁻¹ * τ) x ≠ x := by
  sorry

private lemma row_relabelling {α : Type*} [DecidableEq α] (ρ σ τ : Equiv.Perm α) :
    IsStronglyComplementary ((ρ⁻¹ * σ).permMatrix ℕ) ((ρ⁻¹ * τ).permMatrix ℕ) ↔
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ) := by
  sorry

private lemma lift_family {n : ℕ} (s : Finset (Matrix (Fin n) (Fin n) ℕ))
    (hs : ∀ p ∈ s, IsPermutationMatrix p) :
    ∃ t : Finset (Equiv.Perm (Fin n)),
      t.image (fun σ => σ.permMatrix ℕ) = s ∧ t.card = s.card := by
  sorry

private lemma normalize_family {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (hs : s.Pairwise (fun σ τ =>
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))) (hne : s.Nonempty) :
    ∃ t : Finset (Equiv.Perm (Fin n)), t.card = s.card ∧ 1 ∈ t ∧
      t.Pairwise (fun σ τ =>
        IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ)) := by
  sorry

private lemma normalized_involutions {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (h1 : 1 ∈ s) (hs : s.Pairwise (fun σ τ =>
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))) :
    (∀ σ ∈ s, σ ^ 2 = 1) ∧ (s : Set (Equiv.Perm (Fin n))).Pairwise Commute := by
  sorry

private lemma closure_exponent_two {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (hs : ∀ σ ∈ s, σ ^ 2 = 1)
    (hc : (s : Set (Equiv.Perm (Fin n))).Pairwise Commute) :
    ∀ g ∈ Subgroup.closure (s : Set (Equiv.Perm (Fin n))), g ^ 2 = 1 := by
  sorry

private lemma orbit_evaluation_bound {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (hs : s.Pairwise (fun σ τ =>
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))) (x : Fin n) :
    s.card ≤ Nat.card (MulAction.orbit (Subgroup.closure (s : Set _)) x) := by
  sorry

private lemma least_orbit_divisor {n : ℕ} (hn : 1 ≤ n)
    (g : Subgroup (Equiv.Perm (Fin n))) (hg : IsPGroup 2 g) :
    ∃ x : Fin n, ∃ a : ℕ, Nat.card (MulAction.orbit g x) = 2 ^ a ∧ 2 ^ a ∣ n := by
  sorry

private lemma permutation_family_upper {n : ℕ} (hn : 1 ≤ n)
    (s : Finset (Equiv.Perm (Fin n))) (hs : s.Pairwise (fun σ τ =>
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))) :
    s.card ≤ 2 ^ padicValNat 2 n := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨t, hcard, h1, ht⟩ := normalize_family s hs hne
    obtain ⟨hi, hc⟩ := normalized_involutions t h1 ht
    have he := closure_exponent_two t hi hc
    have hg : IsPGroup 2 (Subgroup.closure (t : Set _)) := by
      intro g
      refine ⟨1, ?_⟩
      apply Subtype.ext
      exact he g g.property
    obtain ⟨x, a, ha, hd⟩ := least_orbit_divisor hn (Subgroup.closure (t : Set _)) hg
    have hb := orbit_evaluation_bound t ht x
    rw [ha, hcard] at hb
    exact hb.trans (Nat.pow_le_pow_right (by omega)
      ((padicValNat_dvd_iff_le (by omega)).mp hd))
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [this, Finset.card_empty, Nat.zero_le]

private lemma matrix_family_upper {n : ℕ} (hn : 1 ≤ n)
    (s : Finset (Matrix (Fin n) (Fin n) ℕ)) (hp : ∀ p ∈ s, IsPermutationMatrix p)
    (hs : s.Pairwise IsStronglyComplementary) : s.card ≤ 2 ^ padicValNat 2 n := by
  classical
  obtain ⟨t, ht, hc⟩ := lift_family s hp
  rw [← hc]
  apply permutation_family_upper hn t
  intro σ hσ τ hτ hne
  apply hs
  · rw [← ht]; exact Finset.mem_image_of_mem _ hσ
  · rw [← ht]; exact Finset.mem_image_of_mem _ hτ
  · exact fun h => hne (matrix_injective h)

private lemma two_adic_decomposition {n : ℕ} (hn : 1 ≤ n) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ n = 2 ^ padicValNat 2 n * m := by
  sorry

private lemma elementary_translation_family {n a m : ℕ} (hm : 0 < m)
    (e : Fin n ≃ ((Fin a → ZMod 2) × Fin m)) :
    ∃ s : Finset (Equiv.Perm (Fin n)), s.card = 2 ^ a ∧
      s.Pairwise (fun σ τ =>
        IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ)) := by
  sorry

private lemma matrix_family_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset (Matrix (Fin n) (Fin n) ℕ),
      (∀ p ∈ s, IsPermutationMatrix p) ∧ s.Pairwise IsStronglyComplementary ∧
        s.card = 2 ^ padicValNat 2 n := by
  classical
  obtain ⟨m, hm, _, hnfac⟩ := two_adic_decomposition hn
  have hcard : Fintype.card (Fin n) =
      Fintype.card ((Fin (padicValNat 2 n) → ZMod 2) × Fin m) := by
    simpa only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      using hnfac
  obtain ⟨t, ht, hp⟩ := elementary_translation_family hm (Fintype.equivOfCardEq hcard)
  refine ⟨t.image (fun σ => σ.permMatrix ℕ), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨σ, rfl⟩
  · intro p hp q hq hne
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hq
    exact hp hσ hτ (fun h => hne (congrArg (fun σ => σ.permMatrix ℕ) h))
  · rw [Finset.card_image_of_injective _ matrix_injective, ht]

/-- The maximal size is the largest power of two dividing the dimension. -/
theorem result : claim := by
  intro n hn
  change sSup {k | ∃ s : Finset (Matrix (Fin n) (Fin n) ℕ),
    (∀ p ∈ s, IsPermutationMatrix p) ∧ s.Pairwise IsStronglyComplementary ∧ s.card = k} = _
  obtain ⟨s, hp, hs, hc⟩ := matrix_family_lower hn
  have hb : ∀ k ∈ {k | ∃ t : Finset (Matrix (Fin n) (Fin n) ℕ),
      (∀ p ∈ t, IsPermutationMatrix p) ∧ t.Pairwise IsStronglyComplementary ∧
        t.card = k}, k ≤ 2 ^ padicValNat 2 n := by
    rintro k ⟨t, ht, htcomp, rfl⟩
    exact matrix_family_upper hn t ht htcomp
  apply le_antisymm
  · exact csSup_le ⟨_, s, hp, hs, hc⟩ hb
  · exact le_csSup ⟨_, hb⟩ ⟨s, hp, hs, hc⟩

end StronglyComplementaryPermutationMaximum
