/- GID: D5/S1/Digit/KrehMinimalSetCountabilityRefutation
   generality: G
   mirror-B: D5/B/S1/Digit/KrehMinimalSetCountabilityRefutation
   mirror-E: none(waiver:symbolic-refutation-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Set.Countable]
   utility: none
   digest: Uncountably many infinite positive sets have first minimal-layer sizes 2 and 1. -/

import D5.S1.Digit.KrehMinimalSetLayerGrowthRefutation
import Mathlib.Data.Set.Countable

namespace D5.S1.Digit.KrehMinimalSetCountabilityRefutation

open D5.S1.Digit.KrehMinimalSetLayerGrowthRefutation

/-- The countability assertion from the first sentence of Kreh's Conjecture 18. -/
def claim : Prop :=
  Set.Countable {M : Set ℕ |
    (∀ n ∈ M, 0 < n) ∧ M.Infinite ∧ eta M 1 ≤ eta M 0}

/-- A powerset-indexed family of infinite positive sets, each with first two
minimal layers of sizes `2` and `1`, refutes the countability assertion. -/
theorem result : ¬ claim := by
  classical
  let u : ℕ → ℕ := fun j => 16 * 10 ^ j
  let T : Set ℕ → Set ℕ := fun A =>
    {x | ∃ n, x = u (2 * n) ∨ (n ∈ A ∧ x = u (2 * n + 1))}
  let F : Set ℕ → Set ℕ := fun A => {1, 6} ∪ T A
  have digits_u (j : ℕ) :
      (Nat.digits 10 (u j)).reverse = [1, 6] ++ List.replicate j 0 := by
    rw [show u j = 10 ^ j * 16 by simp [u, Nat.mul_comm]]
    rw [Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
    norm_num
  have u_order (i j : ℕ) : digitSubseq (u i) (u j) ↔ i ≤ j := by
    simp only [digitSubseq, digits_u]
    simp
  have u_injective : Function.Injective u := by
    intro i j hij
    apply Nat.le_antisymm
    · exact (u_order i j).mp (hij ▸ List.Sublist.refl _)
    · exact (u_order j i).mp (hij ▸ List.Sublist.refl _)
  have u_lower (j : ℕ) : 16 ≤ u j := by
    have hp : 0 < 10 ^ j := pow_pos (by norm_num) _
    dsimp [u]
    omega
  have one_u (j : ℕ) : digitSubseq 1 (u j) := by
    simp [digitSubseq, digits_u]
  have not_u_one (j : ℕ) : ¬ digitSubseq (u j) 1 := by
    intro h
    have hlen := List.Sublist.length_le h
    simp [digits_u] at hlen
  have not_u_six (j : ℕ) : ¬ digitSubseq (u j) 6 := by
    intro h
    have hlen := List.Sublist.length_le h
    simp [digits_u] at hlen
  have t_in_range (A : Set ℕ) : T A ⊆ Set.range u := by
    rintro x ⟨n, hx | ⟨_, hx⟩⟩
    · exact ⟨2 * n, hx.symm⟩
    · exact ⟨2 * n + 1, hx.symm⟩
  have zero_mem (A : Set ℕ) : u 0 ∈ T A :=
    ⟨0, Or.inl rfl⟩
  have minF (A : Set ℕ) : minimal (F A) = {1, 6} := by
    ext x
    constructor
    · rintro ⟨hx, hmin⟩
      rcases hx with hx | hx
      · exact hx
      · obtain ⟨j, rfl⟩ := t_in_range A hx
        have he := hmin 1 (by simp [F]) (one_u j)
        have hl := u_lower j
        omega
    · intro hx
      refine ⟨Or.inl hx, ?_⟩
      intro b hb hsub
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rcases hb with hb | hb
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with rfl | rfl
          · rfl
          · exfalso
            simp [digitSubseq] at hsub
        · obtain ⟨j, rfl⟩ := t_in_range A hb
          exact (not_u_one j hsub).elim
      · rcases hb with hb | hb
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with rfl | rfl
          · exfalso
            simp [digitSubseq] at hsub
          · rfl
        · obtain ⟨j, rfl⟩ := t_in_range A hb
          exact (not_u_six j hsub).elim
  have peel_one (A : Set ℕ) : peel (F A) 1 = T A := by
    change F A \ minimal (F A) = T A
    rw [minF]
    ext x
    constructor
    · rintro ⟨hx, hnot⟩
      rcases hx with hx | hx
      · exact (hnot hx).elim
      · exact hx
    · intro hx
      refine ⟨Or.inr hx, ?_⟩
      obtain ⟨j, rfl⟩ := t_in_range A hx
      have hl := u_lower j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
  have minT (A : Set ℕ) : minimal (T A) = {u 0} := by
    ext x
    constructor
    · rintro ⟨hx, hmin⟩
      obtain ⟨j, rfl⟩ := t_in_range A hx
      exact (hmin (u 0) (zero_mem A) ((u_order 0 j).mpr (Nat.zero_le j))).symm
    · intro hx
      have he : x = u 0 := hx
      subst x
      refine ⟨zero_mem A, ?_⟩
      intro b hb hsub
      obtain ⟨j, rfl⟩ := t_in_range A hb
      have hj : j = 0 := Nat.eq_zero_of_le_zero ((u_order j 0).mp hsub)
      subst j
      rfl
  have eta_zero (A : Set ℕ) : eta (F A) 0 = 2 := by
    change (minimal (F A)).ncard = 2
    rw [minF, Set.ncard_pair (by decide : (1 : ℕ) ≠ 6)]
  have eta_one (A : Set ℕ) : eta (F A) 1 = 1 := by
    rw [eta, peel_one, minT, Set.ncard_singleton]
  have positive (A : Set ℕ) : ∀ n ∈ F A, 0 < n := by
    intro n hn
    rcases hn with hn | hn
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl <;> norm_num
    · obtain ⟨j, rfl⟩ := t_in_range A hn
      have hl := u_lower j
      omega
  have infinite (A : Set ℕ) : (F A).Infinite := by
    have hi : Function.Injective (fun n => u (2 * n)) := by
      intro i j h
      have he := u_injective h
      omega
    apply Set.infinite_of_injective_forall_mem hi
    intro n
    exact Or.inr ⟨n, Or.inl rfl⟩
  have odd_mem (A : Set ℕ) (j : ℕ) : u (2 * j + 1) ∈ F A ↔ j ∈ A := by
    constructor
    · intro hx
      rcases hx with hx | ⟨n, he | ⟨hn, he⟩⟩
      · have hl := u_lower (2 * j + 1)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        omega
      · have hi := u_injective he
        omega
      · have hi := u_injective he
        have hj : j = n := by omega
        simpa [hj] using hn
    · intro hj
      exact Or.inr ⟨j, Or.inr ⟨hj, rfl⟩⟩
  have F_injective : Function.Injective F := by
    intro A B h
    ext j
    rw [← odd_mem A j, ← odd_mem B j, h]
  intro hcount
  obtain ⟨encode, hencode⟩ := Set.countable_iff_exists_injective.mp hcount
  let E : Set ℕ → {M : Set ℕ |
      (∀ n ∈ M, 0 < n) ∧ M.Infinite ∧ eta M 1 ≤ eta M 0} :=
    fun A => ⟨F A, positive A, infinite A, by rw [eta_one, eta_zero]; omega⟩
  have hE : Function.Injective E := by
    intro A B h
    apply F_injective
    exact congrArg Subtype.val h
  exact Function.cantor_injective (fun A => encode (E A)) (hencode.comp hE)

#print axioms result

end D5.S1.Digit.KrehMinimalSetCountabilityRefutation
