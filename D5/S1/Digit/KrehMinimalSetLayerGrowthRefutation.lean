/- GID: D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation
   generality: G
   mirror-B: D5/B/S1/Digit/KrehMinimalSetLayerGrowthRefutation
   mirror-E: none(waiver:symbolic-refutation-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Defs, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: An infinite decimal-subsequence set has minimal-layer sizes 1, 2, 1, 1, forever. -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Card

namespace D5.S1.Digit.KrehMinimalSetLayerGrowthRefutation

/-- The printed decimal digits of `a` occur in order among those of `b`. -/
def digitSubseq (a b : ℕ) : Prop :=
  ((Nat.digits 10 a).reverse).Sublist ((Nat.digits 10 b).reverse)

/-- The elements of `M` minimal under decimal-digit subsequence. -/
def minimal (M : Set ℕ) : Set ℕ :=
  {a | a ∈ M ∧ ∀ b ∈ M, digitSubseq b a → b = a}

/-- Successively remove the current minimal elements. -/
def peel (M : Set ℕ) : ℕ → Set ℕ
  | 0 => M
  | k + 1 => peel M k \ minimal (peel M k)

/-- The number of minimal elements at layer `k`. -/
noncomputable def eta (M : Set ℕ) (k : ℕ) : ℕ :=
  (minimal (peel M k)).ncard

/-- The divergent-layer assertion from the second sentence of Kreh's Conjecture 18. -/
def claim : Prop :=
  ∀ M : Set ℕ, (∀ n ∈ M, 0 < n) → M.Infinite → eta M 0 < eta M 1 →
    ∀ B : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → B ≤ eta M k

private def u (j : ℕ) : ℕ := 110 * 10 ^ j

private def witness : Set ℕ :=
  {1, 10, 11} ∪ Set.range u

private def rest : Set ℕ :=
  {10, 11} ∪ Set.range u

private def tail (k : ℕ) : Set ℕ :=
  Set.range fun j => u (k + j)

/-- Kreh's asserted divergence fails for an infinite positive set whose layer
sizes begin `1, 2` and then remain `1`. -/
theorem result : ¬ claim := by
  have digits_u (j : ℕ) :
      (Nat.digits 10 (u j)).reverse = [1, 1, 0] ++ List.replicate j 0 := by
    rw [show u j = 10 ^ j * 110 by simp [u, Nat.mul_comm]]
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
  have u_lower (j : ℕ) : 110 ≤ u j := by
    have hp : 0 < 10 ^ j := pow_pos (by norm_num) _
    simp only [u]
    omega
  have digits_one : (Nat.digits 10 1).reverse = [1] := by norm_num
  have digits_ten : (Nat.digits 10 10).reverse = [1, 0] := by norm_num
  have digits_eleven : (Nat.digits 10 11).reverse = [1, 1] := by norm_num
  have one_ten : digitSubseq 1 10 := by
    simp [digitSubseq]
  have one_eleven : digitSubseq 1 11 := by
    simp [digitSubseq]
  have one_u (j : ℕ) : digitSubseq 1 (u j) := by
    simp [digitSubseq, digits_u]
  have ten_u (j : ℕ) : digitSubseq 10 (u j) := by
    simp [digitSubseq, digits_u]
  have eleven_u (j : ℕ) : digitSubseq 11 (u j) := by
    simp [digitSubseq, digits_u]
  have not_ten_eleven : ¬ digitSubseq 10 11 := by
    simp only [digitSubseq, digits_ten, digits_eleven]
    simp
  have not_eleven_ten : ¬ digitSubseq 11 10 := by
    simp only [digitSubseq, digits_eleven, digits_ten]
    simp
  have not_ten_one : ¬ digitSubseq 10 1 := by
    simp only [digitSubseq, digits_ten, digits_one]
    simp
  have not_eleven_one : ¬ digitSubseq 11 1 := by
    simp only [digitSubseq, digits_eleven, digits_one]
    simp
  have not_u_one (j : ℕ) : ¬ digitSubseq (u j) 1 := by
    intro h
    have hlen := List.Sublist.length_le h
    simp [digits_u] at hlen
  have not_u_ten (j : ℕ) : ¬ digitSubseq (u j) 10 := by
    intro h
    have hlen := List.Sublist.length_le h
    simp [digits_u] at hlen
  have not_u_eleven (j : ℕ) : ¬ digitSubseq (u j) 11 := by
    intro h
    have hlen := List.Sublist.length_le h
    simp [digits_u] at hlen
  have minimal_witness : minimal witness = {1} := by
    ext x
    constructor
    · rintro ⟨hx, hmin⟩
      rcases hx with (hx | ⟨j, rfl⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl | rfl | rfl)
        · simp
        · exact (by
            have := hmin 1 (by simp [witness]) one_ten
            omega)
        · exact (by
            have := hmin 1 (by simp [witness]) one_eleven
            omega)
      · have := hmin 1 (by simp [witness]) (one_u j)
        have := u_lower j
        simp
        omega
    · intro hx
      have hx1 : x = 1 := by simpa using hx
      subst x
      refine ⟨by simp [witness], ?_⟩
      intro b hb hsub
      rcases hb with (hb | ⟨j, rfl⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with (rfl | rfl | rfl)
        · rfl
        · exact (not_ten_one hsub).elim
        · exact (not_eleven_one hsub).elim
      · exact (not_u_one j hsub).elim
  have peel_one : peel witness 1 = rest := by
    change witness \ minimal witness = rest
    rw [minimal_witness]
    ext x
    constructor
    · rintro ⟨hx, hx1⟩
      rcases hx with (hx | hx)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl | rfl | rfl)
        · simp at hx1
        · simp [rest]
        · simp [rest]
      · exact Or.inr hx
    · intro hx
      constructor
      · rcases hx with (hx | hx)
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
      · intro hx1
        have hxone : x = 1 := by simpa using hx1
        subst x
        rcases hx with (hx | ⟨j, hj⟩)
        · simp at hx
        · have hu := u_lower j
          omega
  have minimal_rest : minimal rest = {10, 11} := by
    ext x
    constructor
    · rintro ⟨hx, hmin⟩
      rcases hx with (hx | ⟨j, rfl⟩)
      · simpa using hx
      · have := hmin 10 (by simp [rest]) (ten_u j)
        have := u_lower j
        simp
        omega
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl)
      · refine ⟨by simp [rest], ?_⟩
        intro b hb hsub
        rcases hb with (hb | ⟨j, rfl⟩)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with (rfl | rfl)
          · rfl
          · exact (not_eleven_ten hsub).elim
        · exact (not_u_ten j hsub).elim
      · refine ⟨by simp [rest], ?_⟩
        intro b hb hsub
        rcases hb with (hb | ⟨j, rfl⟩)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with (rfl | rfl)
          · exact (not_ten_eleven hsub).elim
          · rfl
        · exact (not_u_eleven j hsub).elim
  have minimal_tail (k : ℕ) : minimal (tail k) = {u k} := by
    ext x
    constructor
    · rintro ⟨⟨j, rfl⟩, hmin⟩
      have hsub : digitSubseq (u k) (u (k + j)) :=
        (u_order k (k + j)).mpr (by omega)
      have heq := hmin (u k) ⟨0, by simp⟩ hsub
      have hindex := u_injective heq
      have hj : j = 0 := by omega
      subst j
      simp
    · intro hx
      have hx' : x = u k := by simpa using hx
      subst x
      refine ⟨⟨0, by simp⟩, ?_⟩
      intro b hb hsub
      rcases hb with ⟨j, rfl⟩
      have hle := (u_order (k + j) k).mp hsub
      have hj : j = 0 := by omega
      subst j
      simp
  have tail_diff (k : ℕ) : tail k \ {u k} = tail (k + 1) := by
    ext x
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      cases j with
      | zero => simp at hj
      | succ j =>
          refine ⟨j, ?_⟩
          exact congrArg u (by omega)
    · rintro ⟨j, rfl⟩
      constructor
      · refine ⟨j + 1, ?_⟩
        exact congrArg u (by omega)
      · intro heq
        have hindex := u_injective (by simpa using heq)
        omega
  have peel_two : peel witness 2 = tail 0 := by
    rw [show (2 : ℕ) = 1 + 1 by omega, peel, peel_one, minimal_rest]
    ext x
    constructor
    · rintro ⟨hx, hnot⟩
      rcases hx with (hx | hx)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl | rfl) <;> simp at hnot
      · rcases hx with ⟨j, rfl⟩
        exact ⟨j, congrArg u (by omega)⟩
    · rintro ⟨j, rfl⟩
      constructor
      · exact Or.inr ⟨j, congrArg u (by omega)⟩
      · intro hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with (hu | hu)
        · have := u_lower (0 + j)
          omega
        · have := u_lower (0 + j)
          omega
  have peel_tail (k : ℕ) : peel witness (k + 2) = tail k := by
    induction k with
    | zero => simpa using peel_two
    | succ k ih =>
        rw [show k.succ + 2 = (k + 2) + 1 by omega, peel, ih, minimal_tail, tail_diff]
  have eta_zero : eta witness 0 = 1 := by
    rw [eta]
    change (minimal witness).ncard = 1
    rw [minimal_witness, Set.ncard_singleton]
  have eta_one : eta witness 1 = 2 := by
    rw [eta, peel_one, minimal_rest, Set.ncard_pair (by omega : (10 : ℕ) ≠ 11)]
  have eta_tail (k : ℕ) : eta witness (k + 2) = 1 := by
    rw [eta, peel_tail, minimal_tail, Set.ncard_singleton]
  have witness_positive : ∀ n ∈ witness, 0 < n := by
    intro n hn
    rcases hn with (hn | ⟨j, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with (rfl | rfl | rfl) <;> norm_num
    · have := u_lower j
      omega
  have witness_infinite : witness.Infinite := by
    apply Set.infinite_of_injective_forall_mem u_injective
    intro j
    exact Or.inr ⟨j, rfl⟩
  intro hclaim
  have hgrowth := hclaim witness witness_positive witness_infinite (by omega)
  rcases hgrowth 2 with ⟨N, hN⟩
  have hbound := hN (N + 2) (by omega)
  rw [eta_tail N] at hbound
  omega

#print axioms result

end D5.S1.Digit.KrehMinimalSetLayerGrowthRefutation
