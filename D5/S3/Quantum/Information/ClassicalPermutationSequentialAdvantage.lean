/- GID: D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two adaptive queries distinguish permutations beyond every parallel strategy. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Tactic.Linarith

/-! Randomized two-use strategies for finite classical permutation ensembles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage

open Convexity

/-- Average success with a random input pair and a decoder conditioned on both inputs
and both outputs. Every probability vector is allowed. -/
noncomputable def parallelSuccess {n m : ℕ} (p : StdSimplex ℝ (Fin m))
    (π : Fin m → Equiv.Perm (Fin n)) (q : StdSimplex ℝ (Fin n × Fin n))
    (δ : (Fin n × Fin n) → (Fin n × Fin n) → StdSimplex ℝ (Fin m)) : ℝ :=
  ∑ i, p.weights i * ∑ x, q.weights x * (δ x (π i x.1, π i x.2)).weights i

/-- Average success when the second random input depends on the first input and output,
and the randomized decoder sees the full two-query transcript. -/
noncomputable def sequentialSuccess {n m : ℕ} (p : StdSimplex ℝ (Fin m))
    (π : Fin m → Equiv.Perm (Fin n)) (q₁ : StdSimplex ℝ (Fin n))
    (q₂ : Fin n → Fin n → StdSimplex ℝ (Fin n))
    (δ : Fin n → Fin n → Fin n → Fin n → StdSimplex ℝ (Fin m)) : ℝ :=
  ∑ i, p.weights i * ∑ x₁, q₁.weights x₁ *
    ∑ x₂, (q₂ x₁ (π i x₁)).weights x₂ * (δ x₁ (π i x₁) x₂ (π i x₂)).weights i

/-- Some finite permutation ensemble admits a two-use sequential strategy whose success
strictly exceeds a common upper bound for all randomized two-use parallel strategies. -/
def claim : Prop :=
  ∃ (n m : ℕ) (p : StdSimplex ℝ (Fin m)) (π : Fin m → Equiv.Perm (Fin n))
    (q₁ : StdSimplex ℝ (Fin n)) (q₂ : Fin n → Fin n → StdSimplex ℝ (Fin n))
    (δ : Fin n → Fin n → Fin n → Fin n → StdSimplex ℝ (Fin m)) (c : ℝ),
    (∀ (q : StdSimplex ℝ (Fin n × Fin n))
      (d : (Fin n × Fin n) → (Fin n × Fin n) → StdSimplex ℝ (Fin m)),
      parallelSuccess p π q d ≤ c) ∧ c < sequentialSuccess p π q₁ q₂ δ

private def channels (i : Fin 4) : Equiv.Perm (Fin 6) :=
  if i = 0 then 1 else if i = 1 then Equiv.swap 2 3 else
    if i = 2 then Equiv.swap 0 1 else Equiv.swap 0 1 * Equiv.swap 4 5

private noncomputable def secondInput (_ y : Fin 6) : StdSimplex ℝ (Fin 6) :=
  .single (if y = 0 then 2 else 4)

private noncomputable def decoder (_ y₁ _ y₂ : Fin 6) : StdSimplex ℝ (Fin 4) :=
  .single (if y₁ = 0 then if y₂ = 2 then 0 else 1 else if y₂ = 4 then 2 else 3)

private lemma sequential_perfect :
    sequentialSuccess StdSimplex.barycenter channels (.single 0) secondInput decoder = 1 := by
  unfold sequentialSuccess secondInput decoder channels
  conv_lhs =>
    arg 2
    intro i
    rw [StdSimplex.weights_barycenter_apply]
  norm_num [Fin.sum_univ_succ,
    StdSimplex.weights_single, Finsupp.single_apply, Equiv.swap_apply_def]

private lemma transcript_collision (x : Fin 6 × Fin 6) :
    (channels 0 x.1, channels 0 x.2) = (channels 1 x.1, channels 1 x.2) ∨
    (channels 0 x.1, channels 0 x.2) = (channels 2 x.1, channels 2 x.2) ∨
    (channels 2 x.1, channels 2 x.2) = (channels 3 x.1, channels 3 x.2) := by
  revert x
  decide

private lemma two_weights_le_one {m : ℕ} (d : StdSimplex ℝ (Fin m))
    (a b : Fin m) (h : a ≠ b) : d.weights a + d.weights b ≤ 1 := by
  simpa only [d.total_of_fintype] using
    (Finset.add_le_sum (s := Finset.univ) (fun i _ => d.weights_nonneg i)
      (Finset.mem_univ a) (Finset.mem_univ b) h)

private lemma fixed_input_bound
    (δ : (Fin 6 × Fin 6) → (Fin 6 × Fin 6) → StdSimplex ℝ (Fin 4))
    (x : Fin 6 × Fin 6) :
    ∑ i, (δ x (channels i x.1, channels i x.2)).weights i ≤ 3 := by
  have h₀ := (δ x (channels 0 x.1, channels 0 x.2)).weights_apply_le_one 0
  have h₁ := (δ x (channels 1 x.1, channels 1 x.2)).weights_apply_le_one 1
  have h₂ := (δ x (channels 2 x.1, channels 2 x.2)).weights_apply_le_one 2
  have h₃ := (δ x (channels 3 x.1, channels 3 x.2)).weights_apply_le_one 3
  rw [Fin.sum_univ_four]
  rcases transcript_collision x with h | h | h
  · have hp := two_weights_le_one (δ x (channels 0 x.1, channels 0 x.2)) 0 1 (by decide)
    rw [h] at hp
    rw [h]
    linarith
  · have hp := two_weights_le_one (δ x (channels 0 x.1, channels 0 x.2)) 0 2 (by decide)
    rw [h] at hp
    rw [h]
    linarith
  · have hp := two_weights_le_one (δ x (channels 2 x.1, channels 2 x.2)) 2 3 (by decide)
    rw [h] at hp
    rw [h]
    linarith

private lemma parallel_bound (q : StdSimplex ℝ (Fin 6 × Fin 6))
    (δ : (Fin 6 × Fin 6) → (Fin 6 × Fin 6) → StdSimplex ℝ (Fin 4)) :
    parallelSuccess StdSimplex.barycenter channels q δ ≤ 3 / 4 := by
  calc
    parallelSuccess StdSimplex.barycenter channels q δ =
        ∑ x, q.weights x * (1 / 4 *
          ∑ i, (δ x (channels i x.1, channels i x.2)).weights i) := by
      unfold parallelSuccess
      conv_lhs =>
        arg 2
        intro i
        rw [StdSimplex.weights_barycenter_apply]
      simp only [Fintype.card_fin, Nat.cast_ofNat, one_div]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      exact mul_left_comm _ _ _
    _ ≤ ∑ x, q.weights x * (1 / 4 * 3) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (fixed_input_bound δ x) (by norm_num)) (q.weights_nonneg x)
    _ = 3 / 4 := by
      rw [← Finset.sum_mul, q.total_of_fintype]
      norm_num

/-- Sequential strategies can strictly outperform all parallel strategies for classical
permutation channels, even with only two uses of the same unknown channel. -/
theorem result : claim := by
  refine ⟨6, 4, StdSimplex.barycenter, channels, .single 0, secondInput, decoder, 3 / 4,
    parallel_bound, ?_⟩
  rw [sequential_perfect]
  norm_num

end D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage
