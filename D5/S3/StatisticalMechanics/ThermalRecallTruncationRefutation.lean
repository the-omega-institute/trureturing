/- GID: D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/ThermalRecallTruncationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.claim; result=D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.result; claim=D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.claim
   digest: Removing intermediate memory resets can increase permutation approximation error. -/

import D5.S3.Combinatorics.Permutation.AdamsonFlahertyPotapovSpirakisTwoSwapGreedy
import D5.S3.Entropy.Mixing.MixtureEntropyBracket
import D5.S3.TotalVariation.CycleSingleCutMinimax

/-! Finite thermalisation protocols with and without intermediate memory resets. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.ThermalRecallTruncationRefutation

open scoped BigOperators
open D5.S3.Combinatorics.Permutation.AdamsonFlahertyPotapovSpirakisTwoSwapGreedy
  (applySwaps)
open D5.S3.Divergence.ChainRule (marginal)
open D5.S3.Entropy.Mixing.MixtureEntropyBracket (mixtureJoint)
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.CycleSingleCutMinimax (Probability)

noncomputable section

/-- Two-level thermalisation at infinite temperature. -/
def average {d n : ℕ} (a b : Fin d × Fin n)
    (v : Fin d × Fin n → ℝ) : Fin d × Fin n → ℝ :=
  fun x => if x = a ∨ x = b then (v a + v b) / 2 else v x

/-- Rounds increase the first memory index; steps increase the second memory index. -/
def block {d : ℕ} (n : ℕ) (i j : Fin d)
    (v : Fin d × Fin n → ℝ) : Fin d × Fin n → ℝ :=
  (List.finRange n).foldl
    (fun u k => (List.finRange n).foldl (fun u l => average (i, k) (j, l) u) u) v

/-- Couple a system population vector to a uniform memory. -/
def joint {d : ℕ} (n : ℕ) (p : Fin d → ℝ) : Fin d × Fin n → ℝ :=
  mixtureJoint p (fun (_ : Fin d) (_ : Fin n) => (n : ℝ)⁻¹)

/-- Reset the memory to its uniform infinite-temperature state. -/
def reset {d n : ℕ} (v : Fin d × Fin n → ℝ) : Fin d × Fin n → ℝ :=
  joint n (marginal v)

/-- Composite protocol with the intermediate resets removed, read on the system. -/
def truncatedOutput {d : ℕ} (n : ℕ) (p : Fin d → ℝ)
    (w : List (Fin d × Fin d)) : Fin d → ℝ :=
  marginal (w.foldl (fun v z => block n z.1 z.2 v) (joint n p))

/-- Composite protocol with a memory reset after every block. -/
def resetOutput {d : ℕ} (n : ℕ) (p : Fin d → ℝ)
    (w : List (Fin d × Fin d)) : Fin d → ℝ :=
  marginal (w.foldl (fun v z => reset (block n z.1 z.2 v)) (joint n p))

/-- Each swap is adjacent in current population order and increases inversion length. -/
def IsReducedNeighbourWord {d : ℕ} (p : Fin d → ℝ) : List (Fin d × Fin d) → Prop :=
  fun w => ∀ (n : ℕ) (hn : n < w.length),
    let z := w[n]
    let r := applySwaps p (w.take n)
    z.1 < z.2 ∧ r z.2 < r z.1 ∧ ∀ c, ¬ (r z.2 < r c ∧ r c < r z.1)

/-- Improved convergence of the truncated protocol for every reduced neighbour word. -/
def claim : Prop :=
  ∀ (d n : ℕ) (p : Fin d → ℝ) (w : List (Fin d × Fin d)),
    0 < n → (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → StrictAnti p →
    IsReducedNeighbourWord p w →
    totalVariation (applySwaps p w) (truncatedOutput n p w) ≤
      totalVariation (applySwaps p w) (resetOutput n p w)

private def p : Fin 4 → ℝ := ![1/2, 1/4, 2/9, 1/36]

private def w : List (Fin 4 × Fin 4) := [(0, 1), (2, 3), (0, 3)]

private theorem instance_hypotheses :
    Probability p ∧ StrictAnti p ∧ IsReducedNeighbourWord p w := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [p.eq_1]
  · norm_num [p.eq_1, Fin.sum_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [p.eq_1] at *
  · intro k hk
    have hk' : k < 3 := hk
    change
      let z := w[k]
      let r := (w.take k).foldl (fun r z => r ∘ Equiv.swap z.1 z.2) p
      z.1 < z.2 ∧ r z.2 < r z.1 ∧ ∀ c, ¬ (r z.2 < r c ∧ r c < r z.1)
    interval_cases k <;>
      norm_num [w.eq_1, p.eq_1, Function.comp_apply,
        Equiv.swap_apply_def, Fin.forall_fin_succ]

private theorem target_values : applySwaps p w = ![2/9, 1/2, 1/36, 1/4] := by
  change w.foldl (fun r z => r ∘ Equiv.swap z.1 z.2) p = _
  funext i
  fin_cases i <;>
    norm_num [p.eq_1, w.eq_1, Function.comp_apply, Equiv.swap_apply_def]

private theorem joint_values :
    joint 2 p = fun x => ![![1/4, 1/4], ![1/8, 1/8], ![1/9, 1/9], ![1/72, 1/72]] x.1 x.2 := by
  funext x
  rcases x with ⟨i, m⟩
  change p i / 2 = _
  fin_cases i <;> fin_cases m <;> norm_num [p.eq_1]

private theorem truncated_block_one :
    block 2 0 1 (fun x => ![![1/4, 1/4], ![1/8, 1/8], ![1/9, 1/9], ![1/72, 1/72]] x.1 x.2) =
      fun x => ![![5/32, 3/16], ![7/32, 3/16], ![1/9, 1/9], ![1/72, 1/72]] x.1 x.2 := by
  change (List.finRange 2).foldl
      (fun (u : Fin 4 × Fin 2 → ℝ) k => (List.finRange 2).foldl
        (fun u l x => if x = (0, k) ∨ x = (1, l) then
          (u (0, k) + u (1, l)) / 2 else u x) u) _ = _
  funext x
  rcases x with ⟨i, m⟩
  fin_cases i <;> fin_cases m <;>
    norm_num [List.finRange_succ, List.finRange_zero]

private theorem truncated_block_two :
    block 2 2 3 (fun x => ![![5/32, 3/16], ![7/32, 3/16], ![1/9, 1/9], ![1/72, 1/72]] x.1 x.2) =
      fun x => ![![5/32, 3/16], ![7/32, 3/16], ![11/288, 1/16], ![25/288, 1/16]] x.1 x.2 := by
  change (List.finRange 2).foldl
      (fun (u : Fin 4 × Fin 2 → ℝ) k => (List.finRange 2).foldl
        (fun u l x => if x = (2, k) ∨ x = (3, l) then
          (u (2, k) + u (3, l)) / 2 else u x) u) _ = _
  funext x
  rcases x with ⟨i, m⟩
  fin_cases i <;> fin_cases m <;>
    norm_num [List.finRange_succ, List.finRange_zero]

private theorem truncated_block_three :
    block 2 0 3 (fun x => ![![5/32, 3/16], ![7/32, 3/16], ![11/288, 1/16], ![25/288, 1/16]] x.1 x.2) =
      fun x => ![![53/576, 71/576], ![7/32, 3/16], ![11/288, 1/16], ![89/576, 71/576]] x.1 x.2 := by
  change (List.finRange 2).foldl
      (fun (u : Fin 4 × Fin 2 → ℝ) k => (List.finRange 2).foldl
        (fun u l x => if x = (0, k) ∨ x = (3, l) then
          (u (0, k) + u (3, l)) / 2 else u x) u) _ = _
  funext x
  rcases x with ⟨i, m⟩
  fin_cases i <;> fin_cases m <;>
    norm_num [List.finRange_succ, List.finRange_zero]

private theorem reset_block_one :
    reset (fun x => ![![5/32, 3/16], ![7/32, 3/16], ![1/9, 1/9], ![1/72, 1/72]] x.1 x.2) =
      fun x => ![![11/64, 11/64], ![13/64, 13/64], ![1/9, 1/9], ![1/72, 1/72]] x.1 x.2 := by
  funext x
  rcases x with ⟨i, m⟩
  dsimp only [reset, joint, mixtureJoint, marginal]
  fin_cases i <;> fin_cases m <;> norm_num [Fin.sum_univ_two]

private theorem reset_block_two_raw :
    block 2 2 3 (fun x => ![![11/64, 11/64], ![13/64, 13/64], ![1/9, 1/9], ![1/72, 1/72]] x.1 x.2) =
      fun x => ![![11/64, 11/64], ![13/64, 13/64], ![11/288, 1/16], ![25/288, 1/16]] x.1 x.2 := by
  change (List.finRange 2).foldl
      (fun (u : Fin 4 × Fin 2 → ℝ) k => (List.finRange 2).foldl
        (fun u l x => if x = (2, k) ∨ x = (3, l) then
          (u (2, k) + u (3, l)) / 2 else u x) u) _ = _
  funext x
  rcases x with ⟨i, m⟩
  fin_cases i <;> fin_cases m <;>
    norm_num [List.finRange_succ, List.finRange_zero]

private theorem reset_block_two :
    reset (fun x => ![![11/64, 11/64], ![13/64, 13/64], ![11/288, 1/16], ![25/288, 1/16]] x.1 x.2) =
      fun x => ![![11/64, 11/64], ![13/64, 13/64], ![29/576, 29/576], ![43/576, 43/576]] x.1 x.2 := by
  funext x
  rcases x with ⟨i, m⟩
  dsimp only [reset, joint, mixtureJoint, marginal]
  fin_cases i <;> fin_cases m <;> norm_num [Fin.sum_univ_two]

private theorem reset_block_three_raw :
    block 2 0 3 (fun x => ![![11/64, 11/64], ![13/64, 13/64], ![29/576, 29/576], ![43/576, 43/576]] x.1 x.2) =
      fun x => ![![19/192, 71/576], ![13/64, 13/64], ![29/576, 29/576], ![85/576, 71/576]] x.1 x.2 := by
  change (List.finRange 2).foldl
      (fun (u : Fin 4 × Fin 2 → ℝ) k => (List.finRange 2).foldl
        (fun u l x => if x = (0, k) ∨ x = (3, l) then
          (u (0, k) + u (3, l)) / 2 else u x) u) _ = _
  funext x
  rcases x with ⟨i, m⟩
  fin_cases i <;> fin_cases m <;>
    norm_num [List.finRange_succ, List.finRange_zero]

private theorem reset_block_three :
    reset (fun x => ![![19/192, 71/576], ![13/64, 13/64], ![29/576, 29/576], ![85/576, 71/576]] x.1 x.2) =
      fun x => ![![1/9, 1/9], ![13/64, 13/64], ![29/576, 29/576], ![13/96, 13/96]] x.1 x.2 := by
  funext x
  rcases x with ⟨i, m⟩
  dsimp only [reset, joint, mixtureJoint, marginal]
  fin_cases i <;> fin_cases m <;> norm_num [Fin.sum_univ_two]

private theorem truncated_values :
    truncatedOutput 2 p w = ![31/144, 13/32, 29/288, 5/18] := by
  rw [truncatedOutput, w, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  dsimp only
  rw [joint_values, truncated_block_one, truncated_block_two, truncated_block_three]
  funext i
  change (∑ m : Fin 2, _) = _
  fin_cases i <;> norm_num [Fin.sum_univ_two]

private theorem reset_values :
    resetOutput 2 p w = ![2/9, 13/32, 29/288, 13/48] := by
  rw [resetOutput, w, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  dsimp only
  rw [joint_values, truncated_block_one, reset_block_one, reset_block_two_raw,
    reset_block_two, reset_block_three_raw, reset_block_three]
  funext i
  change (∑ m : Fin 2, _) = _
  fin_cases i <;> norm_num [Fin.sum_univ_two]

private theorem distance_gap :
    totalVariation (applySwaps p w) (truncatedOutput 2 p w) =
      totalVariation (applySwaps p w) (resetOutput 2 p w) + 1/144 := by
  rw [target_values, truncated_values, reset_values]
  rw [totalVariation, totalVariation]
  norm_num [Fin.sum_univ_four]

/-- Intermediate memory resets can improve a finite permutation approximation. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hp, hanti, hw⟩ := instance_hypotheses
  have hle := h 4 2 p w (by norm_num) hp.1 hp.2 hanti hw
  have hgap := distance_gap
  linarith

end

end D5.S3.StatisticalMechanics.ThermalRecallTruncationRefutation
