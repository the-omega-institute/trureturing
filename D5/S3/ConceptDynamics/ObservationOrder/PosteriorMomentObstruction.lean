/- GID: D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.claim; result=D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.result; claim=D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.claim
   digest: A rational five-cycle moment refutes sufficiency of centered positive semidefiniteness. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! # Centered posterior moment obstruction -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Matrix

namespace D5.S3.ConceptDynamics.ObservationOrder.PosteriorMomentObstruction
noncomputable section

private def M : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (5 * (if i = j then 1 else 0) +
    3 * (if j = i + 1 ∨ i = j + 1 then 1 else 0)) / 55

private def p : Fin 5 → ℝ := fun _ => 1 / 5

private theorem entries : ∀ i j, 0 ≤ M i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [M]

private theorem rows : ∀ i, ∑ j, M i j = p i := by
  intro i
  fin_cases i <;> norm_num [Fin.sum_univ_succ, M, p]

private theorem symmetric : M.IsSymm := by
  ext i j
  simp [M, eq_comm, or_comm]

private theorem noMixture (k : ℕ) (m : Fin k → ℝ) (v : Fin k → Fin 5 → ℝ)
    (hm : ∀ a, 0 ≤ m a) (hv : ∀ a i, 0 ≤ v a i) :
    (fun i j => ∑ a, m a * v a i * v a j : Matrix (Fin 5) (Fin 5) ℝ) ≠ M := by
  intro h
  have entry (i j : Fin 5) : ∑ a, m a * v a i * v a j = M i j :=
    congrFun (congrFun h i) j
  have zero (i j : Fin 5) (hz : M i j = 0) (a : Fin k) :
      m a * v a i * v a j = 0 := by
    have hs := entry i j
    rw [hz] at hs
    have hn (b : Fin k) : 0 ≤ m b * v b i * v b j :=
      mul_nonneg (mul_nonneg (hm b) (hv b i)) (hv b j)
    exact le_antisymm ((Finset.single_le_sum (fun b _ => hn b)
      (Finset.mem_univ a)).trans_eq hs) (hn a)
  have per (a : Fin k) :
      0 ≤ (m a * v a 0 * v a 0 + m a * v a 1 * v a 1 +
        m a * v a 2 * v a 2 + m a * v a 3 * v a 3 + m a * v a 4 * v a 4) -
      2 * (m a * v a 0 * v a 1 + m a * v a 1 * v a 2 +
        m a * v a 2 * v a 3 + m a * v a 3 * v a 4 + m a * v a 4 * v a 0) := by
    by_cases hz : m a = 0
    · simp [hz]
    have nz (i j : Fin 5) (hij : M i j = 0) : v a i = 0 ∨ v a j = 0 :=
      (mul_eq_zero.mp (zero i j hij a)).imp_left fun h =>
        (mul_eq_zero.mp h).resolve_left hz
    rcases nz 0 2 (by norm_num [M]) with h0 | h2 <;>
      rcases nz 1 3 (by norm_num [M]) with h1 | h3 <;>
      rcases nz 2 4 (by norm_num [M]) with h2' | h4 <;>
      rcases nz 3 0 (by norm_num [M]) with h3' | h0' <;>
      rcases nz 4 1 (by norm_num [M]) with h4' | h1' <;>
      simp_all only [mul_zero, zero_mul, add_zero, zero_add, sub_zero] <;>
      nlinarith only [mul_nonneg (hm a) (sq_nonneg (v a 0 - v a 1)),
        mul_nonneg (hm a) (sq_nonneg (v a 1 - v a 2)),
        mul_nonneg (hm a) (sq_nonneg (v a 2 - v a 3)),
        mul_nonneg (hm a) (sq_nonneg (v a 3 - v a 4)),
        mul_nonneg (hm a) (sq_nonneg (v a 4 - v a 0)),
        mul_nonneg (hm a) (sq_nonneg (v a 0)),
        mul_nonneg (hm a) (sq_nonneg (v a 1)),
        mul_nonneg (hm a) (sq_nonneg (v a 2)),
        mul_nonneg (hm a) (sq_nonneg (v a 3)),
        mul_nonneg (hm a) (sq_nonneg (v a 4))]
  have total := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => per a)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, entry] at total
  norm_num [M] at total

private theorem centered : (M - vecMulVec p p).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [M, p, conjTranspose_apply, vecMulVec_apply, eq_comm, or_comm]
  · intro x
    let a := 14 * x 0 + 4 * x 1 - 11 * x 2 - 11 * x 3 + 4 * x 4
    let b := 18 * x 1 + 10 * x 2 - 11 * x 3 - 17 * x 4
    let c := 5 * x 2 - x 3 - 4 * x 4
    let d := x 3 - x 4
    have identity :
        star x ⬝ᵥ ((M - vecMulVec p p) *ᵥ x) =
          (a^2 / 14 + 5 * b^2 / 126 + c^2 / 18 + d^2 / 2) / 275 := by
      norm_num [dotProduct, mulVec, Fin.sum_univ_succ, vecMulVec_apply, M, p,
        a, b, c, d]
      ring
    rw [identity]
    positivity

/-- Finite second moments of posterior probability vectors at the given uniform prior. -/
private def Realizable (moment : Matrix (Fin 5) (Fin 5) ℝ) : Prop :=
  ∃ (k : ℕ) (mass : Fin k → ℝ) (posterior : Fin k → Fin 5 → ℝ),
    (∀ a, 0 ≤ mass a) ∧ (∑ a, mass a) = 1 ∧
    (∀ a i, 0 ≤ posterior a i) ∧ (∀ a, (∑ i, posterior a i) = 1) ∧
    (fun i j => ∑ a, mass a * posterior a i * posterior a j) = moment

/-- The candidate sufficient conditions at the uniform prior on five targets. -/
def claim : Prop :=
  ∀ moment : Matrix (Fin 5) (Fin 5) ℝ,
    moment.IsSymm →
    (∀ i j, 0 ≤ moment i j) →
    (∀ i, (∑ j, moment i j) = p i) →
    (moment - vecMulVec p p).PosSemidef →
    Realizable moment

/-- The rational cycle of length five satisfies the matrix constraints and refutes the claim. -/
theorem result : ¬ claim := by
  intro sufficiency
  obtain ⟨k, mass, posterior, hmass, _, hposterior, _, hmoment⟩ :=
    sufficiency M symmetric entries rows centered
  exact noMixture k mass posterior hmass hposterior hmoment

end

end D5.S3.ConceptDynamics.ObservationOrder.PosteriorMomentObstruction
