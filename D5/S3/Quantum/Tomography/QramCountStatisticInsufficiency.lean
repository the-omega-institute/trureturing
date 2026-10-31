/- GID: D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/QramCountStatisticInsufficiency
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.claim; result=D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.result; claim=D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.claim
   digest: The plus-count statistic loses exact-weight discrimination information. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The equal-prior exact-weight model of L. Bohac, arXiv:2512.17503v1,
Remark 5.3. The function is sampled once and shared by all copies. The witness measures
both registers in the Walsh basis and rejects equal nonzero outcomes. -/

set_option autoImplicit false

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency

/-- The number of true addresses of a Boolean memory. -/
def weight {n : ℕ} (f : Fin (2 ^ n) → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x = true).card

/-- The uniform prior is supported on all memories of exactly this weight. -/
def weightClass (n m : ℕ) : Finset (Fin (2 ^ n) → Bool) :=
  Finset.univ.filter fun f => weight f = m

/-- The normalized phase address state produced by one query. -/
def addressState (n : ℕ) (f : Fin (2 ^ n) → Bool) : Fin (2 ^ n) → ℂ :=
  fun x => (-1 : ℂ) ^ (f x).toNat / (Real.sqrt (2 ^ n) : ℂ)

/-- The all-plus address state. -/
def plusState (n : ℕ) : Fin (2 ^ n) → ℂ := addressState n (fun _ => false)

/-- The induced state of copies of the same uniformly sampled exact-weight memory. -/
def copyState (n t m : ℕ) :
    Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ :=
  (1 / (weightClass n m).card : ℂ) •
    ∑ f ∈ weightClass n m, Matrix.of fun x y =>
      ∏ i, addressState n f (x i) * star (addressState n f (y i))

/-- The single-register plus projector. -/
def plusProj (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.vecMulVec (plusState n) (star (plusState n))

/-- The projector for exactly `k` plus outcomes in `t` registers. -/
def countProj (n t k : ℕ) :
    Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin t)).powersetCard k, Matrix.of fun x y =>
    ∏ i, (if i ∈ s then plusProj n else 1 - plusProj n) (x i) (y i)

/-- Equal-prior success, accepting the first weight with effect `e`. -/
def successProb (n t m₀ m₁ : ℕ)
    (e : Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ) : ℝ :=
  (1 / 2 : ℝ) * (Matrix.trace (copyState n t m₀ * e)).re +
    (1 / 2 : ℝ) * (Matrix.trace (copyState n t m₁ * (1 - e))).re

/-- A deterministic decision rule using only the number of plus outcomes. -/
def countTest (n t : ℕ) (g : Fin (t + 1) → Bool) :
    Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ :=
  ∑ k : Fin (t + 1), if g k then countProj n t k else 0

/-- Sufficiency of the plus count for every equal-prior exact-weight test. -/
def claim : Prop :=
  ∀ n ≥ 1, ∀ t ≥ 1, ∀ m₀ m₁, m₀ ≤ 2 ^ n → m₁ ≤ 2 ^ n →
    ∀ e : Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ,
      e.PosSemidef → (1 - e).PosSemidef →
        ∃ g : Fin (t + 1) → Bool,
          successProb n t m₀ m₁ e ≤ successProb n t m₀ m₁ (countTest n t g)

private def walsh (y x : Fin 4) : ℂ :=
  (![![1, 1, 1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1],
    ![1, -1, -1, 1]] : Fin 4 → Fin 4 → ℂ) y x / 2

private def walshPair (y z : Fin 4) (x : Fin 2 → Fin 4) : ℂ :=
  walsh y (x 0) * walsh z (x 1)

private def reject : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ :=
  ∑ y : Fin 3, Matrix.vecMulVec (walshPair y.succ y.succ)
    (star (walshPair y.succ y.succ))

private def witness : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ := 1 - reject

private lemma walsh_orthogonal (y z : Fin 4) :
    (star (walsh y)) ⬝ᵥ walsh z = if y = z then 1 else 0 := by
  sorry

private lemma plus_walsh : plusState 2 = walsh 0 := by
  sorry

private lemma weight_one_law (y z : Fin 4) :
    Matrix.trace (copyState 2 2 1 *
      Matrix.vecMulVec (walshPair y z) (star (walshPair y z))) = (1 / 16 : ℂ) := by
  sorry

private lemma weight_two_state : copyState 2 2 2 = (1 / 3 : ℂ) • reject := by
  sorry

private lemma reject_projector : rejectᴴ = reject ∧ reject * reject = reject := by
  sorry

private lemma witness_valid : witness.PosSemidef ∧ (1 - witness).PosSemidef := by
  sorry

private lemma witness_success : successProb 2 2 1 2 witness = 29 / 32 := by
  sorry

private lemma count_laws (k : Fin 3) :
    Matrix.trace (copyState 2 2 1 * countProj 2 2 k) =
      (![9 / 16, 3 / 8, 1 / 16] : Fin 3 → ℂ) k ∧
    Matrix.trace (copyState 2 2 2 * countProj 2 2 k) =
      (![1, 0, 0] : Fin 3 → ℂ) k := by
  sorry

private lemma count_bound (g : Fin 3 → Bool) :
    successProb 2 2 1 2 (countTest 2 2 g) ≤ 23 / 32 := by
  sorry

/-- The count statistic is insufficient, already for two copies and four addresses. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨g, hg⟩ := h 2 (by norm_num) 2 (by norm_num) 1 2 (by norm_num)
    (by norm_num) witness witness_valid.1 witness_valid.2
  have hb := count_bound g
  rw [witness_success] at hg
  linarith

end D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency
