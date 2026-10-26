/- GID: D5/S3/Observer/Linear/GainRayEvaluation
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayEvaluation
   mirror-E: none(waiver:distinct-original-clock-evaluation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: Distinct clock evaluation has exact injective and surjective interfaces at the declared degree. -/

import D5.S3.Observer.Linear.GainRayWorld
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false
noncomputable section
namespace D5.S3.Observer.Linear.GainRay

/-- Nodes are explicit; original acquisition uses their consecutive natural casts. -/
def evaluation (d n : ℕ) (t : Fin n → ℝ) : Matrix (Fin n) (Fin (d + 1)) ℝ :=
  fun i k => t i ^ (k : ℕ)

def evaluate (d n : ℕ) (t : Fin n → ℝ) : Coeff d →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.mulVecLin (evaluation d n t)

private theorem evaluation_polynomial (d n : ℕ) (t : Fin n → ℝ) (β : Coeff d)
    (i : Fin n) : evaluate d n t β i = (gain d β).eval (t i) := by
  simp [evaluate, evaluation, Matrix.mulVecLin, Matrix.mulVec, dotProduct, gain,
    Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, mul_comm]

/-- All original clock embeddings are injective, including the zero clock. -/
def clocks (n : ℕ) (i : Fin n) : ℝ := (i.val : ℝ)

/-- Enough distinct clocks determine the whole ordinary coefficient vector. -/
theorem evaluation_injective (d n : ℕ) (t : Fin n → ℝ)
    (ht : Function.Injective t) (hn : d + 1 ≤ n) :
    Function.Injective (evaluate d n t) := by
  intro β γ he
  apply Polynomial.injective_ofFn (d + 1)
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset (Fin n))
    (fun _ _ _ _ h => ht h)
  · simpa using lt_of_lt_of_le (Polynomial.ofFn_degree_lt β) (by exact_mod_cast hn)
  · simpa using lt_of_lt_of_le (Polynomial.ofFn_degree_lt γ) (by exact_mod_cast hn)
  · intro i _
    change (gain d β).eval (t i) = (gain d γ).eval (t i)
    rw [← evaluation_polynomial, ← evaluation_polynomial]
    exact congrFun he i

/-- At most d+1 distinct prescribed values are attained without a sign promise. -/
theorem evaluation_surjective (d n : ℕ) (t : Fin n → ℝ)
    (ht : Function.Injective t) (hn : n ≤ d + 1) :
    Function.Surjective (evaluate d n t) := by
  intro y
  classical
  by_cases hz : n = 0
  · subst n
    exact ⟨0, Subsingleton.elim _ _⟩
  let p := Lagrange.interpolate (Finset.univ : Finset (Fin n)) t y
  have hp : p.degree < (n : ℕ) := by
    simpa [p] using Lagrange.degree_interpolate_lt y
      (fun _ _ _ _ h => ht h)
  have hdeg : p.natDegree < d + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact ((Polynomial.natDegree_lt_iff_degree_lt h0).mpr hp).trans_le hn
  refine ⟨Polynomial.toFn (d + 1) p, ?_⟩
  ext i
  rw [evaluation_polynomial]
  change (Polynomial.ofFn (d + 1) (Polynomial.toFn (d + 1) p)).eval (t i) = _
  rw [Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg]
  exact Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => ht h) (Finset.mem_univ i)

/-- A right inverse for every short, distinct-clock evaluation map. -/
def evaluationRightInverse (d n : ℕ) (t : Fin n → ℝ)
    (ht : Function.Injective t) (hn : n ≤ d + 1) : (Fin n → ℝ) → Coeff d :=
  Function.surjInv (evaluation_surjective d n t ht hn)

/-- The coefficient-and-drift extension of the pure-J history map is onto. -/
theorem pureJ_history_surjective (d n : ℕ) (hn : n ≤ d + 1) :
    Function.Surjective (fun b : Coeff d × ℝ =>
      fun i : Fin n => (gain d b.1).eval (clocks n i) + b.2) := by
  intro y
  have ht : Function.Injective (clocks n) := by
    intro i j h
    apply Fin.ext
    dsimp [clocks] at h
    exact_mod_cast h
  obtain ⟨β, hβ⟩ := evaluation_surjective d n (clocks n) ht hn y
  refine ⟨(β, 0), ?_⟩
  ext i
  simpa [evaluation_polynomial] using congrFun hβ i

#print axioms pureJ_history_surjective
end D5.S3.Observer.Linear.GainRay
