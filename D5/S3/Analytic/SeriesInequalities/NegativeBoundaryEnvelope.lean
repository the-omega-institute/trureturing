/- GID: D5/S3/Analytic/SeriesInequalities/NegativeBoundaryEnvelope
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/NegativeBoundaryEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative boundaries share an attained critical envelope with a nonzero weighted limit. -/

import D5.S3.Analytic.SeriesInequalities.FiniteSourceClosure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open scoped BigOperators ENNReal
open Filter Topology Finset

set_option autoImplicit false
set_option maxRecDepth 3000

namespace D5.S3.Analytic.SeriesInequalities.NegativeBoundaryEnvelope

open FiniteSourceCriticalTail

/-- The scalar amplitude recurrence of the constant negative boundary. -/
noncomputable def amplitude (A : ℝ) : ℕ → ℝ
  | 0 => A
  | k + 1 => amplitude A k + A * ∑ j : Fin (k + 1), amplitude A j
termination_by k => k

/-- The actual nonlinear extension of any real negative boundary stays between
zero and the constant-negative extension. At the critical weight the latter
has an explicit positive limiting amplitude, over either real-like field. -/
theorem negative_boundary_envelope {K : Type*} [RCLike K]
    (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hcrit : A * ρ = (1 - ρ) ^ 2) :
    (∀ k, 0 ≤ amplitude A k ∧
      ρ ^ k * amplitude A k = A / (1 + ρ) * (1 + ρ ^ (2 * k + 1))) ∧
    (∀ n k, extension (fun _ : ℕ => -(A : K)) n k = -(amplitude A k : K)) ∧
    (∀ x : ℕ → ℝ, (∀ n, 0 ≤ x n ∧ x n ≤ A) → ∀ n k,
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ amplitude A k ∧
        extension (fun j => -(x j : K)) n k = -(q : K)) := by
  classical
  have hpos : ∀ k, 0 ≤ amplitude A k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => simpa [amplitude] using hA.le
      | succ k =>
        rw [amplitude]
        exact add_nonneg (ih k (by omega))
          (mul_nonneg hA.le (sum_nonneg fun j _ => ih j j.isLt))
  have hconst : ∀ n k, extension (fun _ : ℕ => -(A : K)) n k =
      -(amplitude A k : K) := by
    intro n k
    induction k using Nat.strong_induction_on generalizing n with
    | h k ih =>
      cases k with
      | zero => simp [extension, amplitude]
      | succ k =>
        rw [extension, amplitude, ih k (by omega)]
        simp_rw [ih _ (Fin.isLt _), neg_mul_neg]
        simp only [map_add, map_mul, map_sum]
        rw [← sum_mul]
        ring
  have hrec (k : ℕ) : amplitude A (k + 2) =
      (A + 2) * amplitude A (k + 1) - amplitude A k := by
    have hs : (∑ j : Fin (k + 2), amplitude A j) =
        (∑ j : Fin (k + 1), amplitude A j) + amplitude A (k + 1) :=
      Fin.sum_univ_castSucc _
    rw [show k + 2 = (k + 1) + 1 by omega, amplitude, hs]
    have hk := congrArg id (amplitude.eq_2 A k)
    dsimp at hk
    linarith
  have hc : (A + 2) * ρ = 1 + ρ ^ 2 := by nlinarith [hcrit]
  have hd : 1 + ρ ≠ 0 := by positivity
  have hformula : ∀ k, ρ ^ k * amplitude A k =
      A / (1 + ρ) * (1 + ρ ^ (2 * k + 1)) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simp [amplitude]; field_simp
    | one =>
      have hu1 : amplitude A 1 = A + A * A := by rw [amplitude]; simp [amplitude]
      rw [hu1]
      norm_num
      field_simp
      nlinarith [congrArg (fun x : ℝ => (1 + ρ) * x) hcrit]
    | more k ih0 ih1 =>
      have hw : ρ ^ (k + 2) * amplitude A (k + 2) =
          (1 + ρ ^ 2) * (ρ ^ (k + 1) * amplitude A (k + 1)) -
            ρ ^ 2 * (ρ ^ k * amplitude A k) := by
        rw [hrec, ← hc, pow_add, pow_succ]
        ring
      rw [hw, ih0, ih1]
      simp only [show 2 * (k + 2) + 1 = (2 * k + 1) + 4 by omega,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
      ring
  refine ⟨fun k => ⟨hpos k, hformula k⟩, hconst, ?_⟩
  intro x hx n k
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    cases k with
    | zero => exact ⟨x n, (hx n).1, by simpa [amplitude] using (hx n).2, by simp [extension]⟩
    | succ k =>
      obtain ⟨q, hq0, hqA, hq⟩ := ih k (by omega) (n + 1)
      have hj : ∀ j : Fin (k + 1), ∃ t : ℝ, 0 ≤ t ∧ t ≤ amplitude A j ∧
          extension (fun i => -(x i : K)) n j = -(t : K) :=
        fun j => ih j j.isLt n
      choose t ht0 htA ht using hj
      refine ⟨q + ∑ j : Fin (k + 1), t j * x (k - j),
        add_nonneg hq0 (sum_nonneg fun j _ => mul_nonneg (ht0 j) (hx _).1), ?_, ?_⟩
      · rw [amplitude, mul_sum]
        apply add_le_add hqA
        apply sum_le_sum
        intro j hj
        calc
          t j * x (k - j) ≤ amplitude A j * A :=
            mul_le_mul (htA j) (hx _).2 (hx _).1 (hpos j)
          _ = A * amplitude A j := mul_comm _ _
      · rw [extension, hq]
        simp_rw [ht, neg_mul_neg]
        simp only [map_add, map_sum, map_mul]
        ring

#print axioms negative_boundary_envelope
end D5.S3.Analytic.SeriesInequalities.NegativeBoundaryEnvelope
