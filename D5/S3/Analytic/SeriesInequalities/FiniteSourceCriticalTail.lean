/- GID: D5/S3/Analytic/SeriesInequalities/FiniteSourceCriticalTail
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/FiniteSourceCriticalTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite boundaries have geometric antidiagonal decay at the critical weight. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
For a boundary bounded in norm by A and supported through M, the finite mass
polynomial x + A * sum_{i=0}^M x^(i+1) is strictly below one at the critical
weight rho. Continuity gives a larger radius R still below one. Strong column
induction bounds the actual recursive extension by A/R^k. Multiplication by
rho^(n+k) then gives a geometric bound uniform over each antidiagonal tail.

The argument works in any normed ring, including the real and complex numbers.
It uses finite support of the boundary, with no truncation of output coordinates
and no assumption of a generating-function identity or image compactness.
-/

open scoped BigOperators
open Filter Topology Finset

set_option autoImplicit false
set_option maxRecDepth 2000

namespace D5.S3.Analytic.SeriesInequalities.FiniteSourceCriticalTail

/-- The actual boundary extension by the subtraction-and-convolution column recurrence. -/
noncomputable def extension {K : Type*} [NormedRing K] (b : ℕ → K) (n : ℕ) : ℕ → K
  | 0 => b n
  | k + 1 => extension b (n + 1) k -
      ∑ j : Fin (k + 1), extension b n j * b (k - j)
termination_by k => k

/-- The supremum of the weighted norms on one actual antidiagonal tail. -/
noncomputable def antidiagonalTail {K : Type*} [NormedRing K]
    (ρ : ℝ) (T : ℕ → ℕ → K) (L : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ n k : ℕ, L ≤ n + k ∧ x = ρ ^ (n + k) * ‖T n k‖}

/-- A finite boundary at the critical amplitude has a strictly larger geometric radius.
The last two clauses bound the antidiagonal suprema and prove their convergence to zero. -/
theorem finite_source_critical_tail {K : Type*} [NormedRing K]
    (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hcrit : A * ρ = (1 - ρ) ^ 2)
    (M : ℕ) (b : ℕ → K) (hb : ∀ n, ‖b n‖ ≤ A)
    (hsupport : ∀ n, M < n → b n = 0) :
    ∃ R : ℝ, ρ < R ∧ R < 1 ∧
      (∀ n k, ‖extension b n k‖ * R ^ k ≤ A) ∧
      (∀ L, antidiagonalTail ρ (extension b) L ≤ A * (ρ / R) ^ L) ∧
      Tendsto (antidiagonalTail ρ (extension b)) atTop (𝓝 0) := by
  classical
  let g : ℝ → ℝ := fun x => x + A * ∑ i ∈ range (M + 1), x ^ (i + 1)
  have hgρ : g ρ < 1 := by
    have hs : (∑ i ∈ range (M + 1), ρ ^ (i + 1)) =
        ρ * ∑ i ∈ range (M + 1), ρ ^ i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [pow_succ, mul_comm]
    have heq : g ρ = 1 - (1 - ρ) * ρ ^ (M + 1) := by
      dsimp [g]
      rw [hs, ← mul_assoc, hcrit]
      have hh := geom_sum_mul_neg ρ (M + 1)
      nlinarith [mul_pos (sub_pos.mpr hρ1) (pow_pos hρ (M + 1))]
    rw [heq]
    exact sub_lt_self _ (mul_pos (sub_pos.mpr hρ1) (pow_pos hρ (M + 1)))
  have hg : Continuous g := by unfold g; fun_prop
  have hev : ∀ᶠ x in 𝓝 ρ, g x < 1 ∧ x < 1 :=
    (hg.continuousAt.eventually (gt_mem_nhds hgρ)).and (gt_mem_nhds hρ1)
  obtain ⟨l, u, hlu, hsub⟩ := hev.exists_Ioo_subset
  obtain ⟨R, hρR, hRu⟩ := exists_between hlu.2
  have hR := hsub ⟨hlu.1.trans hρR, hRu⟩
  have hR0 : 0 < R := hρ.trans hρR
  have hmass : R + A * ∑ i ∈ range (M + 1), R ^ (i + 1) ≤ 1 := hR.1.le
  have hpartial : ∀ k, (∑ i ∈ range (k + 1), ‖b i‖ * R ^ (i + 1)) ≤
      A * ∑ i ∈ range (M + 1), R ^ (i + 1) := by
    intro k
    calc
      (∑ i ∈ range (k + 1), ‖b i‖ * R ^ (i + 1)) ≤
          ∑ i ∈ range (max (k + 1) (M + 1)), ‖b i‖ * R ^ (i + 1) := by
        apply sum_le_sum_of_subset_of_nonneg (range_mono (le_max_left _ _))
        intro i hi hin
        positivity
      _ = ∑ i ∈ range (M + 1), ‖b i‖ * R ^ (i + 1) := by
        symm
        apply sum_subset (range_mono (le_max_right _ _))
        intro i hi hin
        have hMi : M < i := by simpa using hin
        simp [hsupport i hMi]
      _ ≤ ∑ i ∈ range (M + 1), A * R ^ (i + 1) := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hb i) (by positivity)
      _ = A * ∑ i ∈ range (M + 1), R ^ (i + 1) := (mul_sum _ _ _).symm
  have hbound : ∀ k n, ‖extension b n k‖ * R ^ k ≤ A := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n
      cases k with
      | zero => simpa [extension] using hb n
      | succ k =>
        have hterm : ∀ j : Fin (k + 1),
            ‖extension b n j * b (k - j)‖ * R ^ (k + 1) ≤
              A * (‖b (k - j)‖ * R ^ (k - j + 1)) := by
          intro j
          have hexp : R ^ (k + 1) = R ^ (j : ℕ) * R ^ (k - j + 1) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            ‖extension b n j * b (k - j)‖ * R ^ (k + 1) ≤
                (‖extension b n j‖ * ‖b (k - j)‖) * R ^ (k + 1) :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (by positivity)
            _ = (‖extension b n j‖ * R ^ (j : ℕ)) *
                (‖b (k - j)‖ * R ^ (k - j + 1)) := by rw [hexp]; ring
            _ ≤ A * (‖b (k - j)‖ * R ^ (k - j + 1)) :=
              mul_le_mul_of_nonneg_right (ih j j.isLt n) (by positivity)
        have hsum : (∑ j : Fin (k + 1), ‖b (k - j)‖ * R ^ (k - j + 1)) =
            ∑ i ∈ range (k + 1), ‖b i‖ * R ^ (i + 1) := by
          rw [Fin.sum_univ_eq_sum_range (fun j => ‖b (k - j)‖ * R ^ (k - j + 1)) (k + 1)]
          simpa using sum_range_reflect (fun i => ‖b i‖ * R ^ (i + 1)) (k + 1)
        calc
          ‖extension b n (k + 1)‖ * R ^ (k + 1) ≤
              (‖extension b (n + 1) k‖ +
                ∑ j : Fin (k + 1), ‖extension b n j * b (k - j)‖) * R ^ (k + 1) := by
            rw [extension]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
          _ = (‖extension b (n + 1) k‖ * R ^ k) * R +
              ∑ j : Fin (k + 1), ‖extension b n j * b (k - j)‖ * R ^ (k + 1) := by
            rw [add_mul, sum_mul, pow_succ]
            ring
          _ ≤ A * R + ∑ j : Fin (k + 1),
              A * (‖b (k - j)‖ * R ^ (k - j + 1)) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right (ih k (by omega) (n + 1)) hR0.le
            · exact sum_le_sum fun j hj => hterm j
          _ = A * (R + ∑ i ∈ range (k + 1), ‖b i‖ * R ^ (i + 1)) := by
            rw [← mul_sum, hsum, mul_add]
          _ ≤ A * (R + A * ∑ i ∈ range (M + 1), R ^ (i + 1)) := by
            exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hpartial k)) hA.le
          _ ≤ A := by nlinarith [hmass]
  have hq0 : 0 ≤ ρ / R := (div_pos hρ hR0).le
  have hq1 : ρ / R < 1 := (div_lt_one hR0).mpr hρR
  have hρq : ρ ≤ ρ / R := (le_div_iff₀ hR0).mpr (by nlinarith [hR.2])
  have htail : ∀ L n k, L ≤ n + k →
      ρ ^ (n + k) * ‖extension b n k‖ ≤ A * (ρ / R) ^ L := by
    intro L n k hL
    have hcol : ‖extension b n k‖ ≤ A / R ^ k :=
      (le_div_iff₀ (pow_pos hR0 k)).mpr (hbound k n)
    calc
      ρ ^ (n + k) * ‖extension b n k‖ ≤ ρ ^ (n + k) * (A / R ^ k) :=
        mul_le_mul_of_nonneg_left hcol (by positivity)
      _ = A * (ρ ^ n * (ρ / R) ^ k) := by rw [pow_add, div_pow]; ring
      _ ≤ A * ((ρ / R) ^ n * (ρ / R) ^ k) := by gcongr
      _ = A * (ρ / R) ^ (n + k) := by rw [pow_add]
      _ ≤ A * (ρ / R) ^ L := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        exact pow_le_pow_of_le_one hq0 hq1.le hL
  have hset : ∀ L, Set.Nonempty
      {x : ℝ | ∃ n k : ℕ, L ≤ n + k ∧ x = ρ ^ (n + k) * ‖extension b n k‖} := by
    intro L
    exact ⟨ρ ^ (L + 0) * ‖extension b L 0‖, L, 0, by omega, rfl⟩
  have hsup : ∀ L, antidiagonalTail ρ (extension b) L ≤ A * (ρ / R) ^ L := by
    intro L
    apply csSup_le (hset L)
    rintro x ⟨n, k, hL, rfl⟩
    exact htail L n k hL
  have hnonneg : ∀ L, 0 ≤ antidiagonalTail ρ (extension b) L := by
    intro L
    have hbounded : BddAbove
        {x : ℝ | ∃ n k : ℕ, L ≤ n + k ∧ x = ρ ^ (n + k) * ‖extension b n k‖} := by
      refine ⟨A * (ρ / R) ^ L, ?_⟩
      rintro x ⟨n, k, hL, rfl⟩
      exact htail L n k hL
    exact le_csSup_of_le hbounded ⟨L, 0, by omega, rfl⟩ (by positivity)
  refine ⟨R, hρR, hR.2, fun n k => hbound k n, hsup, ?_⟩
  have ht : Tendsto (fun L : ℕ => A * (ρ / R) ^ L) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul A
  exact squeeze_zero hnonneg hsup ht

#print axioms finite_source_critical_tail
end D5.S3.Analytic.SeriesInequalities.FiniteSourceCriticalTail
