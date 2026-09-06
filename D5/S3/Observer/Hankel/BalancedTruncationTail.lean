/- GID: D5/S3/Observer/Hankel/BalancedTruncationTail
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/BalancedTruncationTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Iterated actual principal truncation has the twice-discarded-diagonal finite and infinite input-output energy bound. -/

import D5.S3.Observer.Hankel.BalancedTruncationStep
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.BalancedTruncationTail

open D5.S3.Observer.Hankel.BalancedSteinEnergy
open D5.S3.Observer.Hankel.BalancedTruncationStep
open scoped BigOperators

variable {n r m p : ℕ}

/-- The Euclidean norm of a finite time-output window. -/
def windowNorm (y : ℕ → Fin p → ℝ) (N : ℕ) : ℝ :=
  ‖(WithLp.toLp 2 (fun q : Fin N × Fin p => y q.1 q.2) :
      EuclideanSpace ℝ (Fin N × Fin p))‖

theorem windowNorm_nonneg (y : ℕ → Fin p → ℝ) (N : ℕ) : 0 ≤ windowNorm y N :=
  norm_nonneg _

/-- Window norms are exactly the sum-of-squares energy used by the Stein proof. -/
theorem windowNorm_sq (y : ℕ → Fin p → ℝ) (N : ℕ) :
    (windowNorm y N) ^ 2 = ∑ k ∈ Finset.range N, squareSum (y k) := by
  unfold windowNorm
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ q : Fin N × Fin p, (y q.1 q.2) ^ 2) = _
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_range (n := N) (fun k => squareSum (y k))).symm

@[simp] theorem windowNorm_zero (N : ℕ) : windowNorm (fun _ => (0 : Fin p → ℝ)) N = 0 := by
  have h := windowNorm_sq (fun _ => (0 : Fin p → ℝ)) N
  simp only [squareSum_zero, Finset.sum_const_zero] at h
  nlinarith [windowNorm_nonneg (fun _ => (0 : Fin p → ℝ)) N]

/-- The usual norm triangle inequality, applied to a telescoping output difference. -/
theorem windowNorm_triangle (a b c : ℕ → Fin p → ℝ) (N : ℕ) :
    windowNorm (fun k => a k - c k) N ≤
      windowNorm (fun k => a k - b k) N + windowNorm (fun k => b k - c k) N := by
  let va : EuclideanSpace ℝ (Fin N × Fin p) :=
    WithLp.toLp 2 (fun q => (a q.1 - c q.1) q.2)
  let vb : EuclideanSpace ℝ (Fin N × Fin p) :=
    WithLp.toLp 2 (fun q => (a q.1 - b q.1) q.2)
  let vc : EuclideanSpace ℝ (Fin N × Fin p) :=
    WithLp.toLp 2 (fun q => (b q.1 - c q.1) q.2)
  have hv : va = vb + vc := by
    ext q
    change a q.1 q.2 - c q.1 q.2 =
      (a q.1 q.2 - b q.1 q.2) + (b q.1 q.2 - c q.1 q.2)
    ring
  change ‖va‖ ≤ ‖vb‖ + ‖vc‖
  rw [hv]
  exact norm_add_le _ _

/-- The unsquared two-sigma bound for a single actual truncation. -/
theorem single_truncation_window_bound (w : Fin (n + 1) → ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin (n + 1)) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin (n + 1)) ℝ) (h : BalancedStein w A B C)
    (u : ℕ → Fin m → ℝ) (N : ℕ) :
    windowNorm (fun k => matrixResponse A B C u k -
      matrixResponse (truncateA A) (truncateB B) (truncateC C) u k) N ≤
      2 * w (Fin.last n) * windowNorm u N := by
  have hb := finite_horizon_output_bound w A B C h u N
  rw [← windowNorm_sq, ← windowNorm_sq] at hb
  have hr : 0 ≤ 2 * w (Fin.last n) * windowNorm u N :=
    mul_nonneg (by have := h.1 (Fin.last n); positivity) (windowNorm_nonneg u N)
  apply (sq_le_sq₀ (windowNorm_nonneg _ N) hr).mp
  nlinarith [hb]

/-- Principal transition block retaining exactly the first r state coordinates. -/
def prefixA (h : r ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

/-- Input rows belonging to the retained prefix. -/
def prefixB (h : r ≤ n) (B : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin r) (Fin m) ℝ :=
  B.submatrix (Fin.castLE h) id

/-- Output columns belonging to the retained prefix. -/
def prefixC (h : r ≤ n) (C : Matrix (Fin p) (Fin n) ℝ) : Matrix (Fin p) (Fin r) ℝ :=
  C.submatrix id (Fin.castLE h)

/-- Sum of the discarded diagonal entries; no ordering hypothesis is needed for this sum. -/
def tailWeight (w : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ i, if r ≤ i.val then w i else 0

theorem tailWeight_nonneg (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (r : ℕ) :
    0 ≤ tailWeight w r := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hw i
  · exact le_rfl

@[simp] theorem tailWeight_self (w : Fin n → ℝ) : tailWeight w n = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [if_neg (not_le.mpr i.isLt)]

/-- Removing the last coordinate removes exactly its weight from the tail sum. -/
theorem tailWeight_step (w : Fin (n + 1) → ℝ) (hr : r ≤ n) :
    tailWeight w r = tailWeight (keep w) r + w (Fin.last n) := by
  unfold tailWeight
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, if_pos hr, keep]

/-- The full twice-tail bound, obtained by actual successive principal truncation.
The standard diagonal Stein assumptions imply the assumptions at every stage. -/
theorem balanced_truncation_window_bound (m p : ℕ) :
    ∀ (n : ℕ) (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
      (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin p) (Fin n) ℝ),
      BalancedStein w A B C → ∀ (r : ℕ) (hr : r ≤ n) (u : ℕ → Fin m → ℝ) (N : ℕ),
      windowNorm (fun k => matrixResponse A B C u k -
        matrixResponse (prefixA hr A) (prefixB hr B) (prefixC hr C) u k) N ≤
        2 * tailWeight w r * windowNorm u N := by
  intro n
  induction n with
  | zero =>
      intro w A B C h r hr u N
      have er : r = 0 := Nat.eq_zero_of_le_zero hr
      subst r
      have ea : prefixA hr A = A := rfl
      have eb : prefixB hr B = B := rfl
      have ec : prefixC hr C = C := rfl
      simp [ea, eb, ec]
  | succ n ih =>
      intro w A B C h r hr u N
      by_cases er : r = n + 1
      · subst r
        have ea : prefixA hr A = A := rfl
        have eb : prefixB hr B = B := rfl
        have ec : prefixC hr C = C := rfl
        simp [ea, eb, ec]
      · have hrn : r ≤ n := by omega
        have hT := truncate_preserves_stein w A B C h
        have h1 := single_truncation_window_bound w A B C h u N
        have h2 := ih (keep w) (truncateA A) (truncateB B) (truncateC C) hT r hrn u N
        have ea : prefixA hrn (truncateA A) = prefixA hr A := rfl
        have eb : prefixB hrn (truncateB B) = prefixB hr B := rfl
        have ec : prefixC hrn (truncateC C) = prefixC hr C := rfl
        rw [ea, eb, ec] at h2
        calc
          windowNorm (fun k => matrixResponse A B C u k -
              matrixResponse (prefixA hr A) (prefixB hr B) (prefixC hr C) u k) N ≤
            windowNorm (fun k => matrixResponse A B C u k -
              matrixResponse (truncateA A) (truncateB B) (truncateC C) u k) N +
            windowNorm (fun k => matrixResponse (truncateA A) (truncateB B) (truncateC C) u k -
              matrixResponse (prefixA hr A) (prefixB hr B) (prefixC hr C) u k) N :=
            windowNorm_triangle _ _ _ N
          _ ≤ 2 * w (Fin.last n) * windowNorm u N +
              2 * tailWeight (keep w) r * windowNorm u N := add_le_add h1 h2
          _ = 2 * tailWeight w r * windowNorm u N := by
            rw [tailWeight_step w hrn]
            ring

/-- Squared-energy version for every finite observation horizon. -/
theorem balanced_truncation_energy_bound (w : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (h : BalancedStein w A B C)
    (r : ℕ) (hr : r ≤ n) (u : ℕ → Fin m → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, squareSum (matrixResponse A B C u k -
      matrixResponse (prefixA hr A) (prefixB hr B) (prefixC hr C) u k)) ≤
    (2 * tailWeight w r) ^ 2 * ∑ k ∈ Finset.range N, squareSum (u k) := by
  have hb := balanced_truncation_window_bound m p n w A B C h r hr u N
  have hs := mul_self_le_mul_self (windowNorm_nonneg _ N) hb
  rw [← windowNorm_sq, ← windowNorm_sq]
  nlinarith [hs]

/-- Finite-energy inputs produce finite-energy truncation errors, with the same
constant on the entire half-line. Summability of the error is proved. -/
theorem balanced_truncation_l2_bound (w : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (h : BalancedStein w A B C)
    (r : ℕ) (hr : r ≤ n) (u : ℕ → Fin m → ℝ)
    (hu : Summable (fun k => squareSum (u k))) :
    Summable (fun k => squareSum (matrixResponse A B C u k -
      matrixResponse (prefixA hr A) (prefixB hr B) (prefixC hr C) u k)) ∧
    (∑' k, squareSum (matrixResponse A B C u k -
      matrixResponse (prefixA hr A) (prefixB hr B) (prefixC hr C) u k)) ≤
    (2 * tailWeight w r) ^ 2 * ∑' k, squareSum (u k) := by
  let err := fun k => squareSum (matrixResponse A B C u k -
    matrixResponse (prefixA hr A) (prefixB hr B) (prefixC hr C) u k)
  have he : ∀ k, 0 ≤ err k := fun _ => squareSum_nonneg _
  have hpartial (N : ℕ) : ∑ k ∈ Finset.range N, err k ≤
      (2 * tailWeight w r) ^ 2 * ∑' k, squareSum (u k) := by
    have hi : (∑ k ∈ Finset.range N, squareSum (u k)) ≤ ∑' k, squareSum (u k) :=
      Summable.sum_le_tsum (Finset.range N) (fun k _ => squareSum_nonneg (u k)) hu
    exact (balanced_truncation_energy_bound w A B C h r hr u N).trans
      (mul_le_mul_of_nonneg_left hi (sq_nonneg _))
  exact ⟨summable_of_sum_range_le he hpartial, Real.tsum_le_of_sum_range_le he hpartial⟩

#print axioms balanced_truncation_window_bound
#print axioms balanced_truncation_l2_bound

end D5.S3.Observer.Hankel.BalancedTruncationTail
