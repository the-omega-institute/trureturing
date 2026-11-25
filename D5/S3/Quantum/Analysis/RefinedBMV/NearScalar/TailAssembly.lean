/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/TailAssembly
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Taylor
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.TwoCommutator
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.AnalyticTail
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Order.BigOperators.Expect

/-! The degree-three-and-higher coefficient bounds for the four-copy near-scalar comparator. -/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarTailAssembly

open RefinedBMV (evalWord)
open RefinedBMV.Algebra44 (realTrace)
open RefinedBMVNearScalarTaylor
  (orderedProd gapWeight gapWeight_nonneg sum_gapWeight traceCoeff traceCoeff_sub_sorted)
open RefinedBMVNearScalarTwoCommutator (abs_realTrace_sub_sorted_le_nearScalar)
open private evalWord_block43 from D5.S3.Quantum.Analysis.RefinedBMV43
open private orderedProd_succ from D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Taylor
open private hasSum_analytic_tail from D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.AnalyticTail

/-- The word with one `false` at the end of each gap of `true` letters. -/
def gapWord {r : ℕ} (k : Fin r → ℕ) : List Bool :=
  (List.ofFn fun i => List.replicate (k i) true ++ [false]).flatten

private theorem gapWord_succ {r : ℕ} (k : Fin (r + 1) → ℕ) :
    gapWord k =
      (List.replicate (k 0) true ++ [false]) ++ gapWord (fun i => k i.succ) := by
  simp only [gapWord, List.ofFn_succ, List.flatten_cons]

theorem gapWord_count_true {r : ℕ} (k : Fin r → ℕ) :
    (gapWord k).count true = ∑ i, k i := by
  induction r with
  | zero => simp [gapWord]
  | succ r ih =>
      rw [gapWord_succ, Fin.sum_univ_succ]
      simp [List.count_append, ih]

theorem gapWord_count_false {r : ℕ} (k : Fin r → ℕ) :
    (gapWord k).count false = r := by
  induction r with
  | zero => simp [gapWord]
  | succ r ih =>
      rw [gapWord_succ]
      simp [List.count_append, List.count_replicate, ih, Nat.add_comm]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem evalWord_gapWord (H B : Matrix n n ℂ) {r : ℕ} (k : Fin r → ℕ) :
    evalWord H B (gapWord k) = orderedProd (fun i => H ^ k i * B) := by
  induction r with
  | zero => simp [gapWord, evalWord, orderedProd]
  | succ r ih =>
      rw [gapWord_succ, List.append_assoc, evalWord_block43, orderedProd_succ]
      change H ^ k 0 * (B * evalWord H B (gapWord (fun i => k i.succ))) =
        (H ^ k 0 * B) * orderedProd (fun i : Fin r => H ^ k i.succ * B)
      rw [ih, mul_assoc]

local notation "opNorm" =>
  fun A : Matrix n n ℂ => ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖

/-- The factorial mass scales the uniform word bound at each Taylor degree. -/
theorem abs_traceCoeff_sub_sorted_le (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian)
    (g : Fin 4 → ℝ) (hg : ∀ i, 0 ≤ g i) {p : ℝ} (hp : ∑ i, g i = p) (m : ℕ) :
    |traceCoeff g H B m -
        (p ^ m / (m.factorial : ℝ)) * (Matrix.trace (H ^ m * B ^ 4)).re| ≤
      96 * (m : ℝ) ^ 4 * (p ^ m / (m.factorial : ℝ)) *
        opNorm H ^ (m - 2) * ‖B * (H * B - B * H)‖ ^ 2 := by
  let deviation (k : Fin 4 → ℕ) : ℝ :=
    (Matrix.trace (orderedProd fun i => H ^ k i * B)).re -
      (Matrix.trace (H ^ m * B ^ 4)).re
  let bound := 96 * (m : ℝ) ^ 4 * opNorm H ^ (m - 2) * ‖B * (H * B - B * H)‖ ^ 2
  rw [← hp, traceCoeff_sub_sorted, hp]
  calc
    |∑ k ∈ Finset.Nat.antidiagonalTuple 4 m, gapWeight g k * deviation k| ≤
        ∑ k ∈ Finset.Nat.antidiagonalTuple 4 m, |gapWeight g k * deviation k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple 4 m, gapWeight g k * bound := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hword := abs_realTrace_sub_sorted_le_nearScalar H B hH hB (gapWord k) m
        ((gapWord_count_true k).trans (Finset.Nat.mem_antidiagonalTuple.mp hk))
        (gapWord_count_false k)
      have hweight := gapWeight_nonneg hg k
      rw [abs_mul, abs_of_nonneg hweight]
      apply mul_le_mul_of_nonneg_left _ hweight
      simpa only [deviation, bound, realTrace, evalWord_gapWord] using hword
    _ = _ := by
      rw [← Finset.sum_mul, sum_gapWeight, hp]
      simp only [bound, div_eq_mul_inv]
      ring

/-- The uniform composition coefficient minus the coefficient at four equal gaps. -/
def defectCoeff (p : ℕ) (H B : Matrix n n ℂ) (m : ℕ) : ℝ :=
  (Finset.Nat.antidiagonalTuple 4 p).expect
      (fun g => traceCoeff (fun i => (g i : ℝ)) H B m) -
    traceCoeff (fun _ => (p : ℝ) / 4) H B m

private theorem pow_mul_pow_sub_two (p M : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    p ^ m * M ^ (m - 2) = p ^ 2 * (p * M) ^ (m - 2) := by
  calc
    p ^ m * M ^ (m - 2) = p ^ (2 + (m - 2)) * M ^ (m - 2) := by
      rw [show 2 + (m - 2) = m by omega]
    _ = _ := by rw [pow_add, mul_pow, mul_assoc]

/-- The common sorted coefficient cancels between the mean and the balanced gaps. -/
theorem abs_defectCoeff_le (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (p m : ℕ) (hm : 3 ≤ m) :
    |defectCoeff p H B m| ≤
      192 * (m : ℝ) ^ 4 * (p : ℝ) ^ 2 * ‖B * (H * B - B * H)‖ ^ 2 *
        ((p : ℝ) * opNorm H) ^ (m - 2) / (m.factorial : ℝ) := by
  let compositions := Finset.Nat.antidiagonalTuple 4 p
  let coeff (g : Fin 4 → ℕ) := traceCoeff (fun i => (g i : ℝ)) H B m
  let balanced := traceCoeff (fun _ => (p : ℝ) / 4) H B m
  let sorted := ((p : ℝ) ^ m / (m.factorial : ℝ)) * (Matrix.trace (H ^ m * B ^ 4)).re
  let bound := 96 * (m : ℝ) ^ 4 * ((p : ℝ) ^ m / (m.factorial : ℝ)) *
    opNorm H ^ (m - 2) * ‖B * (H * B - B * H)‖ ^ 2
  have hnonempty : compositions.Nonempty := by
    refine ⟨Pi.single (0 : Fin 4) p, Finset.Nat.mem_antidiagonalTuple.mpr ?_⟩
    simpa only [Finset.mem_univ, if_true] using
      (Finset.sum_pi_single' (0 : Fin 4) p Finset.univ)
  have hcoeff (g : Fin 4 → ℕ) (hg : g ∈ compositions) : |coeff g - sorted| ≤ bound := by
    have htotal : (∑ i, (g i : ℝ)) = (p : ℝ) := by
      rw [← Nat.cast_sum, Finset.Nat.mem_antidiagonalTuple.mp hg]
    exact abs_traceCoeff_sub_sorted_le H B hH hB (fun i => (g i : ℝ))
      (fun i => Nat.cast_nonneg (g i)) htotal m
  have hbalanced : |balanced - sorted| ≤ bound := by
    have htotal : (∑ _i : Fin 4, (p : ℝ) / 4) = (p : ℝ) := by
      norm_num [Finset.sum_const, nsmul_eq_mul] <;> ring
    exact abs_traceCoeff_sub_sorted_le H B hH hB (fun _ => (p : ℝ) / 4)
      (fun _ => by positivity) htotal m
  have hmean : |compositions.expect coeff - sorted| ≤ bound := by
    rw [← Finset.expect_const hnonempty sorted,
      ← Finset.expect_sub_distrib compositions coeff (fun _ => sorted)]
    exact (Finset.abs_expect_le compositions (fun g => coeff g - sorted)).trans
      (Finset.expect_le hnonempty hcoeff)
  change |compositions.expect coeff - balanced| ≤ _
  calc
    _ ≤ |compositions.expect coeff - sorted| + |balanced - sorted| := by
      rw [abs_sub_comm balanced sorted]
      exact abs_sub_le _ _ _
    _ ≤ bound + bound := add_le_add hmean hbalanced
    _ = 192 * (m : ℝ) ^ 4 * ((p : ℝ) ^ m * opNorm H ^ (m - 2)) *
        ‖B * (H * B - B * H)‖ ^ 2 / (m.factorial : ℝ) := by
      simp only [bound, div_eq_mul_inv]
      ring
    _ = _ := by
      rw [pow_mul_pow_sub_two (p : ℝ) (opNorm H) (by omega : 2 ≤ m)]
      simp only [div_eq_mul_inv]
      ring

/-- Summing the coefficients from degree three gives the analytic tail bound. -/
theorem hasSum_defectCoeff_tail (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (p : ℕ) (hx : (p : ℝ) * opNorm H < 1) :
    HasSum (fun j : ℕ => defectCoeff p H B (j + 3))
        (∑' j : ℕ, defectCoeff p H B (j + 3)) ∧
      |(∑' j : ℕ, defectCoeff p H B (j + 3))| ≤
        2592 * (p : ℝ) ^ 2 * ‖B * (H * B - B * H)‖ ^ 2 * ((p : ℝ) * opNorm H) /
          (1 - (p : ℝ) * opNorm H) := by
  exact hasSum_analytic_tail (f := fun j => defectCoeff p H B (j + 3))
    (p := (p : ℝ)) (K := ‖B * (H * B - B * H)‖)
    (mul_nonneg (Nat.cast_nonneg p) (norm_nonneg _)) hx (fun j => by
      simpa only [show j + 3 - 2 = j + 1 by omega] using
        abs_defectCoeff_le H B hH hB p (j + 3) (by omega))

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarTailAssembly
