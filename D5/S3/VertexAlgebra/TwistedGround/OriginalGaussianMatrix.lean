/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianMatrix
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual native Gaussian finite sections obey the uniform complex-disk squared-norm bound. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
The native matrix keeps the original pairScalar coefficients, positive
frequencies, and finite-section indexing. The finite central-binomial boundary
estimate is consumed by the existing scaled quadratic-row theorem; radial
Hermitian control and a two-sided unitary phase congruence give the complex disk
bound. The infinite operator and analytic consequences are separate statements.
-/

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

noncomputable section
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix

def centralWeight (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / (4 : ℝ)^n

def matrixEntry (z : ℂ) (s t : ℕ) : ℂ :=
  pairScalar s t /
    ((Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (t : ℝ) : ℂ)) *
    z^(s+t)

def finiteSection (N : ℕ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => matrixEntry z (i.val+1) (j.val+1)

lemma centralWeight_zero : centralWeight 0 = 1 := by
  norm_num [centralWeight, Nat.centralBinom]

private lemma centralWeight_one : centralWeight 1 = (1 / 2 : ℝ) := by
  norm_num [centralWeight, Nat.centralBinom]

private lemma centralWeight_pos (n : ℕ) : 0 < centralWeight n := by
  apply div_pos
  · exact_mod_cast Nat.centralBinom_pos n
  · positivity

lemma centralWeight_nonneg (n : ℕ) : 0 ≤ centralWeight n :=
  (centralWeight_pos n).le

lemma centralWeight_step (n : ℕ) :
    (2 * (n + 1) : ℝ) * centralWeight (n + 1) =
      (2 * n + 1) * centralWeight n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hcR : ((n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ)) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast h
  simp only [centralWeight, pow_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat]
  field_simp
  nlinarith [hcR]

lemma halfBinomial_eq_signed_centralWeight (n : ℕ) :
    halfBinomial n = (-1 : ℂ)^n * (centralWeight n : ℂ) := by
  induction n with
  | zero =>
      simp [halfBinomial, centralWeight_zero]
  | succ n ih =>
      rw [half_successor, ih, pow_succ]
      have h := congrArg (fun x : ℝ => (x : ℂ)) (centralWeight_step n)
      have hn : (n + 1 : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      field_simp [hn]
      norm_num at h ⊢
      ring_nf at ⊢
      have h' : 2 * ((n : ℂ) + 1) * (centralWeight (n + 1) : ℂ) =
          (2 * (n : ℂ) + 1) * (centralWeight n : ℂ) := by
        convert h using 1 <;> ring
      rw [show 1 + n = n + 1 by omega] at ⊢
      linear_combination h'

private lemma central_weighted_partial_sum_exact (s N : ℕ) (hs : 0 < s) :
    (s : ℝ) * centralWeight s *
        (∑ t ∈ Finset.range N,
          centralWeight (t + 1) / ((s : ℝ) + (t : ℝ) + 1)) ≤
      1 - centralWeight (N + 1) - centralWeight s := by
  let S : ℕ → ℝ := fun k =>
    ∑ t ∈ Finset.range (N + 1),
      centralWeight t / ((k : ℝ) + (t : ℝ))
  let T : ℕ → ℝ := fun k => (k : ℝ) * centralWeight k * S k
  have hden (k t : ℕ) (hk : 0 < k) :
      (k : ℝ) + (t : ℝ) ≠ 0 := by positivity
  have hterm (t : ℕ) :
      centralWeight t / ((t : ℝ) + 1) =
        2 * (centralWeight t - centralWeight (t + 1)) := by
    have h := centralWeight_step t
    have ht : (t + 1 : ℝ) ≠ 0 := by positivity
    field_simp [ht]
    linear_combination h
  have hbase : T 1 = 1 - centralWeight (N + 1) := by
    have hs' := Finset.sum_range_sub' (fun t : ℕ => centralWeight t) (N + 1)
    have hsum : S 1 = 2 * (centralWeight 0 - centralWeight (N + 1)) := by
      dsimp [S]
      norm_num only [Nat.cast_one]
      change (∑ t ∈ Finset.range (N + 1),
        centralWeight t / ((1 : ℝ) + (t : ℝ))) = _
      calc
        (∑ t ∈ Finset.range (N + 1), centralWeight t / ((1 : ℝ) + (t : ℝ))) =
            ∑ t ∈ Finset.range (N + 1),
              2 * (centralWeight t - centralWeight (t + 1)) := by
                apply Finset.sum_congr rfl
                intro t ht
                convert hterm t using 1 <;> ring
        _ = 2 * (centralWeight 0 - centralWeight (N + 1)) := by
          calc
            _ = 2 * (∑ t ∈ Finset.range (N + 1),
                (centralWeight t - centralWeight (t + 1))) := by
                  rw [Finset.mul_sum]
            _ = _ := by rw [Finset.sum_range_sub']
    dsimp [T]
    rw [hsum, centralWeight_zero, centralWeight_one]
    ring
  have hB (k t : ℕ) (hk : 0 < k) :
      (2 * (t + 1) : ℝ) * centralWeight (t + 1) /
          ((k : ℝ) + (t : ℝ) + 1) -
        (2 * t : ℝ) * centralWeight t / ((k : ℝ) + (t : ℝ)) =
      2 * (k : ℝ) * centralWeight t / ((k : ℝ) + (t : ℝ)) -
        (2 * (k : ℝ) + 1) * centralWeight t /
          ((k : ℝ) + (t : ℝ) + 1) := by
    have h := centralWeight_step t
    have h₁ : (k : ℝ) + (t : ℝ) ≠ 0 := hden k t hk
    have h₂ : (k : ℝ) + (t : ℝ) + 1 ≠ 0 := by positivity
    rw [show (2 * (t + 1) : ℝ) * centralWeight (t + 1) =
      (2 * (t : ℝ) + 1) * centralWeight t by
        simpa [Nat.cast_add, Nat.cast_one] using h]
    field_simp [h₁, h₂]
    ring
  have hrec (k : ℕ) (hk : 0 < k) :
      T (k + 1) = T k - centralWeight k * (N + 1) *
        centralWeight (N + 1) / ((k : ℝ) + (N : ℝ) + 1) := by
    have hsum := Finset.sum_range_sub
      (fun t : ℕ => (2 * (t : ℝ) * centralWeight t) /
        ((k : ℝ) + (t : ℝ))) (N + 1)
    have hsum' :
        2 * (k : ℝ) * S k - (2 * (k : ℝ) + 1) * S (k + 1) =
          2 * (N + 1) * centralWeight (N + 1) /
            ((k : ℝ) + (N : ℝ) + 1) := by
      dsimp [S]
      simp only [Nat.cast_add, Nat.cast_one]
      calc
        2 * (k : ℝ) *
              (∑ t ∈ Finset.range (N + 1),
                centralWeight t / ((k : ℝ) + (t : ℝ))) -
            (2 * (k : ℝ) + 1) *
              (∑ t ∈ Finset.range (N + 1),
                centralWeight t / ((k : ℝ) + 1 + (t : ℝ))) =
            ∑ t ∈ Finset.range (N + 1),
              (2 * (k : ℝ) * centralWeight t / ((k : ℝ) + (t : ℝ)) -
                (2 * (k : ℝ) + 1) * centralWeight t /
                  ((k : ℝ) + 1 + (t : ℝ))) := by
                    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro t ht
                    ring
        _ = ∑ t ∈ Finset.range (N + 1),
              ((2 * (t + 1) : ℝ) * centralWeight (t + 1) /
                  ((k : ℝ) + (t : ℝ) + 1) -
                (2 * t : ℝ) * centralWeight t / ((k : ℝ) + (t : ℝ))) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    rw [show (k : ℝ) + 1 + (t : ℝ) =
                      (k : ℝ) + (t : ℝ) + 1 by ring]
                    simpa [Nat.cast_add, Nat.cast_one, Nat.add_comm,
                      Nat.add_left_comm, Nat.add_assoc] using (hB k t hk).symm
        _ = _ := by
          have hh := hsum
          simp only [Nat.cast_add, Nat.cast_one] at hh
          simpa [add_assoc, add_comm, add_left_comm] using hh
    have hks := centralWeight_step k
    have hrel :
        (k : ℝ) * centralWeight k * S k -
            (k + 1 : ℝ) * centralWeight (k + 1) * S (k + 1) =
          centralWeight k * (N + 1) * centralWeight (N + 1) /
            ((k : ℝ) + (N : ℝ) + 1) := by
      calc
        (k : ℝ) * centralWeight k * S k -
              (k + 1 : ℝ) * centralWeight (k + 1) * S (k + 1) =
            centralWeight k / 2 *
              (2 * (k : ℝ) * S k - (2 * (k : ℝ) + 1) * S (k + 1)) := by
                have hks' : 2 * ((k : ℝ) + 1) * centralWeight (k + 1) =
                    (2 * (k : ℝ) + 1) * centralWeight k := by
                  simpa [Nat.add_comm, Nat.cast_add, Nat.cast_one] using hks
                calc
                  _ = centralWeight k / 2 *
                        (2 * (k : ℝ) * S k - (2 * (k : ℝ) + 1) * S (k + 1)) +
                      S (k + 1) / 2 *
                        ((2 * (k : ℝ) + 1) * centralWeight k -
                          2 * ((k : ℝ) + 1) * centralWeight (k + 1)) := by ring
                  _ = centralWeight k / 2 *
                        (2 * (k : ℝ) * S k - (2 * (k : ℝ) + 1) * S (k + 1)) := by
                          rw [hks']
                          ring
        _ = _ := by rw [hsum']; ring
    dsimp [T]
    norm_num [Nat.cast_add, Nat.cast_one] at ⊢
    linear_combination -hrel
  have hupper : ∀ k : ℕ, T (k + 1) ≤ 1 - centralWeight (N + 1) := by
    intro k
    induction k with
    | zero => exact le_of_eq hbase
    | succ k ih =>
        have hr := hrec (k + 1) (by omega)
        have hnon : 0 ≤ centralWeight (k + 1) * (N + 1) *
            centralWeight (N + 1) / ((k + 1 : ℝ) + (N : ℝ) + 1) := by
          apply div_nonneg
          · exact mul_nonneg (mul_nonneg (centralWeight_nonneg _) (by positivity))
              (centralWeight_nonneg _)
          · positivity
        calc
          T (k + 1 + 1) = T (k + 1) - centralWeight (k + 1) * (N + 1) *
              centralWeight (N + 1) / ((k + 1 : ℝ) + (N : ℝ) + 1) := by
                simpa [Nat.cast_add, Nat.cast_one] using hr
          _ ≤ T (k + 1) := sub_le_self _ hnon
          _ ≤ 1 - centralWeight (N + 1) := ih
  have hmain : T s ≤ 1 - centralWeight (N + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    simpa using hupper k
  have hsplit := Finset.sum_range_succ' (fun t : ℕ =>
    centralWeight t / ((s : ℝ) + (t : ℝ))) N
  have hspos : (s : ℝ) ≠ 0 := by positivity
  have hsplit' : S s =
      (∑ t ∈ Finset.range N,
        centralWeight (t + 1) / ((s : ℝ) + (t : ℝ) + 1)) +
        1 / (s : ℝ) := by
    dsimp [S]
    rw [show (N + 1) = N + 1 by rfl, hsplit]
    simp only [centralWeight_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro t ht
      congr 1
      norm_num [Nat.cast_add]
      ring
    · norm_num
  rw [show T s = (s : ℝ) * centralWeight s * S s by rfl, hsplit'] at hmain
  have hbs : 0 ≤ centralWeight (N + 1) := centralWeight_nonneg _
  have hrew : (s : ℝ) * centralWeight s * (1 / (s : ℝ)) = centralWeight s := by
    field_simp [hspos]
  rw [mul_add, hrew] at hmain
  have hexact : (s : ℝ) * centralWeight s *
      (∑ t ∈ Finset.range N,
        centralWeight (t + 1) / ((s : ℝ) + (t : ℝ) + 1)) ≤
      1 - centralWeight (N + 1) - centralWeight s := by linarith
  exact hexact

private lemma central_weighted_partial_sum_le (s N : ℕ) (hs : 0 < s) :
    (s : ℝ) * centralWeight s *
        (∑ t ∈ Finset.range N,
          centralWeight (t + 1) / ((s : ℝ) + (t : ℝ) + 1)) ≤
      1 - centralWeight s := by
  have h := central_weighted_partial_sum_exact s N hs
  linarith [centralWeight_nonneg (N + 1)]

lemma matrixEntry_norm (z : ℂ) (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    ‖matrixEntry z s t‖ =
      Real.sqrt (s : ℝ) * Real.sqrt (t : ℝ) * centralWeight s *
        centralWeight t * ‖z‖ ^ (s + t) / (s + t : ℝ) := by
  have hst : (s + t : ℝ) ≠ 0 := by positivity
  have hss : Real.sqrt (s : ℝ) ≠ 0 := by positivity
  have htt : Real.sqrt (t : ℝ) ≠ 0 := by positivity
  simp only [matrixEntry, pairScalar, norm_mul, norm_div, norm_pow]
  rw [halfBinomial_eq_signed_centralWeight s,
    halfBinomial_eq_signed_centralWeight t]
  simp [Complex.norm_real, Real.norm_eq_abs, norm_pow,
    abs_of_nonneg (centralWeight_nonneg s), abs_of_nonneg (centralWeight_nonneg t),
    abs_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < s)),
    abs_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < t)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ s + t)]
  have hsqrt : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = s :=
    Real.mul_self_sqrt (by positivity)
  have htsqrt : Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) = t :=
    Real.mul_self_sqrt (by positivity)
  have hsqrt2 : Real.sqrt (s : ℝ) ^ 2 = s :=
    Real.sq_sqrt (by positivity)
  have htsqrt2 : Real.sqrt (t : ℝ) ^ 2 = t :=
    Real.sq_sqrt (by positivity)
  have hsum_norm : ‖(s : ℂ) + (t : ℂ)‖ = (s + t : ℝ) := by
    calc
      ‖(s : ℂ) + (t : ℂ)‖ = ‖((s + t : ℝ) : ℂ)‖ := by
        congr 1
        norm_num
      _ = ‖(s + t : ℝ)‖ := Complex.norm_real _
      _ = (s + t : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        positivity
  rw [hsum_norm]
  field_simp [hss, htt, hst]
  rw [hsqrt2, htsqrt2]
  ring

private lemma finiteSection_weighted_row_le (N : ℕ) (z : ℂ) (hz : ‖z‖ < 1)
    (i : Fin N) :
    (∑ j : Fin N, ‖finiteSection N z i j‖ *
      (1 / Real.sqrt ((j.val : ℝ) + 1))) ≤
      ‖z‖ ^ 2 * (1 / Real.sqrt ((i.val : ℝ) + 1)) := by
  classical
  let s : ℕ := i.val + 1
  have hs : 0 < s := by dsimp [s]; omega
  have hsreal : (s : ℝ) = (i.val : ℝ) + 1 := by
    dsimp [s]
    norm_num
  have hrho0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hrho1 : ‖z‖ ≤ 1 := hz.le
  have hterm (j : Fin N) :
      ‖finiteSection N z i j‖ *
          (1 / Real.sqrt ((j.val : ℝ) + 1)) ≤
        ‖z‖ ^ 2 * Real.sqrt (s : ℝ) * centralWeight s *
          centralWeight (j.val + 1) /
            ((s : ℝ) + (j.val : ℝ) + 1) := by
    have ht : 0 < j.val + 1 := by omega
    have hpow : ‖z‖ ^ (s + (j.val + 1)) ≤ ‖z‖ ^ 2 := by
      apply pow_le_pow_of_le_one hrho0 hrho1
      dsimp [s]
      omega
    rw [finiteSection, matrixEntry_norm z s (j.val + 1) hs ht]
    have hjcast : ((j.val + 1 : ℕ) : ℝ) = (j.val : ℝ) + 1 := by norm_num
    have hsqrt : Real.sqrt ((j.val : ℝ) + 1) > 0 := by positivity
    have hden : (s : ℝ) + (j.val : ℝ) + 1 > 0 := by positivity
    have hcancel :
        Real.sqrt (s : ℝ) * Real.sqrt ((j.val + 1 : ℕ) : ℝ) *
            centralWeight s * centralWeight (j.val + 1) *
            ‖z‖ ^ (s + (j.val + 1)) /
              ((s : ℝ) + ((j.val + 1 : ℕ) : ℝ)) *
              (1 / Real.sqrt ((j.val : ℝ) + 1)) =
          Real.sqrt (s : ℝ) * centralWeight s * centralWeight (j.val + 1) *
            ‖z‖ ^ (s + (j.val + 1)) /
              ((s : ℝ) + (j.val : ℝ) + 1) := by
      rw [hjcast]
      field_simp [ne_of_gt hsqrt, ne_of_gt hden]
      ring
    rw [hcancel]
    have hcoeff : 0 ≤ Real.sqrt (s : ℝ) * centralWeight s *
        centralWeight (j.val + 1) / ((s : ℝ) + (j.val : ℝ) + 1) := by
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (centralWeight_nonneg _))
          (centralWeight_nonneg _)
      · exact (le_of_lt hden)
    calc
      Real.sqrt (s : ℝ) * centralWeight s * centralWeight (j.val + 1) *
          ‖z‖ ^ (s + (j.val + 1)) /
            ((s : ℝ) + (j.val : ℝ) + 1) =
          (Real.sqrt (s : ℝ) * centralWeight s * centralWeight (j.val + 1) /
            ((s : ℝ) + (j.val : ℝ) + 1)) * ‖z‖ ^ (s + (j.val + 1)) := by ring
      _ ≤
        (Real.sqrt (s : ℝ) * centralWeight s * centralWeight (j.val + 1) /
            ((s : ℝ) + (j.val : ℝ) + 1)) * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hpow hcoeff
      _ = _ := by ring
  let f : ℕ → ℝ := fun j => if hj : j < N then
    ‖finiteSection N z i ⟨j, hj⟩‖ *
      (1 / Real.sqrt ((j : ℝ) + 1)) else 0
  have hsum_eq :
      (∑ j : Fin N, ‖finiteSection N z i j‖ *
        (1 / Real.sqrt ((j.val : ℝ) + 1))) =
      ∑ j : Fin N, f j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, j.isLt]
  rw [hsum_eq, Fin.sum_univ_eq_sum_range f N]
  calc
    (∑ x ∈ Finset.range N,
        f x) ≤
      ∑ x ∈ Finset.range N,
        ‖z‖ ^ 2 * Real.sqrt (s : ℝ) * centralWeight s *
          centralWeight (x + 1) /
            ((s : ℝ) + (x : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro x hx
          have hxlt : x < N := Finset.mem_range.mp hx
          simpa [f, hxlt] using hterm ⟨x, hxlt⟩
    _ = ‖z‖ ^ 2 * Real.sqrt (s : ℝ) * centralWeight s *
          (∑ x ∈ Finset.range N,
            centralWeight (x + 1) /
              ((s : ℝ) + (x : ℝ) + 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ ≤ ‖z‖ ^ 2 * (1 / Real.sqrt (s : ℝ)) := by
      have hw := central_weighted_partial_sum_le s N hs
      have hsqrt : 0 < Real.sqrt (s : ℝ) := by positivity
      have hsqrt_sq : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hq : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
      have hpartial : centralWeight s *
          (∑ x ∈ Finset.range N,
            centralWeight (x + 1) /
              ((s : ℝ) + (x : ℝ) + 1)) ≤
          (1 - centralWeight s) / (s : ℝ) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < (s : ℝ))).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hw
      have hqroot : 0 ≤ ‖z‖ ^ 2 * Real.sqrt (s : ℝ) :=
        mul_nonneg hq (le_of_lt hsqrt)
      have hmul : ‖z‖ ^ 2 * Real.sqrt (s : ℝ) * centralWeight s *
          (∑ x ∈ Finset.range N,
            centralWeight (x + 1) /
              ((s : ℝ) + (x : ℝ) + 1)) ≤
          ‖z‖ ^ 2 * Real.sqrt (s : ℝ) *
            ((1 - centralWeight s) / (s : ℝ)) := by
        calc
          ‖z‖ ^ 2 * Real.sqrt (s : ℝ) * centralWeight s *
              (∑ x ∈ Finset.range N,
                centralWeight (x + 1) /
                  ((s : ℝ) + (x : ℝ) + 1)) =
              (‖z‖ ^ 2 * Real.sqrt (s : ℝ)) *
                (centralWeight s *
                  (∑ x ∈ Finset.range N,
                    centralWeight (x + 1) /
                      ((s : ℝ) + (x : ℝ) + 1))) := by ring
          _ ≤ (‖z‖ ^ 2 * Real.sqrt (s : ℝ)) *
                ((1 - centralWeight s) / (s : ℝ)) :=
            mul_le_mul_of_nonneg_left hpartial hqroot
          _ = ‖z‖ ^ 2 * Real.sqrt (s : ℝ) *
                ((1 - centralWeight s) / (s : ℝ)) := by ring
      have hfrac : (1 - centralWeight s) / (s : ℝ) ≤ 1 / (s : ℝ) := by
        exact div_le_div_of_nonneg_right
          (sub_le_self 1 (centralWeight_nonneg s)) (le_of_lt (by positivity))
      have hmul2 : ‖z‖ ^ 2 * Real.sqrt (s : ℝ) *
          ((1 - centralWeight s) / (s : ℝ)) ≤
          ‖z‖ ^ 2 * Real.sqrt (s : ℝ) * (1 / (s : ℝ)) :=
        mul_le_mul_of_nonneg_left hfrac hqroot
      calc
        _ ≤ ‖z‖ ^ 2 * Real.sqrt (s : ℝ) *
              ((1 - centralWeight s) / (s : ℝ)) := hmul
        _ ≤ ‖z‖ ^ 2 * Real.sqrt (s : ℝ) * (1 / (s : ℝ)) := hmul2
        _ = ‖z‖ ^ 2 * (1 / Real.sqrt (s : ℝ)) := by
          field_simp [ne_of_gt hsqrt]
          rw [hsqrt_sq]
  simpa [hsreal, s]

private lemma pairScalar_conj (s t : ℕ) : conj (pairScalar s t) = pairScalar s t := by
  rw [pairScalar, halfBinomial_eq_signed_centralWeight,
    halfBinomial_eq_signed_centralWeight]
  simp only [map_div₀, map_mul, map_natCast, Complex.conj_ofReal,
    map_pow, map_neg, map_one, map_add, map_inv₀]

private lemma pairScalar_comm (s t : ℕ) : pairScalar s t = pairScalar t s := by
  unfold pairScalar
  ring

lemma finiteSection_radial_hermitian (N : ℕ) (rho : ℝ) :
    (finiteSection N (rho : ℂ)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [finiteSection, finiteSection, matrixEntry, matrixEntry]
  simp only [star_mul, star_div₀, star_pow, map_natCast, Complex.conj_ofReal,
    map_neg, map_one, map_add]
  have hpair : star (pairScalar (j.val + 1) (i.val + 1)) =
      pairScalar (j.val + 1) (i.val + 1) := by
    simpa [Complex.star_def] using pairScalar_conj (j.val + 1) (i.val + 1)
  rw [hpair]
  simp [Complex.star_def]
  rw [pairScalar_comm (j.val + 1) (i.val + 1)]
  ring

private def phaseDiagonal (N : ℕ) (u : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => u ^ (i.val + 1))

private lemma phaseDiagonal_unitary (N : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    phaseDiagonal N u ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  apply Matrix.diagonal_mem_unitary.mpr
  apply Pi.mem_unitary_iff.mpr
  intro i
  apply Unitary.mem_iff_star_mul_self.mpr
  change conj (u ^ (i.val + 1)) * u ^ (i.val + 1) = 1
  rw [map_pow, ← mul_pow, RCLike.conj_mul, hu]
  norm_num

private lemma finiteSection_phase_congruence (N : ℕ) (rho : ℝ) (u : ℂ) :
    finiteSection N ((rho : ℂ) * u) =
      phaseDiagonal N u * finiteSection N (rho : ℂ) * phaseDiagonal N u := by
  ext i j
  change matrixEntry ((rho : ℂ) * u) (i.val + 1) (j.val + 1) =
    (phaseDiagonal N u * finiteSection N (rho : ℂ) * phaseDiagonal N u) i j
  simp only [phaseDiagonal]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp [finiteSection, phaseDiagonal, matrixEntry, pow_add]
  ring

private lemma radial_quadratic_bound (N : ℕ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hrho1 : rho < 1) (a : Fin N → ℂ) :
    ‖∑ i, ∑ j, (a i * conj (a j)) * finiteSection N (rho : ℂ) i j‖ ≤
      rho ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
  have h := D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound.norm_complex_quadratic_le_scaled_rows
    a (finiteSection N (rho : ℂ)) (fun _ => 1)
      (fun i => 1 / Real.sqrt ((i.val : ℝ) + 1)) (rho ^ 2)
      (by intro i; positivity)
      (by
        intro i j
        have hh := (finiteSection_radial_hermitian N rho).apply i j
        have hn := congrArg norm hh
        simpa using hn.symm)
      (by
        intro i
        have hnorm : ‖(rho : ℂ)‖ < 1 := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hrho] using hrho1
        simpa using finiteSection_weighted_row_le N (rho : ℂ) hnorm i)
  simpa using h

private lemma radial_norm_le (N : ℕ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hrho1 : rho < 1) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)
        (finiteSection N (rho : ℂ))‖ ≤ rho ^ 2 := by
  by_cases hN : N = 0
  · subst N
    simp [finiteSection]
    positivity
  let T := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)
      (finiteSection N (rho : ℂ))
  have hT : (T : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] _).IsSymmetric := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (finiteSection_radial_hermitian N rho)
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT]
  apply ciSup_le
  intro x
  by_cases hx : ‖x‖ = 0
  · simp [ContinuousLinearMap.rayleighQuotient, hx]
    positivity
  have hnormpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx))
  have hquad :
      inner ℂ x (T x) =
        ∑ i, ∑ j, (star (WithLp.ofLp x i) * WithLp.ofLp x j) *
          finiteSection N (rho : ℂ) i j := by
    dsimp [T]
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
    simp only [dotProduct, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    change finiteSection N (rho : ℂ) i j * WithLp.ofLp x j *
      star (WithLp.ofLp x i) =
      star (WithLp.ofLp x i) * WithLp.ofLp x j *
        finiteSection N (rho : ℂ) i j
    ring
  have hq := radial_quadratic_bound N rho hrho hrho1
    (fun i => star (WithLp.ofLp x i))
  simp only [starRingEnd_apply, star_star, norm_star] at hq
  have hnum :
      |(T.reApplyInnerSelf x)| ≤ rho ^ 2 * ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
    calc
      |Complex.re (inner ℂ x (T x))| ≤ ‖inner ℂ x (T x)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖∑ i, ∑ j, (star (WithLp.ofLp x i) * WithLp.ofLp x j) *
          finiteSection N (rho : ℂ) i j‖ := by rw [hquad]
      _ ≤ rho ^ 2 * ∑ i, ‖WithLp.ofLp x i‖ ^ 2 := hq
      _ = rho ^ 2 * ‖x‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
  simp only [ContinuousLinearMap.rayleighQuotient, abs_div]
  rw [abs_of_nonneg (sq_nonneg ‖x‖)]
  exact (div_le_iff₀ hnormpos).2 hnum

private lemma phase_norm_le (N : ℕ) (rho : ℝ) (u : ℂ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hu : ‖u‖ = 1) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)
        (finiteSection N ((rho : ℂ) * u))‖ ≤ rho ^ 2 := by
  rw [finiteSection_phase_congruence]
  let U : Matrix.unitaryGroup (Fin N) ℂ :=
    ⟨phaseDiagonal N u, phaseDiagonal_unitary N u hu⟩
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  change ‖(U : Matrix (Fin N) (Fin N) ℂ) *
      finiteSection N (rho : ℂ) * (U : Matrix (Fin N) (Fin N) ℂ)‖ ≤ rho ^ 2
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  exact radial_norm_le N rho hrho hrho1

theorem finiteSection_opNorm_le (N : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := Complex)
        (finiteSection N z)‖ ≤ ‖z‖ ^ 2 := by
  by_cases hz0 : z = 0
  · subst z
    have hzero : finiteSection N 0 = 0 := by
      ext i j
      rw [finiteSection, matrixEntry]
      have hpos : 0 < (i.val + 1) + (j.val + 1) := by omega
      simp [zero_pow (Nat.ne_of_gt hpos)]
    rw [hzero]
    simp
  let rho : ℝ := ‖z‖
  have hrho0 : 0 ≤ rho := by
    dsimp [rho]
    exact norm_nonneg _
  have hrho1 : rho < 1 := by simpa [rho] using hz
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    exact norm_pos_iff.mpr hz0
  let u : ℂ := z / (rho : ℂ)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho_pos]
    exact div_self (ne_of_gt hrho_pos)
  have hzrepr : z = (rho : ℂ) * u := by
    dsimp [u]
    field_simp [ne_of_gt hrho_pos]
  calc
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := Complex)
        (finiteSection N z)‖ =
        ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := Complex)
          (finiteSection N ((rho : ℂ) * u))‖ := by rw [hzrepr]
    _ ≤ rho ^ 2 := phase_norm_le N rho u hrho0 hrho1 hu
    _ = ‖z‖ ^ 2 := by simp [rho]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianMatrix
