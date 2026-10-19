/- GID: D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff
   mirror-E: none(waiver:analytic-hilbert-fourier-identification-without-executable-mirror)
   anchors: []
   utility: none
   digest: Actual physical matrix bounds yield summable infinite shift and finite-prime coefficient tails for natural N < M and a > 0. -/

import D5.S3.Weil.ZetaBridge.PhysicalCompressedCosineMatrix
import D5.S3.Weil.ZetaBridge.WeilArithmeticFourierDualTail
import D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace PhysicalPrimeTwoCutoff

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
open D5.S3.Weil.ZetaBridge.WeilArithmeticFourierDualTail (coefficient_bound)
open D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
  (inverse_square_partial_le inverse_square_summable)

/- No resonant division is made in the imported physical matrix. The following
normalization is used ONLY at n<m, so both u-v and u+v are nonzero. -/
private lemma overlap_quotient (a t u v : ℝ)
    (hd : u - v ≠ 0) (hp : u + v ≠ 0)
    (hu : Real.sin (u * a) = 0) (hv : Real.sin (v * a) = 0) :
    Real.cos ((u + v) * t / 2) * S ((2 * a - t) / 2) (u - v) +
      Real.cos ((u - v) * t / 2) * S ((2 * a - t) / 2) (u + v) =
      -(Real.cos (u * a) * Real.cos (v * a)) *
        (u * Real.sin (u * t) - v * Real.sin (v * t)) / (u ^ 2 - v ^ 2) := by
  have hden : u ^ 2 - v ^ 2 ≠ 0 := by
    rw [show u ^ 2 - v ^ 2 = (u - v) * (u + v) by ring]
    exact mul_ne_zero hd hp
  have hsminus : Real.sin ((u - v) * ((2 * a - t) / 2)) =
      -(Real.cos (u * a) * Real.cos (v * a)) *
        Real.sin ((u - v) * t / 2) := by
    rw [show (u - v) * ((2 * a - t) / 2) =
        (u * a - v * a) - (u - v) * t / 2 by ring,
      Real.sin_sub, Real.sin_sub, Real.cos_sub, hu, hv]
    ring
  have hsplus : Real.sin ((u + v) * ((2 * a - t) / 2)) =
      -(Real.cos (u * a) * Real.cos (v * a)) *
        Real.sin ((u + v) * t / 2) := by
    rw [show (u + v) * ((2 * a - t) / 2) =
        (u * a + v * a) - (u + v) * t / 2 by ring,
      Real.sin_sub, Real.sin_add, Real.cos_add, hu, hv]
    ring
  have hminus :
      2 * Real.cos ((u + v) * t / 2) * Real.sin ((u - v) * t / 2) =
        Real.sin (u * t) - Real.sin (v * t) := by
    calc
      _ = Real.sin (((u - v) * t / 2) + ((u + v) * t / 2)) -
          Real.sin (((u + v) * t / 2) - ((u - v) * t / 2)) := by
        rw [Real.sin_add, Real.sin_sub]
        ring
      _ = _ := by congr 2 <;> ring
  have hplus :
      2 * Real.cos ((u - v) * t / 2) * Real.sin ((u + v) * t / 2) =
        Real.sin (u * t) + Real.sin (v * t) := by
    calc
      _ = Real.sin (((u - v) * t / 2) + ((u + v) * t / 2)) +
          Real.sin (((u + v) * t / 2) - ((u - v) * t / 2)) := by
        rw [Real.sin_add, Real.sin_sub]
        ring
      _ = _ := by congr 2 <;> ring
  rw [S_of_ne _ _ hd, S_of_ne _ _ hp, hsminus, hsplus]
  have hminus' : Real.cos ((u + v) * t / 2) *
      Real.sin ((u - v) * t / 2) =
        (Real.sin (u * t) - Real.sin (v * t)) / 2 := by linarith
  have hplus' : Real.cos ((u - v) * t / 2) *
      Real.sin ((u + v) * t / 2) =
        (Real.sin (u * t) + Real.sin (v * t)) / 2 := by linarith
  calc
    _ = -(Real.cos (u * a) * Real.cos (v * a)) *
        ((Real.cos ((u + v) * t / 2) * Real.sin ((u - v) * t / 2)) / (u - v) +
         (Real.cos ((u - v) * t / 2) * Real.sin ((u + v) * t / 2)) / (u + v)) := by ring
    _ = _ := by
      rw [hminus', hplus']
      field_simp [hd, hp, hden]
      <;> ring

private lemma frequency_mul_radius (a : ℝ) (ha : 0 < a) (n : ℕ) :
    omega a n * a = (n : ℝ) * Real.pi := by
  unfold omega
  field_simp [ha.ne']
  <;> ring

/-- Exact original-compression offdiagonal formula. Its sign and denominator
match the proposed expression. This includes n=0, s=0 and |s|=2a. Outside
support the imported matrixEntry_eq_matrix has value zero. -/
theorem matrixEntry_offdiagonal (a : ℝ) (ha : 0 < a)
    (n m : ℕ) (hnm : n < m) (s : ℝ) (hs : |s| ≤ 2 * a) :
    matrixEntry a n m s = (-1 : ℝ) ^ (n + m + 1) *
      amplitude a n * amplitude a m *
      (omega a n * Real.sin (omega a n * |s|) -
        omega a m * Real.sin (omega a m * |s|)) /
        ((omega a n) ^ 2 - (omega a m) ^ 2) := by
  have hnr : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : 0 < 2 * Real.pi / (2 * a) := by positivity
  have hf (k : ℕ) : omega a k = (2 * Real.pi / (2 * a)) * (k : ℝ) := by
    unfold omega
    ring
  have hlt : omega a n < omega a m := by
    rw [hf, hf]
    exact mul_lt_mul_of_pos_left hnr hc
  have hn : 0 ≤ omega a n := by rw [hf]; positivity
  have hd : omega a n - omega a m ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlt)
  have hp : omega a n + omega a m ≠ 0 := ne_of_gt (by linarith)
  have hu : Real.sin (omega a n * a) = 0 := by
    rw [frequency_mul_radius a ha n, Real.sin_nat_mul_pi]
  have hv : Real.sin (omega a m * a) = 0 := by
    rw [frequency_mul_radius a ha m, Real.sin_nat_mul_pi]
  rw [matrixEntry_eq_matrix a ha, PhysicalCompressedCosineMatrix.matrix, if_pos hs,
    overlap_quotient a |s| (omega a n) (omega a m) hd hp hu hv,
    frequency_mul_radius a ha n, frequency_mul_radius a ha m,
    Real.cos_nat_mul_pi, Real.cos_nat_mul_pi]
  rw [pow_succ, pow_add]
  ring

private lemma amplitude_nonnegative (a : ℝ) (n : ℕ) : 0 ≤ amplitude a n := by
  unfold amplitude
  split_ifs <;> positivity

/-- Normalization loss is at most one; the zero-mode case has square 1/2. -/
private lemma amplitude_radius_bound (a : ℝ) (ha : 0 < a)
    (n m : ℕ) (hm : m ≠ 0) :
    0 ≤ a * amplitude a n * amplitude a m ∧
      a * amplitude a n * amplitude a m ≤ 1 := by
  have hpos : 0 ≤ a * amplitude a n * amplitude a m :=
    mul_nonneg (mul_nonneg ha.le (amplitude_nonnegative a n))
      (amplitude_nonnegative a m)
  have hb : (Real.sqrt (2 / (2 * a))) ^ 2 = 1 / a := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 / (2 * a))]
    field_simp [ha.ne']
  have hd : (Real.sqrt (2 * a)) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  by_cases hn : n = 0
  · have he : (a * amplitude a n * amplitude a m) ^ 2 = (1 / 2 : ℝ) := by
      simp only [amplitude, if_pos hn, if_neg hm]
      rw [mul_pow, mul_pow, div_pow, hb, hd]
      field_simp [ha.ne']
      <;> ring
    exact ⟨hpos, by nlinarith⟩
  · have he : a * amplitude a n * amplitude a m = 1 := by
      simp only [amplitude, if_neg hn, if_neg hm]
      rw [mul_assoc, ← pow_two, hb]
      exact mul_one_div_cancel ha.ne'
    exact ⟨hpos, he.le⟩

/-- The quotient is normalized to the existing owner's exact coefficient
estimate. Its proof is not copied here or accessed through a private name. -/
private lemma matrixEntry_dimensionless (a : ℝ) (ha : 0 < a)
    (n m : ℕ) (hnm : n < m) (s : ℝ) (hs : |s| ≤ 2 * a) :
    matrixEntry a n m s = (-1 : ℝ) ^ (n + m) *
      (a * amplitude a n * amplitude a m / Real.pi) *
      (((n : ℝ) * Real.sin (omega a n * |s|) -
        (m : ℝ) * Real.sin (omega a m * |s|)) /
        ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) := by
  rw [matrixEntry_offdiagonal a ha n m hnm s hs]
  have hnr : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (m : ℝ) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  have hden' : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := ne_of_lt (by nlinarith)
  have hf (k : ℕ) : omega a k = Real.pi / a * (k : ℝ) := by
    unfold omega
    field_simp [ha.ne']
    <;> ring
  have hfreq : (omega a n) ^ 2 - (omega a m) ^ 2 ≠ 0 := by
    rw [hf, hf]
    have hc : 0 < Real.pi / a := div_pos Real.pi_pos ha
    have hsep : Real.pi / a * (n : ℝ) < Real.pi / a * (m : ℝ) :=
      mul_lt_mul_of_pos_left hnr hc
    have hn : 0 ≤ Real.pi / a * (n : ℝ) := by positivity
    exact ne_of_lt (by nlinarith)
  simp_rw [hf] at hfreq
  rw [hf, hf, pow_succ]
  field_simp [ha.ne', Real.pi_ne_zero, hden, hden', hfreq]
  <;> ring

/-- Uniform sharp-constant offdiagonal bound for the actual physical pairing.
Both shift signs, the two support endpoints and the constant mode are included. -/
theorem matrixEntry_uniform_bound (a : ℝ) (ha : 0 < a)
    (n m : ℕ) (hnm : n < m) (s : ℝ) :
    |matrixEntry a n m s| ≤ 1 / (Real.pi * ((m : ℝ) - (n : ℝ))) := by
  have hnr : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hsep : 0 < (m : ℝ) - (n : ℝ) := sub_pos.mpr hnr
  by_cases hs : |s| ≤ 2 * a
  · have hq := coefficient_bound (Nat.cast_nonneg n) hnr
        (Real.abs_sin_le_one (omega a n * |s|))
        (Real.abs_sin_le_one (omega a m * |s|))
    obtain ⟨hA0, hA1⟩ := amplitude_radius_bound a ha n m (by omega)
    rw [matrixEntry_dimensionless a ha n m hnm s hs, abs_mul, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (div_nonneg hA0 Real.pi_pos.le)]
    calc
      _ ≤ (a * amplitude a n * amplitude a m / Real.pi) *
          (1 / ((m : ℝ) - (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ (1 / Real.pi) * (1 / ((m : ℝ) - (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hA1 Real.pi_pos.le) (by positivity)
      _ = _ := one_div_mul_one_div _ _
  · rw [matrixEntry_eq_matrix a ha, PhysicalCompressedCosineMatrix.matrix, if_neg hs, abs_zero]
    positivity

/-! Coefficients are actual integrals before they are rewritten as matrix rows. -/
def headMass (N : ℕ) (v : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ‖v n‖ ^ 2

def shiftCoefficient (a : ℝ) (N : ℕ) (v : ℕ → ℂ) (s : ℝ) (m : ℕ) : ℂ :=
  pairing a s (fun x => (mode a m x : ℂ))
    (profile a (Finset.range (N + 1)) v)

/-- Exact mixed physical pairing: no complex cross term has been discarded. -/
theorem shiftCoefficient_eq (a : ℝ) (ha : 0 < a)
    (N : ℕ) (v : ℕ → ℂ) (s : ℝ) (m : ℕ) :
    shiftCoefficient a N v s m =
      ∑ n ∈ Finset.range (N + 1), v n * (matrixEntry a n m s : ℂ) := by
  classical
  have h := pairing_finite a s ({m} : Finset ℕ) (Finset.range (N + 1))
    (fun _ => (1 : ℂ)) v (fun k x => (mode a k x : ℂ))
    (fun k x => (mode a k x : ℂ))
    (by intro k _; unfold mode; fun_prop)
    (by intro k _; unfold mode; fun_prop)
  simp only [Finset.sum_singleton, one_mul] at h
  change shiftCoefficient a N v s m = _
  unfold shiftCoefficient profile
  rw [h]
  apply Finset.sum_congr rfl
  intro n _
  rw [pairing_ofReal]
  change v n * (matrixEntry a m n s : ℂ) = _
  rw [matrixEntry_symmetric a ha m n s]

private lemma finite_row_sq (N : ℕ) (v : ℕ → ℂ) (k : ℕ → ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hk : ∀ n ∈ Finset.range (N + 1), |k n| ≤ D) :
    ‖∑ n ∈ Finset.range (N + 1), v n * (k n : ℂ)‖ ^ 2 ≤
      headMass N v * ((N : ℝ) + 1) * D ^ 2 := by
  have htri : ‖∑ n ∈ Finset.range (N + 1), v n * (k n : ℂ)‖ ≤
      ∑ n ∈ Finset.range (N + 1), ‖v n‖ * |k n| := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      (norm_sum_le (Finset.range (N + 1)) (fun n => v n * (k n : ℂ)))
  calc
    _ ≤ (∑ n ∈ Finset.range (N + 1), ‖v n‖ * |k n|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ headMass N v * ∑ n ∈ Finset.range (N + 1), |k n| ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ headMass N v * ∑ _n ∈ Finset.range (N + 1), D ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun n hn => pow_le_pow_left₀ (abs_nonneg _) (hk n hn) 2)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by simp; ring

/-- This is derived using the actual physical matrix, without an entry-bound
supplier. The weaker common denominator m-N is used only after n≤N. -/
theorem shiftCoefficient_sq (a : ℝ) (ha : 0 < a)
    (N : ℕ) (v : ℕ → ℂ) (s : ℝ) (m : ℕ) (hNm : N < m) :
    ‖shiftCoefficient a N v s m‖ ^ 2 ≤
      (headMass N v * ((N : ℝ) + 1) / Real.pi ^ 2) *
        (((m : ℝ) - (N : ℝ))⁻¹) ^ 2 := by
  have hsep : 0 < (m : ℝ) - (N : ℝ) := sub_pos.mpr (by exact_mod_cast hNm)
  rw [shiftCoefficient_eq a ha]
  have h := finite_row_sq N v (fun n => matrixEntry a n m s)
    (1 / (Real.pi * ((m : ℝ) - (N : ℝ)))) (by positivity) (by
      intro n hn
      have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
      have hnm : n < m := lt_of_le_of_lt hnN hNm
      have hnNr : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      exact (matrixEntry_uniform_bound a ha n m hnm s).trans
        (one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left (by linarith :
            (m : ℝ) - (N : ℝ) ≤ (m : ℝ) - (n : ℝ)) Real.pi_pos.le)))
  convert h using 1 <;>
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, mul_pow] <;> ring

private lemma complete_tail (N M : ℕ) (hNM : N < M)
    (c : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ m, N < m → ‖c m‖ ^ 2 ≤ C * (((m : ℝ) - (N : ℝ))⁻¹) ^ 2) :
    Summable (fun j : ℕ => ‖c (M + j + 1)‖ ^ 2) ∧
      (∑' j : ℕ, ‖c (M + j + 1)‖ ^ 2) ≤ C / ((M : ℝ) - (N : ℝ)) := by
  let d : ℝ := (M : ℝ) - (N : ℝ)
  have hd : 0 < d := sub_pos.mpr (by exact_mod_cast hNM)
  have hmajor := (inverse_square_summable hd).mul_left C
  have hpoint (j : ℕ) : ‖c (M + j + 1)‖ ^ 2 ≤ C * ((d + (j : ℝ) + 1)⁻¹) ^ 2 := by
    have h := hc (M + j + 1) (by omega)
    convert h using 1 <;> push_cast <;> dsimp [d] <;> ring
  have hs : Summable (fun j : ℕ => ‖c (M + j + 1)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint hmajor
  have hb : (∑' j : ℕ, ((d + (j : ℝ) + 1)⁻¹) ^ 2) ≤ d⁻¹ :=
    Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) (inverse_square_partial_le hd)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' j : ℕ, C * ((d + (j : ℝ) + 1)⁻¹) ^ 2 := hs.tsum_le_tsum hpoint hmajor
    _ = C * ∑' j : ℕ, ((d + (j : ℝ) + 1)⁻¹) ^ 2 := by rw [tsum_mul_left]
    _ ≤ C * d⁻¹ := mul_le_mul_of_nonneg_left hb hC
    _ = _ := by rw [div_eq_mul_inv]

/-- Complete infinite tail of actual compression pairings, including summability.
This is coefficient-space truth only until the concrete L2 bridge is checked. -/
theorem shift_complete_tail (a : ℝ) (ha : 0 < a)
    (N M : ℕ) (hNM : N < M) (v : ℕ → ℂ) (s : ℝ) :
    Summable (fun j : ℕ => ‖shiftCoefficient a N v s (M + j + 1)‖ ^ 2) ∧
      (∑' j : ℕ, ‖shiftCoefficient a N v s (M + j + 1)‖ ^ 2) ≤
        ((N : ℝ) + 1) / (Real.pi ^ 2 * ((M : ℝ) - (N : ℝ))) * headMass N v := by
  have hE : 0 ≤ headMass N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨hs, hb⟩ := complete_tail N M hNM (shiftCoefficient a N v s)
    (headMass N v * ((N : ℝ) + 1) / Real.pi ^ 2) (by positivity)
    (fun m hm => shiftCoefficient_sq a ha N v s m hm)
  refine ⟨hs, ?_⟩
  convert hb using 1 <;>
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, mul_pow] <;> ring

/-! Prime cutoff is arithmetic and distinct from both mode cutoffs N and M. -/
def primeMass (a : ℝ) : ℝ := ∑ r ∈ Finset.Icc 1 (primeCutoff a), primeWeight r

def symmetricPrimeEntry (a : ℝ) (n m : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (primeCutoff a), primeWeight r *
    (matrixEntry a n m (Real.log (r : ℝ)) +
      matrixEntry a n m (-Real.log (r : ℝ)))

/-- The physical source retains both shifts; the factor two is a triangle
bound on their sum, with no phase averaging or cancellation premise. -/
private lemma symmetricPrimeEntry_bound (a : ℝ) (ha : 0 < a)
    (n m : ℕ) (hnm : n < m) :
    |symmetricPrimeEntry a n m| ≤
      2 * primeMass a / (Real.pi * ((m : ℝ) - (n : ℝ))) := by
  have hd : 0 < Real.pi * ((m : ℝ) - (n : ℝ)) := by
    apply mul_pos Real.pi_pos
    exact sub_pos.mpr (by exact_mod_cast hnm)
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 (primeCutoff a),
        |primeWeight r * (matrixEntry a n m (Real.log (r : ℝ)) +
          matrixEntry a n m (-Real.log (r : ℝ)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 (primeCutoff a),
        primeWeight r * (2 / (Real.pi * ((m : ℝ) - (n : ℝ)))) := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_of_nonneg (prime_weight_nonnegative r)]
      apply mul_le_mul_of_nonneg_left _ (prime_weight_nonnegative r)
      have h := (abs_add_le _ _).trans (add_le_add
        (matrixEntry_uniform_bound a ha n m hnm (Real.log (r : ℝ)))
        (matrixEntry_uniform_bound a ha n m hnm (-Real.log (r : ℝ))))
      convert h using 1 <;> ring
    _ = _ := by rw [← Finset.sum_mul]; unfold primeMass; ring

/-- An actual whole-line integral of the original compressed finite action. -/
def primeCoefficient (a : ℝ) (N : ℕ) (v : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∫ x : ℝ, (mode a m x : ℂ) *
    primeAction a (primeCutoff a) (profile a (Finset.range (N + 1)) v) x

/-- Coefficient-level bridge to the original action. Integrability follows
from continuous factors on bounded physical overlap, rather than totalized
undefined integration. No orthogonal projection is presumed in this lemma. -/
theorem primeCoefficient_eq_shifts (a : ℝ) (N : ℕ) (v : ℕ → ℂ) (m : ℕ) :
    primeCoefficient a N v m =
      ∑ r ∈ Finset.Icc 1 (primeCutoff a), (primeWeight r : ℂ) *
        (shiftCoefficient a N v (Real.log (r : ℝ)) m +
          shiftCoefficient a N v (-Real.log (r : ℝ)) m) := by
  have hmode : Continuous (fun x => (mode a m x : ℂ)) := by unfold mode; fun_prop
  have hp := profile_continuous a (Finset.range (N + 1)) v
  have hi (r : ℕ) (s : ℝ) : Integrable (fun x => (mode a m x : ℂ) *
      compression a s (profile a (Finset.range (N + 1)) v) x) :=
    integrable_compression_product a s hmode hp
  have he : (fun x => (mode a m x : ℂ) *
      primeAction a (primeCutoff a) (profile a (Finset.range (N + 1)) v) x) =
      (fun x => ∑ r ∈ Finset.Icc 1 (primeCutoff a), (primeWeight r : ℂ) *
        ((mode a m x : ℂ) * compression a (Real.log (r : ℝ))
            (profile a (Finset.range (N + 1)) v) x +
         (mode a m x : ℂ) * compression a (-Real.log (r : ℝ))
            (profile a (Finset.range (N + 1)) v) x)) := by
    funext x
    unfold primeAction
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [primeCoefficient, he]
  rw [integral_finsetSum (f := fun r x => (primeWeight r : ℂ) *
    ((mode a m x : ℂ) * compression a (Real.log (r : ℝ))
        (profile a (Finset.range (N + 1)) v) x +
     (mode a m x : ℂ) * compression a (-Real.log (r : ℝ))
        (profile a (Finset.range (N + 1)) v) x)) _ (fun r _ =>
    ((hi r (Real.log (r : ℝ))).add (hi r (-Real.log (r : ℝ)))).const_mul _)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_const_mul, integral_add (hi r _) (hi r _)] <;> rfl

/-- Exact row expansion of the physical prime coefficient. Multiplying by
conj(v_m) and summing retains all mixed complex terms of the source form. -/
theorem primeCoefficient_eq (a : ℝ) (ha : 0 < a)
    (N : ℕ) (v : ℕ → ℂ) (m : ℕ) :
    primeCoefficient a N v m =
      ∑ n ∈ Finset.range (N + 1), v n * (symmetricPrimeEntry a n m : ℂ) := by
  rw [primeCoefficient_eq_shifts]
  simp_rw [shiftCoefficient_eq a ha, ← Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp only [symmetricPrimeEntry, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma primeCoefficient_sq (a : ℝ) (ha : 0 < a)
    (N : ℕ) (v : ℕ → ℂ) (m : ℕ) (hNm : N < m) :
    ‖primeCoefficient a N v m‖ ^ 2 ≤
      (4 * primeMass a ^ 2 * headMass N v * ((N : ℝ) + 1) / Real.pi ^ 2) *
        (((m : ℝ) - (N : ℝ))⁻¹) ^ 2 := by
  have hW : 0 ≤ primeMass a := Finset.sum_nonneg fun r _ => prime_weight_nonnegative r
  have hsep : 0 < (m : ℝ) - (N : ℝ) := sub_pos.mpr (by exact_mod_cast hNm)
  rw [primeCoefficient_eq a ha]
  have h := finite_row_sq N v (symmetricPrimeEntry a · m)
    (2 * primeMass a / (Real.pi * ((m : ℝ) - (N : ℝ)))) (by positivity) (by
      intro n hn
      have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
      have hnm : n < m := lt_of_le_of_lt hnN hNm
      have hnNr : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      exact (symmetricPrimeEntry_bound a ha n m hnm).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (by linarith :
            (m : ℝ) - (N : ℝ) ≤ (m : ℝ) - (n : ℝ)) Real.pi_pos.le)))
  convert h using 1 <;>
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, mul_pow] <;> ring

/-- The complete infinite coefficient allowance for the actual symmetric
prime-power action, with the exact arithmetic cutoff and both shifts. -/
theorem prime_complete_tail (a : ℝ) (ha : 0 < a)
    (N M : ℕ) (hNM : N < M) (v : ℕ → ℂ) :
    Summable (fun j : ℕ => ‖primeCoefficient a N v (M + j + 1)‖ ^ 2) ∧
      (∑' j : ℕ, ‖primeCoefficient a N v (M + j + 1)‖ ^ 2) ≤
        4 * primeMass a ^ 2 * ((N : ℝ) + 1) /
          (Real.pi ^ 2 * ((M : ℝ) - (N : ℝ))) * headMass N v := by
  have hE : 0 ≤ headMass N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨hs, hb⟩ := complete_tail N M hNM (primeCoefficient a N v)
    (4 * primeMass a ^ 2 * headMass N v * ((N : ℝ) + 1) / Real.pi ^ 2)
    (by positivity) (fun m hm => primeCoefficient_sq a ha N v m hm)
  refine ⟨hs, ?_⟩
  convert hb using 1 <;>
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, mul_pow] <;> ring

end PhysicalPrimeTwoCutoff
