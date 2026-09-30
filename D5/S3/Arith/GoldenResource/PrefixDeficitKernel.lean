/- GID: D5/S3/Arith/GoldenResource/PrefixDeficitKernel
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/PrefixDeficitKernel
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: A finite geometric-prefix deficit is an exact integral with uniform reserve bounds. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.GoldenResource.PrefixDeficitKernel

open Finset Real Set MeasureTheory

/-- The finite geometric normalization. -/
def S (a : ℕ) (t : ℝ) : ℝ := ∑ k ∈ range (a + 1), t ^ k

/-- The matching harmonic power prefix. -/
def Q (a : ℕ) (t : ℝ) : ℝ := ∑ k ∈ range a, t ^ (k + 1) / (k + 1)

/-- The triangular remaining-exponent polynomial. -/
def P (a : ℕ) (t : ℝ) : ℝ := ∑ k ∈ range (a + 1), ((a : ℝ) - k) * t ^ k

/-- The harmonic-prefix deficit of the geometric logarithm. -/
def D (a : ℕ) (t : ℝ) : ℝ := Q a t - Real.log (S a t)

/-- Exact interval-integral representation and two-sided uniform reserve,
with the stronger lower denominator `1 + z`. -/
theorem result (a : ℕ) (z : ℝ) (ha : 1 ≤ a) (hz : 0 < z) (hz1 : z < 1) :
    IntervalIntegrable (fun t : ℝ => t ^ a * P a t / S a t) volume 0 z ∧
    D a z = (∫ t in (0 : ℝ)..z, t ^ a * P a t / S a t) ∧
    (a : ℝ) * z ^ (a + 1) / (((a : ℝ) + 1) * (1 + z)) ≤ D a z ∧
    D a z ≤ (a : ℝ) * z ^ (a + 1) / ((a : ℝ) + 1) := by
  have hSstep (b : ℕ) (t : ℝ) : S (b + 1) t = S b t + t ^ (b + 1) := by
    exact sum_range_succ _ _
  have hPstep (b : ℕ) (t : ℝ) : P (b + 1) t = P b t + S b t := by
    change (∑ k ∈ range (b + 1 + 1), (((b + 1 : ℕ) : ℝ) - k) * t ^ k) =
      (∑ k ∈ range (b + 1), ((b : ℝ) - k) * t ^ k) + ∑ k ∈ range (b + 1), t ^ k
    rw [sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, sub_self, zero_mul,
      add_zero]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    ring
  have hgeom (b : ℕ) (t : ℝ) : (1 - t) * S b t = 1 - t ^ (b + 1) := by
    simpa only [S, mul_comm] using geom_sum_mul_neg t (b + 1)
  have htri (b : ℕ) (t : ℝ) : (1 - t) * P b t = (b : ℝ) + 1 - S b t := by
    induction b with
    | zero => simp [P, S]
    | succ b ih =>
      rw [hPstep, mul_add, ih, hgeom, hSstep]
      push_cast
      ring
  have hSpos (b : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 < S b t := by
    have h := single_le_sum (f := fun k : ℕ => t ^ k)
      (fun k _ => pow_nonneg ht k) (mem_range.mpr (Nat.zero_lt_succ b))
    have : (1 : ℝ) ≤ S b t := by simpa [S] using h
    linarith
  have hkernelLower (b : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      (b : ℝ) * S b t ≤ (1 + t) * P b t := by
    induction b with
    | zero => simp [P, S]
    | succ b ih =>
      have htail : ((b : ℝ) + 1) * t ^ (b + 1) ≤ t * S b t := by
        calc
          _ = ∑ _k ∈ range (b + 1), t ^ (b + 1) := by simp
          _ ≤ ∑ k ∈ range (b + 1), t ^ (k + 1) := by
            apply sum_le_sum
            intro k hk
            have hk' := mem_range.mp hk
            exact pow_le_pow_of_le_one ht ht1 (by omega)
          _ = t * S b t := by
            simp only [S, mul_sum, pow_succ]
            apply sum_congr rfl
            intro k hk
            ring
      rw [hPstep, hSstep]
      push_cast
      nlinarith
  have hkernelUpper (b : ℕ) (t : ℝ) (ht : 0 ≤ t) : P b t ≤ (b : ℝ) * S b t := by
    dsimp [P, S]
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht k)
    exact sub_le_self _ (Nat.cast_nonneg k)
  have hderiv (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
      HasDerivAt (D a) (t ^ a * P a t / S a t) t := by
    let slope : ℝ := ∑ k ∈ range (a + 1), (k : ℝ) * t ^ (k - 1)
    have hs : HasDerivAt (S a) slope t := by
      exact HasDerivAt.fun_sum fun k hk => hasDerivAt_pow k t
    have hq : HasDerivAt (Q a) (∑ k ∈ range a, t ^ k) t := by
      apply HasDerivAt.fun_sum
      intro k hk
      apply ((hasDerivAt_pow (k + 1) t).div_const (k + 1 : ℝ)).congr_deriv
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      exact mul_div_cancel_left₀ (t ^ k) (by positivity : (k : ℝ) + 1 ≠ 0)
    have hdgeom : HasDerivAt (fun x : ℝ => (1 - x) * S a x)
        (-((a : ℝ) + 1) * t ^ a) t := by
      have heq : (fun x : ℝ => (1 - x) * S a x) = fun x => 1 - x ^ (a + 1) :=
        funext (hgeom a)
      rw [heq]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, neg_mul] using
        (hasDerivAt_pow (a + 1) t).const_sub 1
    have hcancel : -S a t + (1 - t) * slope = -((a : ℝ) + 1) * t ^ a := by
      have hh := (((hasDerivAt_id t).const_sub 1).mul hs).unique hdgeom
      simpa only [neg_mul, one_mul, id_eq] using hh
    have hsplit : S a t = (∑ k ∈ range a, t ^ k) + t ^ a := by
      exact sum_range_succ _ _
    have hSnz := (hSpos a t ht).ne'
    have htnz : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
    have htr := htri a t
    have hg := hgeom a t
    have hpow : t ^ (a + 1) = t ^ a * t := pow_succ t a
    change HasDerivAt (fun x => Q a x - Real.log (S a x)) _ t
    apply (hq.sub (hs.log hSnz)).congr_deriv
    apply (eq_div_iff hSnz).mpr
    field_simp [hSnz]
    apply mul_left_cancel₀ htnz
    have hprev : (1 - t) * (∑ k ∈ range a, t ^ k) = 1 - t ^ a := by
      simpa only [mul_comm] using geom_sum_mul_neg t a
    rw [hpow] at hg
    linear_combination (∑ k ∈ range a, t ^ k) * hg - hcancel - t ^ a * htr +
      t ^ a * hprev - (1 - t ^ a) * hsplit
  have hScont : Continuous (S a) := by
    exact continuous_finsetSum _ fun k hk => continuous_pow k
  have hPcont : Continuous (P a) := by
    exact continuous_finsetSum _ fun k hk => continuous_const.mul (continuous_pow k)
  have hcont : ContinuousOn (fun t : ℝ => t ^ a * P a t / S a t) (Icc 0 z) := by
    exact ((continuous_pow a).mul hPcont).continuousOn.div hScont.continuousOn
      (fun t ht => (hSpos a t ht.1).ne')
  have hint : IntervalIntegrable (fun t : ℝ => t ^ a * P a t / S a t) volume 0 z :=
    hcont.intervalIntegrable_of_Icc hz.le
  have hidentity : D a z = ∫ t in (0 : ℝ)..z, t ^ a * P a t / S a t := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => by
        have hh : t ∈ Icc (0 : ℝ) z := by simpa [uIcc_of_le hz.le] using ht
        exact hderiv t hh.1 (hh.2.trans_lt hz1)) hint
    have hzero : D a 0 = 0 := by simp [D, Q, S]
    simpa only [hzero, sub_zero] using h.symm
  have hminor : IntervalIntegrable (fun t : ℝ => (a : ℝ) * t ^ a / (1 + z)) volume 0 z :=
    (continuous_const.mul (continuous_pow a) |>.div_const (1 + z)).intervalIntegrable 0 z
  have hmajor : IntervalIntegrable (fun t : ℝ => (a : ℝ) * t ^ a) volume 0 z :=
    (continuous_const.mul (continuous_pow a)).intervalIntegrable 0 z
  have hlower := intervalIntegral.integral_mono_on hz.le hminor hint (fun t ht => by
    have ht1 : t ≤ 1 := (ht.2.trans hz1.le)
    have hsp := hSpos a t ht.1
    have hpoly := hkernelLower a t ht.1 ht1
    have hpos : 0 ≤ P a t := by
      have h := hkernelLower a t ht.1 ht1
      have han : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have htp : 0 < 1 + t := by linarith [ht.1]
      nlinarith
    apply (div_le_div_iff₀ (by linarith : 0 < 1 + z) hsp).mpr
    have hcompare : (a : ℝ) * S a t ≤ (1 + z) * P a t :=
      hpoly.trans (mul_le_mul_of_nonneg_right (by linarith [ht.2]) hpos)
    nlinarith [mul_le_mul_of_nonneg_right hcompare (pow_nonneg ht.1 a)])
  have hupper := intervalIntegral.integral_mono_on hz.le hint hmajor (fun t ht => by
    apply (div_le_iff₀ (hSpos a t ht.1)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hkernelUpper a t ht.1) (pow_nonneg ht.1 a)])
  have hminorEval : (∫ t in (0 : ℝ)..z, (a : ℝ) * t ^ a / (1 + z)) =
      (a : ℝ) * z ^ (a + 1) / (((a : ℝ) + 1) * (1 + z)) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero a), sub_zero]
    rw [← mul_div_assoc, div_div]
  have hmajorEval : (∫ t in (0 : ℝ)..z, (a : ℝ) * t ^ a) =
      (a : ℝ) * z ^ (a + 1) / ((a : ℝ) + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero a), sub_zero]
    ring
  exact ⟨hint, hidentity, by simpa only [hminorEval, ← hidentity] using hlower,
    by simpa only [hmajorEval, ← hidentity] using hupper⟩

#print axioms result

end D5.S3.Arith.GoldenResource.PrefixDeficitKernel
