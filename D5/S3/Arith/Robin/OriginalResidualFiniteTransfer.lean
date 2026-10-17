/- GID: D5/S3/Arith/Robin/OriginalResidualFiniteTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalResidualFiniteTransfer
   mirror-E: none(waiver:finite-analytic-inequality)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius, mathlib/module/Mathlib.Algebra.BigOperators.Module]
   utility: none
   digest: The actual finite Mobius floor residual has a two-moment transfer bound with centered periodic variation, weighted floor counting and exact prefix and constant payments. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import D5.S3.Arith.Robin.ActualOddMobiusFinitePairing

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.OriginalResidualFiniteTransfer

open D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix)

/-- Absolute mass on the complete original integer block. -/
def mass (N : ℕ) (a : ℕ → ℝ) : ℝ := ∑ m ∈ Ico N (2 * N), |a m|

/-- The actual first absolute moment, before replacing indices by a block ceiling. -/
def firstAbsoluteMoment (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Ico N (2 * N), (m : ℝ) * |a m|

/-- Variation of the block extended by zero, including both endpoint jumps. -/
def variation (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  |a N| + (∑ m ∈ Ico N (2 * N - 1), |a (m + 1)-a m|) + |a (2 * N - 1)|

/-- Natural division is the literal floor of the nonnegative real quotient. -/
def floorPair (N : ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Ico N (2 * N), a m * (m / d : ℕ)

def logPair (N : ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  Real.log ((N : ℝ)/d) * floorPair N a d

def logDifference (N : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  logPair N a k-logPair N a (k + 1)

def weightedVariation (N h : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Ico h N, (k : ℝ)*|logDifference N a k|

/-- All original Mobius indices are retained. -/
def coefficient (N d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ)*Real.log ((N : ℝ)/d)/Real.log N

def response (N m : ℕ) : ℝ :=
  1 + (∑ d ∈ Ioc 0 N, coefficient N d / d)*(m : ℝ) -
    ∑ d ∈ Ioc 0 N, coefficient N d*(m / d : ℕ)

def residual (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Ico N (2 * N), a m * response N m

/-- The +2 pays the literal -2 in a supplied spectral prefix. -/
def replacement (N q : ℕ) (a F : ℕ → ℝ) : ℝ :=
  -(∑ k ∈ Ico (q + 1) N, (F k+2)*logDifference N a k)/Real.log N

/-- Integer remainders centered at their exact residue mean. -/
def centered (d m : ℕ) : ℝ :=
  (m % d : ℕ)/(d : ℝ)-((d : ℝ)-1)/(2 * d)

private def periodicPrimitive (d m : ℕ) : ℝ :=
  (m % d : ℕ)*((m % d : ℕ)-(d : ℝ))/(2 * d)

private theorem primitive_step {d : ℕ} (hd : 0 < d) (m : ℕ) :
    periodicPrimitive d (m + 1)-periodicPrimitive d m = centered d m := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hr := Nat.mod_lt m hd
  have hm : (m + 1)%d = (m % d+1)%d := (Nat.mod_add_mod m d 1).symm
  by_cases he : m % d+1 = d
  · have hs : (m + 1)%d = 0 := by rw [hm, he, Nat.mod_self]
    have he' : ((m % d : ℕ) : ℝ)+1 = d := by exact_mod_cast he
    simp only [periodicPrimitive, centered, hs, Nat.cast_zero, zero_mul, zero_div]
    field_simp
    nlinarith
  · have hs : (m + 1)%d = m % d+1 := by rw [hm, Nat.mod_eq_of_lt (by omega)]
    simp only [periodicPrimitive, centered, hs, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring

private theorem primitive_bound {d : ℕ} (hd : 0 < d) (m : ℕ) :
    |periodicPrimitive d m| ≤ (d : ℝ)/2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ ((m % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr : ((m % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt m hd).le
  have hp : periodicPrimitive d m ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr0 (by linarith))
      (by positivity)
  rw [abs_of_nonpos hp, periodicPrimitive]
  rw [← neg_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mpr
  have hprod : ((m % d : ℕ) : ℝ)*((d : ℝ)-((m % d : ℕ) : ℝ)) ≤ (d : ℝ)*d :=
    mul_le_mul hr (by linarith) (by linarith) (by positivity)
  nlinarith


private theorem centered_prefix {d : ℕ} (hd : 0 < d) (b l : ℕ) :
    |∑ m ∈ Ico b (b + l), centered d m| ≤ (d : ℝ) := by
  have he : (∑ m ∈ Ico b (b + l), centered d m) =
      periodicPrimitive d (b + l)-periodicPrimitive d b := by
    simp_rw [← primitive_step hd]
    exact sum_Ico_sub _ (by omega)
  rw [he]
  exact (abs_sub _ _).trans (by linarith [primitive_bound hd (b + l), primitive_bound hd b])

theorem centered_floor {d : ℕ} (hd : 0 < d) (m : ℕ) :
    (m / d : ℕ) = (m : ℝ)/d-centered d m-((d : ℝ)-1)/(2 * d) := by
  have he := Nat.mod_add_div m d
  have he' : ((m % d : ℕ) : ℝ)+(d : ℝ)*(m / d : ℕ) = m := by exact_mod_cast he
  unfold centered
  field_simp
  nlinarith

private theorem pair_centered {N d : ℕ} (a : ℕ → ℝ) (hd : 0 < d)
    (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0) :
    floorPair N a d = -(∑ m ∈ Ico N (2 * N), a m*centered d m) := by
  unfold floorPair
  simp_rw [centered_floor hd, mul_sub]
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul]
  have he : (∑ m ∈ Ico N (2 * N), a m*((m : ℝ)/d)) = 0 := by
    calc
      _ = (∑ m ∈ Ico N (2 * N), (m : ℝ)*a m)/d := by
        rw [sum_div]
        apply sum_congr rfl
        intro m _
        ring
      _ = 0 := by rw [hm, zero_div]
  rw [he, hz]
  ring

private theorem pair_endpoints {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ)
    (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0) :
    floorPair N a 1 = 0 ∧ floorPair N a N = 0 := by
  constructor
  · simpa [floorPair, mul_comm] using hm
  · have he : ∀ m ∈ Ico N (2 * N), m/N = 1 := by
      intro m hm
      have hm' := mem_Ico.mp hm
      apply Nat.div_eq_of_lt_le <;> omega
    calc
      floorPair N a N = ∑ m ∈ Ico N (2 * N), a m*1 := by
        apply sum_congr rfl
        intro m hm
        rw [he m hm, Nat.cast_one]
      _ = 0 := by simpa using hz

private theorem mass_nonneg (N : ℕ) (a : ℕ → ℝ) : 0 ≤ mass N a :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem variation_nonneg (N : ℕ) (a : ℕ → ℝ) : 0 ≤ variation N a := by
  unfold variation
  positivity

private theorem centered_bound {d : ℕ} (hd : 0 < d) (m : ℕ) :
    |centered d m| ≤ 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ ((m % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr : ((m % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt m hd).le
  have hfrac : 0 ≤ ((m % d : ℕ) : ℝ)/(d : ℝ) := div_nonneg hr0 hd'.le
  have hfrac1 : ((m % d : ℕ) : ℝ)/(d : ℝ) ≤ 1 := (div_le_one hd').mpr hr
  have hc0 : 0 ≤ ((d : ℝ)-1)/(2 * d) := div_nonneg (by linarith) (by positivity)
  have hc1 : ((d : ℝ)-1)/(2 * d) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  exact abs_le.mpr ⟨by unfold centered; linarith, by unfold centered; linarith⟩

private theorem pair_mass_bound {N d : ℕ} (a : ℕ → ℝ) (hd : 0 < d)
    (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0) :
    |floorPair N a d| ≤ mass N a := by
  rw [pair_centered a hd hz hm, abs_neg]
  calc
    _ ≤ ∑ m ∈ Ico N (2 * N), |a m*centered d m| := abs_sum_le_sum_abs _ _
    _ ≤ mass N a := by
      apply sum_le_sum
      intro m _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (centered_bound hd m) (abs_nonneg _)).trans_eq
        (mul_one _)

/-- The constant cancels in the signed telescope, before any absolute values. -/
private theorem centered_pair_by_parts {N d : ℕ} (hN : 0 < N) (a : ℕ → ℝ)
    (hd : 0 < d) (s : ℝ) :
    (∑ m ∈ Ico N (2 * N), a m*centered d m) =
      a (2 * N - 1)*(periodicPrimitive d (2 * N)+s)-
        a N*(periodicPrimitive d N+s)-
          ∑ m ∈ Ico N (2 * N - 1),
            (a (m+1)-a m)*(periodicPrimitive d (m+1)+s) := by
  have hp (n : ℕ) : (∑ m ∈ range n, centered d m) = periodicPrimitive d n := by
    rw [range_eq_Ico]
    simp_rw [← primitive_step hd]
    rw [sum_Ico_sub _ (Nat.zero_le n)]
    simp [periodicPrimitive]
  have he := sum_Ico_by_parts a (centered d) (by omega : N < 2 * N)
  simp only [smul_eq_mul] at he
  simp_rw [hp] at he
  have hcancel : (∑ m ∈ Ico N (2 * N - 1), (a (m+1)-a m)) =
      a (2 * N - 1)-a N := sum_Ico_sub a (by omega)
  have hs : (∑ m ∈ Ico N (2 * N - 1),
      (a (m+1)-a m)*(periodicPrimitive d (m+1)+s)) =
      (∑ m ∈ Ico N (2 * N - 1), (a (m+1)-a m)*periodicPrimitive d (m+1))+
        (a (2 * N - 1)-a N)*s := by
    simp_rw [mul_add]
    rw [sum_add_distrib, ← sum_mul, hcancel]
  rw [he, hs]
  ring

private theorem centered_pair_of_primitive_range {N d : ℕ} (hN : 0 < N)
    (a : ℕ → ℝ) (hd : 0 < d) (s C : ℝ)
    (hp : ∀ m, |periodicPrimitive d m+s| ≤ C) :
    |∑ m ∈ Ico N (2 * N), a m*centered d m| ≤ C*variation N a := by
  rw [centered_pair_by_parts hN a hd s]
  calc
    _ ≤ |a (2 * N - 1)*(periodicPrimitive d (2 * N)+s)| +
        |a N*(periodicPrimitive d N+s)| +
        |∑ m ∈ Ico N (2 * N - 1),
          (a (m + 1)-a m)*(periodicPrimitive d (m+1)+s)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ |a (2 * N - 1)| *C + |a N| *C +
        ∑ m ∈ Ico N (2 * N - 1), |a (m + 1)-a m| *C := by
      apply add_le_add
      · apply add_le_add <;> rw [abs_mul]
        · exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
      · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
        intro m _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
    _ = C*variation N a := by rw [← sum_mul]; unfold variation; ring

theorem centered_pair_variation_bound {N d : ℕ} (hN : 0 < N) (a : ℕ → ℝ)
    (hd : 0 < d) :
    |∑ m ∈ Ico N (2 * N), a m*centered d m| ≤ (d : ℝ)*variation N a := by
  apply centered_pair_of_primitive_range hN a hd 0 d
  intro m
  simpa only [add_zero] using (primitive_bound hd m).trans
    (by have := Nat.cast_nonneg (α := ℝ) d; linarith)

private theorem primitive_midpoint_bound {d : ℕ} (hd : 0 < d) (m : ℕ) :
    |periodicPrimitive d m+(d : ℝ)/16| ≤ (d : ℝ)/16 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ ((m % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr : ((m % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt m hd).le
  have hhi : periodicPrimitive d m ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr0 (by linarith))
      (by positivity)
  have hlo : -(d : ℝ)/8 ≤ periodicPrimitive d m := by
    unfold periodicPrimitive
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*d)).mpr
    nlinarith [sq_nonneg (2*((m % d : ℕ) : ℝ)-(d : ℝ))]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Midpoint centering preserves the primitive step and pays both zero-extension jumps. -/
theorem centered_pair_variation_sharp_bound {N d : ℕ} (hN : 0 < N) (a : ℕ → ℝ)
    (hd : 0 < d) :
    |∑ m ∈ Ico N (2 * N), a m*centered d m| ≤ (d : ℝ)/16*variation N a := by
  exact centered_pair_of_primitive_range hN a hd ((d : ℝ)/16) ((d : ℝ)/16)
    (primitive_midpoint_bound hd)

private theorem pair_variation_bound {N d : ℕ} (hN : 0 < N) (a : ℕ → ℝ)
    (hd : 0 < d) (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0) :
    |floorPair N a d| ≤ (d : ℝ)*variation N a := by
  rw [pair_centered a hd hz hm, abs_neg]
  exact centered_pair_variation_bound hN a hd

theorem reciprocal_log_step {k : ℕ} (hk : 0 < k) :
    (1 : ℝ) / (k + 1 : ℕ) ≤ Real.log (k + 1 : ℕ) - Real.log (k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have he := Real.one_sub_inv_le_log_of_pos
    (div_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) hk')
  rw [Real.log_div (by positivity) hk'.ne'] at he
  convert he using 1
  push_cast
  field_simp
  <;> ring

/-- Exact weighted counting of the floor drops, with its terminal floor retained. -/
private theorem weighted_floor_identity (m : ℕ) {h N : ℕ} (hh : 0 < h)
    (hN : h < N) :
    (∑ k ∈ Ico h N, (k : ℝ)*((m / k : ℕ)-(m / (k + 1) : ℕ) : ℝ)) =
      (h : ℝ)*(m / h : ℕ) +
        (∑ k ∈ Ico h (N - 1), ((m / (k + 1) : ℕ) : ℝ)) -
          (N - 1 : ℕ)*(m / N : ℕ) := by
  let f : ℕ → ℝ := fun k => (m / k : ℕ)
  have hp (n : ℕ) : (∑ k ∈ range n, (f k-f (k + 1))) = -f n := by
    rw [sum_range_sub']
    simp [f]
  have he := sum_Ico_by_parts (fun k : ℕ => (k : ℝ))
    (fun k => f k-f (k + 1)) hN
  simp only [smul_eq_mul, hp, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
    one_mul, mul_neg, sum_neg_distrib] at he
  change (∑ k ∈ Ico h N, (k : ℝ)*(f k-f (k + 1))) = _
  rw [he]
  dsimp [f]
  ring

/-- On each partial prefix the terminal floor pays the entire negative endpoint term. -/
theorem weighted_floor_prefix_bound {h j m : ℕ} (hh : 0 < h) (hj : h ≤ j)
    (hm : j < m) :
    (∑ k ∈ Ico h (j + 1), (k : ℝ) *
      (((m / k : ℕ) : ℝ) - ((m / (k + 1) : ℕ) : ℝ))) ≤
        (m : ℝ) * (1 + Real.log ((j : ℝ) / h)) - j := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hj' : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le hh hj)
  have hs : (∑ k ∈ Ico h j, (1 : ℝ) / (k + 1 : ℕ)) ≤
      Real.log ((j : ℝ) / h) := by
    calc
      _ ≤ ∑ k ∈ Ico h j, (Real.log (k + 1 : ℕ) - Real.log (k : ℝ)) := by
        apply sum_le_sum
        intro k hk
        exact reciprocal_log_step (by have := mem_Ico.mp hk; omega)
      _ = _ := by
        rw [sum_Ico_sub (fun k : ℕ => Real.log (k : ℝ)) hj,
          Real.log_div hj'.ne' hh'.ne']
  have hsum : (∑ k ∈ Ico h j, ((m / (k + 1) : ℕ) : ℝ)) ≤
      (m : ℝ) * Real.log ((j : ℝ) / h) := by
    calc
      _ ≤ ∑ k ∈ Ico h j, (m : ℝ) * ((1 : ℝ) / (k + 1 : ℕ)) := by
        apply sum_le_sum
        intro k _
        simpa only [mul_one_div] using (Nat.cast_div_le (m := m) (n := k + 1) :
          ((m / (k + 1) : ℕ) : ℝ) ≤ (m : ℝ) / (k + 1 : ℕ))
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
  have hfirst : (h : ℝ) * (m / h : ℕ) ≤ m := by
    calc
      _ ≤ (h : ℝ) * ((m : ℝ) / h) :=
        mul_le_mul_of_nonneg_left (Nat.cast_div_le (m := m) (n := h)) hh'.le
      _ = _ := by field_simp
  have hterminal : (1 : ℕ) ≤ m / (j + 1) := by
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hterminal' : (j : ℝ) ≤ (j : ℝ) * (m / (j + 1) : ℕ) := by
    have ht : (1 : ℝ) ≤ (m / (j + 1) : ℕ) := by exact_mod_cast hterminal
    nlinarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]
  have hid := weighted_floor_identity m hh (show h < j + 1 by omega)
  simp only [Nat.add_sub_cancel] at hid
  rw [hid]
  linarith

theorem weighted_floor_bound {N h m : ℕ} (hh : 0 < h) (hN : h < N)
    (hm : m < 2 * N) :
    (∑ k ∈ Ico h N, (k : ℝ)*((m / k : ℕ)-(m / (k + 1) : ℕ) : ℝ)) ≤
      2 * N * (1 + Real.log (2 * (N : ℝ)/h)) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log ((N : ℝ)/h) := Real.log_nonneg
    ((one_le_div hh').mpr (by exact_mod_cast hN.le))
  have hs : (∑ k ∈ Ico h N, (1 : ℝ) / (k + 1 : ℕ)) ≤ Real.log ((N : ℝ)/h) := by
    calc
      _ ≤ ∑ k ∈ Ico h N, (Real.log (k + 1 : ℕ)-Real.log (k : ℝ)) := by
        apply sum_le_sum
        intro k hk
        exact reciprocal_log_step (by have := mem_Ico.mp hk; omega)
      _ = Real.log ((N : ℝ)/h) := by
        rw [sum_Ico_sub (fun k : ℕ => Real.log (k : ℝ)) hN.le,
          Real.log_div hN'.ne' hh'.ne']
  have hs' : (∑ k ∈ Ico h (N - 1), ((m / (k + 1) : ℕ) : ℝ)) ≤
      (m : ℝ)*Real.log ((N : ℝ)/h) := by
    calc
      _ ≤ ∑ k ∈ Ico h N, ((m / (k + 1) : ℕ) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (by omega))
          (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ k ∈ Ico h N, (m : ℝ)*((1 : ℝ)/(k + 1 : ℕ)) := by
        apply sum_le_sum
        intro k _
        simpa only [mul_one_div] using (Nat.cast_div_le (m := m) (n := k + 1) :
          ((m / (k + 1) : ℕ) : ℝ) ≤ (m : ℝ)/(k + 1 : ℕ))
      _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
  have hfirst : (h : ℝ)*(m / h : ℕ) ≤ m := by
    have he := (Nat.cast_div_le (m := m) (n := h) : ((m / h : ℕ) : ℝ) ≤ (m : ℝ)/h)
    calc
      _ ≤ (h : ℝ)*((m : ℝ)/h) := mul_le_mul_of_nonneg_left he hh'.le
      _ = _ := by field_simp
  rw [weighted_floor_identity m hh hN]
  have ht : (0 : ℝ) ≤ (N - 1 : ℕ)*(m / N : ℕ) := by positivity
  have hm' : (m : ℝ) ≤ 2 * N := by exact_mod_cast hm.le
  have hl : Real.log ((N : ℝ)/h) ≤ Real.log (2 * (N : ℝ)/h) :=
    Real.log_le_log (div_pos hN' hh')
      (div_le_div_of_nonneg_right (by linarith) hh'.le)
  calc
    _ ≤ (m : ℝ)*(1+Real.log ((N : ℝ)/h)) := by linarith
    _ ≤ 2 * N * (1+Real.log ((N : ℝ)/h)) :=
      mul_le_mul_of_nonneg_right hm' (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem log_bounds {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    0 ≤ Real.log ((N : ℝ)/d) ∧ Real.log ((N : ℝ)/d) ≤ Real.log N := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hd hdN)
  constructor
  · exact Real.log_nonneg ((one_le_div hd').mpr (by exact_mod_cast hdN))
  · rw [Real.log_div hN'.ne' hd'.ne']
    have he : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
    linarith

private theorem pair_difference_bound {N k : ℕ} (a : ℕ → ℝ) (hk : 0 < k) :
    |floorPair N a k-floorPair N a (k + 1)| ≤
      ∑ m ∈ Ico N (2 * N), |a m| *
        (((m / k : ℕ) : ℝ)-((m / (k + 1) : ℕ) : ℝ)) := by
  have he : floorPair N a k-floorPair N a (k + 1) =
      ∑ m ∈ Ico N (2 * N), a m *
        (((m / k : ℕ) : ℝ)-((m / (k + 1) : ℕ) : ℝ)) := by
    unfold floorPair
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    ring
  rw [he]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  apply sum_congr rfl
  intro m _
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ?_)]
  exact_mod_cast Nat.div_le_div_left (by omega : k ≤ k + 1) hk

theorem weighted_log_step {k : ℕ} (hk : 0 < k) :
    (k : ℝ)*(Real.log (k + 1 : ℕ)-Real.log (k : ℝ)) ≤ 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have he := Real.log_le_sub_one_of_pos
    (div_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) hk')
  rw [Real.log_div (by positivity) hk'.ne'] at he
  calc
    _ ≤ (k : ℝ)*((k + 1 : ℕ)/(k : ℝ)-1) := mul_le_mul_of_nonneg_left he hk'.le
    _ = 1 := by push_cast; field_simp; ring

private theorem pair_firstMoment_bound {N d : ℕ} (a : ℕ → ℝ) (hd : 0 < d)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ) * a m = 0) :
    |floorPair N a d| ≤ mass N a := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hquot (m : ℕ) : ((m / d : ℕ) : ℝ) =
      (m : ℝ) / d - (m % d : ℕ) / (d : ℝ) := by
    rw [centered_floor hd]
    unfold centered
    ring
  have hlinear : (∑ m ∈ Ico N (2 * N), a m * ((m : ℝ) / d)) = 0 := by
    calc
      _ = (∑ m ∈ Ico N (2 * N), (m : ℝ) * a m) / d := by
        rw [sum_div]
        apply sum_congr rfl
        intro m _
        ring
      _ = 0 := by rw [hm, zero_div]
  have hid : floorPair N a d =
      -(∑ m ∈ Ico N (2 * N), a m * ((m % d : ℕ) / (d : ℝ))) := by
    unfold floorPair
    simp_rw [hquot, mul_sub]
    rw [sum_sub_distrib, hlinear, zero_sub]
  rw [hid, abs_neg]
  calc
    _ ≤ ∑ m ∈ Ico N (2 * N), |a m * ((m % d : ℕ) / (d : ℝ))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ mass N a := by
      apply sum_le_sum
      intro m _
      have hnonneg : 0 ≤ (m % d : ℕ) / (d : ℝ) := by positivity
      have hone : (m % d : ℕ) / (d : ℝ) ≤ 1 :=
        (div_le_one hd').mpr (by exact_mod_cast (Nat.mod_lt m hd).le)
      rw [abs_mul, abs_of_nonneg hnonneg]
      exact (mul_le_mul_of_nonneg_left hone (abs_nonneg _)).trans_eq (mul_one _)

/-- Joint floor-prefix cancellation, using the first moment alone. -/
theorem weightedVariation_firstMoment_bound {N h : ℕ} (hh : 0 < h) (hN : h ≤ N)
    (a : ℕ → ℝ) (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ) * a m = 0) :
    weightedVariation N h a ≤ firstAbsoluteMoment N a *
      (Real.log ((N : ℝ) / h) + Real.log ((N : ℝ) / h) ^ 2 / 2) := by
  rcases lt_or_eq_of_le hN with hlt | rfl
  swap
  · simp [weightedVariation, div_self (show (h : ℝ) ≠ 0 by positivity)]
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hh hN)
  let A := mass N a
  let B := firstAbsoluteMoment N a
  let u := Real.log ((N : ℝ) / h)
  let x (k : ℕ) := Real.log ((N : ℝ) / k)
  let s (k : ℕ) := Real.log ((k : ℝ) / h)
  let δ (k : ℕ) := Real.log (k + 1 : ℕ) - Real.log (k : ℝ)
  let E (k : ℕ) := ∑ m ∈ Ico N (2 * N), |a m| *
    (((m / k : ℕ) : ℝ) - ((m / (k + 1) : ℕ) : ℝ))
  have hB : 0 ≤ B := sum_nonneg fun m _ => mul_nonneg (Nat.cast_nonneg m) (abs_nonneg _)
  have hδ (k : ℕ) (hk : h ≤ k) : 0 ≤ δ k := by
    have hkp : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hh hk)
    exact sub_nonneg.mpr (Real.log_le_log hkp (by push_cast; linarith))
  have htail (k : ℕ) (hk : h ≤ k) (hkN : k ≤ N) :
      x k = ∑ j ∈ Ico k N, δ j := by
    have hkp : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hh hk)
    dsimp [x, δ]
    rw [sum_Ico_sub (fun j : ℕ => Real.log (j : ℝ)) hkN,
      Real.log_div hNp.ne' hkp.ne']
  have hprefix (j : ℕ) (hj : j ∈ Ico h N) :
      (∑ k ∈ Ico h (j + 1), (k : ℝ) * E k) ≤ B * (1 + s j) - j * A := by
    have hji := mem_Ico.mp hj
    calc
      _ = ∑ m ∈ Ico N (2 * N), |a m| *
          (∑ k ∈ Ico h (j + 1), (k : ℝ) *
            (((m / k : ℕ) : ℝ) - ((m / (k + 1) : ℕ) : ℝ))) := by
        dsimp [E]
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro m _
        apply sum_congr rfl
        intro k _
        ring
      _ ≤ ∑ m ∈ Ico N (2 * N), |a m| *
          ((m : ℝ) * (1 + s j) - j) := by
        apply sum_le_sum
        intro m hm'
        exact mul_le_mul_of_nonneg_left
          (weighted_floor_prefix_bound hh hji.1 (by have := mem_Ico.mp hm'; omega))
          (abs_nonneg _)
      _ = (∑ m ∈ Ico N (2 * N), (m : ℝ) * |a m| * (1 + s j)) -
          (∑ m ∈ Ico N (2 * N), (j : ℝ) * |a m|) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro m _
        ring
      _ = _ := by
        rw [← sum_mul, ← mul_sum]
        rfl
  have hcount : (∑ k ∈ Ico h N, (k : ℝ) * x k * E k) ≤
      B * (∑ j ∈ Ico h N, δ j * (1 + s j)) - A * (∑ j ∈ Ico h N, (j : ℝ) * δ j) := by
    calc
      _ = ∑ k ∈ Ico h N, ∑ j ∈ Ico k N, δ j * ((k : ℝ) * E k) := by
        apply sum_congr rfl
        intro k hk
        rw [htail k (mem_Ico.mp hk).1 (mem_Ico.mp hk).2.le]
        simp_rw [mul_sum, sum_mul]
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ j ∈ Ico h N, δ j * (∑ k ∈ Ico h (j + 1), (k : ℝ) * E k) := by
        rw [sum_Ico_Ico_comm]
        simp_rw [← mul_sum]
      _ ≤ ∑ j ∈ Ico h N, δ j * (B * (1 + s j) - j * A) := by
        apply sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hprefix j hj) (hδ j (mem_Ico.mp hj).1)
      _ = ∑ j ∈ Ico h N, (B * (δ j * (1 + s j)) - A * ((j : ℝ) * δ j)) := by
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
  have hpoint (k : ℕ) (hk : k ∈ Ico h N) :
      (k : ℝ) * |logDifference N a k| ≤ (k : ℝ) * x k * E k + A * ((k : ℝ) * δ k) := by
    have hki := mem_Ico.mp hk
    have hkp : 0 < k := lt_of_lt_of_le hh hki.1
    have hkp' : (0 : ℝ) < k := by exact_mod_cast hkp
    have hx : 0 ≤ x k := (log_bounds hkp hki.2.le).1
    have hid : logDifference N a k =
        x k * (floorPair N a k - floorPair N a (k + 1)) + δ k * floorPair N a (k + 1) := by
      dsimp [logDifference, logPair, x, δ]
      rw [Real.log_div hNp.ne' hkp'.ne', Real.log_div hNp.ne' (by positivity)]
      ring
    have hraw : |logDifference N a k| ≤ x k * E k + δ k * A := by
      rw [hid]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg hx]
        exact mul_le_mul_of_nonneg_left (pair_difference_bound a hkp) hx
      · rw [abs_mul, abs_of_nonneg (hδ k hki.1)]
        exact mul_le_mul_of_nonneg_left (pair_firstMoment_bound a (by omega) hm) (hδ k hki.1)
    exact (mul_le_mul_of_nonneg_left hraw hkp'.le).trans_eq (by ring)
  have hcancel : weightedVariation N h a ≤ B * (∑ j ∈ Ico h N, δ j * (1 + s j)) := by
    have hp := sum_le_sum hpoint
    simp only [sum_add_distrib, ← mul_sum] at hp
    change weightedVariation N h a ≤ _ at hp
    linarith
  have hsδ (k : ℕ) (hk : k ∈ Ico h N) : s (k + 1) = s k + δ k := by
    have hkp : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hh (mem_Ico.mp hk).1)
    dsimp [s, δ]
    rw [Real.log_div (by positivity) hh'.ne', Real.log_div hkp.ne' hh'.ne']
    ring
  have hsquare : (∑ k ∈ Ico h N, δ k * s k) ≤ u ^ 2 / 2 := by
    calc
      _ ≤ ∑ k ∈ Ico h N, (s (k + 1) ^ 2 - s k ^ 2) / 2 := by
        apply sum_le_sum
        intro k hk
        rw [hsδ k hk]
        nlinarith [sq_nonneg (δ k)]
      _ = u ^ 2 / 2 := by
        rw [← sum_div, sum_Ico_sub (fun k => s k ^ 2) hN]
        simp [s, u, div_self hh'.ne']
  have hsum : (∑ j ∈ Ico h N, δ j * (1 + s j)) ≤ u + u ^ 2 / 2 := by
    have hsumδ : (∑ j ∈ Ico h N, δ j) = u := (htail h le_rfl hN).symm
    simp_rw [mul_add, mul_one]
    rw [sum_add_distrib, hsumδ]
    linarith
  exact hcancel.trans (mul_le_mul_of_nonneg_left hsum hB)

private theorem weighted_variation_bound {N h : ℕ} (hh : 0 < h) (hN : h < N)
    (a : ℕ → ℝ) (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0) :
    weightedVariation N h a ≤ (N : ℝ)*mass N a *
      (1+2*Real.log ((N : ℝ)/h)*(1+Real.log (2*(N : ℝ)/h))) := by
  let u := Real.log ((N : ℝ) / h)
  let v := Real.log (2 * (N : ℝ) / h)
  have hu : 0 ≤ u := (log_bounds hh hN.le).1
  have hA := mass_nonneg N a
  have hB : firstAbsoluteMoment N a ≤ 2 * (N : ℝ) * mass N a := by
    unfold firstAbsoluteMoment mass
    rw [mul_sum]
    apply sum_le_sum
    intro m hm'
    exact mul_le_mul_of_nonneg_right
      (show (m : ℝ) ≤ 2 * N by exact_mod_cast (mem_Ico.mp hm').2.le) (abs_nonneg _)
  have huv : u ≤ v := by
    apply Real.log_le_log (div_pos (by exact_mod_cast (by omega : 0 < N))
      (by exact_mod_cast hh))
    exact div_le_div_of_nonneg_right
      (by nlinarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]) (by positivity)
  have hshape : 0 ≤ u + u ^ 2 / 2 := by positivity
  have hbudget : 2 * (u + u ^ 2 / 2) ≤ 1 + 2 * u * (1 + v) := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr huv)]
  calc
    _ ≤ firstAbsoluteMoment N a * (u + u ^ 2 / 2) :=
      weightedVariation_firstMoment_bound hh hN.le a hm
    _ ≤ (2 * (N : ℝ) * mass N a) * (u + u ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hB hshape
    _ = ((N : ℝ) * mass N a) * (2 * (u + u ^ 2 / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (mul_nonneg (Nat.cast_nonneg _) hA)

theorem prefix_bound (q : ℕ) : |mobiusPrefix q| ≤ (q : ℝ) := by
  unfold mobiusPrefix
  calc
    _ ≤ ∑ d ∈ Ioc 0 q, |(ArithmeticFunction.moebius d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 q, (1 : ℝ) := sum_le_sum fun d _ => by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    _ = _ := by simp

private theorem residual_identity {N : ℕ} (a : ℕ → ℝ)
    (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0) :
    residual N a = -(∑ d ∈ Ioc 0 N,
      (ArithmeticFunction.moebius d : ℝ)*logPair N a d)/Real.log N := by
  let C := ∑ d ∈ Ioc 0 N, coefficient N d / d
  have hlin : (∑ m ∈ Ico N (2 * N), a m*(C*(m : ℝ))) = 0 := by
    calc
      _ = C*(∑ m ∈ Ico N (2 * N), (m : ℝ)*a m) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro m _
        ring
      _ = 0 := by rw [hm, mul_zero]
  have hdouble : (∑ m ∈ Ico N (2 * N), a m*
      (∑ d ∈ Ioc 0 N, coefficient N d*(m / d : ℕ))) =
        ∑ d ∈ Ioc 0 N, coefficient N d*floorPair N a d := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    unfold floorPair
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    ring
  unfold residual response
  change (∑ m ∈ Ico N (2 * N), a m*(1+C*(m : ℝ)-
      ∑ d ∈ Ioc 0 N, coefficient N d*(m / d : ℕ))) = _
  simp_rw [mul_sub, mul_add, mul_one]
  rw [sum_sub_distrib, sum_add_distrib, hz, hlin, hdouble]
  simp only [zero_add, zero_sub]
  rw [neg_div]
  congr 1
  rw [sum_div]
  apply sum_congr rfl
  intro d _
  unfold coefficient logPair
  ring

private theorem log_pair_variation {N d : ℕ} (hN : 1 < N) (a : ℕ → ℝ)
    (hd : 0 < d) (hdN : d ≤ N)
    (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0) :
    |logPair N a d| ≤ Real.log N*(d : ℝ)*variation N a := by
  have hl := log_bounds hd hdN
  unfold logPair
  rw [abs_mul, abs_of_nonneg hl.1]
  calc
    _ ≤ Real.log ((N : ℝ)/d)*((d : ℝ)*variation N a) :=
      mul_le_mul_of_nonneg_left (pair_variation_bound (by omega) a hd hz hm) hl.1
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right hl.2
        (mul_nonneg (Nat.cast_nonneg d) (variation_nonneg N a))
      nlinarith

theorem sum_indices (q : ℕ) :
    (∑ d ∈ Ioc 0 q, (d : ℝ)) = (q : ℝ)*(q + 1)/2 := by
  have hn := sum_range_id_mul_two (q + 1)
  simp only [Nat.add_sub_cancel] at hn
  have hr := congrArg (fun t : ℕ => (t : ℝ)) hn
  push_cast at hr
  have he : range (q + 1) = insert 0 (Ioc 0 q) := by
    ext d
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [he, sum_insert (by simp), Nat.cast_zero, zero_add] at hr
  push_cast at hr
  linarith

private theorem small_prefix_bound {N q : ℕ} (hN : 1 < N) (hq : q + 1 ≤ N)
    (a : ℕ → ℝ) (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0) :
    |∑ k ∈ Ioc 0 q, mobiusPrefix k*logDifference N a k|/Real.log N ≤
      (3/2 : ℝ)*q*(q + 1)*variation N a := by
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hV := variation_nonneg N a
  have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hsum : |∑ d ∈ Ioc 0 q, (ArithmeticFunction.moebius d : ℝ)*logPair N a d| ≤
      Real.log N*variation N a*((q : ℝ)*(q + 1)/2) := by
    calc
      _ ≤ ∑ d ∈ Ioc 0 q, |(ArithmeticFunction.moebius d : ℝ)*logPair N a d| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 q, Real.log N*(d : ℝ)*variation N a := by
        apply sum_le_sum
        intro d hd
        have hd' := mem_Ioc.mp hd
        rw [abs_mul]
        calc
          _ ≤ 1*|logPair N a d| := mul_le_mul_of_nonneg_right
            (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)) (abs_nonneg _)
          _ ≤ _ := by simpa using log_pair_variation hN a hd'.1 (by omega) hz hm
      _ = _ := by
        have he : (∑ d ∈ Ioc 0 q, Real.log N*(d : ℝ)*variation N a) =
            Real.log N*variation N a*(∑ d ∈ Ioc 0 q, (d : ℝ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro d _
          ring
        rw [he, sum_indices]
  have hterm : |mobiusPrefix q*logPair N a (q + 1)| ≤
      (q : ℝ)*(Real.log N*(q + 1 : ℕ)*variation N a) := by
    rw [abs_mul]
    exact mul_le_mul (prefix_bound q) (log_pair_variation hN a (by omega) hq hz hm)
      (abs_nonneg _) hq'
  have he := D5.S3.Arith.Robin.ActualOddMobiusFinitePairing.prefix_abel (logPair N a) q
  change (∑ k ∈ Ioc 0 q, mobiusPrefix k*logDifference N a k) = _ at he
  rw [he]
  apply (div_le_iff₀ hL).mpr
  calc
    _ ≤ _ := (abs_sub _ _).trans (add_le_add hsum hterm)
    _ = _ := by push_cast; ring

theorem prefix_error_bound {N h : ℕ} (hh : 0 < h) (D F : ℕ → ℝ)
    {ε c : ℝ} (hc : 0 ≤ c)
    (herr : ∀ k ∈ Ico h N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) :
    |∑ k ∈ Ico h N, (F k-mobiusPrefix k)*D k| ≤
      (ε+c/(h : ℝ))*(∑ k ∈ Ico h N, (k : ℝ)*|D k|) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  calc
    _ ≤ ∑ k ∈ Ico h N, |(F k-mobiusPrefix k)*D k| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Ico h N, (ε+c/(h : ℝ))*((k : ℝ)*|D k|) := by
      apply sum_le_sum
      intro k hk
      have hk' : (h : ℝ) ≤ k := by exact_mod_cast (mem_Ico.mp hk).1
      have hratio : 1 ≤ (k : ℝ)/h := (one_le_div hh').mpr hk'
      have hcost : ε*(k : ℝ)+c ≤ (ε+c/(h : ℝ))*(k : ℝ) := by
        have he := mul_le_mul_of_nonneg_left hratio hc
        calc
          _ ≤ ε*(k : ℝ)+c*((k : ℝ)/h) := by linarith
          _ = _ := by ring
      rw [abs_mul]
      calc
        _ ≤ ((ε+c/(h : ℝ))*(k : ℝ))*|D k| :=
          mul_le_mul_of_nonneg_right ((herr k hk).trans hcost) (abs_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [← mul_sum]

private theorem high_error_bound {N h : ℕ} (hh : 0 < h) (a F : ℕ → ℝ)
    {ε c : ℝ} (hc : 0 ≤ c)
    (herr : ∀ k ∈ Ico h N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) :
    |∑ k ∈ Ico h N, (F k-mobiusPrefix k)*logDifference N a k| ≤
      (ε+c/(h : ℝ))*weightedVariation N h a := by
  exact prefix_error_bound hh (logDifference N a) F hc herr

/-- FT11 for the unchanged full Mobius response, with both exact moments and
both nonnegative error constants. The cut q=0 and the one-term high range
q=N-2 are included. -/
theorem originalResidual_finite_transfer {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (a F : ℕ → ℝ) (ε c : ℝ) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hz : ∑ m ∈ Ico N (2 * N), a m = 0)
    (hm : ∑ m ∈ Ico N (2 * N), (m : ℝ)*a m = 0)
    (herr : ∀ k ∈ Ico (q + 1) N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) :
    |residual N a-replacement N q a F| ≤
      (ε+c/(q + 1 : ℕ))/Real.log N * ((N : ℝ)*mass N a*
        (1+2*Real.log ((N : ℝ)/(q + 1 : ℕ))*
          (1+Real.log (2*(N : ℝ)/(q + 1 : ℕ))))) +
        (q + 1 : ℕ)*((3 : ℝ)*(q : ℝ)/2+2)*variation N a := by
  have hN1 : 1 < N := by omega
  have hN0 : 0 < N := by omega
  have hh : q + 1 < N := by omega
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hh' : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hfactor : 0 ≤ (ε+c/(q + 1 : ℕ))/Real.log N := by positivity
  let P := ∑ k ∈ Ioc 0 q, mobiusPrefix k*logDifference N a k
  let T := ∑ k ∈ Ico (q + 1) N, (F k-mobiusPrefix k)*logDifference N a k
  have hGN : logPair N a N = 0 := by
    rw [logPair, (pair_endpoints hN0 a hz hm).2, mul_zero]
  have hsplit : (∑ k ∈ Ioc 0 (N-1), mobiusPrefix k*logDifference N a k) =
      P + ∑ k ∈ Ico (q + 1) N, mobiusPrefix k*logDifference N a k := by
    have he := sum_Ioc_consecutive (f := fun k => mobiusPrefix k*logDifference N a k)
      (Nat.zero_le q) (by omega : q ≤ N-1)
    have hset : Ioc q (N-1) = Ico (q + 1) N := by
      ext k
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [hset] at he
    exact he.symm
  have hE : residual N a =
      -(P + ∑ k ∈ Ico (q + 1) N, mobiusPrefix k*logDifference N a k)/Real.log N := by
    rw [residual_identity a hz hm]
    have he := D5.S3.Arith.Robin.ActualOddMobiusFinitePairing.prefix_abel (logPair N a) (N-1)
    rw [show N-1+1 = N by omega, hGN, mul_zero, sub_zero] at he
    have hs : (∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ)*logPair N a d) =
        ∑ d ∈ Ioc 0 (N-1), (ArithmeticFunction.moebius d : ℝ)*logPair N a d := by
      conv_lhs => rw [show N = (N-1)+1 by omega]
      rw [sum_Ioc_succ_top (Nat.zero_le (N-1))]
      simp only [show N-1+1 = N by omega, hGN, mul_zero, add_zero]
    rw [hs, ← he]
    change -(∑ k ∈ Ioc 0 (N-1), mobiusPrefix k*logDifference N a k)/Real.log N = _
    rw [hsplit]
  have htel : (∑ k ∈ Ico (q + 1) N, logDifference N a k) = logPair N a (q + 1) := by
    have he := sum_Ico_sub (logPair N a) hh.le
    have hs : (∑ k ∈ Ico (q + 1) N, logDifference N a k) =
        -(∑ k ∈ Ico (q + 1) N, (logPair N a (k + 1)-logPair N a k)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro k _
      unfold logDifference
      ring
    rw [hs, he, hGN]
    ring
  have hid : residual N a-replacement N q a F =
      T/Real.log N-P/Real.log N+2*logPair N a (q + 1)/Real.log N := by
    rw [hE]
    unfold replacement
    dsimp [T]
    simp_rw [add_mul, sub_mul]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, htel]
    ring
  have hT : |T|/Real.log N ≤
      (ε+c/(q + 1 : ℕ))/Real.log N*weightedVariation N (q + 1) a := by
    have he := high_error_bound (by omega) a F hc herr
    dsimp [T]
    apply (div_le_iff₀ hL).mpr
    have hid' : ((ε+c/(q + 1 : ℕ))/Real.log N*weightedVariation N (q + 1) a)*
        Real.log N = (ε+c/(q + 1 : ℕ))*weightedVariation N (q + 1) a := by
      field_simp
    rw [hid']
    exact he
  have hP : |P|/Real.log N ≤ (3/2 : ℝ)*q*(q + 1)*variation N a :=
    small_prefix_bound hN1 hh.le a hz hm
  have hG : 2*|logPair N a (q + 1)|/Real.log N ≤
      2*(q + 1 : ℕ)*variation N a := by
    apply (div_le_iff₀ hL).mpr
    have he := log_pair_variation hN1 a (by omega) hh.le hz hm
    push_cast at *
    nlinarith
  rw [hid]
  calc
    _ ≤ |T/Real.log N|+|P/Real.log N|+|2*logPair N a (q + 1)/Real.log N| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = |T|/Real.log N+|P|/Real.log N+2*|logPair N a (q + 1)|/Real.log N := by
      rw [abs_div, abs_div, abs_div, abs_mul, abs_of_pos hL]
      norm_num
    _ ≤ (ε+c/(q + 1 : ℕ))/Real.log N*weightedVariation N (q + 1) a +
        (3/2 : ℝ)*q*(q + 1)*variation N a+2*(q + 1 : ℕ)*variation N a :=
      add_le_add (add_le_add hT hP) hG
    _ ≤ (ε+c/(q + 1 : ℕ))/Real.log N*((N : ℝ)*mass N a*
        (1+2*Real.log ((N : ℝ)/(q + 1 : ℕ))*(1+Real.log (2*(N : ℝ)/(q + 1 : ℕ))))) +
          (3/2 : ℝ)*q*(q + 1)*variation N a+2*(q + 1 : ℕ)*variation N a := by
      gcongr
      exact weighted_variation_bound (by omega) hh a hz hm
    _ = _ := by push_cast; ring

#print axioms originalResidual_finite_transfer

end D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
