/- GID: D5/S3/Analytic/KarpZhangCatalanPower/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangCatalanPower/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both coefficientwise assertions of Karp--Zhang Conjecture 4.2. -/

import D5.S3.Combinatorics.Nonnesting.CatalanLagrangeBridge
import D5.S3.Analytic.KarpZhangReciprocal.Result

/-!
admission_basis: open-problem-resolution (#21083; Proved).
All Coeff, Index and Interval helpers are consumed bind-only declarations,
judged after inlining every helper in this delivery. In particular, tp2
instantiates strictMono_nat_of_lt_succ with a(n,v)/a(n,u), then clears
positive denominators. It supplies no escape witness.

The reflected slice identity also supplies no escape witness: after
inlining the triangular reindexing and boundary helpers, sum_sigma',
sum_bij and sum_sdiff_sub_sum_sdiff reduce it to the explicit maps
(k,j) ↦ (j,k-j), (k,j) ↦ (j,k), and i ↦ m-j-i; their membership,
inverse and summand obligations close by omega, simp and ring.
The coefficient calculus uses the polynomial index law; HasDerivAt.fun_sum
and strictMonoOn_of_deriv_pos give differentiation and monotonicity.
Positivity then instantiates sum_pos', b_pos and the bind-only TP2 order.
There is no independent content-bearing supporting module.

Frozen dependencies below are obtained from compiled constants, expanding
all same-delivery helpers and stopping at frozen D5 owners. The identity
attached to each declaration GID is its declaration statement_id from the
producing Lean reports (.lake/build/stratalint/raw-lean-report.json for the
Catalan bridge; .lake/build/stratalint/scoped-lean-report.json for the 5.2 owner).
A retained state-record pin is labelled module statement_id and records
module membership, not declaration identity. Dependencies from the frozen
5.2 owner are listed separately by current declaration identity. The public
exposures increment, tail_sum and abel_layers belong to this delivery; their
public names are not members of the retained private-name frozen state.
Search covers D5 (including private declarations) and pinned Mathlib;
external-library search is unavailable under this seat's no-network constraint.
Utility none: these degree-uniform identities and inequalities are not
numerical certificates, enumerators, checkers or numerical reductions.
-/

noncomputable section
open Polynomial Finset

namespace D5.S3.Analytic.KarpZhangCatalanPower.Coeff

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.a_eq_polynomial, Coeff.a_nonneg, Coeff.a_pos, Coeff.a_zero_parameter, Coeff.adjacent_ratio, Coeff.adjacent_tp2, Coeff.tp2, Coeff.tp2_le, Index.a_hasDerivAt_poly, Index.b, Index.b_eq_poly, Index.hasDerivAt_a, Index.index_law, Interval.Z, Interval.Z_symm, Interval.derivative_difference, Interval.hasDerivAt_slice, Interval.left_derivative_reindex, Interval.right_derivative_reindex, Interval.sliceDerivative, Interval.sliceDerivative_pos, Interval.tail_nonneg, Result.abel, Result.delta, Result.full_tail, Result.result, Result.tail; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
/-- The literal rising-factorial quotient in formula (15). -/
def a (n : ℕ) (t : ℝ) : ℝ :=
  (ascPochhammer ℝ (2 * n)).eval t /
    ((ascPochhammer ℝ n).eval (t + 1) * (n.factorial : ℝ))

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.a_eq_polynomial, Coeff.coeffPoly_succ_eval, Index.a_hasDerivAt_poly, Index.b_eq_centralBinom, Index.b_eq_poly, Index.hasDerivAt_a, Index.index_law, Index.index_polynomial, Index.natural_coeff, Index.natural_index; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
/-- The polynomial continuation of the coefficient. -/
def coeffPoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C ((n + 1).factorial : ℝ)⁻¹ * X *
      (ascPochhammer ℝ n).comp (X + C (n + 2 : ℝ))

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.a_eq_polynomial, Index.natural_coeff; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
lemma coeffPoly_succ_eval (n : ℕ) (t : ℝ) :
    (coeffPoly (n + 1)).eval t =
      t * (ascPochhammer ℝ n).eval (t + n + 2) / ((n + 1).factorial : ℝ) := by
  simp only [coeffPoly, eval_mul, eval_C, eval_X, eval_comp, eval_add]
  ring

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.a_eq_polynomial; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma poch_split (n : ℕ) (t : ℝ) :
    (ascPochhammer ℝ (2 * (n + 1))).eval t =
      t * (ascPochhammer ℝ (n + 1)).eval (t + 1) *
        (ascPochhammer ℝ n).eval (t + n + 2) := by
  rw [show 2 * (n + 1) = (n + 1 + n) + 1 by omega,
    ascPochhammer_succ_left]
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
  have h := congrArg (fun p : ℝ[X] => p.eval (t + 1))
    (ascPochhammer_mul ℝ (n + 1) n)
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at h
  rw [← h]
  push_cast
  ring

/- proof_shape: bind-only; escape_witness: none; consumers: Index.a_hasDerivAt_poly, Index.hasDerivAt_a, Index.index_law; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
lemma a_eq_polynomial (n : ℕ) {t : ℝ} (ht : -1 < t) :
    a n t = (coeffPoly n).eval t := by
  cases n with
  | zero => simp [a, coeffPoly]
  | succ n =>
    rw [a, poch_split, coeffPoly_succ_eval]
    have hp := (ascPochhammer_pos (n + 1) (t + 1) (by linarith)).ne'
    have hf : ((n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.a_nonneg, Coeff.adjacent_tp2, Coeff.tp2; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
lemma a_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < a n t := by
  exact div_pos (ascPochhammer_pos (2 * n) t ht)
    (mul_pos (ascPochhammer_pos n (t + 1) (by linarith))
      (Nat.cast_pos.mpr (Nat.factorial_pos n)))

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.a_nonneg, Interval.tail_nonneg; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
lemma a_zero_parameter {n : ℕ} (hn : 0 < n) : a n 0 = 0 := by
  simp [a, ascPochhammer_ne_zero_eval_zero ℝ (by omega : 2 * n ≠ 0)]

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.tail_nonneg; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
lemma a_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ a n t := by
  rcases ht.eq_or_lt with rfl | ht
  · cases n with
    | zero => norm_num [a]
    | succ n => rw [a_zero_parameter (by omega)]
  · exact (a_pos n ht).le

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.adjacent_tp2; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
lemma adjacent_ratio (n : ℕ) {t : ℝ} (ht : 0 < t) :
    a (n + 1) t = a n t *
      ((t + 2 * n) * (t + 2 * n + 1) / ((t + n + 1) * (n + 1))) := by
  have hp := (ascPochhammer_pos n (t + 1) (by linarith)).ne'
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have htn : t + n + 1 ≠ 0 := by positivity
  simp only [a, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  push_cast
  field_simp
  ring

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.tp2; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma adjacent_tp2 (n : ℕ) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    a (n + 1) u * a n v < a n u * a (n + 1) v := by
  have hv : 0 < v := hu.trans huv
  rw [adjacent_ratio n hu, adjacent_ratio n hv]
  have hratio :
      (u + 2 * n) * (u + 2 * n + 1) / ((u + n + 1) * (n + 1)) <
        (v + 2 * n) * (v + 2 * n + 1) / ((v + n + 1) * (n + 1)) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hcross :
        (v + 2 * n) * (v + 2 * n + 1) * ((u + n + 1) * (n + 1)) -
          (u + 2 * n) * (u + 2 * n + 1) * ((v + n + 1) * (n + 1)) =
        (v - u) * (n + 1) *
          (u * v + (n + 1) * (u + v) + 3 * n + 1) := by ring
    have hp : 0 < (v - u) * (n + 1) *
        (u * v + (n + 1) * (u + v) + 3 * n + 1) := by positivity
    linarith
  have h := mul_lt_mul_of_pos_left hratio (mul_pos (a_pos n hu) (a_pos n hv))
  nlinarith only [h]

/- proof_shape: bind-only; escape_witness: none; consumers: Coeff.tp2_le, Interval.sliceDerivative_pos; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
theorem tp2 {u v : ℝ} (hu : 0 < u) (huv : u < v) {i l : ℕ} (hil : i < l) :
    a l u * a i v < a i u * a l v := by
  have hmono : StrictMono (fun n : ℕ => a n v / a n u) :=
    strictMono_nat_of_lt_succ (fun n =>
      (div_lt_div_iff₀ (a_pos n hu) (a_pos (n + 1) hu)).mpr
        (by nlinarith only [adjacent_tp2 n hu huv]))
  have h := (div_lt_div_iff₀ (a_pos i hu) (a_pos l hu)).mp (hmono hil)
  nlinarith only [h]

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.sliceDerivative_pos; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
theorem tp2_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {i l : ℕ} (hil : i < l) :
    a l u * a i v ≤ a i u * a l v := by
  rcases huv.eq_or_lt with rfl | h
  · exact le_of_eq (mul_comm _ _)
  · exact (tp2 hu h hil).le

end D5.S3.Analytic.KarpZhangCatalanPower.Coeff
end

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open PowerSeries Set
namespace D5.S3.Analytic.KarpZhangCatalanPower.Index
open P13CatalanLagrangeBridge
open D5.S3.Analytic.KarpZhangCatalanPower.Coeff

/- proof_shape: bind-only; escape_witness: none; consumers: Index.natural_coeff; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
private lemma natural_catalan_coeff (n t : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n (catalanUnit ^ t) =
      ((2*n+t-1).choose n : ℚ) - ((2*n+t-1).choose (n-1) : ℚ) := by
  have hsub : subst q ((1 + PowerSeries.X : PowerSeries ℚ)^t) = catalanUnit ^ t := by
    have hs : HasSubst q := HasSubst.of_constantCoeff_zero' q_constantCoeff
    rw [subst_pow hs, subst_add hs, subst_X hs]
    have ho : subst q (1: PowerSeries ℚ) = 1 := by
      rw [← coe_substAlgHom hs, map_one]
    rw [ho]
    simp [q]
  have ht := q_subst_coefficient_transform ((1+PowerSeries.X)^t) n hn
  rw [hsub] at ht
  have hexp : 2*n-1+t=2*n+t-1 := by omega
  rw [mul_assoc, ← pow_add, hexp] at ht
  rw [one_sub_X_power_coefficient, ite_eq_right (by omega : n ≠ 0)] at ht
  exact ht

/- proof_shape: bind-only; escape_witness: none; consumers: Index.natural_coeff; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma choose_diff (n t : ℕ) :
    ((2*(n+1)+t-1).choose (n+1) : ℚ) - ((2*(n+1)+t-1).choose n : ℚ) =
      (t:ℚ) * (ascPochhammer ℚ n).eval ((t+n+2:ℕ):ℚ) / ((n+1).factorial : ℚ) := by
  have hnat := Nat.ascFactorial_eq_factorial_mul_choose (t+n+1) n
  have hexp : t+n+1+n=2*(n+1)+t-1 := by omega
  rw [hexp] at hnat
  rw [ascPochhammer_nat_eq_natCast_ascFactorial]
  have hcast : (((t+n+2).ascFactorial n : ℕ):ℚ) =
      (n.factorial:ℚ) * ((2*(n+1)+t-1).choose n :ℚ) := by
    exact_mod_cast hnat
  rw [hcast]
  have hchoose := Nat.choose_succ_right_eq (2*(n+1)+t-1) n
  have hchoose' : ((2*(n+1)+t-1).choose (n+1):ℚ) * ((n:ℚ)+1) =
      ((2*(n+1)+t-1).choose n : ℚ) * ((n:ℚ)+(t:ℚ)+1) := by
    have hn : 2*(n+1)+t-1-n=n+t+1 := by omega
    rw [hn] at hchoose
    exact_mod_cast hchoose
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfac : (n.factorial:ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hnp : (n:ℚ)+1 ≠ 0 := by positivity
  field_simp
  nlinarith

/- proof_shape: bind-only; escape_witness: none; consumers: Index.natural_index; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
private lemma natural_coeff (n t : ℕ) :
    (coeffPoly n).eval (t:ℝ) = ((PowerSeries.coeff n (catalanUnit ^ t) : ℚ):ℝ) := by
  cases n with
  | zero => simp [coeffPoly, coeff_zero_eq_constantCoeff_apply, catalanUnit_constantCoeff]
  | succ n =>
    rw [natural_catalan_coeff (n+1) t (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [choose_diff]
    rw [coeffPoly_succ_eval]
    push_cast
    have hcast : (ascPochhammer ℝ n).eval ((t:ℝ)+n+2) =
        (((ascPochhammer ℚ n).eval ((t+n+2:ℕ):ℚ) : ℚ):ℝ) := by
      rw [ascPochhammer_eval₂ (Rat.castHom ℝ)]
      simpa only [Rat.coe_castHom, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat,
        Nat.cast_add, Nat.cast_ofNat] using
        Polynomial.eval₂_at_apply (p := ascPochhammer ℚ n)
          (Rat.castHom ℝ) ((t + n + 2 : ℕ) : ℚ)
    rw [hcast]
    push_cast
    rfl

/- proof_shape: bind-only; escape_witness: none; consumers: Index.index_polynomial; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
private lemma natural_index (s t m : ℕ) :
    ∑ k ∈ Finset.range (m+1),
      (coeffPoly k).eval (s:ℝ) * (coeffPoly (m-k)).eval (t:ℝ) =
      (coeffPoly m).eval ((s:ℝ)+(t:ℝ)) := by
  have hc := congrArg (PowerSeries.coeff m) (pow_add catalanUnit s t)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  have hcR := congrArg (fun x:ℚ => (x:ℝ)) hc
  push_cast at hcR
  simp_rw [natural_coeff]
  rw [← Nat.cast_add, natural_coeff]
  exact hcR.symm

/- proof_shape: bind-only; escape_witness: none; consumers: Index.hasDerivAt_a, Index.index_law; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
theorem index_polynomial (s t : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m+1),
      (coeffPoly k).eval s * (coeffPoly (m-k)).eval t =
      (coeffPoly m).eval (s+t) := by
  classical
  have infiniteN : Set.Infinite (Set.range (fun n:ℕ => (n:ℝ))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  have extension (t:ℕ) :
      (∑ k ∈ Finset.range (m+1),
        coeffPoly k * Polynomial.C ((coeffPoly (m-k)).eval (t:ℝ))) =
      (coeffPoly m).comp (Polynomial.X + Polynomial.C (t:ℝ)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infiniteN.mono
    rintro x ⟨s,rfl⟩
    simpa only [Set.mem_ofPred_eq, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X] using natural_index s t m
  have extension' :
      (∑ k ∈ Finset.range (m+1),
        Polynomial.C ((coeffPoly k).eval s) * coeffPoly (m-k)) =
      (coeffPoly m).comp (Polynomial.C s + Polynomial.X) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infiniteN.mono
    rintro x ⟨t,rfl⟩
    have ht := congrArg (Polynomial.eval s) (extension t)
    simpa only [Set.mem_ofPred_eq, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X] using ht
  have ht := congrArg (Polynomial.eval t) extension'
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X] using ht

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.tail_nonneg, Result.full_tail; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
theorem index_law (s t : ℝ) (m : ℕ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∑ k ∈ Finset.range (m+1), a k s * a (m-k) t = a m (s+t) := by
  simp_rw [a_eq_polynomial _ (by linarith : -1<s),
    a_eq_polynomial _ (by linarith : -1<t)]
  rw [a_eq_polynomial _ (by linarith : -1<s+t)]
  exact index_polynomial s t m

/- proof_shape: bind-only; escape_witness: none; consumers: Index.b_eq_poly, Index.hasDerivAt_a; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma a_hasDerivAt_poly (n : ℕ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (a n) ((coeffPoly n).derivative.eval t) t := by
  apply ((coeffPoly n).hasDerivAt t).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact a_eq_polynomial n hx

/- proof_shape: bind-only; escape_witness: none; consumers: Index.b_eq_centralBinom, Index.b_eq_poly, Index.b_pos, Index.hasDerivAt_a, Interval.derivative_difference, Interval.hasDerivAt_slice, Interval.left_derivative_reindex, Interval.right_derivative_reindex, Interval.sliceDerivative, Interval.sliceDerivative_pos; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
/-- The positive infinitesimal coefficients of the convolution semigroup. -/
def b (j : ℕ) : ℝ := deriv (a j) 0

/- proof_shape: bind-only; escape_witness: none; consumers: Index.b_eq_centralBinom, Index.hasDerivAt_a; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma b_eq_poly (j : ℕ) : b j = (coeffPoly j).derivative.eval 0 :=
  (a_hasDerivAt_poly j (by norm_num)).deriv

/- proof_shape: bind-only; escape_witness: none; consumers: Index.b_pos; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
theorem b_eq_centralBinom (j : ℕ) (hj : 1 ≤ j) :
    b j = ((2*j).choose j :ℝ)/(2*j) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  rw [b_eq_poly]
  have hb : (coeffPoly (n+1)).derivative.eval 0 =
      (ascPochhammer ℝ n).eval ((n:ℝ)+2) / ((n+1).factorial :ℝ) := by
    simp [coeffPoly, Polynomial.derivative_mul, Polynomial.derivative_comp,
      Polynomial.eval_comp, div_eq_mul_inv]
    ring
  rw [hb]
  have hf := Nat.ascFactorial_eq_factorial_mul_choose (n+1) n
  have he : n+1+n=2*n+1 := by omega
  rw [he] at hf
  have hreal : (ascPochhammer ℝ n).eval ((n:ℝ)+2) =
      (n.factorial:ℝ) * ((2*n+1).choose n:ℝ) := by
    rw [show (n:ℝ)+2=((n+2:ℕ):ℝ) by push_cast; ring,
      ascPochhammer_nat_eq_natCast_ascFactorial]
    exact_mod_cast hf
  rw [hreal, Nat.factorial_succ]
  have hc := Nat.choose_succ_succ' (2*n+1) n
  have hsym : (2*n+1).choose (n+1)=(2*n+1).choose n :=
    Nat.choose_symm_half n
  rw [hsym] at hc
  rw [show 2*n+1+1=2*(n+1) by omega] at hc
  have hcR : ((2*(n+1)).choose (n+1):ℝ)=2*((2*n+1).choose n:ℝ) := by
    have h := congrArg (fun x:ℕ => (x:ℝ)) hc
    push_cast at h
    linarith
  rw [hcR]
  have hfac : (n.factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hnp : (n:ℝ)+1≠0 := by positivity
  push_cast
  field_simp

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.sliceDerivative_pos; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
theorem b_pos (j : ℕ) (hj : 1 ≤ j) : 0 < b j := by
  rw [b_eq_centralBinom j hj]
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega : j≤2*j)
  · positivity

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.hasDerivAt_slice; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
theorem hasDerivAt_a (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (a n) (∑ j ∈ Finset.Icc 1 n, b j * a (n-j) t) t := by
  have hleft : HasDerivAt
      (fun s:ℝ => ∑ j ∈ Finset.range (n+1),
        (coeffPoly j).eval s * (coeffPoly (n-j)).eval t)
      (∑ j ∈ Finset.range (n+1),
        (coeffPoly j).derivative.eval 0 * (coeffPoly (n-j)).eval t) 0 := by
    exact HasDerivAt.fun_sum (fun j _ =>
      ((coeffPoly j).hasDerivAt 0).mul_const ((coeffPoly (n-j)).eval t))
  have hright : HasDerivAt (fun s:ℝ => (coeffPoly n).eval (s+t))
      ((coeffPoly n).derivative.eval t) 0 := by
    simpa only [id_eq, zero_add, mul_one, Function.comp_def] using
      ((coeffPoly n).hasDerivAt (0+t)).comp 0 ((hasDerivAt_id 0).add_const t)
  have hfun : (fun s:ℝ => ∑ j ∈ Finset.range (n+1),
        (coeffPoly j).eval s * (coeffPoly (n-j)).eval t) =
      (fun s:ℝ => (coeffPoly n).eval (s+t)) := by
    funext s
    exact index_polynomial s t n
  rw [hfun] at hleft
  have hd := hright.unique hleft
  have hder := a_hasDerivAt_poly n (by linarith : -1<t)
  rw [hd] at hder
  convert hder using 1
  simp_rw [← b_eq_poly, ← a_eq_polynomial _ (by linarith : -1<t)]
  apply Finset.sum_subset
  · intro j hj
    have h := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro j hj hnot
    have hj0 : j=0 := by
      have h := Finset.mem_range.mp hj
      have h' : ¬(1≤j ∧ j≤n) := by simpa only [Finset.mem_Icc] using hnot
      omega
    subst j
    simp [b_eq_poly, coeffPoly]

end D5.S3.Analytic.KarpZhangCatalanPower.Index

end

noncomputable section
open Finset
open D5.S3.Analytic.KarpZhangCatalanPower.Coeff
open D5.S3.Analytic.KarpZhangCatalanPower.Index
namespace D5.S3.Analytic.KarpZhangCatalanPower.Interval

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.derivative_difference, Interval.left_derivative_reindex, Interval.left_reindex, Interval.mem_left, Interval.reflected_interval; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private def leftWindow (m q j : ℕ) : Finset ℕ :=
  (range (m - j + 1)).filter fun i => q ≤ i + j ∧ i + j ≤ m - q

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.derivative_difference, Interval.mem_right, Interval.reflected_interval, Interval.right_derivative_reindex, Interval.right_reindex; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private def rightWindow (m q j : ℕ) : Finset ℕ :=
  (range (m - j + 1)).filter fun i => q ≤ i ∧ i ≤ m - q

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.R_lt, Interval.R_one, Interval.derivative_difference, Interval.mem_R, Interval.reflected_interval, Interval.sliceDerivative, Interval.sliceDerivative_pos; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
/-- The left-only part of a pair of reflected truncated intervals. -/
def R (m q j : ℕ) : Finset ℕ :=
  (range (m - j + 1)).filter fun i => q ≤ i + j ∧ i + j ≤ m - q ∧ i < q

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.left_reindex, Interval.reflected_interval; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma mem_left {m q j i : ℕ} : i ∈ leftWindow m q j ↔
    i ≤ m - j ∧ q ≤ i + j ∧ i + j ≤ m - q := by
  simp only [leftWindow, mem_filter, mem_range, Nat.lt_succ_iff]

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.reflected_interval, Interval.right_reindex; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma mem_right {m q j i : ℕ} : i ∈ rightWindow m q j ↔
    i ≤ m - j ∧ q ≤ i ∧ i ≤ m - q := by
  simp only [rightWindow, mem_filter, mem_range, Nat.lt_succ_iff]

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.R_lt, Interval.R_one, Interval.derivative_difference, Interval.reflected_interval; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma mem_R {m q j i : ℕ} : i ∈ R m q j ↔
    i ≤ m - j ∧ q ≤ i + j ∧ i + j ≤ m - q ∧ i < q := by
  simp only [R, mem_filter, mem_range, Nat.lt_succ_iff]

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.sliceDerivative_pos; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma R_lt {m q j i : ℕ} (hmq : 2 * q ≤ m) (hj : j ≤ m)
    (hi : i ∈ R m q j) : i < m - j - i := by
  rw [mem_R] at hi
  omega

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.derivative_difference; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
lemma reflected_interval {m q j : ℕ} (hmq : 2 * q ≤ m) (hj : j ≤ m)
    (w : ℕ → ℝ) :
    (∑ i ∈ (range (m - j + 1)).filter (fun i => q ≤ i + j ∧ i + j ≤ m - q), w i) -
      (∑ i ∈ (range (m - j + 1)).filter (fun i => q ≤ i ∧ i ≤ m - q), w i) =
      ∑ i ∈ R m q j, (w i - w (m - j - i)) := by
  change (∑ i ∈ leftWindow m q j, w i) - (∑ i ∈ rightWindow m q j, w i) = _
  have hl : leftWindow m q j \ rightWindow m q j = R m q j := by
    ext i
    simp only [mem_sdiff, mem_left, mem_right, mem_R]
    omega
  have hr : ∑ i ∈ rightWindow m q j \ leftWindow m q j, w i =
      ∑ i ∈ R m q j, w (m - j - i) := by
    apply sum_bij (fun i _ => m - j - i)
    · intro i hi
      simp only [mem_sdiff, mem_right, mem_left] at hi
      rw [mem_R]
      omega
    · intro i hi k hk hik
      simp only [mem_sdiff, mem_right, mem_left] at hi hk
      omega
    · intro i hi
      rw [mem_R] at hi
      refine ⟨m - j - i, ?_, ?_⟩
      · simp only [mem_sdiff, mem_right, mem_left]
        omega
      · omega
    · intro i hi
      simp only [mem_sdiff, mem_right, mem_left] at hi
      congr 1
      omega
  rw [sum_sub_distrib, ← hr, ← hl]
  exact (sum_sdiff_sub_sum_sdiff).symm

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.left_derivative_reindex; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma left_reindex {m q : ℕ} (hmq : 2 * q ≤ m) (F : ℕ → ℕ → ℝ) :
    (∑ k ∈ Icc q (m - q), ∑ j ∈ Icc 1 k, F j (k - j)) =
      ∑ j ∈ Icc 1 m, ∑ i ∈ leftWindow m q j, F j i := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => (⟨p.2, p.1 - p.2⟩ : Σ _ : ℕ, ℕ))
  · intro p hp
    simp only [mem_sigma, mem_Icc] at hp
    simp only [mem_sigma, mem_Icc, mem_left]
    omega
  · intro p hp r hr hpr
    simp only [mem_sigma, mem_Icc] at hp hr
    have h1 := congrArg Sigma.fst hpr
    have h2 := congrArg Sigma.snd hpr
    dsimp only at h1 h2
    exact Sigma.ext (by omega) (by simpa only [heq_eq_eq] using h1)
  · intro p hp
    simp only [mem_sigma, mem_Icc, mem_left] at hp
    refine ⟨⟨p.2 + p.1,p.1⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_Icc]
      omega
    · simp
  · intro p hp
    rfl

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.right_derivative_reindex; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma right_reindex {m q : ℕ} (hmq : 2 * q ≤ m) (F : ℕ → ℕ → ℝ) :
    (∑ k ∈ Icc q (m - q), ∑ j ∈ Icc 1 (m - k), F j k) =
      ∑ j ∈ Icc 1 m, ∑ i ∈ rightWindow m q j, F j i := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => (⟨p.2,p.1⟩ : Σ _ : ℕ, ℕ))
  · intro p hp
    simp only [mem_sigma, mem_Icc] at hp
    simp only [mem_sigma, mem_Icc, mem_right]
    omega
  · intro p hp r hr hpr
    have h1 := congrArg Sigma.fst hpr
    have h2 := congrArg Sigma.snd hpr
    dsimp only at h1 h2
    exact Sigma.ext h2 (by simpa only [heq_eq_eq] using h1)
  · intro p hp
    simp only [mem_sigma, mem_Icc, mem_right] at hp
    refine ⟨⟨p.2,p.1⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_Icc]
      omega
    · rfl
  · intro p hp
    rfl

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.Z_symm, Interval.balancing, Interval.hasDerivAt_slice, Interval.slice_strictMonoOn; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
/-- The central convolution interval. -/
def Z (m q : ℕ) (u v : ℝ) : ℝ := ∑ k ∈ Icc q (m - q), a k u * a (m - k) v

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.derivative_difference, Interval.hasDerivAt_slice, Interval.sliceDerivative_pos, Interval.slice_strictMonoOn; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
/-- The reflected determinant expression for a constant-sum derivative. -/
def sliceDerivative (m q : ℕ) (u v : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 m, b j * ∑ i ∈ R m q j,
    (a i u * a (m - j - i) v - a (m - j - i) u * a i v)

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.derivative_difference; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma left_derivative_reindex {m q : ℕ} (hmq : 2 * q ≤ m) (u v : ℝ) :
    (∑ k ∈ Icc q (m - q), (∑ j ∈ Icc 1 k, b j * a (k - j) u) * a (m - k) v) =
      ∑ j ∈ Icc 1 m, b j * ∑ i ∈ leftWindow m q j, a i u * a (m - j - i) v := by
  calc
    _ = ∑ k ∈ Icc q (m - q), ∑ j ∈ Icc 1 k,
          b j * (a (k - j) u * a (m - j - (k - j)) v) := by
      apply sum_congr rfl
      intro k hk
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      simp only [mem_Icc] at hk hj
      rw [show m - j - (k - j) = m - k by omega]
      ring
    _ = _ := by
      rw [left_reindex hmq (fun j i => b j * (a i u * a (m - j - i) v))]
      simp only [mul_sum]

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.derivative_difference; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma right_derivative_reindex {m q : ℕ} (hmq : 2 * q ≤ m) (u v : ℝ) :
    (∑ k ∈ Icc q (m - q), a k u * (∑ j ∈ Icc 1 (m - k), b j * a (m - k - j) v)) =
      ∑ j ∈ Icc 1 m, b j * ∑ i ∈ rightWindow m q j, a i u * a (m - j - i) v := by
  calc
    _ = ∑ k ∈ Icc q (m - q), ∑ j ∈ Icc 1 (m - k),
          b j * (a k u * a (m - j - k) v) := by
      apply sum_congr rfl
      intro k hk
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [show m - k - j = m - j - k by omega]
      ring
    _ = _ := by
      rw [right_reindex hmq]
      simp only [mul_sum]

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.hasDerivAt_slice; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma derivative_difference {m q : ℕ} (hmq : 2 * q ≤ m) (u v : ℝ) :
    (∑ k ∈ Icc q (m - q), (∑ j ∈ Icc 1 k, b j * a (k - j) u) * a (m - k) v) -
    (∑ k ∈ Icc q (m - q), a k u * (∑ j ∈ Icc 1 (m - k), b j * a (m - k - j) v)) =
      sliceDerivative m q u v := by
  rw [left_derivative_reindex hmq, right_derivative_reindex hmq]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  simp only [mem_Icc] at hj
  rw [← mul_sub]
  unfold leftWindow rightWindow
  rw [reflected_interval hmq hj.2]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi0 := (mem_R.mp hi).1
  rw [show m - j - (m - j - i) = i by omega]

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.slice_strictMonoOn; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
lemma hasDerivAt_slice
    {m q : ℕ} (hmq : 2 * q ≤ m) {S r : ℝ} (hr : 0 < r) (hv : 0 < S - r) :
    HasDerivAt (fun r => Z m q r (S - r)) (sliceDerivative m q r (S - r)) r := by
  have H := HasDerivAt.fun_sum (u := Icc q (m - q)) (fun k _ =>
    (hasDerivAt_a k hr.le).mul ((hasDerivAt_a (m - k) hv.le).comp r
      ((hasDerivAt_const r S).sub (hasDerivAt_id r))))
  change HasDerivAt (fun r => Z m q r (S - r)) _ r at H
  convert H using 1
  simp only [Function.comp_apply, mul_neg_one, zero_sub]
  rw [← derivative_difference hmq]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  ring

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.sliceDerivative_pos; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma R_one {m q : ℕ} (hq : 1 ≤ q) (hmq : 2 * q ≤ m) :
    q - 1 ∈ R m q 1 := by
  rw [mem_R]
  omega

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.slice_strictMonoOn; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma sliceDerivative_pos
    {m q : ℕ} (hq : 1 ≤ q) (hmq : 2 * q ≤ m) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    0 < sliceDerivative m q u v := by
  apply sum_pos'
  · intro j hj
    simp only [mem_Icc] at hj
    apply mul_nonneg (b_pos j (by omega)).le
    apply sum_nonneg
    intro i hi
    exact sub_nonneg.mpr (tp2_le hu huv.le (R_lt hmq hj.2 hi))
  · refine ⟨1, by simp only [mem_Icc]; omega, ?_⟩
    apply mul_pos (b_pos 1 (by omega))
    apply sum_pos'
    · intro i hi
      exact (sub_pos.mpr (tp2 hu huv (R_lt hmq (by omega) hi))).le
    · exact ⟨q - 1,R_one hq hmq,
        sub_pos.mpr (tp2 hu huv (R_lt hmq (by omega) (R_one hq hmq)))⟩

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.balancing; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
lemma Z_symm {m q : ℕ} (hmq : 2 * q ≤ m) (u v : ℝ) : Z m q u v = Z m q v u := by
  unfold Z
  simp only [← Finset.Ico_succ_right_eq_Icc, Nat.succ_eq_succ, Nat.succ_eq_add_one]
  have h := Finset.sum_Ico_reflect (fun k => a k v * a (m - k) u) q
    (m := m - q + 1) (n := m) (by omega)
  have hlo : m + 1 - (m - q + 1) = q := by omega
  have hhi : m + 1 - q = m - q + 1 := by omega
  rw [hlo, hhi] at h
  rw [h.symm]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_Ico.mp hk
  rw [Nat.sub_sub_self (by omega : k ≤ m)]
  exact mul_comm _ _

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.balancing; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
lemma slice_strictMonoOn
    {m q : ℕ} (hq : 1 ≤ q) (hmq : 2 * q ≤ m) {S : ℝ} (hS : 0 < S) :
    StrictMonoOn (fun r => Z m q r (S - r)) (Set.Ioc 0 (S / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (S / 2))
  · intro r hr
    have hv : 0 < S - r := by linarith [hr.2]
    exact (hasDerivAt_slice hmq hr.1 hv).continuousAt.continuousWithinAt
  · intro r hr
    simp only [interior_Ioc, Set.mem_Ioo] at hr
    have hv : 0 < S - r := by linarith [hr.2]
    rw [(hasDerivAt_slice hmq hr.1 hv).deriv]
    exact sliceDerivative_pos hq hmq hr.1 (by linarith [hr.2])

/- proof_shape: bind-only; escape_witness: none; consumers: Interval.tail_nonneg; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
private lemma balancing
    {m q : ℕ} (hq : 1 ≤ q) (hmq : 2 * q ≤ m) {μ α β : ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Z m q μ (μ + α + β) ≤ Z m q (μ + α) (μ + β) := by
  let S := 2 * μ + α + β
  have hS : 0 < S := by dsimp [S]; linarith
  have hmono := (slice_strictMonoOn hq hmq hS).monotoneOn
  by_cases hab : α ≤ β
  · have h := hmono (show μ∈Set.Ioc 0 (S / 2) by dsimp [S]; constructor <;> linarith)
      (show μ + α∈Set.Ioc 0 (S / 2) by dsimp [S]; constructor <;> linarith) (by linarith : μ ≤ μ + α)
    simpa only [show S - μ = μ + α + β by dsimp [S]; ring,
      show S - (μ + α) = μ + β by dsimp [S]; ring] using h
  · have h := hmono (show μ∈Set.Ioc 0 (S / 2) by dsimp [S]; constructor <;> linarith)
      (show μ + β∈Set.Ioc 0 (S / 2) by dsimp [S]; constructor <;> linarith) (by linarith : μ ≤ μ + β)
    dsimp only at h
    rw [show S - μ = μ + α + β by dsimp [S]; ring,
      show S - (μ + β) = μ + α by dsimp [S]; ring] at h
    exact h.trans_eq (Z_symm hmq (μ + β) (μ + α))

/- proof_shape: bind-only; escape_witness: none; consumers: Result.tail; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
lemma tail_nonneg
    {m q : ℕ} (hmq : 2 * q ≤ m) {μ α β : ℝ}
    (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ ∑ k ∈ Icc q (m - q),
      (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β)) := by
  by_cases hq0 : q = 0
  · subst q
    rw [Nat.sub_zero, ← Nat.range_succ_eq_Icc_zero, sum_sub_distrib,
      index_law (μ + α) (μ + β) m (by linarith) (by linarith),
      index_law μ (μ + α + β) m hμ (by linarith)]
    have he : μ + α + (μ + β) = μ + (μ + α + β) := by ring
    simp only [he, sub_self, le_refl]
  · have hq : 1 ≤ q := by omega
    rcases hμ.eq_or_lt with rfl | hμ
    · apply sum_nonneg
      intro k hk
      simp only [mem_Icc] at hk
      rw [a_zero_parameter (by omega)]
      simp only [zero_add, zero_mul, sub_zero]
      exact mul_nonneg (a_nonneg k hα) (a_nonneg (m - k) hβ)
    · rw [sum_sub_distrib]
      exact sub_nonneg.mpr (balancing hq hmq hμ hα hβ)

end D5.S3.Analytic.KarpZhangCatalanPower.Interval

end

noncomputable section
open Finset
namespace D5.S3.Analytic.KarpZhangCatalanPower.Result

open Coeff Index

/- proof_shape: bind-only; escape_witness: none; consumers: Result.claim, Result.convex_ratio, Result.convex_step, Result.positive_all, Result.result, Result.zero_tail; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
/-- Definition 1.1: a nonnegative nontrivial sequence with the reversed
adjacent inequalities, with indices in ℕ = {1,2,…}. No support condition. -/
def IsLogConvex (h : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ h k) ∧ (∃ k, h k ≠ 0) ∧
    (∀ k, 1 ≤ k → h k ^ 2 ≤ h (k - 1) * h (k + 1))

/- proof_shape: bind-only; escape_witness: none; consumers: Result.abel, Result.claim, Result.result; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
/-- Degree-m coefficient of the Turanian of the formal series (15). -/
def delta (h : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), h k * h (m - k) *
    (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β))

/- proof_shape: content; escape_witness: Result.zero_tail; consumers: Result.convex_step; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma zero_tail {h : ℕ → ℝ} (hh : IsLogConvex h) (hz : h 1 = 0)
    (n : ℕ) : h (n + 1) = 0 := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    have he := hh.2.2 (n + 2) (by omega)
    rw [show n + 2 - 1 = n + 1 by omega, ih, zero_mul] at he
    simpa only [Nat.add_assoc] using (sq_nonpos_iff (h (n + 2))).mp he

/- proof_shape: content; escape_witness: Result.positive_all; consumers: Result.convex_ratio, Result.convex_step; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma positive_all {h : ℕ → ℝ} (hh : IsLogConvex h) (h1 : 0 < h 1)
    (n : ℕ) : 0 < h n := by
  have h0 : 0 < h 0 := by
    have he := hh.2.2 1 (by omega)
    norm_num only [Nat.sub_self] at he
    by_contra hn
    have hz : h 0 = 0 := le_antisymm (le_of_not_gt hn) (hh.1 0)
    rw [hz, zero_mul] at he
    nlinarith only [he, h1]
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih ih1 =>
    have he := hh.2.2 (n + 1) (by omega)
    rw [Nat.add_sub_cancel] at he
    by_contra hn
    have hz : h (n + 2) = 0 := le_antisymm (le_of_not_gt hn) (hh.1 _)
    rw [show n + 1 + 1 = n + 2 by omega, hz, mul_zero] at he
    nlinarith only [he, ih1]

/- proof_shape: content; escape_witness: Result.positive_all; consumers: Result.convex_step; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma convex_ratio {h : ℕ → ℝ} (hh : IsLogConvex h) (h1 : 0 < h 1)
    (a n : ℕ) : h (a + 1) / h a ≤ h (a + n + 1) / h (a + n) := by
  have hmono : Monotone (fun k : ℕ => h (k + 1) / h k) :=
    monotone_nat_of_le_succ (fun k => by
      have he := hh.2.2 (k + 1) (by omega)
      rw [Nat.add_sub_cancel] at he
      apply (div_le_div_iff₀ (positive_all hh h1 k)
        (positive_all hh h1 (k + 1))).mpr
      nlinarith only [he])
  exact hmono (by omega : a ≤ a + n)

/- proof_shape: content; escape_witness: Result.zero_tail, Result.positive_all; consumers: Result.result; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: none. -/
private lemma convex_step {h : ℕ → ℝ} (hh : IsLogConvex h)
    (m k : ℕ) (hk : k < m / 2) :
    h (k + 1) * h (m - (k + 1)) ≤ h k * h (m - k) := by
  by_cases hz : h 1 = 0
  · rw [zero_tail hh hz k, zero_mul]
    exact mul_nonneg (hh.1 _) (hh.1 _)
  · have h1 : 0 < h 1 := lt_of_le_of_ne (hh.1 1) (Ne.symm hz)
    have he := convex_ratio hh h1 k (m - k - 1 - k)
    rw [show k + (m - k - 1 - k) + 1 = m - k by omega,
      show k + (m - k - 1 - k) = m - (k + 1) by omega] at he
    have hc := (div_le_div_iff₀ (positive_all hh h1 _) (positive_all hh h1 _)).mp he
    nlinarith only [hc]

/- proof_shape: bind-only; escape_witness: none; consumers: Result.result; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: D5/S3/Analytic/KarpZhangReciprocal/Result.abel_layers [statement_id=sha256:1f4c98d526cdc81a6201b601b53c9ae3d7f1341af0d6daaf3cd848ef99f7e763]; D5/S3/Analytic/KarpZhangReciprocal/Result.increment [statement_id=sha256:1207b96dae6c500c52707f41fe79b5e5058f4c0aa52be6412607471cb02c05b8]; D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum [statement_id=sha256:47b3c03268296e64f4b0bf24d2c278d331ce0da2c2acf1874e481088ac6793fd]. -/
private lemma abel (h : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) :
    delta h μ α β m =
      ∑ q ∈ range (m / 2 + 1),
        KarpZhangReciprocal.Result.increment (fun i => h i * h (m - i)) q *
        (∑ k ∈ Icc q (m - q),
          (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β))) := by
  rw [delta, KarpZhangReciprocal.Result.abel_layers]
  apply sum_congr rfl
  intro q hq
  congr 1
  let K := fun k => a k (μ + α) * a (m - k) (μ + β) -
    a k μ * a (m - k) (μ + α + β)
  rw [← KarpZhangReciprocal.Result.tail_sum K m q (by have := mem_range.mp hq; omega)]
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_Icc]
  omega

/- proof_shape: bind-only; escape_witness: none; consumers: Result.result; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
private lemma tail {m q : ℕ} (hq : q ∈ range (m / 2 + 1))
    {μ α β : ℝ} (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ ∑ k ∈ Icc q (m - q),
      (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β)) :=
  Interval.tail_nonneg (by have := mem_range.mp hq; omega) hμ hα hβ

/- proof_shape: bind-only; escape_witness: none; consumers: Result.result; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: none. -/
private lemma full_tail (m : ℕ) {μ α β : ℝ}
    (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (∑ k ∈ Icc 0 (m - 0),
      (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β))) = 0 := by
  rw [Nat.sub_zero, ← Nat.range_succ_eq_Icc_zero, sum_sub_distrib,
    index_law (μ + α) (μ + β) m (by linarith) (by linarith),
    index_law μ (μ + α + β) m hμ (by linarith)]
  rw [show μ + α + (μ + β) = μ + (μ + α + β) by ring, sub_self]

/- proof_shape: bind-only; escape_witness: none; consumers: Result.result; admission_basis: open-problem-resolution.
   direct frozen dependencies: none; 5.2 owner dependencies: D5/S3/Analytic/KarpZhangReciprocal/Result.IsLogConcave [statement_id=sha256:b42cbcf21ac638e1b04c3104e1ecca467dd7f5283382d61727edd4354b0c30a0]. -/
/-- Conjecture 4.2, including the nonnegative base-parameter boundary. -/
def claim : Prop :=
  ∀ (h : ℕ → ℝ) (μ α β : ℝ) (m : ℕ), 0 ≤ μ → 0 ≤ α → 0 ≤ β →
    (KarpZhangReciprocal.Result.IsLogConcave h → 0 ≤ delta h μ α β m) ∧
    (IsLogConvex h → delta h μ α β m ≤ 0)

/- proof_shape: content; escape_witness: Result.zero_tail, Result.positive_all; consumers: external Conjecture 4.2 settlement; admission_basis: open-problem-resolution.
   direct frozen dependencies: D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS [statement_id=sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit [statement_id=sha256:5e098d038c5b114c26c920876e1d467579862700fdcbb0dee72e3b5ced96a902; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff [statement_id=sha256:c9334674dda36d5d013ed24766e26f0e97251556416206cc532408d30287dd33; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient [statement_id=sha256:706c7e8f9ee9216f3af5d08cbb7460a5dd6dc5924b3bf1bc1a531f267cee08b5; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q [statement_id=sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff [statement_id=sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform [statement_id=sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f; module statement_id=sha256:b9b725a6d260124db3ccab51dd843e7dab3c2801f402827582a8d081ac273f7e]; 5.2 owner dependencies: D5/S3/Analytic/KarpZhangReciprocal/Result.IsLogConcave [statement_id=sha256:b42cbcf21ac638e1b04c3104e1ecca467dd7f5283382d61727edd4354b0c30a0]; D5/S3/Analytic/KarpZhangReciprocal/Result.abel_layers [statement_id=sha256:1f4c98d526cdc81a6201b601b53c9ae3d7f1341af0d6daaf3cd848ef99f7e763]; D5/S3/Analytic/KarpZhangReciprocal/Result.balanced_step [statement_id=sha256:140a2a4910e9527641f28cb4c26ce135410f92b1634e3f35f50ae0c8d6efd5f6]; D5/S3/Analytic/KarpZhangReciprocal/Result.increment [statement_id=sha256:1207b96dae6c500c52707f41fe79b5e5058f4c0aa52be6412607471cb02c05b8]; D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum [statement_id=sha256:47b3c03268296e64f4b0bf24d2c278d331ce0da2c2acf1874e481088ac6793fd]. -/
/-- Both coefficient signs for all nonnegative real shifts and every degree. -/
theorem result : claim := by
  intro h μ α β m hμ hα hβ
  constructor
  · intro hh
    rw [abel]
    apply sum_nonneg
    intro q hq
    apply mul_nonneg
    · unfold KarpZhangReciprocal.Result.increment
      split_ifs with hz
      · exact mul_nonneg (hh.1 _) (hh.1 _)
      · have he := KarpZhangReciprocal.Result.balanced_step hh m (q - 1)
          (by have := mem_range.mp hq; omega)
        rw [show q - 1 + 1 = q by omega] at he
        exact sub_nonneg.mpr he
    · exact tail hq hμ hα hβ
  · intro hh
    rw [abel]
    apply sum_nonpos
    intro q hq
    by_cases hz : q = 0
    · subst q
      rw [full_tail m hμ hα hβ, mul_zero]
    · apply mul_nonpos_of_nonpos_of_nonneg
      · unfold KarpZhangReciprocal.Result.increment
        rw [ite_eq_right hz]
        have he := convex_step hh m (q - 1) (by have := mem_range.mp hq; omega)
        rw [show q - 1 + 1 = q by omega] at he
        exact sub_nonpos.mpr he
      · exact tail hq hμ hα hβ

end D5.S3.Analytic.KarpZhangCatalanPower.Result
