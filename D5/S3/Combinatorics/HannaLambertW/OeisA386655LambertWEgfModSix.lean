/- GID: D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix
   generality: I
   mirror-B: D5/B/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Lambert W coefficients and finite-ring binomial periodicity prove Hanna mod six. -/

/-
admission_basis: open-problem-resolution (#18668; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19849
Every theorem below has proof_shape: bind-only and escape_witness: none.
forward_unit: proof_shape: bind-only; escape_witness: none; consumers: T, T_inverse.
T_zero: proof_shape: bind-only; escape_witness: none; consumers: T_equation, T_eq_W, coeff_exp_W.
T_inverse: proof_shape: bind-only; escape_witness: none; consumers: T_equation.
T_equation: proof_shape: bind-only; escape_witness: none; consumers: T_eq_W, coeff_exp_W.
E_mul: proof_shape: bind-only; escape_witness: none; consumers: coeff_exp_W.
E_pow: proof_shape: bind-only; escape_witness: none; consumers: T_eq_W, coeff_exp_W.
E_coeff: proof_shape: bind-only; escape_witness: none; consumers: T_eq_W, derivative_E, coeff_exp_W, egf_rearranged, egf_closed.
T_eq_W: proof_shape: bind-only; escape_witness: none; consumers: coeff_exp_W.
lagrange_subst: proof_shape: bind-only; escape_witness: none; consumers: coeff_exp_W.
derivative_E: proof_shape: bind-only; escape_witness: none; consumers: coeff_exp_W.
coeff_exp_W: proof_shape: bind-only; escape_witness: none; consumers: egf_closed.
sum_triangle: proof_shape: bind-only; escape_witness: none; consumers: egf_rearranged.
coeff_binomial: proof_shape: bind-only; escape_witness: none; consumers: egf_rearranged.
factorial_ratio: proof_shape: bind-only; escape_witness: none; consumers: egf_rearranged.
egf_rearranged: proof_shape: bind-only; escape_witness: none; consumers: egf_closed.
egf_closed: proof_shape: bind-only; escape_witness: none; consumers: result in all four delivered modules.
B_succ: proof_shape: bind-only; escape_witness: none; consumers: Bs_succ.
Bs_succ: proof_shape: bind-only; escape_witness: none; consumers: B_period.
B_period: proof_shape: bind-only; escape_witness: none; consumers: B_reduce.
cube_eq: proof_shape: bind-only; escape_witness: none; consumers: pow_shift_two.
pow_shift_two: proof_shape: bind-only; escape_witness: none; consumers: pow_positive.
pow_positive: proof_shape: bind-only; escape_witness: none; consumers: pow_redPow.
pow_redPow: proof_shape: bind-only; escape_witness: none; consumers: interior_weight, closedR_B.
redPow_product: proof_shape: bind-only; escape_witness: none; consumers: interior_weight, closedR_B.
redPow_square: proof_shape: bind-only; escape_witness: none; consumers: closedR_B.
weight_top: proof_shape: bind-only; escape_witness: none; consumers: closedR_B.
B_reduce: proof_shape: bind-only; escape_witness: none; consumers: closedR_reduce.
interior_weight: proof_shape: bind-only; escape_witness: none; consumers: closedR_B.
closedR_B: proof_shape: bind-only; escape_witness: none; consumers: closedR_reduce.
closedR_reduce: proof_shape: bind-only; escape_witness: none; consumers: closedZ_reduce.
closedZ_cast: proof_shape: bind-only; escape_witness: none; consumers: closedZ_reduce.
closedZ_reduce: proof_shape: bind-only; escape_witness: none; consumers: result in all four delivered modules.
values_2: proof_shape: bind-only; escape_witness: none; consumers: pattern_2.
pattern_2: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
Direct frozen dependencies (declaration identities on the merged base):
D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient
  statement_id: sha256:81f9e16808d9c491ff86a34e6bc2734ff65bb35128a1cae2aac5acffd2329b46
D5/S1/Recurrence/Residue/QuarticEGFModFour.F
  statement_id: sha256:00d1d435796f3af5e8009c9808ae0fd87d3c4afe48f8b0955596786da1bcb829
D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.subst_coeff is published here;
  its new public identity is to be read from the scoped freeze report.
The source definitions W and egf retain their displayed expressions.
The forward series is reused from QuarticEGFModFour.F.
Utility none: the conclusions are unbounded symbolic integrality and periodicity.
Finite-ring arithmetic and six initial values are consumed normalization steps.
-/

import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo
import D5.S1.Recurrence.Invariants.TripleIterateShiftModThree
import D5.S1.Recurrence.Residue.QuarticEGFModFour
import D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree

set_option autoImplicit false

namespace D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix

open PowerSeries

/-- The principal branch of Lambert's W as a power series, `W(x) = ∑_{m ≥ 1} (-m)^(m-1) x^m / m!`
(the solution of `W e^W = x` with `W(0) = 0`). -/
noncomputable def W : ℚ⟦X⟧ :=
  mk fun m => if m = 0 then 0 else ((-(m : ℚ)) ^ (m - 1)) / (m.factorial : ℚ)

/-- `m!` times the coefficient of `x^m` in `∑_{n ≥ 0} (q^n x + W(x))^n / n!`. The `n`-th term has order `n`,
so only `n ≤ m` contribute. -/
noncomputable def egf (q m : ℕ) : ℚ :=
  (m.factorial : ℚ) * ∑ n ∈ Finset.range (m + 1),
    coeff m ((C ((q : ℚ) ^ n) * X + W) ^ n) / (n.factorial : ℚ)

/-- A386655: the e.g.f. `∑_{n ≥ 0} (2^n x + LambertW(x))^n / n!`. -/
noncomputable def a (m : ℕ) : ℚ := egf 2 m

/-- A386655 ("Conjecture: for n >= 6, a(n) (mod 6) equals [1, 0, 3, 0, 3, 2] repeating."). -/
def claim : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∃ z : ℤ, (z : ℚ) = a n ∧ z % 6 = ([1, 0, 3, 0, 3, 2] : List ℤ).getD ((n - 6) % 6) 0


open PowerSeries
open scoped BigOperators
noncomputable section

private theorem forward_unit : IsUnit (coeff 1 D5.S1.Recurrence.Residue.QuarticEGFModFour.F) := by
  simp [D5.S1.Recurrence.Residue.QuarticEGFModFour.F]

private def T : (PowerSeries ℚ) := D5.S1.Recurrence.Residue.QuarticEGFModFour.F.substInvOfIsUnit forward_unit
private theorem T_zero : constantCoeff T = 0 := by
  simp [T]

private theorem T_inverse : subst T D5.S1.Recurrence.Residue.QuarticEGFModFour.F = X := by
  exact subst_substInvOfIsUnit_right D5.S1.Recurrence.Residue.QuarticEGFModFour.F (by simp [D5.S1.Recurrence.Residue.QuarticEGFModFour.F]) forward_unit

private theorem T_equation : T = X * subst T ((rescale (-1) (exp ℚ))) := by
  have ht : HasSubst T := HasSubst.of_constantCoeff_zero' T_zero
  have hinv : exp ℚ * (rescale (-1) (exp ℚ)) = 1 := by
    exact exp_mul_exp_neg_eq_one
  have hmap := congrArg (substAlgHom ht) hinv
  simp only [map_mul, map_one, coe_substAlgHom] at hmap
  have ht_inv := T_inverse
  simp only [D5.S1.Recurrence.Residue.QuarticEGFModFour.F, subst_mul ht, subst_X ht] at ht_inv
  calc
    T = T * (subst T (exp ℚ) * subst T ((rescale (-1) (exp ℚ)))) := by rw [hmap]; ring
    _ = (T * subst T (exp ℚ)) * subst T ((rescale (-1) (exp ℚ))) := by ring
    _ = X * subst T ((rescale (-1) (exp ℚ))) := by rw [ht_inv]

private theorem E_mul (y z : ℚ) : (rescale y (exp ℚ)) * (rescale z (exp ℚ)) = (rescale (y+z) (exp ℚ)) := by
  exact exp_mul_exp_eq_exp_add y z

private theorem E_pow (y : ℚ) (n : ℕ) : (rescale y (exp ℚ)) ^ n = (rescale ((n : ℚ)*y) (exp ℚ)) := by
    rw [← map_pow, exp_pow_eq_rescale_exp, rescale_rescale]


private theorem E_coeff (y : ℚ) (n : ℕ) : coeff n ((rescale y (exp ℚ))) = y^n / (n.factorial : ℚ) := by
  simp [ coeff_exp, div_eq_mul_inv]

private theorem T_eq_W : T = W := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, T_zero, W]
  | succ n =>
    have h := D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient
      T ((rescale (-1) (exp ℚ))) T_zero T_equation (n+1) 1 (by omega) (by omega)
    simp only [pow_one, Nat.cast_one, one_mul, Nat.add_sub_cancel] at h
    rw [E_pow, E_coeff] at h
    simp only [W, coeff_mk, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hn : ((n+1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    apply (eq_div_iff (mul_ne_zero hn (by positivity))).2
    linear_combination (norm := (field_simp; ring)) (n.factorial : ℚ) * h

private theorem lagrange_subst (root factor F : (PowerSeries ℚ)) (hzero : constantCoeff root = 0)
    (heq : root = X * subst root factor) (n : ℕ) :
    ((n+1 : ℕ) : ℚ) * coeff (n+1) (subst root F) =
      coeff n (PowerSeries.derivative F * factor^(n+1)) := by
  classical
  rw [D5.S1.Recurrence.Invariants.TripleIterateShiftModThree.subst_coeff F root hzero, Finset.sum_range_succ', coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [pow_zero, coeff_one, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte, mul_zero, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb : j+1 ≤ n+1 := by simpa using Finset.mem_range.mp hj
  have h := D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient
    root factor hzero heq (n+1) (j+1) (by omega) hjb
  simp only [Nat.add_sub_add_right] at h
  rw [coeff_derivative]
  push_cast at h ⊢
  linear_combination coeff (j+1) F * h

private theorem derivative_E (y : ℚ) : PowerSeries.derivative ((rescale y (exp ℚ))) = C y * (rescale y (exp ℚ)) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_derivative, coeff_C_mul, E_coeff, E_coeff, pow_succ,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem coeff_exp_W (y : ℚ) (n : ℕ) :
    coeff (n+1) (subst W ((rescale y (exp ℚ)))) =
      y * (y - ((n+1 : ℕ) : ℚ))^n / ((n+1).factorial : ℚ) := by
  rw [← T_eq_W]
  have h := lagrange_subst T ((rescale (-1) (exp ℚ))) ((rescale y (exp ℚ))) T_zero T_equation n
  rw [derivative_E, E_pow, mul_assoc, E_mul] at h
  simp only [mul_neg_one, coeff_C_mul, E_coeff] at h
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hn : ((n+1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  apply (eq_div_iff (mul_ne_zero hn (by positivity))).2
  linear_combination (norm := (field_simp; ring)) (n.factorial : ℚ) * h

end

open PowerSeries
open scoped BigOperators
noncomputable section

private theorem sum_triangle (f : ℕ → ℕ → ℚ) (n : ℕ) :
    (∑ m ∈ Finset.range (n+1), ∑ k ∈ Finset.range (m+1), f m k) =
      ∑ k ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n-k+1), f (k+r) k := by
  calc
    _ = ∑ m ∈ Finset.range (n+1), ∑ k ∈ Finset.range (m+1), f (k+(m-k)) k := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.add_sub_of_le (Finset.mem_range_succ_iff.mp hk)]
    _ = ∑ k ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n+1-k), f (k+r) k :=
      Finset.sum_range_diag_flip (n+1) (fun k r => f (k+r) k)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range_succ_iff.mp hk
      rw [show n+1-k = n-k+1 by omega]

private theorem coeff_binomial (q m n : ℕ) (hm : m ≤ n) :
    coeff n ((C ((q : ℚ)^m) * X + W)^m) =
      ∑ k ∈ Finset.range (m+1), (m.choose k : ℚ) *
        (q : ℚ)^(m*k) * coeff (n-k) (W^(m-k)) := by
  classical
  rw [add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ m := Finset.mem_range_succ_iff.mp hk
  have hexp : (C ((q : ℚ)^m) * X)^k * W^(m-k) *
      (m.choose k : (PowerSeries ℚ)) = C ((m.choose k : ℚ) * (q : ℚ)^(m*k)) *
        (X^k * W^(m-k)) := by
    rw [mul_pow, ← map_pow, ← pow_mul]
    rw [← map_natCast C (m.choose k), map_mul]
    ring
  rw [hexp, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega)]

private theorem factorial_ratio (m k : ℕ) (hk : k ≤ m) :
    (m.choose k : ℚ) / (m.factorial : ℚ) =
      1 / (k.factorial : ℚ) / ((m-k).factorial : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hc : (m.choose k : ℚ) * (k.factorial : ℚ) * ((m-k).factorial : ℚ) =
      (m.factorial : ℚ) := by exact_mod_cast h
  field_simp
  linear_combination hc

private theorem egf_rearranged (q n : ℕ) : egf q n =
    (n.factorial : ℚ) * ∑ k ∈ Finset.range (n+1),
      ((q : ℚ)^(k*k) / (k.factorial : ℚ)) *
        coeff (n-k) (subst W ((rescale ((q : ℚ)^k) (exp ℚ)))) := by
  classical
  unfold egf
  congr 1
  calc
    (∑ m ∈ Finset.range (n+1),
        coeff n ((C ((q : ℚ)^m) * X + W)^m) / (m.factorial : ℚ)) =
      ∑ m ∈ Finset.range (n+1), ∑ k ∈ Finset.range (m+1),
        ((m.choose k : ℚ) * (q : ℚ)^(m*k) * coeff (n-k) (W^(m-k))) /
          (m.factorial : ℚ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [coeff_binomial q m n (by simpa using Finset.mem_range.mp hm), Finset.sum_div]
    _ = ∑ k ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n-k+1),
        (((k+r).choose k : ℚ) * (q : ℚ)^((k+r)*k) *
          coeff (n-k) (W^r)) / ((k+r).factorial : ℚ) := by
      rw [sum_triangle]
      simp only [Nat.add_sub_cancel_left]
    _ = ∑ k ∈ Finset.range (n+1), ((q : ℚ)^(k*k) / (k.factorial : ℚ)) *
        coeff (n-k) (subst W ((rescale ((q : ℚ)^k) (exp ℚ)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [D5.S1.Recurrence.Invariants.TripleIterateShiftModThree.subst_coeff _ _ (by simp [W]), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [E_coeff, ← pow_mul]
      have hratio := factorial_ratio (k+r) k (by omega)
      rw [Nat.add_sub_cancel_left] at hratio
      have hp : (q : ℚ)^((k+r)*k) = (q : ℚ)^(k*k) * (q : ℚ)^(k*r) := by
        rw [show (k+r)*k = k*k+k*r by ring, pow_add]
      rw [hp]
      linear_combination (norm := ring) ((q : ℚ)^(k*k) * (q : ℚ)^(k*r) *
        coeff (n-k) (W^r)) * hratio

def closedZ (q n : ℕ) : ℤ :=
    (q : ℤ)^(n*n) + ∑ k ∈ Finset.range n,
      (n.choose k : ℤ) * (q : ℤ)^(k*(k+1)) *
        ((q : ℤ)^k - ((n-k : ℕ) : ℤ))^(n-k-1)

theorem egf_closed (q n : ℕ) : egf q n = (closedZ q n : ℚ) := by
  classical
  rw [egf_rearranged, Finset.sum_range_succ, mul_add, Finset.mul_sum]
  have top : (n.factorial : ℚ) *
      (((q : ℚ)^(n*n) / (n.factorial : ℚ)) *
        coeff (n-n) (subst W ((rescale ((q : ℚ)^n) (exp ℚ))))) = (q : ℚ)^(n*n) := by
    rw [Nat.sub_self, D5.S1.Recurrence.Invariants.TripleIterateShiftModThree.subst_coeff _ _ (by simp [W])]
    simp [E_coeff] <;> field_simp

  rw [top]
  simp only [closedZ, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, Int.cast_sub]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  obtain ⟨d, hd⟩ : ∃ d : ℕ, n-k = d+1 := ⟨n-k-1, by omega⟩
  simp only [hd]
  rw [coeff_exp_W]
  simp only [Nat.add_sub_cancel]
  have hf : ((n.choose k : ℚ) * (k.factorial : ℚ) * ((d+1).factorial : ℚ)) =
      (n.factorial : ℚ) := by
    rw [← hd]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (show k ≤ n by omega)
  have hp : (q : ℚ)^(k*k) * (q : ℚ)^k = (q : ℚ)^(k*(k+1)) := by
    rw [← pow_add]
    congr 1
  rw [← hf, ← hp]
  field_simp

end

open scoped BigOperators
open Finset

private def Bs (f : (ZMod 6) → (ZMod 6)) (j : (ZMod 6)) (n : ℕ) : (ZMod 6) :=
  D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
    (fun k => f ((k : ZMod 6) + j)) (fun _ => 1) n

private theorem B_succ (f : ZMod 6 → ZMod 6) (n : ℕ) :
    D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f (k : ZMod 6)) (fun _ => 1) (n+1) =
      D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f (k : ZMod 6)) (fun _ => 1) n +
      D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f ((k : ZMod 6) + 1)) (fun _ => 1) n := by
  simpa only [D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul,
    Nat.cast_add, Nat.cast_one, Nat.add_assoc, mul_one] using
    Finset.sum_choose_succ_mul (fun i _ => f (i : ZMod 6)) n

private theorem Bs_succ (f : (ZMod 6) → (ZMod 6)) (j : (ZMod 6)) (n : ℕ) :
    Bs f j (n+1) = Bs f j n + Bs f (j+1) n := by
  simp only [Bs]
  have h := B_succ (fun k => f (k + j)) n
  simpa only [add_assoc, add_comm, add_left_comm] using h

private theorem B_period (f : (ZMod 6) → (ZMod 6)) (n : ℕ) :
    D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f (k : ZMod 6)) (fun _ => 1) (n+9) =
      D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f (k : ZMod 6)) (fun _ => 1) (n+3) := by
  have h0 (m : ℕ) : Bs f 0 m =
      D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f (k : ZMod 6)) (fun _ => 1) m := by simp [Bs]
  rw [← h0, ← h0]
  simp only [Bs_succ]
  norm_num [Bs]
  ring_nf
  have h6 : (6 : (ZMod 6)) = 0 := (ZMod.val_eq_zero _).mp rfl
  have h7 : (7 : (ZMod 6)) = 1 := ZMod.toAddCircle_inj.mp rfl
  have h8 : (8 : (ZMod 6)) = 2 := ZMod.toAddCircle_inj.mp rfl
  have h9 : (9 : (ZMod 6)) = 3 := ZMod.toAddCircle_inj.mp rfl
  have h36 : (36 : (ZMod 6)) = 0 := (ZMod.val_eq_zero _).mp rfl
  have h84 : (84 : (ZMod 6)) = 0 := (ZMod.val_eq_zero _).mp rfl
  have h126 : (126 : (ZMod 6)) = 0 := (ZMod.val_eq_zero _).mp rfl
  simp only [h6, h7, h8, h9, h36, h84, h126, zero_add, mul_zero, add_zero]

private theorem cube_eq (x : (ZMod 6)) : x^3 = x := by
  fin_cases x <;> rfl

private theorem pow_shift_two (x : (ZMod 6)) (n : ℕ) : x^(n+3) = x^(n+1) := by
  rw [pow_add, cube_eq, pow_add, pow_one]

private theorem pow_positive (x : (ZMod 6)) (n : ℕ) : x^(n+1) = x^(1+n%2) := by
  have hp : Function.Periodic (fun m : ℕ => x^(m+1)) 2 := by
    intro m
    simpa only [Nat.add_assoc, Nat.reduceAdd] using pow_shift_two x m
  simpa only [Nat.add_comm] using (hp.map_mod_nat n).symm

private def redPow (x e : (ZMod 6)) : (ZMod 6) := x^(1+(e+1).val%2)
private def weight (q s t : (ZMod 6)) : (ZMod 6) := q^2 * redPow (redPow q t - s + t) (s-t-1)
private def correction (q s : (ZMod 6)) : (ZMod 6) :=
   redPow (1-s) (s-1) - weight q s 0 + s*(q^2 - weight q s (s-1))

private theorem pow_redPow (x : (ZMod 6)) (m : ℕ) (hm : 0 < m) :
    x^m = redPow x (m : (ZMod 6)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n+1 := ⟨m-1, by omega⟩
  rw [pow_positive]
  unfold redPow
  congr 1
  simp only [ZMod.val_add, ZMod.val_natCast, ZMod.val_one_eq_one_mod]
  norm_num
  omega

private theorem redPow_product (x e : (ZMod 6)) : redPow x (e*(e+1)) = x^2 := by
  fin_cases x <;> fin_cases e <;> decide

private theorem redPow_square (x e : (ZMod 6)) : redPow x (e*e) = redPow x e := by
  fin_cases x <;> fin_cases e <;> decide


private theorem weight_top (q s : (ZMod 6)) : weight q s s = redPow q s := by
  fin_cases q <;> fin_cases s <;> decide

private theorem B_reduce (f : (ZMod 6) → (ZMod 6)) (n : ℕ) :
    D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f (k : ZMod 6)) (fun _ => 1) (n+6) =
      D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f (k : ZMod 6)) (fun _ => 1) (n%6+6) := by
  have hp : Function.Periodic (fun m : ℕ =>
      D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => f (k : ZMod 6)) (fun _ => 1) (m+6)) 6 := by
    intro m
    simpa only [Nat.add_assoc, Nat.reduceAdd] using B_period f (m+3)
  exact (hp.map_mod_nat n).symm

private theorem interior_weight (q : (ZMod 6)) (n k : ℕ) (hk : 0 < k) (hkn : k+1 < n) :
    q^(k*(k+1)) * (q^k - ((n-k : ℕ) : (ZMod 6)))^(n-k-1) =
      weight q (n : (ZMod 6)) (k : (ZMod 6)) := by
  rw [pow_redPow q (k*(k+1)) (by positivity)]
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, redPow_product]
  rw [pow_redPow q k hk]
  rw [pow_redPow _ (n-k-1) (by omega)]
  rw [Nat.cast_sub (by omega : k ≤ n), Nat.cast_sub (by omega : 1 ≤ n-k),
    Nat.cast_sub (by omega : k ≤ n)]
  simp only [Nat.cast_one]
  unfold weight
  congr 2 <;> ring

private theorem closedR_B (q : (ZMod 6)) (n : ℕ) (hn : 2 ≤ n) :
    ((closedZ q.val n : ℤ) : ZMod 6) =
      D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
        (fun k => weight q (n : (ZMod 6)) (k : ZMod 6)) (fun _ => 1) n +
      correction q (n : (ZMod 6)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m+2 := ⟨n-2, by omega⟩
  have hB : D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
      (fun k => weight q ((m+2 : ℕ) : (ZMod 6)) (k : ZMod 6)) (fun _ => 1) (m+2) =
      (∑ k ∈ range m, ((m+2).choose (k+1) : (ZMod 6)) *
        weight q ((m+2 : ℕ) : (ZMod 6)) ((k+1 : ℕ) : (ZMod 6))) +
      weight q ((m+2 : ℕ) : (ZMod 6)) 0 +
      ((m+2 : ℕ) : (ZMod 6)) * weight q ((m+2 : ℕ) : (ZMod 6)) ((m+1 : ℕ) : (ZMod 6)) +
      weight q ((m+2 : ℕ) : (ZMod 6)) ((m+2 : ℕ) : (ZMod 6)) := by
    rw [D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul,
      sum_range_succ, sum_range_succ, sum_range_succ']
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.choose_zero_right,
      Nat.cast_zero, Nat.choose_succ_self_right, mul_one]
  have hlast : q^((m+1)*(m+1+1)) = q^2 := by
    rw [pow_redPow q _ (by positivity)]
    have hc : (((m+1)*(m+1+1) : ℕ) : (ZMod 6)) = (((m+1 : ℕ) : (ZMod 6)))*(((m+1 : ℕ) : (ZMod 6))+1) := by push_cast; ring
    rw [hc, redPow_product]
  have htop : q^((m+2)*(m+2)) = redPow q ((m+2 : ℕ) : (ZMod 6)) := by
    rw [pow_redPow q _ (by positivity), Nat.cast_mul, redPow_square]
  have hzero : (1 - ((m+2 : ℕ) : (ZMod 6)))^(m+1) =
      redPow (1 - ((m+2 : ℕ) : (ZMod 6))) (((m+2 : ℕ) : (ZMod 6))-1) := by
    rw [pow_redPow _ _ (by positivity)]
    congr 1
    push_cast
    ring
  have hinterior : (∑ k ∈ range m, ((m+2).choose (k+1) : (ZMod 6)) *
      q^((k+1)*(k+1+1)) *
        (q^(k+1) - ((m+2-(k+1) : ℕ) : (ZMod 6)))^(m+2-(k+1)-1)) =
      ∑ k ∈ range m, ((m+2).choose (k+1) : (ZMod 6)) *
        weight q ((m+2 : ℕ) : (ZMod 6)) ((k+1 : ℕ) : (ZMod 6)) := by
    apply sum_congr rfl
    intro k hk
    rw [mul_assoc, interior_weight q (m+2) (k+1) (by omega) (by
      have := mem_range.mp hk
      omega)]
  have hC : ((closedZ q.val (m+2) : ℤ) : ZMod 6) =
      redPow q ((m+2 : ℕ) : (ZMod 6)) +
      (∑ k ∈ range m, ((m+2).choose (k+1) : (ZMod 6)) *
        weight q ((m+2 : ℕ) : (ZMod 6)) ((k+1 : ℕ) : (ZMod 6))) +
      redPow (1 - ((m+2 : ℕ) : (ZMod 6))) (((m+2 : ℕ) : (ZMod 6))-1) +
      ((m+2 : ℕ) : (ZMod 6)) * q^2 := by
    simp only [closedZ, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_sub, ZMod.natCast_zmod_val]
    rw [sum_range_succ, sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, zero_mul, pow_zero,
      one_mul, Nat.sub_zero, mul_one, Nat.choose_succ_self_right]
    rw [show m+2-1=m+1 by omega, show m+2-(m+1)=1 by omega]
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [hlast, htop, hzero, hinterior]
    ring
  rw [hC, hB, correction, weight_top]
  have hs : ((m+1 : ℕ) : (ZMod 6)) = ((m+2 : ℕ) : (ZMod 6))-1 := by push_cast; ring
  rw [hs]
  ring

private theorem closedR_reduce (q : (ZMod 6)) (n : ℕ) :
    ((closedZ q.val (n+6) : ℤ) : ZMod 6) = ((closedZ q.val (n%6+6) : ℤ) : ZMod 6) := by
  rw [closedR_B q _ (by omega), closedR_B q _ (by omega)]
  have hs : ((n+6 : ℕ) : (ZMod 6)) = ((n%6+6 : ℕ) : (ZMod 6)) := by
    simp [Nat.cast_add, ZMod.natCast_mod]
  rw [hs, B_reduce]


private theorem closedZ_cast (q n : ℕ) : (closedZ q n : (ZMod 6)) = ((closedZ (q : ZMod 6).val n : ℤ) : ZMod 6) := by
  simp only [closedZ, Int.cast_add, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Int.cast_sub, ZMod.natCast_zmod_val]

theorem closedZ_reduce (q n : ℕ) (hn : 6 ≤ n) :
    closedZ q n % 6 = closedZ q ((n-6)%6+6) % 6 := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ 6).mp
  rw [closedZ_cast q n, closedZ_cast q ((n-6)%6+6)]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m+6 := ⟨n-6, by omega⟩
  simpa only [Nat.add_sub_cancel] using closedR_reduce (q : (ZMod 6)) m


open scoped BigOperators

private theorem values_2 : ∀ r : Fin 6, (closedZ 2 (r.val+6)) % 6 =
    ([1,0,3,0,3,2] : List ℤ).getD r.val 0 := by
  decide

private theorem pattern_2 (n : ℕ) (hn : 6 ≤ n) :
    closedZ 2 n % 6 =
      ([1,0,3,0,3,2] : List ℤ).getD ((n-6)%6) 0 := by
  rw [closedZ_reduce 2 n hn]
  exact values_2 ⟨(n-6)%6, Nat.mod_lt _ (by decide)⟩

theorem result : claim := by
  intro n hn
  refine ⟨closedZ 2 n, ?_, pattern_2 n hn⟩
  change (closedZ 2 n : ℚ) = egf 2 n
  exact (egf_closed 2 n).symm

end D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix
