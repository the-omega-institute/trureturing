/- GID: D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor
   generality: G
   mirror-B: D5/B/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Generalized Fibonacci reciprocal tails have the conjectured integer floor. -/

/-
Admission and declaration assessment
admission_basis: open-problem-resolution (#18768; Proved)
escape_witness: none
Direct frozen dependencies:
D5/S0/Observation/MatrixTracePowerSum.pow_add_two,
statement_id: sha256:477f52a1cada3768c6c6695f7bf1e92216cc53ac6f22ad3f67270f1f31f452be.
The S0 general matrix-power recurrence is imported directly; this module remains S1.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19868.
Public result: result : claim; proof_shape: content, by the expanded inductive
recurrence estimates and the companion-matrix stride identity.
U is the source recurrence; claim includes convergence and the first floor identity.
The difference of successive terms uses Mathlib's fwdDiff 1, with no new alias.
All coefficients and indices remain symbolic. No declaration is a finite enumeration,
checker, numeric reduction or certified instance; utility is none.
The LucasEvenDescent companion requires a unit second coefficient, whereas t here
is an arbitrary positive integer. Its unit-parameter theorems do not cover this domain.

Per-theorem assessment (same-delivery helpers expanded;
escape_witness: none for every declaration; other frozen dependencies: none):
U: proof_shape: bind-only (source definition); consumers: claim, u_rec, matrix_shape,
matrix_entry, stride_rec, integer_growth, stride_parameters, result.
claim: proof_shape: bind-only (source proposition); consumer: result.
RecData: proof_shape: bind-only (private hypotheses); consumers: all real-recurrence
helpers and result.
M: proof_shape: bind-only (private companion data); consumers: matrix_shape,
matrix_entry, stride_rec, stride_parameters, result.
b_step_of: proof_shape: bind-only; consumers: growth, b_step.
growth: proof_shape: content; consumers: positive, b_step, d_mono, b_pos, inv_b_limit,
summable_tail.
positive: proof_shape: content; consumers: reciprocal_lower, reciprocal_upper, summable_tail_gt.
b_step: proof_shape: content; consumers: b_mono.
cassini: proof_shape: content; consumers: reciprocal_lower, reciprocal_upper.
d_mono: proof_shape: content; consumers: domination.
domination: proof_shape: content; consumers: reciprocal_upper.
u_rec: proof_shape: bind-only; consumers: matrix_shape, integer_growth, stride_parameters.
matrix_shape: proof_shape: content; consumers: matrix_entry, stride_parameters.
matrix_entry: proof_shape: content; consumers: stride_rec.
stride_rec: proof_shape: content; frozen dependency: MatrixTracePowerSum.pow_add_two;
consumers: result.
integer_growth: proof_shape: content; consumers: stride_parameters.
stride_parameters: proof_shape: content; consumers: result.
b_pos: proof_shape: content; consumers: reciprocal_lower, tail_lower, recurrence_floor.
b_mono: proof_shape: content; consumers: reciprocal_upper, upper_has_sum, summable_tail_gt, tail_lower.
reciprocal_lower: proof_shape: content; consumers: tail_lower.
reciprocal_upper: proof_shape: content; consumers: summable_tail_gt.
inv_b_limit: proof_shape: content; consumers: upper_has_sum, tail_lower.
telescoping_has_sum: proof_shape: bind-only; consumers: upper_has_sum, tail_lower.
upper_has_sum: proof_shape: content; consumers: summable_tail_gt.
summable_tail_gt: proof_shape: content; consumers: summable_tail, recurrence_floor.
summable_tail: proof_shape: content; consumers: tail_lower, result.
tail_lower: proof_shape: content; consumers: recurrence_floor.
recurrence_floor: proof_shape: content; consumers: result.
result: proof_shape: content; frozen dependency: MatrixTracePowerSum.pow_add_two;
consumers: external settling conclusion.
-/

import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor

/-- The generalized Fibonacci numbers `{n}_{s,t}`: `{0} = 0`, `{1} = 1`, `{n} = s{n − 1} + t{n − 2}`. -/
def U (s t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => s * U s t (n + 1) + t * U s t n

/-- Amdeberhan–Chen–Moll–Sagan, Ann. Comb. 18 (2014), Conjecture 4.6, first clause ("If s > t ≥ 1 with
(s, −t) ≠ (2, −1) and n, r ∈ P then ⌊(∑_{k=n}^∞ 1/{rk}_{s,−t})^{−1}⌋ = {rn}_{s,−t} − {r(n − 1)}_{s,−t} − 1"),
together with the convergence of the series that the identity presupposes. -/
def claim : Prop :=
  ∀ s t : ℤ, 1 ≤ t → t < s → (s, -t) ≠ (2, -1) → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
    Summable (fun k : ℕ => (1 : ℝ) / (U s (-t) (r * (n + k)) : ℝ)) ∧
      ⌊(∑' k : ℕ, (1 : ℝ) / (U s (-t) (r * (n + k)) : ℝ))⁻¹⌋ =
        U s (-t) (r * n) - U s (-t) (r * (n - 1)) - 1

end D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor

namespace D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor

open Filter Topology

private structure RecData (a : ℕ → ℝ) (P Q c : ℝ) : Prop where
  zero : a 0 = 0
  one : a 1 = c
  step : ∀ k, a (k+2) = P*a (k+1)-Q*a k
  q : 1 ≤ Q
  pq : Q+1 ≤ P
  p3 : 3 ≤ P
  c1 : 1 ≤ c
  cp : c+1 ≤ P


variable {a : ℕ → ℝ} {P Q c : ℝ}

private theorem b_step_of (h : RecData a P Q c) (k : ℕ)
    (ha0 : 0 ≤ a k) (hb : c ≤ fwdDiff 1 a k) :
    fwdDiff 1 a k+c ≤ fwdDiff 1 a (k+1) := by
  have ha : fwdDiff 1 a k ≤ a (k+1) := sub_le_self _ ha0
  have hmul := mul_nonneg (show 0 ≤ P-Q-1 by linarith [h.pq]) (sub_nonneg.mpr ha)
  have hmul' := mul_nonneg (show 0 ≤ P-3 by linarith [h.p3])
    (show 0 ≤ fwdDiff 1 a k by linarith [h.c1])
  have hr := h.step k
  dsimp [fwdDiff] at *
  nlinarith

private theorem growth (h : RecData a P Q c) (k : ℕ) :
    0 ≤ a k ∧ c*((k:ℝ)+1) ≤ fwdDiff 1 a k := by
  induction k with
  | zero => simp [fwdDiff, h.zero, h.one]
  | succ k ih =>
    have hc := h.c1
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hb : c ≤ fwdDiff 1 a k := by nlinarith
    have hstep := b_step_of h k ih.1 hb
    constructor
    · dsimp [fwdDiff] at hb
      linarith [ih.1]
    · push_cast
      nlinarith [ih.2]

private theorem positive (h : RecData a P Q c) (k : ℕ) : 0 < a (k+1) := by
  have hg := growth h k
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  dsimp [fwdDiff] at hg
  nlinarith [h.c1]

private theorem b_step (h : RecData a P Q c) (k : ℕ) : fwdDiff 1 a k+c ≤ fwdDiff 1 a (k+1) := by
  have hg := growth h k
  have hc := h.c1
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hb : c ≤ fwdDiff 1 a k := by nlinarith
  exact b_step_of h k hg.1 hb

private theorem cassini (h : RecData a P Q c) (k : ℕ) :
    a (k+1)^2-a k*a (k+2) = c^2*Q^k := by
  induction k with
  | zero => simp [h.zero, h.one]
  | succ k ih =>
    calc
      a (k+1+1)^2-a (k+1)*a (k+1+2) =
          Q*(a (k+1)^2-a k*a (k+2)) := by
        rw [show k+1+1=k+2 by omega, h.step (k+1), h.step k]
        ring
      _ = c^2*Q^(k+1) := by rw [ih, pow_succ Q k]; ring

private theorem d_mono (h : RecData a P Q c) :
    Monotone (fun k => a (k+1)-Q*a k) := by
  apply monotone_nat_of_le_succ
  intro k
  have hh := mul_nonneg (show 0 ≤ P-Q-1 by linarith [h.pq]) (growth h (k+1)).1
  rw [show k+1+1=k+2 by omega, h.step k]
  nlinarith

private theorem domination (h : RecData a P Q c) (k : ℕ) :
    c^2*Q^k+1 ≤ a (k+2)-a k := by
  induction k with
  | zero =>
    simp only [pow_zero, mul_one, h.step 0, h.zero, h.one, mul_zero, sub_zero]
    nlinarith [h.c1, h.cp]
  | succ k ih =>
    have hd := d_mono h (show k ≤ k+2 by omega)
    dsimp only at hd
    have hs : Q*(a (k+2)-a k) ≤ a (k+1+2)-a (k+1) := by
      nlinarith only [hd]
    have hQ := h.q
    have hmul := mul_le_mul_of_nonneg_left ih (show 0 ≤ Q by linarith)
    rw [pow_succ Q k]
    nlinarith

end D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor

namespace D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor

open Matrix

private def M (s t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![s,-t;1,0]

private theorem u_rec (s t : ℤ) (k : ℕ) :
    U s (-t) (k+2) = s*U s (-t) (k+1)-t*U s (-t) k := by
  simp only [U]
  ring

private theorem matrix_shape (s t : ℤ) (k : ℕ) :
    M s t ^ (k+1) =
      !![U s (-t) (k+2), -t*U s (-t) (k+1);
         U s (-t) (k+1), -t*U s (-t) k] := by
  induction k with
  | zero => simp [M, U]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, u_rec]
    all_goals ring

private theorem matrix_entry (s t : ℤ) (k : ℕ) : (M s t ^ k) 1 0 = U s (-t) k := by
  cases k with
  | zero => simp [U]
  | succ k => rw [matrix_shape]; rfl

private theorem stride_rec (s t : ℤ) (r k : ℕ) :
    U s (-t) (r*(k+2)) = (M s t^r).trace*U s (-t) (r*(k+1)) -
      t^r*U s (-t) (r*k) := by
  let A := M s t^r
  have hdet : A.det = t^r := by simp [A, M, Matrix.det_fin_two]
  have hh := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℤ => B 1 0)
    (D5.S0.Observation.MatrixTracePowerSum.pow_add_two A k)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hdet] at hh
  simpa only [A, ← pow_mul, matrix_entry] using hh

private theorem integer_growth (s t : ℤ) (ht : 1 ≤ t) (hst : t+1 ≤ s) :
    ∀ k : ℕ, 0 ≤ U s (-t) k ∧
      1 ≤ U s (-t) (k+1)-t*U s (-t) k ∧
      t^k ≤ U s (-t) (k+1)-U s (-t) k := by
  intro k
  induction k with
  | zero => simp [U]
  | succ k ih =>
    have htp : 0 ≤ t := Int.le_of_lt ht
    have hpow : 0 < t^k := pow_pos (by omega) k
    have hU : 0 ≤ U s (-t) (k+1) := by
      have := mul_nonneg htp ih.1
      nlinarith [ih.2.1]
    have hm := mul_nonneg (show 0 ≤ s-t-1 by omega) hU
    have hp := mul_le_mul_of_nonneg_left ih.2.2 htp
    rw [show k+1+1=k+2 by omega, u_rec, pow_succ]
    refine ⟨hU, ?_, ?_⟩ <;> nlinarith [ih.2.1]

private theorem stride_parameters (s t : ℤ) (hs : 3 ≤ s) (ht : 1 ≤ t) (hst : t+1 ≤ s)
    (r : ℕ) (hr : 1 ≤ r) :
    1 ≤ U s (-t) r ∧ t^r+1 ≤ (M s t^r).trace ∧
      U s (-t) r+2 ≤ (M s t^r).trace := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hj := integer_growth s t ht hst j
  have hj1 := integer_growth s t ht hst (j+1)
  have hp : 0 < t^j := pow_pos (by omega) j
  have hu : 1 ≤ U s (-t) (j+1) := by
    have := mul_nonneg (show 0 ≤ t by omega) hj.1
    nlinarith [hj.2.1]
  rw [matrix_shape, Matrix.trace_fin_two]
  simp only [neg_mul]
  change 1 ≤ U s (-t) (j+1) ∧
    t^(j+1)+1 ≤ U s (-t) (j+2)-t*U s (-t) j ∧
    U s (-t) (j+1)+2 ≤ U s (-t) (j+2)-t*U s (-t) j
  have hm := mul_nonneg (show 0 ≤ s-3 by omega) (show 0 ≤ U s (-t) (j+1) by omega)
  have hrec := u_rec s t j
  exact ⟨hu, by linarith [hj1.2.2, hj.2.1], by nlinarith [hj.2.1]⟩

end D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor

namespace D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor
open Filter Topology

variable {a : ℕ → ℝ} {P Q c : ℝ}

private theorem b_pos (h : RecData a P Q c) (k : ℕ) : 0 < fwdDiff 1 a k := by
  have hg := (growth h k).2
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [h.c1]

private theorem b_mono (h : RecData a P Q c) : Monotone (fwdDiff 1 a) := by
  apply monotone_nat_of_le_succ
  intro k
  linarith [b_step h k, h.c1]

private theorem reciprocal_lower (h : RecData a P Q c) (k : ℕ) :
    1/fwdDiff 1 a k-1/fwdDiff 1 a (k+1) < 1/a (k+1) := by
  have hy := positive h k
  have hb := b_pos h k
  have hb' := b_pos h (k+1)
  have hd := cassini h k
  have he : 1/fwdDiff 1 a k-1/fwdDiff 1 a (k+1)-1/a (k+1) =
      -(a (k+1)^2-a k*a (k+2))/(a (k+1)*fwdDiff 1 a k*fwdDiff 1 a (k+1)) := by
    field_simp [ne_of_gt hy, ne_of_gt hb, ne_of_gt hb']
    dsimp [fwdDiff]
    ring
  rw [hd] at he
  have hn : 0 < c^2*Q^k := mul_pos (sq_pos_of_pos (by linarith [h.c1]))
    (pow_pos (by linarith [h.q]) k)
  have hh := div_neg_of_neg_of_pos (show -(c^2*Q^k) < 0 by linarith) (mul_pos (mul_pos hy hb) hb')
  linarith

private theorem reciprocal_upper (h : RecData a P Q c) (k : ℕ) (hb : 1 < fwdDiff 1 a k) :
    1/a (k+1) ≤ 1/(fwdDiff 1 a k-1)-1/(fwdDiff 1 a (k+1)-1) := by
  have hy := positive h k
  have hb' : 1 < fwdDiff 1 a (k+1) := lt_of_lt_of_le hb (b_mono h (by omega))
  have hd := cassini h k
  have he : 1/(fwdDiff 1 a k-1)-1/(fwdDiff 1 a (k+1)-1)-1/a (k+1) =
      (a (k+2)-a k-1-(a (k+1)^2-a k*a (k+2)))/
        (a (k+1)*(fwdDiff 1 a k-1)*(fwdDiff 1 a (k+1)-1)) := by
    field_simp [ne_of_gt hy, show fwdDiff 1 a k-1 ≠ 0 by linarith, show fwdDiff 1 a (k+1)-1 ≠ 0 by linarith]
    dsimp [fwdDiff]
    ring
  rw [hd] at he
  have hnum : 0 ≤ a (k+2)-a k-1-c^2*Q^k := by linarith [domination h k]
  have hden : 0 < a (k+1)*(fwdDiff 1 a k-1)*(fwdDiff 1 a (k+1)-1) :=
    mul_pos (mul_pos hy (sub_pos.mpr hb)) (sub_pos.mpr hb')
  have hh := div_nonneg hnum hden.le
  linarith

private theorem inv_b_limit (h : RecData a P Q c) (m : ℕ) (e : ℝ) (he : e ≤ 1) :
    Tendsto (fun k : ℕ => (fwdDiff 1 a (m+k)-e)⁻¹) atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  apply tendsto_atTop_mono _ (tendsto_natCast_atTop_atTop (R := ℝ))
  intro k
  have hg := (growth h (m+k)).2
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  push_cast at hg
  nlinarith [h.c1]

private theorem telescoping_has_sum (f : ℕ → ℝ) (hm : Antitone f)
    (hz : Tendsto f atTop (𝓝 0)) : HasSum (fun k => f k-f (k+1)) (f 0) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => sub_nonneg.mpr (hm (by omega))) _).2
  simp_rw [Finset.sum_range_sub']
  simpa using (tendsto_const_nhds.sub hz : Tendsto (fun k => f 0-f k) atTop (𝓝 (f 0-0)))

private theorem upper_has_sum (h : RecData a P Q c) (m : ℕ) (hm : 1 < fwdDiff 1 a m) :
    HasSum (fun k => 1/(fwdDiff 1 a (m+k)-1)-1/(fwdDiff 1 a (m+k+1)-1)) (1/(fwdDiff 1 a m-1)) := by
  apply telescoping_has_sum
  · intro i j hij
    apply one_div_le_one_div_of_le
    · linarith [b_mono h (show m ≤ m+i by omega)]
    · linarith [b_mono h (Nat.add_le_add_left hij m)]
  · simpa only [one_div] using inv_b_limit h m 1 le_rfl

private theorem summable_tail_gt (h : RecData a P Q c) (m : ℕ) (hm : 1 < fwdDiff 1 a m) :
    Summable (fun k => 1/a (m+k+1)) ∧
      (∑' k, 1/a (m+k+1)) ≤ 1/(fwdDiff 1 a m-1) := by
  have hu := upper_has_sum h m hm
  have hle : ∀ k, 1/a (m+k+1) ≤ 1/(fwdDiff 1 a (m+k)-1)-1/(fwdDiff 1 a (m+k+1)-1) := by
    intro k
    exact reciprocal_upper h _ (lt_of_lt_of_le hm (b_mono h (by omega)))
  have hs := Summable.of_nonneg_of_le (fun k => (one_div_pos.mpr (positive h (m+k))).le) hle hu.summable
  exact ⟨hs, hu.tsum_eq ▸ hs.tsum_le_tsum hle hu.summable⟩

private theorem summable_tail (h : RecData a P Q c) (m : ℕ) :
    Summable (fun k => 1/a (m+k+1)) := by
  have hm : 1 < fwdDiff 1 a (m+1) := by
    have hg := (growth h (m+1)).2
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hg
    nlinarith [h.c1]
  have hs := (summable_tail_gt h (m+1) hm).1
  apply (summable_nat_add_iff 1).1
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

private theorem tail_lower (h : RecData a P Q c) (m : ℕ) :
    1/fwdDiff 1 a m < ∑' k, 1/a (m+k+1) := by
  have hl : HasSum (fun k => 1/fwdDiff 1 a (m+k)-1/fwdDiff 1 a (m+k+1)) (1/fwdDiff 1 a m) := by
    apply telescoping_has_sum
    · intro i j hij
      exact one_div_le_one_div_of_le (b_pos h _) (b_mono h (Nat.add_le_add_left hij m))
    · simpa only [one_div, sub_zero] using inv_b_limit h m 0 (by norm_num)
  have hs := summable_tail h m
  have ht := Summable.tsum_lt_tsum (fun k => (reciprocal_lower h (m+k)).le)
    (reciprocal_lower h (m+0)) hl.summable hs
  simpa only [Nat.add_zero, hl.tsum_eq] using ht

end D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor

namespace D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor

variable {a : ℕ → ℝ} {P Q c : ℝ}

private theorem recurrence_floor (h : RecData a P Q c) (m : ℕ) (B : ℤ)
    (hB : (B:ℝ) = fwdDiff 1 a m) :
    ⌊(∑' k : ℕ, 1/a (m+k+1))⁻¹⌋ = B-1 := by
  let S := ∑' k : ℕ, 1/a (m+k+1)
  have hlo : 1/fwdDiff 1 a m < S := tail_lower h m
  have hS : 0 < S := lt_trans (one_div_pos.mpr (b_pos h m)) hlo
  have hb : (0:ℝ) < B := by rw [hB]; exact b_pos h m
  have hB1 : (1:ℤ) ≤ B := by
    have : (0:ℤ) < B := by exact_mod_cast hb
    omega
  have hhi : S⁻¹ < (B:ℝ) := by
    rw [hB]
    simpa only [one_div] using (one_div_lt (b_pos h m) hS).mp hlo
  have hlo' : (B:ℝ)-1 ≤ S⁻¹ := by
    by_cases hB2 : (1:ℤ) < B
    · have hb2 : 0 < fwdDiff 1 a m-1 := by rw [← hB]; exact_mod_cast (show (0:ℤ) < B-1 by omega)
      have hup := (summable_tail_gt h m (by linarith)).2
      have hh := (le_one_div hS hb2).mp hup
      simpa only [one_div, ← hB] using hh
    · have hBe : B = 1 := by omega
      simp only [hBe, Int.cast_one, sub_self]
      exact (inv_pos.mpr hS).le
  apply Int.floor_eq_iff.2
  push_cast
  exact ⟨hlo', by linarith⟩

theorem result : claim := by
  intro s t ht hts hne n r hn hr
  have hs : 3 ≤ s := by
    by_contra h
    have hs2 : s = 2 := by omega
    have ht1 : t = 1 := by omega
    exact hne (by simp [hs2, ht1])
  have hst : t+1 ≤ s := Int.add_one_le_of_lt hts
  let a : ℕ → ℝ := fun k => (U s (-t) (r*k) : ℝ)
  let p : ℤ := (M s t^r).trace
  have hp := stride_parameters s t hs ht hst r hr
  have hd : RecData a (p:ℝ) ((t^r:ℤ):ℝ) (U s (-t) r:ℝ) := by
    constructor
    · simp [a, U]
    · simp [a]
    · intro k
      have hh := stride_rec s t r k
      dsimp [a, p]
      exact_mod_cast hh
    · exact_mod_cast one_le_pow₀ ht
    · exact_mod_cast hp.2.1
    · have : (3:ℤ) ≤ p := by dsimp [p]; omega
      exact_mod_cast this
    · exact_mod_cast hp.1
    · have : U s (-t) r+1 ≤ p := by dsimp [p]; omega
      exact_mod_cast this
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  subst n
  have hsum := summable_tail hd m
  have hf := recurrence_floor hd m (U s (-t) (r*(m+1))-U s (-t) (r*m)) (by
    simp [a, fwdDiff])
  constructor
  · simpa [a, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
  · simpa [a, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf

end D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor
