/- GID: D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The second exterior trace of the serpentine matrix has Spezia’s magnitude. -/

/-
admission_basis: open-problem-resolution (#21795; Proved).
Direct dependency re-pinned in this delivery: D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.alternating_sum (statement_id sha256:7828bcd429333f8019de3f31ccf9d8a958fb0acbea6449a87f7aab7c2e969a26), applied in sum_mixed_raw; the remaining dependencies are Mathlib.
escape_witness: none (the admission uses the external named settlement).
traceExt: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
M: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
a: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
claim: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
w: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
u: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
U: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
V: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
sign_eq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.factorization, D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_mixed_raw.
factorization: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.charpoly_factor.
charpoly_factor: proof_shape: bind-only; escape_witness: none; consumers: coefficient_two, D5.S3.Quantum.Matrix.SpeziaSerpentineHigherExteriorTrace.result.
sum_linear: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_w, D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_w_sq.
sum_quadratic: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_w_sq.
sum_sign: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_sgn, D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.mixed_moment.
sum_mixed_raw: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.mixed_moment.
sum_w: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_u, D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_wu.
sum_w_sq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_wu.
sum_sgn: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.small_product.
mixed_moment: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.small_product.
u_centered: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_u, D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.sum_wu.
sum_u: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.small_product.
sum_wu: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.small_product.
small_product: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.small_det.
small_det: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.coefficient_two.
coefficient_two: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.result.
a_nonneg: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.result.
result: proof_shape: bind-only; escape_witness: none; consumers: external settlement.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21995.
The characteristic-coefficient exterior trace includes the zero-space case k > n.
The source’s one-based row and column numbers are i.val + 1 and j.val + 1.
-/
import D5.S3.Combinatorics.Permanental.SunAbsoluteDifferenceCongruences
import Mathlib.NumberTheory.Bernoulli

set_option autoImplicit false
set_option maxHeartbeats 800000
open Finset BigOperators

namespace D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace

/-- Exterior trace in the characteristic-coefficient convention used by the Spezia family.
For k > n the exterior space is zero-dimensional, so its trace is zero. -/
noncomputable def traceExt {R : Type*} [CommRing R] {n : ℕ}
    (k : ℕ) (A : Matrix (Fin n) (Fin n) R) : R :=
  if k ≤ n then (-1) ^ k * A.charpoly.coeff (n - k) else 0

/-- A317614's M[i,j,n], with source indices i+1,j+1 in {1,...,n}.
All arithmetic in the entries is integer arithmetic. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if Odd (i.val + 1) then
    ((j.val : ℤ) + 1) + (n : ℤ) * (((i.val : ℤ) + 1) - 1)
  else
    (n : ℤ) * ((i.val : ℤ) + 1) - ((j.val : ℤ) + 1) + 1

/-- A322844's defining rational expression, with epsilon = n mod 2. -/
def a (n : ℕ) : ℚ :=
  (1 / 12 : ℚ) * (n : ℚ) ^ 2 *
    (3 * (1 + (n : ℚ) ^ 2) - 2 * (2 + (n : ℚ) ^ 2) * ((n % 2 : ℕ) : ℚ))

/-- A322844, first conjecture line: for every n > 1, a(n) is the absolute value
of the trace of the second exterior power of M(n). -/
def claim : Prop :=
  ∀ n : ℕ, 1 < n → ((|traceExt 2 (M n)| : ℤ) : ℚ) = a n


def w (n i : ℕ) : ℚ := (i : ℚ) + 1 - ((n : ℚ) + 1) / 2

def u (n i : ℕ) : ℚ := (n : ℚ) * ((i : ℚ) + 1) - ((n : ℚ) - 1) / 2

def U (n : ℕ) : Matrix (Fin n) (Fin 2) ℚ :=
  fun i j => if j = 0 then u n i.val else (-1 : ℚ) ^ i.val

def V (n : ℕ) : Matrix (Fin 2) (Fin n) ℚ :=
  fun i j => if i = 0 then 1 else w n j.val

private lemma sign_eq (i : ℕ) : (-1 : ℚ) ^ i = if Odd (i + 1) then 1 else -1 := by
  simpa only [Nat.odd_add_one, Nat.not_odd_iff_even] using
    (neg_one_pow_eq_ite (R := ℚ) (n := i))

private lemma factorization (n : ℕ) : (M n).map (Int.castRingHom ℚ) = U n * V n := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, U, V]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 from one_ne_zero, ite_false, mul_one]
  rw [sign_eq]
  change ((M n i j : ℤ) : ℚ) = _
  unfold M u w
  split_ifs <;> push_cast <;> ring


theorem charpoly_factor (n : ℕ) (hn : 2 ≤ n) :
    ((M n).map (Int.castRingHom ℚ)).charpoly =
      Polynomial.X ^ (n - 2) * (V n * U n).charpoly := by
  rw [factorization]
  simpa using Matrix.charpoly_mul_comm_of_le (U n) (V n) (by simpa using hn)


private lemma sum_linear (n : ℕ) :
    (∑ i ∈ range n, ((i : ℚ) + 1)) = (n : ℚ) * ((n : ℚ) + 1) / 2 := by
  have h := sum_Ico_pow n 1
  rw [Finset.sum_Ico_eq_sum_range] at h
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one] at h
  convert h using 1 <;> simp only [add_comm]
  ring

private lemma sum_quadratic (n : ℕ) :
    (∑ i ∈ range n, ((i : ℚ) + 1) ^ 2) =
      (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) / 6 := by
  have h := sum_Ico_pow n 2
  rw [Finset.sum_Ico_eq_sum_range] at h
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two] at h
  convert h using 1 <;> simp only [add_comm]
  ring

private lemma sum_sign (n : ℕ) : (∑ i ∈ range n, (-1 : ℚ) ^ i) = (n % 2 : ℕ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  change (∑ i : Fin n, (-1 : ℚ) ^ i.val) = (n % 2 : ℕ)
  rw [Fin.sum_neg_one_pow]
  split_ifs with hn
  · simp [Nat.even_iff.mp hn]
  · simp [Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hn)]

private lemma sum_mixed_raw (n : ℕ) :
    (∑ i ∈ range n, ((i : ℚ) + 1) * (-1 : ℚ) ^ i) =
      (-(n : ℚ) + (2 * (n : ℚ) + 1) * (n % 2 : ℕ)) / 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn : n = 2 * (n / 2) := by omega
    let m : ℕ := n / 2
    have h := D5.S3.Combinatorics.Permanental.SunAbsoluteDifferenceCongruences.alternating_sum m 1
    have hq0 : (∑ r ∈ range (2 * m + 1), (-1 : ℚ) ^ r * ((r : ℚ) + 1)) =
        (m : ℚ) + 1 := by
      exact_mod_cast h
    have hq : (∑ r ∈ range (2 * m + 1), ((r : ℚ) + 1) * (-1 : ℚ) ^ r) =
        (m : ℚ) + 1 := by simpa [mul_comm] using hq0
    rw [sum_range_succ] at hq
    norm_num at hq
    have hsum : (∑ r ∈ range (2 * m), ((r : ℚ) + 1) * (-1 : ℚ) ^ r) = -(m : ℚ) := by
      linarith
    calc
      (∑ i ∈ range n, ((i : ℚ) + 1) * (-1 : ℚ) ^ i) =
          ∑ i ∈ range (2 * m), ((i : ℚ) + 1) * (-1 : ℚ) ^ i := by rw [hn, show n / 2 = m by rfl]
      _ = -(m : ℚ) := hsum
      _ = (-(n : ℚ) + (2 * (n : ℚ) + 1) * (n % 2 : ℕ)) / 2 := by
        rw [hn]
        norm_num [Nat.mul_mod, m]
        ring
  · have hn : n = 2 * (n / 2) + 1 := by omega
    let m : ℕ := n / 2
    have h := D5.S3.Combinatorics.Permanental.SunAbsoluteDifferenceCongruences.alternating_sum m 1
    have hq0 : (∑ r ∈ range (2 * m + 1), (-1 : ℚ) ^ r * ((r : ℚ) + 1)) =
        (m : ℚ) + 1 := by
      exact_mod_cast h
    have hq : (∑ r ∈ range (2 * m + 1), ((r : ℚ) + 1) * (-1 : ℚ) ^ r) =
        (m : ℚ) + 1 := by simpa [mul_comm] using hq0
    calc
      (∑ i ∈ range n, ((i : ℚ) + 1) * (-1 : ℚ) ^ i) =
          ∑ i ∈ range (2 * m + 1), ((i : ℚ) + 1) * (-1 : ℚ) ^ i := by rw [hn, show n / 2 = m by rfl]
      _ = (m : ℚ) + 1 := hq
      _ = (-(n : ℚ) + (2 * (n : ℚ) + 1) * (n % 2 : ℕ)) / 2 := by
        rw [hn]
        norm_num [Nat.mul_mod, m]
        ring

private lemma sum_w (n : ℕ) : (∑ i : Fin n, w n i.val) = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  simp only [w, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sum_linear]
  ring

private lemma sum_w_sq (n : ℕ) :
    (∑ i : Fin n, w n i.val ^ 2) = (n : ℚ) * ((n : ℚ) ^ 2 - 1) / 12 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => w n i ^ 2)]
  have ht : ∀ i : ℕ, w n i ^ 2 = ((i : ℚ) + 1) ^ 2 -
      ((n : ℚ) + 1) * ((i : ℚ) + 1) + ((n : ℚ) + 1) ^ 2 / 4 := by
    intro i
    unfold w
    ring
  simp_rw [ht]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_quadratic, sum_linear]
  simp only [sum_const, card_range, nsmul_eq_mul]
  ring

private lemma sum_sgn (n : ℕ) : (∑ i : Fin n, (-1 : ℚ) ^ i.val) = (n % 2 : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range, sum_sign]

private lemma mixed_moment (n : ℕ) :
    (∑ i : Fin n, w n i.val * (-1 : ℚ) ^ i.val) = -(n : ℚ) * (1 - (n % 2 : ℕ)) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => w n i * (-1 : ℚ) ^ i)]
  simp only [w, sub_mul, sum_sub_distrib, ← mul_sum, sum_mixed_raw, sum_sign]
  ring


open Polynomial

private lemma u_centered (n i : ℕ) :
    u n i = (n : ℚ) * w n i + ((n : ℚ) ^ 2 + 1) / 2 := by
  unfold u w
  ring

private lemma sum_u (n : ℕ) :
    (∑ i : Fin n, u n i.val) = (n : ℚ) * ((n : ℚ) ^ 2 + 1) / 2 := by
  simp_rw [u_centered]
  rw [sum_add_distrib, ← mul_sum, sum_w]
  simp
  ring

private lemma sum_wu (n : ℕ) :
    (∑ i : Fin n, w n i.val * u n i.val) =
      (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 12 := by
  have ht : ∀ i : Fin n, w n i.val * u n i.val =
      (n : ℚ) * w n i.val ^ 2 + ((n : ℚ) ^ 2 + 1) / 2 * w n i.val := by
    intro i
    rw [u_centered]
    ring
  simp_rw [ht]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_w_sq, sum_w]
  ring

private lemma small_product (n : ℕ) :
    V n * U n = !![(n : ℚ) * ((n : ℚ) ^ 2 + 1) / 2, ((n % 2 : ℕ) : ℚ);
      (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 12, -(n : ℚ) * (1 - ((n % 2 : ℕ) : ℚ)) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, U, V, sum_u, sum_sgn, sum_wu, mixed_moment]

private lemma small_det (n : ℕ) : (V n * U n).det = -a n := by
  rw [small_product, Matrix.det_fin_two_of]
  unfold a
  ring

private lemma coefficient_two (n : ℕ) (hn : 2 ≤ n) :
    (((M n).charpoly.coeff (n - 2) : ℤ) : ℚ) = -a n := by
  have hc := congrArg (fun p : ℚ[X] => p.coeff (n - 2)) (charpoly_factor n hn)
  rw [Matrix.charpoly_map, Polynomial.coeff_map] at hc
  change (((M n).charpoly.coeff (n - 2) : ℤ) : ℚ) = _ at hc
  rw [Polynomial.coeff_X_pow_mul', ite_eq_left (le_refl _), Nat.sub_self,
    Matrix.charpoly_fin_two] at hc
  have hc' : (((M n).charpoly.coeff (n - 2) : ℤ) : ℚ) = (V n * U n).det := by
    simpa using hc
  exact hc'.trans (small_det n)

private lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  unfold a
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [he]
    norm_num
    positivity
  · rw [ho]
    have hn : 1 ≤ n := by omega
    have hq : (1 : ℚ) ≤ n := Nat.one_le_cast.mpr hn
    have hs : 0 ≤ (n : ℚ) ^ 2 - 1 := sub_nonneg.mpr (one_le_pow₀ hq)
    have ha : (1 / 12 : ℚ) * (n : ℚ) ^ 2 *
        (3 * (1 + (n : ℚ) ^ 2) - 2 * (2 + (n : ℚ) ^ 2) * (1 : ℕ)) =
        (1 / 12 : ℚ) * (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) := by ring
    rw [ha]
    positivity

theorem result : claim := by
  intro n hn
  have hc := coefficient_two n (by omega)
  have ht : (((traceExt 2 (M n)) : ℤ) : ℚ) = -a n := by
    simpa [traceExt, show 2 ≤ n by omega] using hc
  rw [Int.cast_abs, ht, abs_neg, abs_of_nonneg (a_nonneg n)]

end D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace
