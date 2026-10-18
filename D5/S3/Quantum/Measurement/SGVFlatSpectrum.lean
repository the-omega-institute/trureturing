/- GID: D5/S3/Quantum/Measurement/SGVFlatSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/SGVFlatSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Explicit positive probabilities solve the flat-spectrum system for every copy number. -/

/-
Public theorem: result
proof_shape: content
admission_basis: open-problem-resolution (#17082; Proved)
Direct frozen dependencies: D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084; D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul sha256:87a83e596e2cb46ff2e643c1b4a2d7ea20fce9f162d1f39168edfc4f013b57d6 (result; each declaration is listed below).
escape_witness: none (open-problem-resolution; no escape witness is asserted).
The Racah formula is inline in S. Its existing coefficient owner is
DampedSpinKernelPositivityRefutation.CG, in an I module; this G module
uses the literal expression without a duplicate coefficient declaration.
W_sum and Q_sum prove summation invariants by induction with telescoping certificates.
Their consumers inherit content under inlining; the certificate checks are bind-only.
Uniqueness and polynomial connection identities are not asserted here.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17668

Declaration | proof_shape | direct frozen dependencies | consumers (escape_witness: none)
S | bind-only | none | S_factorization, S_sq_closed, S_sq_rational, claim, explicitQ_kernel_term, result, system_equations
claim | bind-only | none | result
prefactor_formula | bind-only | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084 | S_sq_closed, S_sq_rational, equal_spin_coefficient
prefactor | bind-only | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084 | S_factorization, S_sq_closed, S_sq_rational, equal_spin_coefficient, prefactor_formula
rationalSum | bind-only | none | S_factorization, S_sq_closed, S_sq_rational, rationalSum_binomial
fq_cast | bind-only | none | S_factorization
fz_pos | bind-only | none | S_sq_rational, equal_spin_coefficient
equal_spin_coefficient | bind-only | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084 | S_factorization
S_factorization | bind-only | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084 | S_sq_rational
S_sq_rational | bind-only | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084 | S_sq_closed
binomialKernel | bind-only | none | S_sq_closed, binomial_kernel_closed, kernel_series_coeff, rationalSum_binomial
geo_pow_coeff | bind-only | none | binomial_kernel_closed, kernel_series_coeff
altGeo_add_geo | bind-only | none | kernel_series
altGeo_mul_geo | bind-only | D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul sha256:87a83e596e2cb46ff2e643c1b4a2d7ea20fce9f162d1f39168edfc4f013b57d6 | kernel_series
kernel_series | bind-only | D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul sha256:87a83e596e2cb46ff2e643c1b4a2d7ea20fce9f162d1f39168edfc4f013b57d6 | binomial_kernel_closed
kernel_series_coeff | bind-only | none | binomial_kernel_closed
binomial_kernel_closed | bind-only | D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul sha256:87a83e596e2cb46ff2e643c1b4a2d7ea20fce9f162d1f39168edfc4f013b57d6 | S_sq_closed
sum_shear | bind-only | none | rationalSum_binomial
factorial_binomial_term | bind-only | none | rationalSum_binomial
rationalSum_binomial | bind-only | none | S_sq_closed
fac_ne | bind-only | none | Q_eq_binomial, W_sum, probability_kernel_term
fac_succ | bind-only | none | Q_step_k, Q_step_n, W_step_m, W_step_r
W | bind-only | none | W_step_m, W_step_r, W_sum, W_telescoper, Wcert, Wcert_last, Wcert_zero, explicitQ_kernel_term, probability_kernel_term, system_equations
W_step_m | bind-only | none | W_telescoper
W_step_r | bind-only | none | W_telescoper
H | bind-only | none | W_telescoper, Wcert, Wcert_last, Wcert_zero
Wcert | bind-only | none | W_sum, W_telescoper, Wcert_last, Wcert_zero
W_telescoper | bind-only | none | W_sum
Wcert_zero | bind-only | none | W_sum
Wcert_last | bind-only | none | W_sum
W_sum | content | none | system_equations
choose_rat | bind-only | none | Q_eq_binomial, S_sq_closed
S_sq_closed | bind-only | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084; D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul sha256:87a83e596e2cb46ff2e643c1b4a2d7ea20fce9f162d1f39168edfc4f013b57d6 | explicitQ_kernel_term
explicitQ | bind-only | none | explicitQ_eq_Q, explicitQ_kernel_term, explicitQ_nonneg, explicitQ_pos, explicitQ_sum, result, system_equations
explicitQ_pos | bind-only | none | explicitQ_nonneg
explicitQ_nonneg | bind-only | none | result
Q | bind-only | none | Q_eq_binomial, Q_step_k, Q_step_n, Q_sum, Q_telescoper, Qcert, Qcert_last, Qcert_zero, explicitQ_eq_Q, explicitQ_kernel_term, explicitQ_sum, probability_kernel_term
Q_step_n | bind-only | none | Q_telescoper
Q_step_k | bind-only | none | Q_telescoper
QH | bind-only | none | Q_telescoper, Qcert, Qcert_last, Qcert_zero
Qcert | bind-only | none | Q_sum, Q_telescoper, Qcert_last, Qcert_zero
Q_telescoper | bind-only | none | Q_sum
Qcert_zero | bind-only | none | Q_sum
Qcert_last | bind-only | none | Q_sum
Q_sum | content | none | explicitQ_sum
Q_eq_binomial | bind-only | none | explicitQ_eq_Q
explicitQ_eq_Q | bind-only | none | explicitQ_kernel_term, explicitQ_sum
explicitQ_sum | content | none | result
probability_kernel_term | bind-only | none | explicitQ_kernel_term
explicitQ_kernel_term | bind-only | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084; D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul sha256:87a83e596e2cb46ff2e643c1b4a2d7ea20fce9f162d1f39168edfc4f013b57d6 | system_equations
system_equations | content | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084; D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul sha256:87a83e596e2cb46ff2e643c1b4a2d7ea20fce9f162d1f39168edfc4f013b57d6 | result
result | content | D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq sha256:5f3a9ee4845e0af930ca84d8f7d5109a14f121e680c054a08e51be139e312084; D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul sha256:87a83e596e2cb46ff2e643c1b4a2d7ea20fce9f162d1f39168edfc4f013b57d6 | settling result
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
import D5.S3.Zeros.Convolution.AlternatingFactorialSum
noncomputable section
open scoped BigOperators
open Finset PowerSeries
namespace D5.S3.Quantum.Measurement.SGVFlatSpectrum
/-- `S_{j,J} = Σ_{m=-j}^{j} C^{J0}_{jm, j -m}`, with `tj = 2j`; `m = j - i` for `i = 0, …, 2j`. -/
def S (tj J : ℕ) : ℝ :=
  let fz (x : ℤ) : ℝ := (Nat.factorial x.toNat : ℝ)
  let clebschGordan (a b c : ℕ) (x y z : ℤ) : ℝ :=
    if z = x + y ∧ (c : ℤ) ≤ a + b ∧ (a : ℤ) ≤ b + c ∧ (b : ℤ) ≤ a + c ∧ Even ((a : ℤ) + b + c) ∧
        |x| ≤ a ∧ |y| ≤ b ∧ |z| ≤ c ∧ Even ((a : ℤ) + x) ∧ Even ((b : ℤ) + y) ∧ Even ((c : ℤ) + z) then
      Real.sqrt ((c + 1) * fz ((c + a - b) / 2) * fz ((c - a + b) / 2) * fz ((a + b - c) / 2) /
          fz ((a + b + c) / 2 + 1)) *
        Real.sqrt (fz ((c + z) / 2) * fz ((c - z) / 2) * fz ((a - x) / 2) * fz ((a + x) / 2) *
          fz ((b - y) / 2) * fz ((b + y) / 2)) *
        ∑ k ∈ Finset.range (a + b + c + 1),
          if 0 ≤ ((a : ℤ) + b - c) / 2 - k ∧ 0 ≤ (a - x) / 2 - k ∧ 0 ≤ (b + y) / 2 - k ∧
              0 ≤ ((c : ℤ) - b + x) / 2 + k ∧ 0 ≤ ((c : ℤ) - a - y) / 2 + k then
            (-1 : ℝ) ^ k / (fz k * fz (((a : ℤ) + b - c) / 2 - k) * fz ((a - x) / 2 - k) *
              fz ((b + y) / 2 - k) * fz (((c : ℤ) - b + x) / 2 + k) * fz (((c : ℤ) - a - y) / 2 + k))
          else 0
    else 0
  ∑ i ∈ Finset.range (tj + 1),
    clebschGordan tj tj (2 * J) ((tj : ℤ) - 2 * i) (2 * (i : ℤ) - tj) 0

/-- Conjecture 4.6 in the form of Eq. (183): probabilities `q_j`, indexed by `k` with `j = n/2 - k`, solve the system
for every `J ∈ {(n mod 2), …, n - 2, n}`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ q : ℕ → ℝ,
    (∀ k ≤ n / 2, 0 ≤ q k) ∧ (∑ k ∈ Finset.range (n / 2 + 1), q k) = 1 ∧
    ∀ J ≤ n, J % 2 = n % 2 →
      (2 * (J : ℝ) + 1) / (Nat.choose (n + 2) 2 : ℝ) =
        ∑ k ∈ Finset.range (n / 2 + 1),
          if J ≤ n - 2 * k then q k / ((n - 2 * k : ℕ) + 1 : ℝ) * (S (n - 2 * k) J) ^ 2 else 0

private def prefactor (t J : ℕ) : ℚ :=
  (2 * J + 1) * D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah.deltaSq t t (2 * J)
private lemma prefactor_formula (t J : ℕ) : prefactor t J =
    (2 * J + 1) * (Nat.factorial ((J : ℤ).toNat) : ℚ) * (Nat.factorial ((J : ℤ).toNat) : ℚ) * (Nat.factorial (((t : ℤ) - J : ℤ).toNat) : ℚ) / (Nat.factorial (((t : ℤ) + J + 1 : ℤ).toNat) : ℚ) := by
  symm
  have h0 : (((t : ℤ) - J).toNat) = t - J := by
    exact (Int.toNat_sub t J)
  have h1 : (((t : ℤ) + J + 1).toNat) = t + J + 1 := by
    exact (Eq.symm (Nat.add_succ (t + J) 0))
  have h2 : (t + t - 2 * J) / 2 = t - J := by omega
  have h3 : (t + 2 * J - t) / 2 = J := by omega
  have h4 : (t + t + 2 * J) / 2 + 1 = t + J + 1 := by omega
  simp only [prefactor, D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah.deltaSq, Int.toNat_natCast, h0, h1, h2, h3, h4]
  ring
/-- The rational part after extracting the common square root. -/
private def rationalSum (t J : ℕ) : ℚ :=
  ∑ i ∈ range (t + 1), (Nat.factorial ((J : ℤ).toNat) : ℚ) * (Nat.factorial ((i : ℤ).toNat) : ℚ) * (Nat.factorial (((t : ℤ) - i : ℤ).toNat) : ℚ) *
    ∑ k ∈ range (t + t + 2 * J + 1),
      if 0 ≤ (t : ℤ) - J - k ∧ 0 ≤ (i : ℤ) - k ∧
        0 ≤ (J : ℤ) - i + k then
      (-1 : ℚ)^k / ((Nat.factorial ((k : ℤ).toNat) : ℚ) * (Nat.factorial (((t : ℤ) - J - k : ℤ).toNat) : ℚ) * (Nat.factorial (((i : ℤ) - k : ℤ).toNat) : ℚ) *
        (Nat.factorial (((i : ℤ) - k : ℤ).toNat) : ℚ) * (Nat.factorial (((J : ℤ) - i + k : ℤ).toNat) : ℚ) * (Nat.factorial (((J : ℤ) - i + k : ℤ).toNat) : ℚ))
      else 0
private lemma fq_cast (x : ℤ) : ((Nat.factorial ((x : ℤ).toNat) : ℚ) : ℝ) = (Nat.factorial ((x : ℤ).toNat) : ℝ) := by
  exact (Rat.cast_natCast x.toNat.factorial)
private lemma fz_pos (x : ℤ) : 0 < (Nat.factorial ((x : ℤ).toNat) : ℝ) := by
  exact (Nat.cast_pos.mpr (Nat.factorial_pos x.toNat))
private lemma equal_spin_coefficient (t J i : ℕ) (hJ : J ≤ t) (hi : i ≤ t) :
    (let clebschGordan (a b c : ℕ) (x y z : ℤ) : ℝ :=
      if z = x + y ∧ (c : ℤ) ≤ a + b ∧ (a : ℤ) ≤ b + c ∧ (b : ℤ) ≤ a + c ∧ Even ((a : ℤ) + b + c) ∧
          |x| ≤ a ∧ |y| ≤ b ∧ |z| ≤ c ∧ Even ((a : ℤ) + x) ∧ Even ((b : ℤ) + y) ∧ Even ((c : ℤ) + z) then
        Real.sqrt ((c + 1) * (Nat.factorial (((c + a - b) / 2 : ℤ).toNat) : ℝ) * (Nat.factorial (((c - a + b) / 2 : ℤ).toNat) : ℝ) * (Nat.factorial (((a + b - c) / 2 : ℤ).toNat) : ℝ) /
            (Nat.factorial (((a + b + c) / 2 + 1 : ℤ).toNat) : ℝ)) *
          Real.sqrt ((Nat.factorial (((c + z) / 2 : ℤ).toNat) : ℝ) * (Nat.factorial (((c - z) / 2 : ℤ).toNat) : ℝ) * (Nat.factorial (((a - x) / 2 : ℤ).toNat) : ℝ) * (Nat.factorial (((a + x) / 2 : ℤ).toNat) : ℝ) *
            (Nat.factorial (((b - y) / 2 : ℤ).toNat) : ℝ) * (Nat.factorial (((b + y) / 2 : ℤ).toNat) : ℝ)) *
          ∑ k ∈ Finset.range (a + b + c + 1),
            if 0 ≤ ((a : ℤ) + b - c) / 2 - k ∧ 0 ≤ (a - x) / 2 - k ∧ 0 ≤ (b + y) / 2 - k ∧
                0 ≤ ((c : ℤ) - b + x) / 2 + k ∧ 0 ≤ ((c : ℤ) - a - y) / 2 + k then
              (-1 : ℝ) ^ k / ((Nat.factorial ((k : ℤ).toNat) : ℝ) * (Nat.factorial ((((a : ℤ) + b - c) / 2 - k : ℤ).toNat) : ℝ) * (Nat.factorial (((a - x) / 2 - k : ℤ).toNat) : ℝ) *
                (Nat.factorial (((b + y) / 2 - k : ℤ).toNat) : ℝ) * (Nat.factorial ((((c : ℤ) - b + x) / 2 + k : ℤ).toNat) : ℝ) * (Nat.factorial ((((c : ℤ) - a - y) / 2 + k : ℤ).toNat) : ℝ))
            else 0
      else 0;
      clebschGordan t t (2 * J) ((t : ℤ) - 2 * i) (2 * (i : ℤ) - t) 0) =
    Real.sqrt (prefactor t J : ℝ) *
      ((Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial ((i : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - i : ℤ).toNat) : ℝ)) *
      ∑ k ∈ range (t + t + 2 * J + 1),
        if 0 ≤ (t : ℤ) - J - k ∧ 0 ≤ (i : ℤ) - k ∧
          0 ≤ (J : ℤ) - i + k then
        (-1 : ℝ)^k / ((Nat.factorial ((k : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - J - k : ℤ).toNat) : ℝ) * (Nat.factorial (((i : ℤ) - k : ℤ).toNat) : ℝ) *
          (Nat.factorial (((i : ℤ) - k : ℤ).toNat) : ℝ) * (Nat.factorial (((J : ℤ) - i + k : ℤ).toNat) : ℝ) * (Nat.factorial (((J : ℤ) - i + k : ℤ).toNat) : ℝ))
        else 0 := by
  have hvalid :
      (0 : ℤ) = ((t : ℤ) - 2 * i) + (2 * (i : ℤ) - t) ∧
      ((2 * J : ℕ) : ℤ) ≤ (t : ℤ) + t ∧
      (t : ℤ) ≤ t + (2 * J : ℕ) ∧ (t : ℤ) ≤ t + (2 * J : ℕ) ∧
      Even ((t : ℤ) + t + (2 * J : ℕ)) ∧
      |(t : ℤ) - 2 * i| ≤ t ∧ |2 * (i : ℤ) - t| ≤ t ∧
      |(0 : ℤ)| ≤ (2 * J : ℕ) ∧ Even ((t : ℤ) + ((t : ℤ) - 2 * i)) ∧
      Even ((t : ℤ) + (2 * (i : ℤ) - t)) ∧ Even (((2 * J : ℕ) : ℤ) + 0) := by
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩
    · exact ⟨(t : ℤ) + J, by omega⟩
    · rw [abs_le]; constructor <;> omega
    · rw [abs_le]; constructor <;> omega
    · exact ⟨(t : ℤ) - i, by omega⟩
    · exact ⟨(i : ℤ), by omega⟩
    · exact ⟨(J : ℤ), by omega⟩
  dsimp only
  rw [if_pos hvalid]
  have h1 : (((2 * J : ℕ) : ℤ) + t - t) / 2 = J := by omega
  have h2 : (((2 * J : ℕ) : ℤ) - t + t) / 2 = J := by omega
  have h3 : ((t : ℤ) + t - (2 * J : ℕ)) / 2 = (t : ℤ) - J := by omega
  have h4 : ((t : ℤ) + t + (2 * J : ℕ)) / 2 + 1 = (t : ℤ) + J + 1 := by omega
  have h5 : (((2 * J : ℕ) : ℤ) + 0) / 2 = J := by omega
  have h6 : (((2 * J : ℕ) : ℤ) - 0) / 2 = J := by
    exact (Eq.symm (Int.neg_inj.mp (congrArg Neg.neg (id (Eq.symm h5)))))
  have h7 : ((t : ℤ) - ((t : ℤ) - 2 * i)) / 2 = i := by omega
  have h8 : ((t : ℤ) + ((t : ℤ) - 2 * i)) / 2 = (t : ℤ) - i := by omega
  have h9 : ((t : ℤ) - (2 * (i : ℤ) - t)) / 2 = (t : ℤ) - i := by omega
  have h10 : ((t : ℤ) + (2 * (i : ℤ) - t)) / 2 = i := by omega
  have h11 : (((2 * J : ℕ) : ℤ) - t + ((t : ℤ) - 2 * i)) / 2 = (J : ℤ) - i := by omega
  have h12 : (((2 * J : ℕ) : ℤ) - t - (2 * (i : ℤ) - t)) / 2 = (J : ℤ) - i := by omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  have hp : Real.sqrt
      ((Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial ((i : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - i : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - i : ℤ).toNat) : ℝ) * (Nat.factorial ((i : ℤ).toNat) : ℝ)) =
      (Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial ((i : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - i : ℤ).toNat) : ℝ) := by
    rw [show (Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial ((i : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - i : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - i : ℤ).toNat) : ℝ) * (Nat.factorial ((i : ℤ).toNat) : ℝ) =
      ((Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial ((i : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - i : ℤ).toNat) : ℝ))^2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg (fz_pos _).le (fz_pos _).le) (fz_pos _).le)
  rw [hp]
  have hpref : ((2 * J : ℕ) + 1 : ℝ) * (Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial ((J : ℤ).toNat) : ℝ) * (Nat.factorial (((t : ℤ) - J : ℤ).toNat) : ℝ) /
      (Nat.factorial (((t : ℤ) + J + 1 : ℤ).toNat) : ℝ) = (prefactor t J : ℝ) := by
    simp [prefactor_formula]
  rw [hpref]
  congr 2
  funext k
  simp only [and_self, and_self_left]
private lemma S_factorization (t J : ℕ) (hJ : J ≤ t) :
    S t J = Real.sqrt (prefactor t J : ℝ) * (rationalSum t J : ℝ) := by
  rw [S, rationalSum]
  simp only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_one, Rat.cast_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have he := equal_spin_coefficient t J i hJ (by simpa using mem_range.mp hi)
  dsimp only at he
  rw [he]
  simp only [fq_cast]
  ring
private lemma S_sq_rational (t J : ℕ) (hJ : J ≤ t) :
    S t J ^ 2 = ((prefactor t J * rationalSum t J ^ 2 : ℚ) : ℝ) := by
  rw [S_factorization t J hJ, mul_pow, Real.sq_sqrt]
  · push_cast; rfl
  · rw [prefactor_formula]; push_cast
    have := by
      exact (fz_pos ↑J)
    have := by
      exact (fz_pos (↑t - ↑J))
    have := by
      exact (fz_pos (↑t + ↑J + 1))
    positivity
private def binomialKernel (d J : ℕ) : ℚ :=
  ∑ l ∈ range (J + 1), (Nat.choose J l : ℚ) *
    ∑ k ∈ range (d + 1), (-1 : ℚ)^k * Nat.choose (l + k) l *
      Nat.choose (J - l + (d - k)) (J - l)
private lemma geo_pow_coeff (r n : ℕ) :
    ((PowerSeries.mk (1 : ℕ → ℚ)) ^ (r + 1)).coeff n = (Nat.choose (r + n) r : ℚ) := by
  rw [PowerSeries.mk_one_pow_eq_mk_choose_add ℚ r, coeff_mk]
private lemma altGeo_add_geo : (PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) + (PowerSeries.mk (1 : ℕ → ℚ)) = 2 * ((PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) * (PowerSeries.mk (1 : ℕ → ℚ))) := by
  have hb : (PowerSeries.mk (1 : ℕ → ℚ)) * (1 - X) = (1 : PowerSeries ℚ) := by
    exact (mk_one_mul_one_sub_eq_one ℚ)
  have ha : (PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) * (1 + X) = (1 : PowerSeries ℚ) := by
    have h := by
      exact (RingHom.congr_arg (rescale (-1)) hb)
    simpa [map_mul, map_sub, map_one, PowerSeries.rescale_neg_one_X] using h
  calc
    (PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) + (PowerSeries.mk (1 : ℕ → ℚ)) = (PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) * ((PowerSeries.mk (1 : ℕ → ℚ)) * (1 - X)) + ((PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) * (1 + X)) * (PowerSeries.mk (1 : ℕ → ℚ)) := by rw [hb, ha]; ring
    _ = 2 * ((PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) * (PowerSeries.mk (1 : ℕ → ℚ))) := by ring
private lemma altGeo_mul_geo : (PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) * (PowerSeries.mk (1 : ℕ → ℚ)) = PowerSeries.expand 2 (by decide) (PowerSeries.mk (1 : ℕ → ℚ)) := by
  simpa only [invOneSubPow_val_succ_eq_mk_add_choose, Nat.zero_add, Nat.choose_zero_right,
    Nat.cast_one, Pi.one_def] using
    D5.S3.Zeros.Convolution.AlternatingFactorialSum.opposite_inv_series_mul (R := ℚ) 1
private lemma kernel_series (J : ℕ) :
    (∑ l ∈ range (J + 1), (Nat.choose J l : PowerSeries ℚ) *
      (PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) ^ (l + 1) * (PowerSeries.mk (1 : ℕ → ℚ)) ^ (J - l + 1)) =
    (2 : PowerSeries ℚ)^J * PowerSeries.expand 2 (by decide) ((PowerSeries.mk (1 : ℕ → ℚ)) ^ (J + 1)) := by
  calc
    _ = ((PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) * (PowerSeries.mk (1 : ℕ → ℚ))) * ((PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) + (PowerSeries.mk (1 : ℕ → ℚ)))^J := by
      rw [add_pow, mul_sum]
      apply sum_congr rfl
      intro l hl
      rw [pow_succ, pow_succ]
      ring
    _ = (2 : PowerSeries ℚ)^J * ((PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) * (PowerSeries.mk (1 : ℕ → ℚ)))^(J+1) := by rw [altGeo_add_geo, mul_pow, pow_succ]; ring
    _ = _ := by rw [altGeo_mul_geo, map_pow]
private lemma kernel_series_coeff (d J : ℕ) :
    (∑ l ∈ range (J + 1), (Nat.choose J l : PowerSeries ℚ) *
      (PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) ^ (l + 1) * (PowerSeries.mk (1 : ℕ → ℚ)) ^ (J - l + 1)).coeff d = binomialKernel d J := by
  rw [map_sum]
  unfold binomialKernel
  apply sum_congr rfl
  intro l hl
  rw [mul_assoc]
  rw [show (Nat.choose J l : PowerSeries ℚ) = PowerSeries.C (Nat.choose J l : ℚ) by simp]
  rw [PowerSeries.coeff_C_mul]
  congr 1
  rw [PowerSeries.coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => ((PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) ^ (l+1)).coeff a * ((PowerSeries.mk (1 : ℕ → ℚ)) ^ (J-l+1)).coeff b)]
  apply sum_congr rfl
  intro k hk
  rw [show (PowerSeries.rescale (-1 : ℚ) (PowerSeries.mk (1 : ℕ → ℚ))) ^ (l + 1) = PowerSeries.rescale (-1 : ℚ) ((PowerSeries.mk (1 : ℕ → ℚ)) ^ (l + 1)) by rw [map_pow]]
  rw [PowerSeries.coeff_rescale, geo_pow_coeff, geo_pow_coeff]
private lemma binomial_kernel_closed (d J : ℕ) :
    binomialKernel d J =
      if 2 ∣ d then (2 : ℚ)^J * Nat.choose (J + d / 2) J else 0 := by
  rw [← kernel_series_coeff, kernel_series]
  rw [show (2 : PowerSeries ℚ)^J = PowerSeries.C ((2 : ℚ)^J) by norm_cast]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
  split_ifs with h
  · rw [geo_pow_coeff]
  · ring
private lemma sum_shear (J d B : ℕ) (hB : d < B) (f : ℕ → ℕ → ℚ) :
    (∑ i ∈ range (J+d+1), ∑ k ∈ range B,
      if k ≤ d ∧ k ≤ i ∧ i ≤ J+k then f k (i-k) else 0) =
    ∑ k ∈ range (d+1), ∑ l ∈ range (J+1), f k l := by
  rw [← Finset.sum_product', ← Finset.sum_product']
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun p hp => (p.2, p.1-p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_product, mem_range] at hp
    simp only [mem_product, mem_range]
    omega
  · intro p hp q hq he
    simp only [mem_filter, mem_product, mem_range] at hp hq
    have he1 := by
      exact (Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (congrArg Prod.fst he)) J))
    have he2 := by
      exact (Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (congrArg Prod.snd he)) J))
    dsimp only at he1 he2
    apply Prod.ext <;> omega
  · intro q hq
    simp only [mem_product, mem_range] at hq
    refine ⟨(q.1+q.2, q.1), ?_, ?_⟩
    · simp only [mem_filter, mem_product, mem_range]
      omega
    · simp
  · intro p hp
    rfl
private lemma factorial_binomial_term (J d k l : ℕ) (hl : l ≤ J) :
    (J.factorial : ℚ) * (k+l).factorial * (J-l+(d-k)).factorial *
      ((-1 : ℚ)^k / ((k.factorial : ℚ) * (d-k).factorial * l.factorial *
        l.factorial * (J-l).factorial * (J-l).factorial)) =
    (Nat.choose J l : ℚ) * ((-1 : ℚ)^k * Nat.choose (l+k) l *
      Nat.choose (J-l+(d-k)) (J-l)) := by
  rw [Nat.cast_choose ℚ hl, Nat.cast_add_choose, Nat.cast_add_choose]
  have h0 : (k.factorial : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1 : ((d-k).factorial : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (l.factorial : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((J-l).factorial : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [show k+l = l+k by omega]
  field_simp
private lemma rationalSum_binomial (J d : ℕ) : rationalSum (J+d) J = binomialKernel d J := by
  let B := (J+d)+(J+d)+2*J+1
  let f : ℕ → ℕ → ℚ := fun k l => (Nat.choose J l : ℚ) *
    ((-1 : ℚ)^k * Nat.choose (l+k) l * Nat.choose (J-l+(d-k)) (J-l))
  have he : rationalSum (J+d) J =
      ∑ i ∈ range (J+d+1), ∑ k ∈ range B,
        if k ≤ d ∧ k ≤ i ∧ i ≤ J+k then f k (i-k) else 0 := by
    unfold rationalSum
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro k hk
    have hi' : i ≤ J+d := by
      exact (mem_range_succ_iff.mp hi)
    have hcond : (0 ≤ ((J+d : ℕ) : ℤ) - J - k ∧ 0 ≤ (i : ℤ) - k ∧
        0 ≤ (J : ℤ) - i + k) ↔ (k ≤ d ∧ k ≤ i ∧ i ≤ J+k) := by omega
    simp only [hcond]
    split_ifs with h
    · have hl : i-k ≤ J := by omega
      have hki : k+(i-k) = i := by omega
      have hti : J-(i-k)+(d-k) = J+d-i := by omega
      have hcast0 : ((J+d : ℕ) : ℤ) - i = ((J+d-i : ℕ) : ℤ) := by
        exact (Eq.symm (Int.ofNat_sub hi'))
      have hcast1 : ((J+d : ℕ) : ℤ) - J - k = ((d-k : ℕ) : ℤ) := by omega
      have hcast2 : (i : ℤ) - k = ((i-k : ℕ) : ℤ) := by
        exact (Int.sub_eq_iff_eq_add'.mpr (congrArg Nat.cast (id (Eq.symm hki))))
      have hcast3 : (J : ℤ) - i + k = ((J-(i-k) : ℕ) : ℤ) := by omega
      rw [hcast0, hcast1, hcast2, hcast3]
      simp only [Int.toNat_natCast]
      have hh := factorial_binomial_term J d k (i-k) hl
      rw [hki, hti] at hh
      simpa only [f, Nat.sub_add_cancel h.2.1, Nat.add_comm (i-k) k, hti] using hh
    · simp
  rw [he, sum_shear J d B (by dsimp [B]; omega) f]
  rw [sum_comm]
  unfold binomialKernel f
  apply sum_congr rfl
  intro l hl
  rw [mul_sum]
private lemma fac_ne (n : ℕ) : (Nat.factorial (n) : ℚ) ≠ 0 := by
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
private lemma fac_succ (n : ℕ) : (Nat.factorial (n+1) : ℚ) = (n+1) * (Nat.factorial (n) : ℚ) := by
  simp [Nat.factorial_succ]
private def W (J m r : ℕ) : ℚ :=
  (J+2*r+1) * (Nat.factorial (2*J+2*m+2*r+1) : ℚ) * (Nat.factorial (2*(m-r)) : ℚ) * (Nat.factorial (J+r) : ℚ)^2 * (Nat.factorial (2*r) : ℚ) /
  ((Nat.factorial (J+m+r) : ℚ) * (Nat.factorial (J+m+r+1) : ℚ) * (Nat.factorial (m-r) : ℚ)^2 * (Nat.factorial (r) : ℚ)^2 * (Nat.factorial (2*J+2*r+1) : ℚ) * 16^m)
private lemma W_step_m (J m r : ℕ) (hr : r ≤ m) :
    W J (m+1) r * (4*((m-r : ℕ)+1)*(J+m+r+2)) =
      W J m r * ((2*(m-r : ℕ)+1)*(2*J+2*m+2*r+3)) := by
  unfold W
  rw [show 2*J+2*(m+1)+2*r+1 = (2*J+2*m+2*r+1)+2 by omega,
    show m+1-r = (m-r)+1 by omega,
    show 2*((m-r)+1) = 2*(m-r)+2 by omega,
    show J+(m+1)+r = (J+m+r)+1 by omega]
  simp only [fac_succ, pow_succ]
  have hidx : (2*J+2*m+2*r+1 : ℚ) = 2*(J+m+r)+1 := by ring
  have hmr : (m : ℚ) = (m-r : ℕ)+r := by exact_mod_cast (show m = m-r+r by omega)
  push_cast
  field_simp [fac_ne]
  ring
private lemma W_step_r (J m r : ℕ) (hr : r ≤ m) :
    W J (m+1) (r+1) *
      ((r+1)*(J+2*r+1)*(2*J+2*r+3)*(2*(m-r : ℕ)+1)*(J+m+r+3)) =
    W J (m+1) r *
      (((m-r : ℕ)+1)*(2*r+1)*(J+r+1)*(J+2*r+3)*(2*J+2*m+2*r+5)) := by
  unfold W
  rw [show 2*J+2*(m+1)+2*(r+1)+1 = (2*J+2*m+2*r+3)+2 by omega,
      show 2*J+2*(m+1)+2*r+1 = 2*J+2*m+2*r+3 by omega,
      show m+1-(r+1) = m-r by omega,
      show m+1-r = (m-r)+1 by omega,
      show 2*((m-r)+1) = 2*(m-r)+2 by omega,
      show J+(r+1) = J+r+1 by omega,
      show 2*(r+1) = 2*r+2 by omega,
      show J+(m+1)+(r+1) = (J+m+r+1)+1 by omega,
      show J+(m+1)+r = J+m+r+1 by omega,
      show 2*J+(2*r+2)+1 = (2*J+2*r+1)+2 by omega]
  simp only [fac_succ]
  push_cast
  field_simp [fac_ne]
  ring
private def H (J m r : ℕ) : ℚ :=
  -(r : ℚ)*(2*J+4*m+5)*(2*J+2*r+1)*(J+m+r+2) /
    ((m+1)*(J+2*r+1)*(2*J+2*m+3)*(2*J+2*m+2*r+3))
private def Wcert (J m r : ℕ) : ℚ := H J m r * W J (m+1) r
private lemma W_telescoper (J m r : ℕ) (hr : r ≤ m) :
    W J (m+1) r - W J m r = Wcert J m (r+1) - Wcert J m r := by
  have hm := by
    exact (W_step_m J m r hr)
  have hs := by
    exact (W_step_r J m r hr)
  have hn : ((2*(m-r : ℕ)+1)*(2*J+2*m+2*r+3) : ℚ) ≠ 0 := by positivity
  have hd : ((r+1)*(J+2*r+1)*(2*J+2*r+3)*(2*(m-r : ℕ)+1)*(J+m+r+3) : ℚ) ≠ 0 := by positivity
  have hm' : W J m r = W J (m+1) r * (4*((m-r : ℕ)+1)*(J+m+r+2)) /
      ((2*(m-r : ℕ)+1)*(2*J+2*m+2*r+3)) := by
        exact (eq_div_of_mul_eq hn (id (Eq.symm hm)))
  have hs' : W J (m+1) (r+1) = W J (m+1) r *
      (((m-r : ℕ)+1)*(2*r+1)*(J+r+1)*(J+2*r+3)*(2*J+2*m+2*r+5)) /
      ((r+1)*(J+2*r+1)*(2*J+2*r+3)*(2*(m-r : ℕ)+1)*(J+m+r+3)) := by
        exact (eq_div_of_mul_eq hd hs)
  unfold Wcert H
  rw [hm', hs']
  have hmr : (m : ℚ) = (m-r : ℕ)+r := by exact_mod_cast (show m = m-r+r by omega)
  push_cast
  have h1 : (m : ℚ)+1 ≠ 0 := by
    exact (Nat.cast_add_one_ne_zero m)
  have h2 : (J : ℚ)+2*r+1 ≠ 0 := by positivity
  have h3 : (2*J+2*m+3 : ℚ) ≠ 0 := by positivity
  have h4 : (2*J+2*m+2*r+3 : ℚ) ≠ 0 := by
    exact (right_ne_zero_of_mul hn)
  have h5 : (J : ℚ)+2*(r+1)+1 ≠ 0 := by positivity
  have h6 : (2*J+2*m+2*(r+1)+3 : ℚ) ≠ 0 := by positivity
  have h7 : (r : ℚ)+1 ≠ 0 := by
    exact (Nat.cast_add_one_ne_zero r)
  have h8 : (2*J+2*r+3 : ℚ) ≠ 0 := by positivity
  have h9 : (2*(m-r : ℕ)+1 : ℚ) ≠ 0 := by
    exact (mul_ne_zero_iff_right h4).mp hn
  have h10 : (J+m+r+3 : ℚ) ≠ 0 := by
    exact (right_ne_zero_of_mul hd)
  field_simp
  rw [hmr]
  ring
private lemma Wcert_zero (J m : ℕ) : Wcert J m 0 = 0 := by simp [Wcert, H]
private lemma Wcert_last (J m : ℕ) : Wcert J m (m+1) = -W J (m+1) (m+1) := by
  unfold Wcert H
  push_cast
  have h1 : (m : ℚ)+1 ≠ 0 := by
    exact (Nat.cast_add_one_ne_zero m)
  have h2 : (J : ℚ)+2*(m+1)+1 ≠ 0 := by positivity
  have h3 : (2*J+2*m+3 : ℚ) ≠ 0 := by positivity
  have h4 : (2*J+2*m+2*(m+1)+3 : ℚ) ≠ 0 := by positivity
  field_simp
  ring
private lemma W_sum (J m : ℕ) : (∑ r ∈ range (m+1), W J m r) = 1 := by
  induction m with
  | zero =>
    simp [W, Nat.factorial_succ]
    have h1 : (J.factorial : ℚ) ≠ 0 := by
      exact (fac_ne J)
    have h2 : ((2*J).factorial : ℚ) ≠ 0 := by
      exact (fac_ne (2 * J))
    have h3 : (J : ℚ)+1 ≠ 0 := by
      exact (Nat.cast_add_one_ne_zero J)
    have h4 : (2*J+1 : ℚ) ≠ 0 := by positivity
    field_simp
  | succ m ih =>
    rw [sum_range_succ]
    have h : (∑ r ∈ range (m+1), (W J (m+1) r - W J m r)) =
        -W J (m+1) (m+1) := by
      calc
        _ = ∑ r ∈ range (m+1), (Wcert J m (r+1) - Wcert J m r) := by
          apply sum_congr rfl
          intro r hr
          exact W_telescoper J m r (by simpa using mem_range.mp hr)
        _ = Wcert J m (m+1) - Wcert J m 0 := by rw [sum_range_sub]
        _ = _ := by rw [Wcert_zero, Wcert_last]; ring
    rw [sum_sub_distrib, ih] at h
    linear_combination h
private lemma choose_rat (n k : ℕ) (h : k ≤ n) :
    (Nat.choose n k : ℚ) = (Nat.factorial (n) : ℚ) / ((Nat.factorial (k) : ℚ) * (Nat.factorial (n-k) : ℚ)) := by
      exact (Nat.cast_choose ℚ h)
private lemma S_sq_closed (J r : ℕ) :
    S (J+2*r) J ^ 2 =
      (((2*J+1 : ℚ)*4^J * (Nat.factorial (J+r) : ℚ)^2 * (Nat.factorial (2*r) : ℚ) /
        ((Nat.factorial (r) : ℚ)^2 * (Nat.factorial (2*J+2*r+1) : ℚ)) : ℚ) : ℝ) := by
  rw [S_sq_rational _ _ (by omega), rationalSum_binomial, binomial_kernel_closed]
  have he : 2 ∣ 2*r := by
    exact (Nat.dvd_mul_right 2 r)
  rw [if_pos he]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  congr 1
  rw [choose_rat _ _ (by omega)]
  rw [prefactor_formula]
  have h0 : ((J+2*r : ℕ) : ℤ) - J = ((2*r : ℕ) : ℤ) := by
    exact (Int.sub_eq_iff_eq_add'.mpr rfl)
  have h1 : ((J+2*r : ℕ) : ℤ) + J + 1 = ((2*J+2*r+1 : ℕ) : ℤ) := by omega
  rw [h0, h1]
  simp only [Int.toNat_natCast]
  change (2*J+1 : ℚ) * (Nat.factorial (J) : ℚ) * (Nat.factorial (J) : ℚ) * (Nat.factorial (2*r) : ℚ) / (Nat.factorial (2*J+2*r+1) : ℚ) *
    (2^J * ((Nat.factorial (J+r) : ℚ) / ((Nat.factorial (J) : ℚ) * (Nat.factorial (J+r-J) : ℚ))))^2 = _
  rw [show J+r-J = r by omega]
  have hp : ((2 : ℚ)^J)^2 = (4 : ℚ)^J := by rw [← pow_mul, mul_comm J 2, pow_mul]; norm_num
  rw [mul_pow, hp]
  field_simp [fac_ne]
def explicitQ (n k : ℕ) : ℝ :=
  ((n - 2 * k + 1 : ℕ) : ℝ)^2 *
    (Nat.choose (2 * n - 2 * k + 1) (n - k) : ℝ) *
    (Nat.choose (2 * k) k : ℝ) /
    ((4 : ℝ)^n * (Nat.choose (n + 2) 2 : ℝ))
private lemma explicitQ_pos (n k : ℕ) (hk : k ≤ n / 2) : 0 < explicitQ n k := by
  have hc : 0 < (Nat.choose (2 * n - 2 * k + 1) (n - k) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : n-k ≤ 2*n-2*k+1)
  have hd : 0 < (Nat.choose (2 * k) k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ 2*k)
  have he : 0 < (Nat.choose (n + 2) 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n+2)
  unfold explicitQ
  positivity
private lemma explicitQ_nonneg (n k : ℕ) (hk : k ≤ n / 2) : 0 ≤ explicitQ n k := by
  exact (explicitQ_pos n k hk).le
private def Q (n k : ℕ) : ℚ :=
  ((n : ℚ)-2*k+1)^2 * (Nat.factorial (2*(n-k)+1) : ℚ) * (Nat.factorial (2*k) : ℚ) * 2 /
    ((Nat.factorial (n-k) : ℚ)*(Nat.factorial (n-k+1) : ℚ)*(Nat.factorial (k) : ℚ)^2*4^n*(n+1)*(n+2))
private lemma Q_step_n (n k : ℕ) (hk : 2*k ≤ n) :
    Q (n+2) k * (4*(n+3)*(n+4)*((n : ℚ)-k+3)*(n-k+2)*(n-2*k+1)^2) =
    Q n k * ((n+1)*(n+2)*(2*(n-k)+5)*(2*(n-k)+3)*(n-2*k+3)^2) := by
  unfold Q
  rw [show n+2-k = (n-k)+2 by omega,
    show 2*(n-k+2)+1 = (2*(n-k)+1)+2+2 by omega,
    show n-k+2+1 = (n-k+1)+2 by omega]
  simp only [fac_succ, pow_add]
  have hn : (n : ℚ) = (n-k : ℕ)+k := by exact_mod_cast (show n = n-k+k by omega)
  push_cast
  field_simp [fac_ne]
  rw [hn]
  ring
private lemma Q_step_k (n k : ℕ) (hk : 2*k ≤ n) :
    Q (n+2) (k+1) * ((n-2*k+3 : ℚ)^2*(k+1)*(2*n-2*k+5)) =
    Q (n+2) k * ((n-2*k+1 : ℚ)^2*(2*k+1)*(n-k+3)) := by
  unfold Q
  rw [show n+2-(k+1) = (n-k)+1 by omega,
      show n+2-k = (n-k)+2 by omega,
      show 2*(n-k+1)+1 = (2*(n-k)+1)+2 by omega,
      show 2*(n-k+2)+1 = (2*(n-k)+1)+2+2 by omega,
      show 2*(k+1) = 2*k+2 by omega]
  simp only [fac_succ]
  have hn : (n : ℚ) = (n-k : ℕ)+k := by exact_mod_cast (show n = n-k+k by omega)
  push_cast
  field_simp [fac_ne]
  rw [hn]
  ring
private def QH (n k : ℕ) : ℚ :=
  -(k : ℚ) * (8*k^2*n+20*k^2-12*k*n^2-64*k*n-82*k+4*n^3+33*n^2+85*n+68) /
    ((n+1)*(n+2)*(2*n-2*k+5)*(n-2*k+3))
private def Qcert (n k : ℕ) : ℚ := QH n k * Q (n+2) k
private lemma Q_telescoper (n k : ℕ) (hk : 2*k ≤ n) :
    Q (n+2) k - Q n k = Qcert n (k+1) - Qcert n k := by
  have hm := by
    exact (Q_step_n n k hk)
  have hs := by
    exact (Q_step_k n k hk)
  have hnk : (2*k : ℚ) ≤ n := by exact_mod_cast hk
  have hn : ((n+1)*(n+2)*(2*(n-k)+5)*(2*(n-k)+3)*(n-2*k+3)^2 : ℚ) ≠ 0 := by
    have h1 : 0 ≤ (n : ℚ)-k := by nlinarith [show (0 : ℚ) ≤ k by positivity]
    have h2 : 0 < (n : ℚ)-2*k+3 := by linarith
    positivity
  have hd : ((n-2*k+3 : ℚ)^2*(k+1)*(2*n-2*k+5)) ≠ 0 := by
    have h1 : 0 < (n : ℚ)-2*k+3 := by linarith
    have h2 : 0 < (2*n-2*k+5 : ℚ) := by linarith [show (0 : ℚ) ≤ n by positivity]
    positivity
  have hm' : Q n k = Q (n+2) k * (4*(n+3)*(n+4)*((n : ℚ)-k+3)*(n-k+2)*(n-2*k+1)^2) /
    ((n+1)*(n+2)*(2*(n-k)+5)*(2*(n-k)+3)*(n-2*k+3)^2) := by
      exact (eq_div_of_mul_eq hn (id (Eq.symm hm)))
  have hs' : Q (n+2) (k+1) = Q (n+2) k * ((n-2*k+1 : ℚ)^2*(2*k+1)*(n-k+3)) /
    ((n-2*k+3 : ℚ)^2*(k+1)*(2*n-2*k+5)) := by
      exact (eq_div_of_mul_eq hd hs)
  unfold Qcert QH
  rw [hm', hs']
  push_cast
  have h1 : (n : ℚ)+1 ≠ 0 := by
    exact (Nat.cast_add_one_ne_zero n)
  have h2 : (n : ℚ)+2 ≠ 0 := by positivity
  have h3 : (2*n-2*k+5 : ℚ) ≠ 0 := by
    exact (right_ne_zero_of_mul hd)
  have h4 : (n-2*k+3 : ℚ) ≠ 0 := by linarith
  have h5 : (2*n-2*(k+1)+5 : ℚ) ≠ 0 := by linarith [show (0 : ℚ) ≤ n by positivity]
  have h6 : (n-2*(k+1)+3 : ℚ) ≠ 0 := by linarith
  have h7 : (k : ℚ)+1 ≠ 0 := by
    exact (Nat.cast_add_one_ne_zero k)
  field_simp (disch := (first | positivity | linarith))
  ring
private lemma Qcert_zero (n : ℕ) : Qcert n 0 = 0 := by simp [Qcert, QH]
private lemma Qcert_last (n : ℕ) : Qcert n (n/2+1) = -Q (n+2) (n/2+1) := by
  unfold Qcert QH
  set m := n/2
  have hn : n = 2*m ∨ n = 2*m+1 := by dsimp [m]; omega
  rcases hn with hn | hn <;> rw [hn] <;> push_cast
  all_goals
    have h1 : (2*m+1 : ℚ) ≠ 0 := by positivity
    have h2 : (2*m+2 : ℚ) ≠ 0 := by positivity
    have h3 : (2*m+3 : ℚ) ≠ 0 := by positivity
    have h4 : (2*m+5 : ℚ) ≠ 0 := by positivity
    field_simp (disch := (first | positivity | linarith))
    ring
private lemma Q_sum (n : ℕ) : (∑ k ∈ range (n/2+1), Q n k) = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [Q, Nat.factorial]
  | one => norm_num [Q, Nat.factorial]
  | more n ih ih1 =>
    rw [show (n+2)/2+1 = (n/2+1)+1 by omega, sum_range_succ]
    have h : (∑ k ∈ range (n/2+1), (Q (n+2) k - Q n k)) =
        -Q (n+2) (n/2+1) := by
      calc
        _ = ∑ k ∈ range (n/2+1), (Qcert n (k+1) - Qcert n k) := by
          apply sum_congr rfl
          intro k hk
          exact Q_telescoper n k (by
            have : k < n / 2 + 1 := List.mem_range.mp hk
            omega)
        _ = Qcert n (n/2+1) - Qcert n 0 := by rw [sum_range_sub]
        _ = _ := by rw [Qcert_zero, Qcert_last]; ring
    rw [sum_sub_distrib, ih] at h
    linear_combination h
private lemma Q_eq_binomial (n k : ℕ) (hk : 2*k ≤ n) :
    Q n k = ((n-2*k+1 : ℕ) : ℚ)^2 *
      (Nat.choose (2*n-2*k+1) (n-k) : ℚ) * (Nat.choose (2*k) k : ℚ) /
        (4^n * (Nat.choose (n+2) 2 : ℚ)) := by
  rw [show 2*n-2*k+1 = 2*(n-k)+1 by omega]
  rw [choose_rat _ _ (by omega), choose_rat _ _ (by omega), Nat.cast_choose_two]
  rw [show 2*(n-k)+1-(n-k) = n-k+1 by omega, show 2*k-k = k by omega]
  have hc : ((n-2*k+1 : ℕ) : ℚ) = (n : ℚ)-2*k+1 := by
    rw [Nat.cast_add, Nat.cast_sub hk]; push_cast; ring
  rw [hc]
  unfold Q
  push_cast
  field_simp (disch := (first | exact fac_ne _ | positivity | linarith))
  ring
private lemma explicitQ_eq_Q (n k : ℕ) (hk : k ≤ n/2) : explicitQ n k = (Q n k : ℝ) := by
  rw [Q_eq_binomial n k (by omega)]
  unfold explicitQ
  push_cast
  rfl
private lemma explicitQ_sum (n : ℕ) : (∑ k ∈ range (n/2+1), explicitQ n k) = 1 := by
  calc
    _ = ∑ k ∈ range (n/2+1), (Q n k : ℝ) := by
      apply sum_congr rfl
      intro k hk
      exact explicitQ_eq_Q n k (by simpa using mem_range.mp hk)
    _ = ((∑ k ∈ range (n/2+1), Q n k : ℚ) : ℝ) := by push_cast; rfl
    _ = 1 := by rw [Q_sum]; norm_num
private lemma probability_kernel_term (J k r : ℕ) :
    Q (J+2*(k+r)) k / (J+2*r+1) * ((2*J+1 : ℚ)*4^J * (Nat.factorial (J+r) : ℚ)^2 * (Nat.factorial (2*r) : ℚ) / ((Nat.factorial (r) : ℚ)^2 * (Nat.factorial (2*J+2*r+1) : ℚ))) =
      (2*J+1)/(Nat.choose (J+2*(k+r)+2) 2 : ℚ) * W J (k+r) r := by
  unfold Q W
  rw [show J+2*(k+r)-k = J+(k+r)+r by omega,
    show 2*(J+(k+r)+r)+1 = 2*J+2*(k+r)+2*r+1 by omega,
    show k+r-r = k by omega]
  rw [Nat.cast_choose_two]
  push_cast
  have hp : (4 : ℚ)^(J+2*(k+r)) = 4^J * 16^(k+r) := by
    rw [pow_add, pow_mul]; norm_num
  rw [hp]
  have hn : (J+2*r+1 : ℚ) ≠ 0 := by positivity
  field_simp (disch := (first | exact fac_ne _ | positivity | linarith))
  ring
private lemma explicitQ_kernel_term (J m k : ℕ) (hk : k ≤ m) :
    explicitQ (J+2*m) k / ((J+2*m-2*k : ℕ)+1 : ℝ) * S (J+2*m-2*k) J ^ 2 =
      (2*(J : ℝ)+1)/(Nat.choose (J+2*m+2) 2 : ℝ) * (W J m (m-k) : ℝ) := by
  rw [show J+2*m-2*k = J+2*(m-k) by omega]
  rw [S_sq_closed]
  rw [explicitQ_eq_Q _ _ (by omega)]
  have h := by
    exact (probability_kernel_term J k (m - k))
  rw [show k+(m-k) = m by omega] at h
  have hr := (Rat.cast_inj (α := ℝ)).mpr h
  push_cast at hr ⊢
  exact hr
private lemma system_equations (n J : ℕ) (hJ : J ≤ n) (hpar : J%2 = n%2) :
    (2*(J : ℝ)+1)/(Nat.choose (n+2) 2 : ℝ) =
      ∑ k ∈ range (n/2+1), if J ≤ n-2*k then
        explicitQ n k / ((n-2*k : ℕ)+1 : ℝ) * S (n-2*k) J ^ 2 else 0 := by
  obtain ⟨m, hm⟩ : ∃ m, n = J+2*m := by
    refine ⟨(n-J)/2, ?_⟩
    omega
  subst n
  have hsum : (∑ k ∈ range ((J+2*m)/2+1), if J ≤ J+2*m-2*k then
      explicitQ (J+2*m) k / ((J+2*m-2*k : ℕ)+1 : ℝ) * S (J+2*m-2*k) J ^ 2 else 0) =
      ∑ k ∈ range (m+1), explicitQ (J+2*m) k / ((J+2*m-2*k : ℕ)+1 : ℝ) * S (J+2*m-2*k) J ^ 2 := by
    have hsub : range (m+1) ⊆ range ((J+2*m)/2+1) := by
      intro k hk
      have := by
        exact (List.mem_range.mp hk)
      apply mem_range.mpr
      omega
    calc
      _ = ∑ k ∈ range (m+1), if J ≤ J+2*m-2*k then
        explicitQ (J+2*m) k / ((J+2*m-2*k : ℕ)+1 : ℝ) * S (J+2*m-2*k) J ^ 2 else 0 := by
        symm
        apply sum_subset hsub
        intro k hk hnot
        have hk' := by
          exact (List.mem_range.mp hk)
        have hnot' : m < k := by simpa using hnot
        rw [if_neg (by omega)]
      _ = _ := by
        apply sum_congr rfl
        intro k hk
        have hkm : k ≤ m := by
          exact (mem_range_succ_iff.mp hk)
        rw [if_pos (by omega)]
  rw [hsum]
  have he : (∑ k ∈ range (m+1), explicitQ (J+2*m) k /
      ((J+2*m-2*k : ℕ)+1 : ℝ) * S (J+2*m-2*k) J ^ 2) =
      ∑ k ∈ range (m+1), (2*(J : ℝ)+1)/(Nat.choose (J+2*m+2) 2 : ℝ) * (W J m (m-k) : ℝ) := by
    apply sum_congr rfl
    intro k hk
    exact explicitQ_kernel_term J m k (by simpa using mem_range.mp hk)
  rw [he, ← mul_sum]
  have hrange : (∑ k ∈ range (m+1), (W J m (m-k) : ℝ)) = 1 := by
    have hre := sum_range_reflect (fun k => (W J m k : ℝ)) (m+1)
    simp only [Nat.add_sub_cancel] at hre
    rw [hre]
    have h := by
      exact (W_sum J m)
    exact_mod_cast h
  rw [hrange, mul_one]
theorem result : claim := by
  intro n hn
  refine ⟨explicitQ n, ?_, explicitQ_sum n, ?_⟩
  · intro k hk
    exact explicitQ_nonneg n k hk
  · intro J hJ hpar
    exact system_equations n J hJ hpar
end D5.S3.Quantum.Measurement.SGVFlatSpectrum
