/- GID: D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer polynomial denominators of contiguous basic hypergeometric coefficients. -/

/-
proof_shape: per-declaration classifications below.
Classification: the inverse floor estimate and recurrence coefficient membership are degree inductions.
Bind-only helpers are inlined in the compiled proof-term classification; their source declarations
organize proofs with actual consumers under the consumed-helper rule.
The inverse estimate has arbitrary field and subring parameters and is distinct from the integer
numerator conclusion. Its reciprocal coefficient bounds are derived, not assumed. The local pole
estimate supplies the membership used by cleared_ratio_local and localization_descent; both settling
results use denominator_from_localization on this live path.
escape_witness: inverse_floor_bound, on the path to denominator_from_localization
admission_basis: escape-witness (denominator_from_localization)
Direct frozen dependencies: none; all external proof constants are pinned Mathlib.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21724
Declarations: name | proof_shape | escape_witness | consumer(s).
a | bind-only | none | KimStantonSimultaneousDenominator.gamma, KimStantonSimultaneousDenominator.ratio_mem, KimStantonSimultaneousDenominator.u_recurrence, KimStantonSimultaneousDenominator.weights_mem, KimStantonSingleDenominator.gamma, KimStantonSingleDenominator.parameters, KimStantonSingleDenominator.parameters_succ, KimStantonSingleDenominator.ratio_mem
b | bind-only | none | KimStantonSimultaneousDenominator.gamma, KimStantonSimultaneousDenominator.ratio_mem, KimStantonSimultaneousDenominator.u_recurrence, KimStantonSimultaneousDenominator.weights_mem, KimStantonSingleDenominator.gamma, KimStantonSingleDenominator.parameters, KimStantonSingleDenominator.parameters_succ, KimStantonSingleDenominator.ratio_mem
c | bind-only | none | D, D_eq_map, D_factor, S_inv_p, T_F_regular, T_F_simple, T_inv_p, T_inv_product, T_simple_inv_product, cleared_ratio_local, denominator_from_localization, qsf_lower_product, ratio, ratio_local_bound, ratio_local_zero_bound, KimStantonSimultaneousDenominator.claim, KimStantonSimultaneousDenominator.gamma, KimStantonSimultaneousDenominator.ratio_mem, KimStantonSimultaneousDenominator.result, KimStantonSimultaneousDenominator.u_recurrence, KimStantonSimultaneousDenominator.weights_mem, KimStantonSingleDenominator.beta, KimStantonSingleDenominator.beta_mem, KimStantonSingleDenominator.claim, KimStantonSingleDenominator.gamma, KimStantonSingleDenominator.ratio_mem, KimStantonSingleDenominator.result, KimStantonSingleDenominator.u_recurrence
q | bind-only | none | D, D_eq_map, D_factor, S_inv_p, T_F_regular, T_F_simple, T_inv_p, T_inv_product, T_inv_qsf_q, T_simple_inv_product, cleared_ratio_local, denominator_from_localization, evalC, one_sub_q_pow_ne_zero, p_not_dvd_one_sub_q, p_not_dvd_p, q_ne_zero, q_pow_injective, qsf_lower_product, ratio, ratio_local_bound, ratio_local_zero_bound, KimStantonSimultaneousDenominator.gamma, KimStantonSimultaneousDenominator.ratio_mem, KimStantonSimultaneousDenominator.result, KimStantonSimultaneousDenominator.u_recurrence, KimStantonSimultaneousDenominator.weights_mem, KimStantonSingleDenominator.beta, KimStantonSingleDenominator.beta_mem, KimStantonSingleDenominator.gamma, KimStantonSingleDenominator.parameters, KimStantonSingleDenominator.parameters_mem, KimStantonSingleDenominator.parameters_nonzero, KimStantonSingleDenominator.parameters_succ, KimStantonSingleDenominator.ratio_mem, KimStantonSingleDenominator.result, KimStantonSingleDenominator.u_recurrence
qShiftedFactorial | bind-only | none | F, F_constant, T_F_regular, T_F_simple, T_inv_qsf_q, coeff_F_succ, coeff_shift_abc, coeff_shift_abcc, coeff_shift_ac, qsf_lower_product, qsf_shift, qsf_shift_ratio, KimStantonSingleDenominator.F_swap
F | bind-only | none | F_constant, T_F_regular, T_F_simple, coeff_F_succ, coeff_shift_abc, coeff_shift_abcc, coeff_shift_ac, heine_contiguous, ratio, ratio_local_bound, ratio_local_zero_bound, KimStantonSimultaneousDenominator.coeff_F_degreeStep, KimStantonSimultaneousDenominator.coeff_F_parameterStep, KimStantonSimultaneousDenominator.gamma, KimStantonSimultaneousDenominator.norlund_contiguous, KimStantonSimultaneousDenominator.ratio_mem, KimStantonSimultaneousDenominator.result, KimStantonSimultaneousDenominator.u_recurrence, KimStantonSingleDenominator.F_swap, KimStantonSingleDenominator.gamma, KimStantonSingleDenominator.ratio_mem, KimStantonSingleDenominator.result, KimStantonSingleDenominator.u_recurrence
D | bind-only | none | D_nonzero, cleared_ratio_local, denominator_from_localization, KimStantonSimultaneousDenominator.claim, KimStantonSimultaneousDenominator.result, KimStantonSingleDenominator.claim, KimStantonSingleDenominator.result
p | bind-only | none | D_eq_map, D_nonzero, S, S_inv_p, T_F_regular, T_F_simple, T_inv_p, T_inv_product, T_inv_qsf_q, T_simple_inv_product, cleared_ratio_local, denominator_from_localization, evalC_p, map_p, nonzeroFamily, pPrime, p_not_dvd_one_sub_q, p_not_dvd_p, ratio_local_bound, ratio_local_zero_bound, splitC_p
splitC | bind-only | none | pPrime, splitC_p
splitC_p | bind-only | none | pPrime
pPrime | bind-only | none | D_nonzero, T_F_regular, T_F_simple, T_inv_p, T_inv_product, T_inv_qsf_q, T_simple_inv_product, cleared_ratio_local, denominator_from_localization, nonzeroFamily, ratio_local_bound, ratio_local_zero_bound
nonzeroFamily | bind-only | none | S
map_p | bind-only | none | D_eq_map, S_inv_p, T_inv_p, T_simple_inv_product, cleared_ratio_local, ratio_local_bound, ratio_local_zero_bound
q_ne_zero | bind-only | none | p_not_dvd_one_sub_q, p_not_dvd_p
q_pow_injective | bind-only | none | one_sub_q_pow_ne_zero, p_not_dvd_p
one_sub_q_pow_ne_zero | bind-only | none | p_not_dvd_one_sub_q, KimStantonSimultaneousDenominator.u_recurrence, KimStantonSingleDenominator.u_recurrence
evalC | bind-only | none | evalC_p, p_not_dvd_one_sub_q, p_not_dvd_p
evalC_p | bind-only | none | p_not_dvd_one_sub_q, p_not_dvd_p
p_not_dvd_p | bind-only | none | T_inv_p
p_not_dvd_one_sub_q | bind-only | none | T_inv_qsf_q
variable_factor_ne_zero | bind-only | none | cleared_ratio_local, KimStantonSimultaneousDenominator.u_recurrence, KimStantonSingleDenominator.parameters_nonzero, KimStantonSingleDenominator.u_recurrence
Bound | bind-only | none | T_F_simple, bound_mono, bound_mul, bound_neg, bound_sum, cleared_ratio_local, inverse_floor_bound, product_floor_bound, ratio_floor_bound, ratio_local_bound, ratio_local_zero_bound, simple_onset_floor_bound
bound_mono | bind-only | none | inverse_floor_bound, product_floor_bound, ratio_local_zero_bound, simple_onset_floor_bound
bound_mul | bind-only | none | inverse_floor_bound, product_floor_bound
bound_sum | bind-only | none | inverse_floor_bound, product_floor_bound
bound_neg | bind-only | none | inverse_floor_bound
inverse_floor_bound | content | conclusion via degree induction | ratio_floor_bound
product_floor_bound | bind-only | none | ratio_floor_bound
ratio_floor_bound | content | inverse_floor_bound | ratio_local_bound, ratio_local_zero_bound
simple_onset_floor_bound | bind-only | none | ratio_local_bound, ratio_local_zero_bound
regularRing | bind-only | none | T_F_regular, T_F_simple, T_inv_p, T_inv_product, T_inv_qsf_q, T_simple_inv_product, cleared_ratio_local, denominator_from_localization, list_denominator_descent, localization_descent, prime_cancel_denominator, ratio_local_bound, ratio_local_zero_bound, regular_iff, regular_inv
regular_iff | bind-only | none | prime_cancel_denominator, regular_inv
regular_inv | bind-only | none | T_inv_p, T_inv_qsf_q
prime_cancel_denominator | bind-only | none | list_denominator_descent
list_denominator_descent | content | conclusion via finite prime cancellation induction | localization_descent
closureLeNonzero | bind-only | none | S, localization_descent
localization_descent | content | list_denominator_descent | denominator_from_localization
coeff_product_mem | bind-only | none | recurrence_coefficients_mem
recurrence_coefficients_mem | content | conclusion via degree induction | quotient_coefficients_mem
quotient_recurrence | bind-only | none | quotient_coefficients_mem
quotient_coefficients_mem | content | recurrence_coefficients_mem | KimStantonSimultaneousDenominator.ratio_mem, KimStantonSingleDenominator.ratio_mem
qsf_zero | bind-only | none | F_constant
qsf_succ | bind-only | none | coeff_F_succ, qsf_shift_ratio
qsf_shift | bind-only | none | qsf_shift_ratio
qsf_shift_ratio | bind-only | none | coeff_shift_abc, coeff_shift_abcc, coeff_shift_ac
qsf_nonzero | bind-only | none | coeff_shift_abc, coeff_shift_abcc, coeff_shift_ac
F_constant | bind-only | none | heine_contiguous, ratio_local_bound, ratio_local_zero_bound, KimStantonSimultaneousDenominator.norlund_contiguous, KimStantonSimultaneousDenominator.ratio_mem, KimStantonSingleDenominator.ratio_mem
coeff_F_succ | bind-only | none | heine_contiguous, KimStantonSimultaneousDenominator.coeff_F_degreeStep, KimStantonSimultaneousDenominator.norlund_contiguous
coeff_shift_ac | bind-only | none | heine_contiguous
coeff_shift_abc | bind-only | none | KimStantonSimultaneousDenominator.coeff_F_parameterStep, KimStantonSimultaneousDenominator.norlund_contiguous
coeff_shift_abcc | bind-only | none | heine_contiguous
heine_contiguous | bind-only | none | KimStantonSingleDenominator.u_recurrence
S | bind-only | none | S_inv_p, denominator_from_localization, KimStantonSimultaneousDenominator.ratio_mem, KimStantonSimultaneousDenominator.weights_mem, KimStantonSingleDenominator.beta_mem, KimStantonSingleDenominator.parameters_mem, KimStantonSingleDenominator.ratio_mem
S_inv_p | bind-only | none | denominator_from_localization, KimStantonSimultaneousDenominator.weights_mem, KimStantonSingleDenominator.beta_mem
T_inv_p | bind-only | none | T_inv_product, cleared_ratio_local
qsf_mem | bind-only | none | T_F_regular, T_F_simple
qsf_lower_product | bind-only | none | T_F_regular, T_F_simple
T_inv_product | bind-only | none | T_F_regular, T_simple_inv_product
T_simple_inv_product | bind-only | none | T_F_simple
T_inv_qsf_q | bind-only | none | T_F_regular, T_F_simple
T_F_simple | bind-only | none | ratio_local_bound, ratio_local_zero_bound
T_F_regular | bind-only | none | ratio_local_bound, ratio_local_zero_bound
ratio | bind-only | none | cleared_ratio_local, denominator_from_localization, ratio_local_zero_bound, KimStantonSimultaneousDenominator.ratio_mem, KimStantonSimultaneousDenominator.result, KimStantonSingleDenominator.ratio_mem, KimStantonSingleDenominator.result
ratio_local_bound | content | inverse_floor_bound | cleared_ratio_local
ratio_local_zero_bound | content | inverse_floor_bound | cleared_ratio_local
D_eq_map | bind-only | none | D_nonzero, cleared_ratio_local, denominator_from_localization
D_nonzero | bind-only | none | denominator_from_localization
D_factor | bind-only | none | cleared_ratio_local
cleared_ratio_local | content | inverse_floor_bound | denominator_from_localization
denominator_from_localization | content | inverse_floor_bound | KimStantonSimultaneousDenominator.result, KimStantonSingleDenominator.result
The inverse floor bound and recurrence coefficient membership are degree inductions.
Finite prime cancellation constructs the integral numerator; all remaining algebraic helpers
are consumed by the displayed declarations.
-/

import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Localization.AsSubring


set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

open scoped BigOperators


def a : (FractionRing (MvPolynomial (Fin 4) ℤ)) := algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (MvPolynomial.X 0)
def b : (FractionRing (MvPolynomial (Fin 4) ℤ)) := algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (MvPolynomial.X 1)
def c : (FractionRing (MvPolynomial (Fin 4) ℤ)) := algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (MvPolynomial.X 2)
def q : (FractionRing (MvPolynomial (Fin 4) ℤ)) := algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (MvPolynomial.X 3)

/-
The finite-product convention qShiftedFactorial specializes QSeries.qPochhammer
from LeanPool/lean-pool at edbe5bd56f476cc2965564676b66199f281ab714,
LeanPool/PentagonalNumberTheoremAnalytic/QSeries/Defs.lean.
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska.
Released under Apache 2.0; license text: LICENSE; upstream notice chain:
docs/reports/brooks-suppliers/lean-pool-NOTICE.txt (PentagonalNumberTheoremAnalytic).
This convention and its zero/successor normalizations carry no new-content claim.
Replace this specialized convention by direct reuse when the repository's pinned
Mathlib contains an equivalent generic finite q-Pochhammer declaration.
-/
/-- (u;q)_r = product_{j=0}^{r-1} (1-u*q^j), including the empty product. -/
def qShiftedFactorial (u v : (FractionRing (MvPolynomial (Fin 4) ℤ))) (r : ℕ) : (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  ∏ j ∈ Finset.range r, (1 - u * v ^ j)

/-- Standard Gasper--Rahman 2phi1(A,B;C;q,z), as a formal series in z. -/
def F (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) : PowerSeries (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  PowerSeries.mk (fun r : ℕ =>
    qShiftedFactorial A Q r * qShiftedFactorial B Q r /
      (qShiftedFactorial C Q r * qShiftedFactorial Q Q r))

/-- The denominator in Conjectures 8.3 and 8.4; Nat division is floor division. -/
def D (n : ℕ) : (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  ∏ k ∈ Finset.range (n + 1), (1 - c * q ^ k) ^ ((n + 1) / (k + 1))


end D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

def p (k : ℕ) : (MvPolynomial (Fin 4) ℤ) := 1 - MvPolynomial.X 2 * MvPolynomial.X 3 ^ k

private def splitC : (MvPolynomial (Fin 4) ℤ) ≃+* Polynomial (MvPolynomial (Fin 3) ℤ) :=
  (MvPolynomial.renameEquiv ℤ (Equiv.swap (0 : Fin 4) 2)).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv ℤ 3).toRingEquiv

private theorem splitC_p (k : ℕ) : splitC (p k) =
    Polynomial.C (-(MvPolynomial.X 2 : (MvPolynomial (Fin 3) ℤ)) ^ k) * Polynomial.X + Polynomial.C 1 := by
  have hswap : Equiv.swap (0 : Fin 4) 2 3 = 3 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hX : MvPolynomial.finSuccEquiv ℤ 3 (MvPolynomial.X (3 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := ℤ) (j := (2 : Fin 3))
  simp [splitC, p, hswap, hX, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_X_zero,
    show (3 : Fin 4) = (2 : Fin 3).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ, Polynomial.C_pow]
  ring

private theorem pPrime (k : ℕ) : Prime (p k) := by
  apply (MulEquiv.prime_iff splitC).mp
  rw [splitC_p]
  apply irreducible_iff_prime.mp
  exact Polynomial.irreducible_C_mul_X_add_C
    (neg_ne_zero.mpr (pow_ne_zero k (MvPolynomial.X_ne_zero (2 : Fin 3)))) isRelPrime_one_right

theorem nonzeroFamily (r : (MvPolynomial (Fin 4) ℤ)) (hr : r ∈ Set.range p) : r ≠ 0 := by
  obtain ⟨k, rfl⟩ := hr
  exact (pPrime k).ne_zero

private theorem map_p (k : ℕ) : algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) = 1 - c * q ^ k := by
  simp [p, c, q]

private theorem q_ne_zero : q ≠ 0 := by
  simpa only [map_zero, q] using (IsFractionRing.injective (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ))).ne (MvPolynomial.X_ne_zero (3 : Fin 4))

private theorem q_pow_injective : Function.Injective (fun n : ℕ => q ^ n) := by
  intro m n h
  have hR : (MvPolynomial.X (3 : Fin 4) : (MvPolynomial (Fin 4) ℤ)) ^ m = MvPolynomial.X 3 ^ n :=
    IsFractionRing.injective (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (by simpa only [map_pow, q] using h)
  have hd := congrArg MvPolynomial.totalDegree hR
  simpa only [MvPolynomial.totalDegree_X_pow] using hd

theorem one_sub_q_pow_ne_zero (n : ℕ) (hn : n ≠ 0) : 1 - q ^ n ≠ 0 := by
  intro h
  have heq : q ^ n = q ^ 0 := by simpa using (sub_eq_zero.mp h).symm
  exact hn (q_pow_injective heq)

private def evalC (k : ℕ) : (MvPolynomial (Fin 4) ℤ) →+* (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  MvPolynomial.eval₂Hom (Int.castRingHom (FractionRing (MvPolynomial (Fin 4) ℤ)))
    (fun i => if i = 2 then (q ^ k)⁻¹ else algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (MvPolynomial.X i))

private theorem evalC_p (k j : ℕ) : evalC k (p j) = 1 - (q ^ k)⁻¹ * q ^ j := by
  simp [evalC, p, q]

private theorem p_not_dvd_p (k j : ℕ) (hkj : k ≠ j) : ¬ p k ∣ p j := by
  intro h
  have hdiv := map_dvd (evalC k) h
  have h0 : evalC k (p k) = 0 := by simp [evalC_p, q_ne_zero]
  rw [h0, zero_dvd_iff, evalC_p] at hdiv
  have hkq : q ^ k ≠ 0 := pow_ne_zero k q_ne_zero
  have hpow : q ^ k = q ^ j := by
    calc
      q ^ k = q ^ k * 1 := (mul_one _).symm
      _ = q ^ k * ((q ^ k)⁻¹ * q ^ j) := congrArg (fun t : (FractionRing (MvPolynomial (Fin 4) ℤ)) => q ^ k * t) (sub_eq_zero.mp hdiv)
      _ = q ^ j := by rw [← mul_assoc, mul_inv_cancel₀ hkq, one_mul]
  exact hkj (q_pow_injective hpow)

private theorem p_not_dvd_one_sub_q (k n : ℕ) (hn : n ≠ 0) :
    ¬ p k ∣ (1 - MvPolynomial.X 3 ^ n : (MvPolynomial (Fin 4) ℤ)) := by
  intro h
  have hdiv := map_dvd (evalC k) h
  have h0 : evalC k (p k) = 0 := by simp [evalC_p, q_ne_zero]
  rw [h0, zero_dvd_iff] at hdiv
  have hz : 1 - q ^ n = 0 := by simpa [evalC, q] using hdiv
  exact one_sub_q_pow_ne_zero n hn hz

theorem variable_factor_ne_zero (i j : Fin 4) (m : ℕ) :
    1 - algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (MvPolynomial.X i) * algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (MvPolynomial.X j) ^ m ≠ 0 := by
  intro h
  have hR : (1 - MvPolynomial.X i * MvPolynomial.X j ^ m : (MvPolynomial (Fin 4) ℤ)) = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) (by simpa only [map_sub, map_one, map_mul, map_pow, map_zero] using h)
  have h0 := congrArg (MvPolynomial.eval (fun _ : Fin 4 => (0 : ℤ))) hR
  simpa using h0

end D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

end


set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore
variable {K : Type*} [Field K]

/-- Clearing at most e powers of p lands in T. -/
private def Bound (T : Subring K) (p : K) (e : ℕ) (x : K) : Prop := p ^ e * x ∈ T

private theorem bound_mono (T : Subring K) (p : K) (hp : p ∈ T)
    {e d : ℕ} (hed : e ≤ d) {x : K} (hx : Bound T p e x) : Bound T p d x := by
  have hm := T.mul_mem (T.pow_mem hp (d - e)) hx
  simpa only [Bound, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hed] using hm

private theorem bound_mul (T : Subring K) (p : K) {e d : ℕ} {x y : K}
    (hx : Bound T p e x) (hy : Bound T p d y) : Bound T p (e + d) (x * y) := by
  simpa only [Bound, pow_add, mul_mul_mul_comm] using T.mul_mem hx hy

private theorem bound_sum (T : Subring K) (p : K) {I : Type*} (s : Finset I) (e : ℕ)
    (x : I → K) (hx : ∀ i ∈ s, Bound T p e (x i)) : Bound T p e (∑ i ∈ s, x i) := by
  simpa only [Bound, Finset.mul_sum] using T.sum_mem hx

private theorem bound_neg (T : Subring K) (p : K) (e : ℕ) {x : K}
    (hx : Bound T p e x) : Bound T p e (-x) := by
  simpa only [Bound, mul_neg] using T.neg_mem hx

private theorem inverse_floor_bound (T : Subring K) (p : K) (hp : p ∈ T)
    (t : ℕ) (f : PowerSeries K) (h0 : PowerSeries.constantCoeff f = 1)
    (hf : ∀ n : ℕ, Bound T p (n / t) (PowerSeries.coeff n f)) :
    ∀ n : ℕ, Bound T p (n / t) (PowerSeries.coeff n f⁻¹) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [PowerSeries.coeff_inv, h0]
    by_cases hn : n = 0
    · subst n
      simpa [Bound] using T.one_mem
    · simp only [ite_eq_right hn, inv_one, neg_mul, one_mul]
      apply bound_neg
      apply bound_sum
      intro ij hij
      by_cases hj : ij.2 < n
      · simp only [ite_eq_left hj]
        have heq : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        exact bound_mono T p hp (heq ▸ (show ij.1 / t + ij.2 / t ≤ (ij.1 + ij.2) / t from Nat.div_add_div_le_add_div))
          (bound_mul T p (hf ij.1) (ih ij.2 hj))
      · simp only [ite_eq_right hj]
        simp [Bound]

private theorem product_floor_bound (T : Subring K) (p : K) (hp : p ∈ T)
    (t offset : ℕ) (g h : PowerSeries K)
    (hg : ∀ n : ℕ, Bound T p ((n + offset) / t) (PowerSeries.coeff n g))
    (hh : ∀ n : ℕ, Bound T p (n / t) (PowerSeries.coeff n h)) :
    ∀ n : ℕ, Bound T p ((n + offset) / t) (PowerSeries.coeff n (g * h)) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply bound_sum
  intro ij hij
  have heq : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  have hle : (ij.1 + offset) / t + ij.2 / t ≤ (n + offset) / t := by
    calc
      (ij.1 + offset) / t + ij.2 / t ≤ ((ij.1 + offset) + ij.2) / t := Nat.div_add_div_le_add_div
      _ = (n + offset) / t := by rw [show ij.1 + offset + ij.2 = n + offset by omega]
  exact bound_mono T p hp hle (bound_mul T p (hg ij.1) (hh ij.2))

private theorem ratio_floor_bound (T : Subring K) (p : K) (hp : p ∈ T)
    (t offset : ℕ) (f g : PowerSeries K) (h0 : PowerSeries.constantCoeff f = 1)
    (hf : ∀ n : ℕ, Bound T p (n / t) (PowerSeries.coeff n f))
    (hg : ∀ n : ℕ, Bound T p ((n + offset) / t) (PowerSeries.coeff n g)) :
    ∀ n : ℕ, Bound T p ((n + offset) / t) (PowerSeries.coeff n (g * f⁻¹)) := by
  exact product_floor_bound T p hp t offset g f⁻¹ hg
    (inverse_floor_bound T p hp t f h0 hf)

private theorem simple_onset_floor_bound (T : Subring K) (p : K) (hp : p ∈ T)
    (t offset : ℕ) (ht : 0 < t) (f : PowerSeries K)
    (hsimple : ∀ n : ℕ, Bound T p 1 (PowerSeries.coeff n f))
    (hregular : ∀ n : ℕ, n + offset < t → PowerSeries.coeff n f ∈ T) :
    ∀ n : ℕ, Bound T p ((n + offset) / t) (PowerSeries.coeff n f) := by
  intro n
  by_cases hn : n + offset < t
  · simpa only [Bound, Nat.div_eq_of_lt hn, pow_zero, one_mul] using hregular n hn
  · exact bound_mono T p hp ((Nat.le_div_iff_mul_le ht).mpr (by omega)) (hsimple n)

end D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
variable [Algebra R K] [IsFractionRing R K]

private def regularRing (p : R) (hp : Prime p) : Subalgebra R K :=
  letI := Ideal.isPrime_span_singleton_of_prime hp
  Localization.subalgebra.ofField K (Ideal.span {p}).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

private theorem regular_iff (p : R) (hp : Prime p) (x : K) :
    x ∈ regularRing p hp ↔ ∃ N d : R, ¬ p ∣ d ∧ x = algebraMap R K N / algebraMap R K d := by
  letI := Ideal.isPrime_span_singleton_of_prime hp
  change (∃ N d : R, ∃ _ : d ∈ (Ideal.span {p}).primeCompl,
    x = algebraMap R K N * (algebraMap R K d)⁻¹) ↔ _
  simp only [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, exists_prop, div_eq_mul_inv]

private theorem regular_inv (p : R) (hp : Prime p) (d : R) (hd : ¬ p ∣ d) :
    (algebraMap R K d)⁻¹ ∈ regularRing p hp := by
  exact (regular_iff p hp _).mpr ⟨1, d, hd, by simp⟩

private theorem prime_cancel_denominator (p : R) (hp : Prime p) (x : K)
    (hx : x ∈ regularRing p hp) (N B : R) (hB : B ≠ 0)
    (hrepr : x = algebraMap R K N / algebraMap R K (p * B)) :
    ∃ M : R, x = algebraMap R K M / algebraMap R K B := by
  obtain ⟨V, d, hd, hxd⟩ := (regular_iff p hp x).mp hx
  have hd0 : d ≠ 0 := fun h => hd (h ▸ dvd_zero p)
  have hdK : algebraMap R K d ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R K).ne hd0
  have hpK : algebraMap R K p ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R K).ne hp.ne_zero
  have hBK : algebraMap R K B ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R K).ne hB
  have hc : N * d = V * (p * B) := by
    apply IsFractionRing.injective R K
    simpa only [map_mul] using (div_eq_div_iff (mul_ne_zero hpK hBK) hdK).mp
      (by simpa only [map_mul] using hrepr.symm.trans hxd)
  have hpd : p ∣ N * d := by
    rw [hc]
    exact dvd_mul_of_dvd_right (dvd_mul_right p B) V
  obtain ⟨M, hM⟩ := (hp.dvd_or_dvd hpd).resolve_right hd
  refine ⟨M, ?_⟩
  rw [hrepr, hM, map_mul, map_mul]
  exact mul_div_mul_left _ _ hpK

private theorem list_denominator_descent (s : Set R) (hs : ∀ p ∈ s, Prime p)
    (x : K) (hx : ∀ p (hp : p ∈ s), x ∈ regularRing p (hs p hp))
    (l : List R) (hl : ∀ p ∈ l, p ∈ s) (N : R)
    (h : x = algebraMap R K N / algebraMap R K l.prod) :
    ∃ M : R, x = algebraMap R K M := by
  induction l generalizing N with
  | nil => exact ⟨N, by simpa using h⟩
  | cons p l ih =>
    have hps : p ∈ s := hl p (by simp)
    have hp : Prime p := hs p hps
    have htail : ∀ r ∈ l, r ∈ s := fun r hr => hl r (by simp [hr])
    have hprod : l.prod ≠ 0 := List.prod_ne_zero (fun hzero => (hs 0 (htail 0 hzero)).ne_zero rfl)
    obtain ⟨M, hM⟩ := prime_cancel_denominator p hp x (hx p hps) N l.prod hprod
      (by simpa using h)
    exact ih htail M hM

theorem closureLeNonzero (s : Set R) (hs : ∀ p ∈ s, p ≠ 0) :
    Submonoid.closure s ≤ nonZeroDivisors R := by
  apply Submonoid.closure_le.mpr
  intro p hp
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (hs p hp)

private theorem localization_descent (s : Set R) (hs : ∀ p ∈ s, Prime p)
    (x : K) (hx : x ∈ Localization.subalgebra.ofField K (Submonoid.closure s)
      (closureLeNonzero s (fun p hp => (hs p hp).ne_zero)))
    (hlocal : ∀ p (hp : p ∈ s), x ∈ regularRing p (hs p hp)) :
    ∃ M : R, x = algebraMap R K M := by
  obtain ⟨N, d, hd, hxd⟩ := hx
  obtain ⟨l, hl, hld⟩ := Submonoid.exists_list_of_mem_closure hd
  exact list_denominator_descent s hs x hlocal l hl N
    (by simpa only [hld, div_eq_mul_inv] using hxd)

end D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore
variable {K : Type*} [Field K]
open PowerSeries

private theorem coeff_product_mem (T : Subring K) (f g : PowerSeries K) (n : ℕ)
    (hf : ∀ i ≤ n, coeff i f ∈ T) (hg : ∀ i ≤ n, coeff i g ∈ T) :
    coeff n (f * g) ∈ T := by
  rw [coeff_mul]
  apply T.sum_mem
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  exact T.mul_mem (hf ij.1 (by omega)) (hg ij.2 (by omega))

private theorem recurrence_coefficients_mem (T : Subring K)
    (H : ℕ → PowerSeries K) (b alpha ell : ℕ → K)
    (hb : ∀ m, b m ∈ T) (halpha : ∀ m, alpha m ∈ T) (hell : ∀ m, ell m ∈ T)
    (heq : ∀ m, H m = 1 + C (b m) * X ^ 1 * H m +
      (C (alpha m) * X + C (ell m) * X ^ 2) * (H (m + 1) * H m)) :
    ∀ n m : ℕ, coeff n (H m) ∈ T := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m
    have h := congrArg (coeff n) (heq m)
    by_cases hn : n = 0
    · subst n
      have hz : coeff 0 (H m) = 1 := by simpa [coeff_X_pow_mul'] using h
      rw [hz]
      exact T.one_mem
    · have hprod (d : ℕ) (hd : d < n) : coeff d (H (m + 1) * H m) ∈ T :=
        coeff_product_mem T _ _ d (fun i hi => ih i (by omega) (m + 1))
          (fun i hi => ih i (by omega) m)
      have hX (f : PowerSeries K) : coeff n (X * f) = if 1 ≤ n then coeff (n - 1) f else 0 := by
        simpa only [pow_one] using coeff_X_pow_mul' f 1 n
      rw [h]
      simp only [map_add, add_mul, mul_assoc, coeff_C_mul, coeff_X_pow_mul', hX,
        coeff_one, hn, ite_false, zero_add]
      apply T.add_mem
      · apply T.mul_mem (hb m)
        split_ifs with h1
        · exact ih (n - 1) (by omega) m
        · exact T.zero_mem
      · apply T.add_mem
        · apply T.mul_mem (halpha m)
          split_ifs with h1
          · exact hprod (n - 1) (by omega)
          · exact T.zero_mem
        · apply T.mul_mem (hell m)
          split_ifs with h2
          · exact hprod (n - 2) (by omega)
          · exact T.zero_mem

private theorem quotient_recurrence (u : ℕ → PowerSeries K) (b alpha ell : ℕ → K)
    (h0 : ∀ m, constantCoeff (u m) = 1)
    (heq : ∀ m, u m = (1 - C (b m) * X) * u (m + 1) -
      (C (alpha m) * X + C (ell m) * X ^ 2) * u (m + 2)) :
    ∀ m, let H := fun j => u (j + 1) * (u j)⁻¹
      H m = 1 + C (b m) * X ^ 1 * H m +
        (C (alpha m) * X + C (ell m) * X ^ 2) * (H (m + 1) * H m) := by
  intro m
  dsimp only
  have h0m : constantCoeff (u m) ≠ 0 := ne_zero_of_eq_one (h0 m)
  have h0s : constantCoeff (u (m + 1)) ≠ 0 := ne_zero_of_eq_one (h0 (m + 1))
  have hcross : (u (m + 2) * (u (m + 1))⁻¹) * (u (m + 1) * (u m)⁻¹) =
      u (m + 2) * (u m)⁻¹ := by
    calc
      _ = u (m + 2) * ((u (m + 1))⁻¹ * u (m + 1)) * (u m)⁻¹ := by ring
      _ = _ := by rw [PowerSeries.inv_mul_cancel _ h0s, mul_one]
  rw [show m + 1 + 1 = m + 2 by omega, hcross]
  have hmul := congrArg (fun t : PowerSeries K => t * (u m)⁻¹) (heq m)
  rw [PowerSeries.mul_inv_cancel _ h0m] at hmul
  linear_combination -hmul

theorem quotient_coefficients_mem (T : Subring K) (u : ℕ → PowerSeries K) (b alpha ell : ℕ → K)
    (h0 : ∀ m, constantCoeff (u m) = 1)
    (hb : ∀ m, b m ∈ T) (halpha : ∀ m, alpha m ∈ T) (hell : ∀ m, ell m ∈ T)
    (heq : ∀ m, u m = (1 - C (b m) * X) * u (m + 1) -
      (C (alpha m) * X + C (ell m) * X ^ 2) * u (m + 2)) :
    ∀ n m : ℕ, coeff n (u (m + 1) * (u m)⁻¹) ∈ T := by
  exact recurrence_coefficients_mem T _ b alpha ell hb halpha hell
    (quotient_recurrence u b alpha ell h0 heq)

end D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore
open PowerSeries

private theorem qsf_zero (u v : (FractionRing (MvPolynomial (Fin 4) ℤ))) : qShiftedFactorial u v 0 = 1 := by
  simp [qShiftedFactorial]

private theorem qsf_succ (u v : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ) :
    qShiftedFactorial u v (n + 1) = qShiftedFactorial u v n * (1 - u * v ^ n) := by
  exact Finset.prod_range_succ (fun j => 1 - u * v ^ j) n

private theorem qsf_shift (u v : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ) :
    qShiftedFactorial u v (n + 1) = (1 - u) * qShiftedFactorial (u * v) v n := by
  unfold qShiftedFactorial
  rw [Finset.prod_range_succ', mul_comm]
  simp only [pow_zero, mul_one]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [pow_succ']
  ring

private theorem qsf_shift_ratio (u v : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ) (hu : 1 - u ≠ 0) :
    qShiftedFactorial (u * v) v n =
      qShiftedFactorial u v n * (1 - u * v ^ n) / (1 - u) := by
  apply (eq_div_iff hu).mpr
  rw [mul_comm, ← qsf_shift, qsf_succ]

private theorem qsf_nonzero (U Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (hU : ∀ m : ℕ, 1 - U * Q ^ m ≠ 0) (n : ℕ) :
    qShiftedFactorial U Q n ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hU i)

theorem F_constant (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) : constantCoeff (F A B C Q) = 1 := by
  simp [F, constantCoeff_mk, qsf_zero]

theorem coeff_F_succ (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ) :
    coeff (n + 1) (F A B C Q) = coeff n (F A B C Q) *
      ((1 - A * Q ^ n) * (1 - B * Q ^ n)) /
      ((1 - C * Q ^ n) * (1 - Q ^ (n + 1))) := by
  simp only [F, coeff_mk, qsf_succ, pow_succ', div_eq_mul_inv, mul_inv_rev]
  ring

private theorem coeff_shift_ac (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ) (ha : 1 - A ≠ 0)
    (hc : ∀ m : ℕ, 1 - C * Q ^ m ≠ 0)
    (hq : ∀ m : ℕ, 1 - Q ^ (m + 1) ≠ 0) :
    coeff n (F (A * Q) B (C * Q) Q) = coeff n (F A B C Q) *
      ((1 - A * Q ^ n) * (1 - C)) / ((1 - A) * (1 - C * Q ^ n)) := by
  have hc0 : 1 - C ≠ 0 := by simpa using hc 0
  have hqsf : qShiftedFactorial Q Q n ≠ 0 :=
    qsf_nonzero Q Q (fun j => by simpa only [pow_succ'] using hq j) n
  simp only [F, coeff_mk, qsf_shift_ratio A Q n ha, qsf_shift_ratio C Q n hc0]
  field_simp [ha, hc0, hc n, qsf_nonzero C Q hc n, hqsf]
  <;> ring

theorem coeff_shift_abc (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ) (ha : 1 - A ≠ 0) (hb : 1 - B ≠ 0)
    (hc : ∀ m : ℕ, 1 - C * Q ^ m ≠ 0)
    (hq : ∀ m : ℕ, 1 - Q ^ (m + 1) ≠ 0) :
    coeff n (F (A * Q) (B * Q) (C * Q) Q) = coeff n (F A B C Q) *
      ((1 - A * Q ^ n) * (1 - B * Q ^ n) * (1 - C)) /
      ((1 - A) * (1 - B) * (1 - C * Q ^ n)) := by
  have hc0 : 1 - C ≠ 0 := by simpa using hc 0
  have hqsf : qShiftedFactorial Q Q n ≠ 0 :=
    qsf_nonzero Q Q (fun j => by simpa only [pow_succ'] using hq j) n
  simp only [F, coeff_mk, qsf_shift_ratio A Q n ha, qsf_shift_ratio B Q n hb,
    qsf_shift_ratio C Q n hc0]
  field_simp [ha, hb, hc0, hc n, qsf_nonzero C Q hc n, hqsf]
  <;> ring

private theorem coeff_shift_abcc (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ) (ha : 1 - A ≠ 0) (hb : 1 - B ≠ 0)
    (hc : ∀ m : ℕ, 1 - C * Q ^ m ≠ 0)
    (hq : ∀ m : ℕ, 1 - Q ^ (m + 1) ≠ 0) :
    coeff n (F (A * Q) (B * Q) (C * Q ^ 2) Q) = coeff n (F A B C Q) *
      ((1 - A * Q ^ n) * (1 - B * Q ^ n) * (1 - C) * (1 - C * Q)) /
      ((1 - A) * (1 - B) * (1 - C * Q ^ n) * (1 - C * Q ^ (n + 1))) := by
  have hc0 : 1 - C ≠ 0 := by simpa using hc 0
  have hc1 : 1 - C * Q ≠ 0 := by simpa using hc 1
  have hqsf : qShiftedFactorial Q Q n ≠ 0 :=
    qsf_nonzero Q Q (fun j => by simpa only [pow_succ'] using hq j) n
  rw [show C * Q ^ 2 = (C * Q) * Q by ring]
  simp only [F, coeff_mk, qsf_shift_ratio A Q n ha, qsf_shift_ratio B Q n hb,
    qsf_shift_ratio (C * Q) Q n hc1, qsf_shift_ratio C Q n hc0]
  have hp : C * Q * Q ^ n = C * Q ^ (n + 1) := by rw [pow_succ']; ring
  rw [hp]
  field_simp [ha, hb, hc0, hc1, hc n, hc (n + 1), qsf_nonzero C Q hc n, hqsf]
  <;> ring

theorem heine_contiguous (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (ha : 1 - A ≠ 0) (hb : 1 - B ≠ 0)
    (hc : ∀ m : ℕ, 1 - C * Q ^ m ≠ 0)
    (hq : ∀ m : ℕ, 1 - Q ^ (m + 1) ≠ 0) :
    F (A * Q) B (C * Q) Q - F A B C Q =
      PowerSeries.C (((1 - B) * (A - C)) / ((1 - C) * (1 - C * Q))) * X *
        F (A * Q) (B * Q) (C * Q ^ 2) Q := by
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, F_constant]
  | succ n =>
    simp only [map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul]
    simp only [coeff_shift_ac A B C Q (n + 1) ha hc hq, coeff_F_succ,
      coeff_shift_abcc A B C Q n ha hb hc hq]
    have hc0 : 1 - C ≠ 0 := by simpa using hc 0
    have hc1 : 1 - C * Q ≠ 0 := by simpa using hc 1
    field_simp [ha, hb, hc0, hc1, hc n, hc (n + 1), hq n]
    <;> ring

end D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore
open PowerSeries

def S : Subalgebra (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  Localization.subalgebra.ofField (FractionRing (MvPolynomial (Fin 4) ℤ)) (Submonoid.closure (Set.range p))
    (closureLeNonzero (Set.range p) nonzeroFamily)


theorem S_inv_p (k : ℕ) : (1 - c * q ^ k)⁻¹ ∈ S := by
  change ∃ N d : (MvPolynomial (Fin 4) ℤ), ∃ _ : d ∈ Submonoid.closure (Set.range p),
    (1 - c * q ^ k)⁻¹ = algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) N * (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) d)⁻¹
  exact ⟨1, p k, Submonoid.subset_closure ⟨k, rfl⟩, by simp [map_p]⟩

private theorem T_inv_p (k j : ℕ) (hkj : k ≠ j) : (1 - c * q ^ j)⁻¹ ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by
  simpa only [ map_p] using regular_inv (K := (FractionRing (MvPolynomial (Fin 4) ℤ))) (p k) (pPrime k) (p j) (p_not_dvd_p k j hkj)

private theorem qsf_mem (U Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (V : Subring (FractionRing (MvPolynomial (Fin 4) ℤ))) (hU : U ∈ V) (hQ : Q ∈ V) (n : ℕ) :
    qShiftedFactorial U Q n ∈ V := by
  exact V.prod_mem (fun j _ => V.sub_mem V.one_mem (V.mul_mem hU (V.pow_mem hQ j)))

private theorem qsf_lower_product (m n : ℕ) :
    qShiftedFactorial (c * q ^ m) q n =
      ∏ j ∈ Finset.Ico m (m + n), (1 - c * q ^ j) := by
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel_left, qShiftedFactorial]
  apply Finset.prod_congr rfl
  intro j hj
  rw [pow_add]
  ring

private theorem T_inv_product (k : ℕ) (s : Finset ℕ) (hk : k ∉ s) :
    (∏ j ∈ s, (1 - c * q ^ j))⁻¹ ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by
  rw [← Finset.prod_inv_distrib]
  exact ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).prod_mem (fun j hj => T_inv_p k j (fun h => hk (h ▸ hj)))

private theorem T_simple_inv_product (k : ℕ) (s : Finset ℕ) :
    (1 - c * q ^ k) * (∏ j ∈ s, (1 - c * q ^ j))⁻¹ ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by
  by_cases hk : k ∈ s
  · have hp0 : 1 - c * q ^ k ≠ 0 := by
      simpa only [map_p, map_zero] using (IsFractionRing.injective (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ))).ne (pPrime k).ne_zero
    have hi := T_inv_product k (s.erase k) (Finset.notMem_erase k s)
    rw [← Finset.mul_prod_erase s (fun j => 1 - c * q ^ j) hk, mul_inv_rev]
    rw [mul_left_comm, mul_inv_cancel₀ hp0, mul_one]
    exact hi
  · exact ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem (by rw [← map_p]; exact ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem _) (T_inv_product k s hk)

private theorem T_inv_qsf_q (k n : ℕ) : (qShiftedFactorial q q n)⁻¹ ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by
  unfold qShiftedFactorial
  rw [← Finset.prod_inv_distrib]
  apply ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).prod_mem
  intro j hj
  have h := regular_inv (K := (FractionRing (MvPolynomial (Fin 4) ℤ))) (p k) (pPrime k) (1 - MvPolynomial.X 3 ^ (j + 1) : (MvPolynomial (Fin 4) ℤ))
    (p_not_dvd_one_sub_q k (j + 1) (by omega))
  simpa only [ map_sub, map_one, map_mul, map_pow, q, pow_succ'] using h

private theorem T_F_simple (A B : (MvPolynomial (Fin 4) ℤ)) (m k n : ℕ) :
    Bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring (1 - c * q ^ k) 1
      (coeff n (F (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) A) (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) B) (c * q ^ m) q)) := by
  have hnum := ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem
      (qsf_mem (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) A) q ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem A) (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem (MvPolynomial.X 3)) n)
      (qsf_mem (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) B) q ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem B) (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem (MvPolynomial.X 3)) n)
  have hden := T_simple_inv_product k (Finset.Ico m (m + n))
  rw [← qsf_lower_product] at hden
  have hmem := ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem hnum (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem hden (T_inv_qsf_q k n))
  unfold Bound
  rw [Subalgebra.mem_toSubring]
  convert hmem using 1 <;> simp only [pow_one, F, coeff_mk, div_eq_mul_inv, mul_inv_rev] <;> ring

private theorem T_F_regular (A B : (MvPolynomial (Fin 4) ℤ)) (m k n : ℕ) (hk : k ∉ Finset.Ico m (m + n)) :
    coeff n (F (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) A) (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) B) (c * q ^ m) q) ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by
  have hnum := ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem
      (qsf_mem (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) A) q ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem A) (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem (MvPolynomial.X 3)) n)
      (qsf_mem (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) B) q ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem B) (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem (MvPolynomial.X 3)) n)
  have hden := T_inv_product k (Finset.Ico m (m + n)) hk
  rw [← qsf_lower_product] at hden
  have hmem := ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem hnum (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem hden (T_inv_qsf_q k n))
  convert hmem using 1 <;> simp only [F, coeff_mk, div_eq_mul_inv, mul_inv_rev] <;> ring

/-- The ratio with an arbitrary polynomial numerator and a single lower-parameter shift. -/
def ratio (A B Aprime Bprime : (MvPolynomial (Fin 4) ℤ)) : PowerSeries (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  F (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) Aprime) (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) Bprime) (c * q) q *
    (F (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) A) (algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) B) c q)⁻¹

private theorem ratio_local_bound (A B Aprime Bprime : (MvPolynomial (Fin 4) ℤ)) (k : ℕ) :
    ∀ n, Bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring (1 - c * q ^ k) ((n + 1) / (k + 1))
      (coeff n (ratio A B Aprime Bprime)) := by
  have hp : 1 - c * q ^ k ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by rw [← map_p]; exact ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem _
  apply ratio_floor_bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring _ hp (k + 1) 1 _ _ (F_constant _ _ _ _)
  · apply simple_onset_floor_bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring _ hp (k + 1) 0 (by omega)
    · simpa using T_F_simple A B 0 k
    · intro n hn
      simpa only [pow_zero, mul_one, Subalgebra.mem_toSubring] using T_F_regular A B 0 k n (by
        simp only [Finset.mem_Ico, not_and_or]
        omega)
  · apply simple_onset_floor_bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).toSubring _ hp (k + 1) 1 (by omega)
    · simpa using T_F_simple Aprime Bprime 1 k
    · intro n hn
      simpa only [pow_one, Subalgebra.mem_toSubring] using T_F_regular Aprime Bprime 1 k n (by
        simp only [Finset.mem_Ico, not_and_or]
        omega)

private theorem ratio_local_zero_bound (A B Aprime Bprime : (MvPolynomial (Fin 4) ℤ)) :
    ∀ n, Bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) 0).toSubring (1 - c) n (coeff n (ratio A B Aprime Bprime)) := by
  have hp : 1 - c ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) 0 := by
    simpa only [map_p, pow_zero, mul_one] using ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) 0).algebraMap_mem (p 0)
  suffices ∀ n, Bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) 0).toSubring (1 - c) (n / 1) (coeff n (ratio A B Aprime Bprime)) by simpa using this
  apply ratio_floor_bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) 0).toSubring _ hp 1 0 _ _ (F_constant _ _ _ _)
  · apply simple_onset_floor_bound ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) 0).toSubring _ hp 1 0 (by omega)
    · simpa using T_F_simple A B 0 0
    · intro n hn
      simpa only [pow_zero, mul_one, Subalgebra.mem_toSubring] using T_F_regular A B 0 0 n (by
        simp only [Finset.mem_Ico]
        omega)
  · intro n
    apply bound_mono ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) 0).toSubring _ hp (Nat.zero_le _)
    simpa only [Bound, pow_zero, one_mul, pow_one, Subalgebra.mem_toSubring] using
      T_F_regular Aprime Bprime 1 0 n (by simp)


private theorem D_eq_map (n : ℕ) : D n = algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) ((fun n : ℕ => ∏ k ∈ Finset.range (n + 1), p k ^ ((n + 1) / (k + 1))) n) := by
  simp only [ map_prod, map_pow, map_p, D]

private theorem D_nonzero (n : ℕ) : D n ≠ 0 := by
  rw [D_eq_map]
  have hprod : (fun n : ℕ => ∏ k ∈ Finset.range (n + 1), p k ^ ((n + 1) / (k + 1))) n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (pPrime k).ne_zero)
  simpa only [map_zero] using (IsFractionRing.injective (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ))).ne hprod

private theorem D_factor (n k : ℕ) (hk : k ≤ n) :
    D n = (1 - c * q ^ k) ^ ((n + 1) / (k + 1)) *
      ∏ j ∈ (Finset.range (n + 1)).erase k, (1 - c * q ^ j) ^ ((n + 1) / (j + 1)) := by
  exact (Finset.mul_prod_erase (Finset.range (n + 1))
    (fun j => (1 - c * q ^ j) ^ ((n + 1) / (j + 1))) (by simpa using hk)).symm

private theorem cleared_ratio_local (A B Aprime Bprime : (MvPolynomial (Fin 4) ℤ)) (n k : ℕ) :
    D n * coeff n (ratio A B Aprime Bprime) / (1 - c) ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by
  have hrest : (∏ j ∈ (Finset.range (n + 1)).erase k,
      (1 - c * q ^ j) ^ ((n + 1) / (j + 1))) ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by
    apply ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).prod_mem
    intro j hj
    apply ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).pow_mem
    rw [← map_p]
    exact ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem _
  by_cases hk0 : k = 0
  · subst k
    have hp0 : 1 - c ≠ 0 := by
      simpa only [c, pow_zero, mul_one] using variable_factor_ne_zero 2 3 0
    have hb := ratio_local_zero_bound A B Aprime Bprime n
    have heq : D n * coeff n (ratio A B Aprime Bprime) / (1 - c) =
        (∏ j ∈ (Finset.range (n + 1)).erase 0,
          (1 - c * q ^ j) ^ ((n + 1) / (j + 1))) *
        ((1 - c) ^ n * coeff n (ratio A B Aprime Bprime)) := by
      rw [D_factor n 0 (Nat.zero_le _)]
      simp only [Nat.zero_add, Nat.div_one, pow_zero, mul_one, pow_succ]
      field_simp [hp0]
      <;> ring
    rw [heq]
    exact ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) 0).mul_mem hrest hb
  · have hinv : (1 - c)⁻¹ ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by simpa using T_inv_p k 0 hk0
    by_cases hkn : k ≤ n
    · have hb := ratio_local_bound A B Aprime Bprime k n
      have hm := ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem hrest hb) hinv
      convert hm using 1 <;> rw [D_factor n k hkn] <;> simp only [Bound, div_eq_mul_inv] <;> ring
    · have hd : (n + 1) / (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
      have hb := ratio_local_bound A B Aprime Bprime k n
      simp only [hd, Bound, pow_zero, one_mul] at hb
      have hD : D n ∈ (fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k := by rw [D_eq_map]; exact ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).algebraMap_mem _
      simpa only [div_eq_mul_inv] using ((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem (((fun k : ℕ => regularRing (K := FractionRing (MvPolynomial (Fin 4) ℤ)) (p k) (pPrime k)) k).mul_mem hD hb) hinv

theorem denominator_from_localization (A B Aprime Bprime : (MvPolynomial (Fin 4) ℤ))
    (hS : ∀ n : ℕ, coeff n (ratio A B Aprime Bprime) ∈ S) :
    ∀ n : ℕ, ∃ P : (MvPolynomial (Fin 4) ℤ),
      coeff n (ratio A B Aprime Bprime) / (1 - c) = algebraMap (MvPolynomial (Fin 4) ℤ) (FractionRing (MvPolynomial (Fin 4) ℤ)) P / D n := by
  intro n
  have hD : D n ∈ S := by rw [D_eq_map]; exact S.algebraMap_mem _
  have h0 : (1 - c)⁻¹ ∈ S := by simpa using S_inv_p 0
  have hHS : D n * coeff n (ratio A B Aprime Bprime) / (1 - c) ∈ S := by
    simpa only [div_eq_mul_inv] using S.mul_mem (S.mul_mem hD (hS n)) h0
  obtain ⟨P, hP⟩ := localization_descent (Set.range p)
    (by rintro _ ⟨k, rfl⟩; exact pPrime k)
    (D n * coeff n (ratio A B Aprime Bprime) / (1 - c)) hHS
    (by rintro _ ⟨k, rfl⟩; exact cleared_ratio_local A B Aprime Bprime n k)
  refine ⟨P, (eq_div_iff (D_nonzero n)).mpr ?_⟩
  rw [← hP]
  simp only [div_eq_mul_inv]
  ring

end D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

end
