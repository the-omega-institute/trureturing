/- GID: D5/S1/Recurrence/MatharA379464/Result
   generality: I
   mirror-B: D5/B/S1/Recurrence/MatharA379464/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal A379464 path count satisfies Mathar's eight-term recurrence. -/


/-
Public declarations:
  E, L, recurrence, geom, param, transform, b: proof_shape: bind-only (definitions); consumers: coefficient and certificate identities.
  coeff_L: proof_shape: bind-only; escape_witness: none; consumer: result_of_certificate.
  forcing_zero: proof_shape: bind-only; escape_witness: none; consumer: result_of_certificate.
  transform_coefficients: proof_shape: bind-only; escape_witness: none; consumer: literal_certificate.
  explicit_series_certificate: proof_shape: bind-only; escape_witness: none; consumer: literal_certificate.
  literal_certificate: proof_shape: content; escape_witness: MatharA379464Counting.three_positive_rotations; consumer: result.
  claim: proof_shape: bind-only; escape_witness: none; consumer: result.
  result: proof_shape: content; escape_witness: MatharA379464Counting.three_positive_rotations.
Private theorem classifications: coefficient, substitution, conjugation and factorial helpers are bind-only and consumed by later declarations; literal_certificate is consumed by result.
admission_basis: open-problem-resolution (#22234; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25538.
Direct frozen dependencies: A308815DFiniteRecurrence.euler_coeff and HannaDiagonalDerivativeParity.euler.
Euler differentiation uses HannaDiagonalDerivativeParity.euler directly; the claim retains the source's integer polynomials and natural index subtraction.
All declarations quantify over unbounded indices or formal series; utility: none.
-/

import D5.S1.Recurrence.A308815DFiniteRecurrence
import D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity
import D5.S1.Words.LatticePaths.MatharA379464Counting

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace D5.S1.Recurrence.MatharA379464.Result
open D5.S1.Recurrence.A308815DFiniteRecurrence (euler_coeff)
open D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity (euler)
open D5.S1.Words.LatticePaths.MatharA379464Counting
open PowerSeries
open scoped BigOperators
noncomputable section

def E (f : (PowerSeries ℚ)) : (PowerSeries ℚ) := X * (1-X) * derivative f - X*f

def L (f : (PowerSeries ℚ)) : (PowerSeries ℚ) :=
  (1-X)^4 * (C 27*E (E (E f)) + C 216*E (E f) + C 528*E f + C 384*f) -
  C 256*(X^4 * (E (E (E f)) + C 14*E (E f) + C 63*E f + C 90*f))

private theorem E_coeff_succ (f : (PowerSeries ℚ)) (n : ℕ) :
    coeff (n+1) (E f) = (n+1 : ℚ)*(coeff (n+1) f - coeff n f) := by
  have h : E f = X * derivative f - X*(X * derivative f) - X*f := by
    dsimp [E]; ring
  rw [h, map_sub, map_sub, euler_coeff, coeff_succ_X_mul, euler_coeff,
    coeff_succ_X_mul]
  push_cast
  ring

private theorem E2_coeff (f : (PowerSeries ℚ)) (n : ℕ) :
    coeff (n+2) (E (E f)) =
      (n+2 : ℚ)^2 * coeff (n+2) f -
      (n+2 : ℚ)*(2*n+3) * coeff (n+1) f +
      (n+1 : ℚ)*(n+2) * coeff n f := by
  rw [show n+2 = (n+1)+1 by omega, E_coeff_succ, E_coeff_succ, E_coeff_succ]
  push_cast
  ring

private theorem E3_coeff (f : (PowerSeries ℚ)) (n : ℕ) :
    coeff (n+3) (E (E (E f))) =
      (n+3 : ℚ)^3 * coeff (n+3) f -
      (n+3 : ℚ)*(3*(n+2)^2+3*(n+2)+1) * coeff (n+2) f +
      3*(n+2 : ℚ)^2*(n+3) * coeff (n+1) f -
      (n+1 : ℚ)*(n+2)*(n+3) * coeff n f := by
  rw [show n+3 = (n+2)+1 by omega, E_coeff_succ,
    show n+2+1 = (n+1)+2 by omega, E2_coeff,
    E2_coeff]
  push_cast
  ring

private theorem E_coeff_at (f : (PowerSeries ℚ)) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (E f) = (n : ℚ)*(coeff n f - coeff (n-1) f) := by
  have h := E_coeff_succ f (n-1)
  rw [show n-1+1 = n by omega] at h
  have hc : ((n-1 : ℕ) : ℚ) = (n : ℚ)-1 := by exact Nat.cast_sub hn
  rw [hc] at h
  linear_combination h

private theorem E2_coeff_at (f : (PowerSeries ℚ)) (n : ℕ) (hn : 2 ≤ n) :
    coeff n (E (E f)) =
      (n : ℚ)^2 * coeff n f -
      (n : ℚ)*(2*n-1) * coeff (n-1) f +
      (n : ℚ)*(n-1) * coeff (n-2) f := by
  have h := E2_coeff f (n-2)
  rw [show n-2+2 = n by omega, show n-2+1 = n-1 by omega] at h
  have hc : ((n-2 : ℕ) : ℚ) = (n : ℚ)-2 := by exact Nat.cast_sub hn
  rw [hc] at h
  linear_combination h

private theorem E3_coeff_at (f : (PowerSeries ℚ)) (n : ℕ) (hn : 3 ≤ n) :
    coeff n (E (E (E f))) =
      (n : ℚ)^3 * coeff n f -
      (n : ℚ)*(3*n^2-3*n+1) * coeff (n-1) f +
      3*(n : ℚ)*(n-1)^2 * coeff (n-2) f -
      (n : ℚ)*(n-1)*(n-2) * coeff (n-3) f := by
  have h := E3_coeff f (n-3)
  rw [show n-3+3 = n by omega, show n-3+2 = n-1 by omega,
    show n-3+1 = n-2 by omega] at h
  have hc : ((n-3 : ℕ) : ℚ) = (n : ℚ)-3 := by exact Nat.cast_sub hn
  rw [hc] at h
  linear_combination h

def recurrence (v : ℕ → ℚ) (n : ℕ) : ℚ :=
    3 * ((n : ℚ) + 4) * (3 * (n : ℚ) + 4) * (3 * (n : ℚ) + 8) * v n +
    3 * (-63 * (n : ℚ)^3 - 297 * (n : ℚ)^2 - 349 * (n : ℚ) - 60) * v (n - 1) +
    3 * (189 * (n : ℚ)^3 + 270 * (n : ℚ)^2 - 229 * (n : ℚ) - 140) * v (n - 2) +
    15 * (-63 * (n : ℚ)^3 + 117 * (n : ℚ)^2 + 44 * (n : ℚ) - 64) * v (n - 3) +
    (689 * (n : ℚ)^3 - 5372 * (n : ℚ)^2 + 6946 * (n : ℚ) - 1288) * v (n - 4) +
    ((n : ℚ) - 4) * (201 * (n : ℚ)^2 + 2767 * (n : ℚ) - 3011) * v (n - 5) -
    ((n : ℚ) - 5) * (579 * (n : ℚ) + 257) * ((n : ℚ) - 4) * v (n - 6) +
    229 * ((n : ℚ) - 5) * ((n : ℚ) - 6) * ((n : ℚ) - 4) * v (n - 7)

theorem coeff_L (f : (PowerSeries ℚ)) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (L f) = recurrence (fun i => coeff i f) n := by
  have pow4 (g : (PowerSeries ℚ)) : (1-X)^4*g =
      g - C 4*(X^1*g) + C 6*(X^2*g) - C 4*(X^3*g) + X^4*g := by norm_num only [map_ofNat]; ring
  rw [L, pow4]
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul',
    if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
    if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega)]
  simp only [E3_coeff_at f n (by omega), E3_coeff_at f (n-1) (by omega),
    E3_coeff_at f (n-2) (by omega), E3_coeff_at f (n-3) (by omega),
    E3_coeff_at f (n-4) (by omega),
    E2_coeff_at f n (by omega), E2_coeff_at f (n-1) (by omega),
    E2_coeff_at f (n-2) (by omega), E2_coeff_at f (n-3) (by omega),
    E2_coeff_at f (n-4) (by omega),
    E_coeff_at f n (by omega), E_coeff_at f (n-1) (by omega),
    E_coeff_at f (n-2) (by omega), E_coeff_at f (n-3) (by omega),
    E_coeff_at f (n-4) (by omega),
    Nat.sub_sub, Nat.reduceAdd,
    Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega),
    Nat.cast_one, Nat.cast_ofNat]
  dsimp [recurrence]
  ring

theorem forcing_zero (n : ℕ) (hn : 7 ≤ n) :
    coeff n (C 384*(1-X : (PowerSeries ℚ))^3) = 0 := by
  have hp : (1-X : (PowerSeries ℚ))^3 = 1-C 3*X+C 3*X^2-X^3 := by norm_num only [map_ofNat]; ring
  rw [hp]
  simp [coeff_X, coeff_X_pow, show n ≠ 0 by omega, show n ≠ 1 by omega,
    show n ≠ 2 by omega, show n ≠ 3 by omega]

private theorem E_C_mul (r : ℚ) (f : (PowerSeries ℚ)) : E (C r*f) = C r*E f := by
  simp only [E, Derivation.leibniz, derivative_C, zero_mul, zero_add]
  ring

def geom : (PowerSeries ℚ) := PowerSeries.mk (1 : ℕ → ℚ)
def param : (PowerSeries ℚ) := (X*geom)^4
def transform (f : (PowerSeries ℚ)) : (PowerSeries ℚ) := geom*subst param f

private def baseOperator (f : (PowerSeries ℚ)) : (PowerSeries ℚ) :=
  C 27*euler (euler (euler f)) + C 54*euler (euler f) + C 33*euler f + C 6*f -
  X*(C 256*euler (euler (euler f)) + C 896*euler (euler f) + C 1008*euler f + C 360*f)

private theorem geom_inverse : geom*(1-X) = 1 := by
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ

private theorem geom_derivative : derivative geom = geom^2 := by
  have hd := congrArg (derivative (R := ℚ)) geom_inverse
  simp only [Derivation.leibniz, map_sub, derivative_one, derivative_X,
    zero_sub, mul_neg, mul_one] at hd
  linear_combination geom*hd - derivative geom*(geom_inverse)

private theorem param_zero : constantCoeff param = 0 := by simp [param]

private theorem param_differential : X*(1-X)*derivative param = 4*param := by
  simp only [param, derivative_pow, Derivation.leibniz, derivative_X,
    geom_derivative, one_mul, smul_eq_mul]
  linear_combination 4*X^5*geom^4*geom_inverse

private theorem E_transform (f : (PowerSeries ℚ)) : E (transform f) = C 4*transform (euler f) := by
  have hs : HasSubst param := .of_constantCoeff_zero param_zero
  have ht : subst param (euler f) = param*subst param (derivative f) := by
    rw [euler, subst_mul hs, subst_X hs]
  simp only [E, transform, Derivation.leibniz, derivative_subst hs,
    geom_derivative, ht]
  norm_num only [map_ofNat]
  linear_combination X*geom*subst param f*geom_inverse +
    geom*subst param (derivative f)*param_differential

private theorem E2_transform (f : (PowerSeries ℚ)) : E (E (transform f)) = C 16*transform (euler (euler f)) := by
  rw [E_transform, E_C_mul, E_transform]
  rw [← mul_assoc, ← map_mul]
  norm_num

private theorem E3_transform (f : (PowerSeries ℚ)) :
    E (E (E (transform f))) = C 64*transform (euler (euler (euler f))) := by
  rw [E2_transform, E_C_mul, E_transform]
  rw [← mul_assoc, ← map_mul]
  norm_num

private theorem conjugated_operator (f : (PowerSeries ℚ)) :
    L (transform f) = C 64*(1-X)^4*geom*subst param (baseOperator f) := by
  have hs : HasSubst param := .of_constantCoeff_zero param_zero
  have hp : (1-X)^4*param = X^4 := by
    dsimp [param]
    have hg := congrArg (fun f : (PowerSeries ℚ) => f^4) geom_inverse
    linear_combination X^4*hg
  unfold L
  simp_rw [E3_transform, E2_transform, E_transform]
  simp only [transform, baseOperator, subst_sub hs, subst_add hs, subst_mul hs, subst_C,
    subst_X hs]
  norm_num only [map_ofNat]
  linear_combination
    64*geom*(256*subst param (euler (euler (euler f))) +
      896*subst param (euler (euler f)) + 1008*subst param (euler f) +
      360*subst param f)*hp

private theorem certificate_of_base (f : (PowerSeries ℚ)) (hbase : baseOperator f = C 6) :
    L (transform f) = C 384*(1-X)^3 := by
  rw [conjugated_operator, hbase, subst_C]
  norm_num only [map_ofNat]
  linear_combination 384*(1-X)^3*geom_inverse

private theorem base_of_recurrence (v : ℕ → ℚ) (hzero : v 0 = 1)
    (hrec : ∀ k : ℕ,
      3*(k+2 : ℚ)*(3*k+4)*(3*k+5)*v (k+1) =
      8*(2*k+3 : ℚ)*(4*k+3)*(4*k+5)*v k) :
    baseOperator (PowerSeries.mk v) = C 6 := by
  have ht (f : (PowerSeries ℚ)) (n : ℕ) : coeff n (euler f) = (n : ℚ)*coeff n f :=
    euler_coeff f n
  ext n
  cases n with
  | zero => simp [baseOperator, euler, hzero]
  | succ n =>
    have h := hrec n
    simp only [baseOperator, map_sub, map_add, coeff_C_mul, coeff_succ_X_mul,
      ht, coeff_mk, coeff_C, Nat.add_eq_zero_iff,
      Nat.succ_ne_zero, and_false, if_false]
    push_cast
    linear_combination h

def b (k : ℕ) : ℚ :=
  3*(Nat.factorial (4*k+2) : ℚ) /
    ((Nat.factorial k : ℚ)*(Nat.factorial (3*k+3) : ℚ))

private theorem b_zero : b 0 = 1 := by norm_num [b, Nat.factorial]

private theorem b_recurrence (k : ℕ) :
    3*(k+2 : ℚ)*(3*k+4)*(3*k+5)*b (k+1) =
      8*(2*k+3 : ℚ)*(4*k+3)*(4*k+5)*b k := by
  have h4 : (Nat.factorial (4*(k+1)+2) : ℚ) =
      (4*k+6 : ℚ)*(4*k+5)*(4*k+4)*(4*k+3)*Nat.factorial (4*k+2) := by
    rw [show 4*(k+1)+2 = (4*k+2)+1+1+1+1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have h3 : (Nat.factorial (3*(k+1)+3) : ℚ) =
      (3*k+6 : ℚ)*(3*k+5)*(3*k+4)*Nat.factorial (3*k+3) := by
    rw [show 3*(k+1)+3 = (3*k+3)+1+1+1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hf1 : (Nat.factorial (k+1) : ℚ) = (k+1 : ℚ)*Nat.factorial k := by
    rw [Nat.factorial_succ]
    push_cast
    rfl
  have hfk : (Nat.factorial k : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hfk3 : (Nat.factorial (3*k+3) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (3*k+3)
  have hk1 : (k+1 : ℚ) ≠ 0 := by exact Nat.cast_add_one_ne_zero k
  have hk4 : (3*k+4 : ℚ) ≠ 0 := by positivity
  have hk5 : (3*k+5 : ℚ) ≠ 0 := by positivity
  have hk6 : (3*k+6 : ℚ) ≠ 0 := by positivity
  dsimp [b]
  rw [h4, h3, hf1]
  field_simp
  ring

private theorem B_operator : baseOperator (PowerSeries.mk b) = C 6 :=
  base_of_recurrence b b_zero b_recurrence

theorem explicit_series_certificate :
    L (transform (PowerSeries.mk b)) = C 384*(1-X)^3 :=
  certificate_of_base (PowerSeries.mk b) B_operator

private theorem finite_substitution (f : (PowerSeries ℚ)) (j n : ℕ) (hj : j ≤ n) :
    coeff j (subst param f) =
      ∑ i ∈ Finset.range (n+1), coeff i f*coeff j (param^i) := by
  classical
  rw [coeff_subst' (.of_constantCoeff_zero param_zero)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply Finset.mem_range.mpr
  by_contra h
  have hji : j < i := by omega
  have hv : coeff j (param^i) = 0 := by
    apply coeff_of_lt_order
    exact (show (j : ENat) < (i : ENat) by exact_mod_cast hji).trans_le
      (le_order_pow_of_constantCoeff_eq_zero i param_zero)
  exact hi (by simp [hv])

private theorem coeff_mul_substitution (g f : (PowerSeries ℚ)) (n : ℕ) :
    coeff n (g*subst param f) =
      ∑ i ∈ Finset.range (n+1), coeff i f*coeff n (g*param^i) := by
  classical
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [finite_substitution f _ n (Nat.sub_le n _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem coeff_geom_param (n k : ℕ) :
    coeff n (geom*param^k) = (n.choose (4*k) : ℚ) := by
  have hp : geom*param^k = X^(4*k)*geom^(4*k+1) := by
    dsimp [param]
    rw [← pow_mul, mul_pow]
    ring
  rw [hp, coeff_X_pow_mul']
  by_cases hk : 4*k ≤ n
  · rw [if_pos hk]
    unfold geom
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add ℚ (4*k), coeff_mk,
      show 4*k+(n-4*k) = n by omega]
  · rw [if_neg hk, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

theorem transform_coefficients (f : (PowerSeries ℚ)) (n : ℕ) :
    coeff n (transform f) =
      ∑ k ∈ Finset.range (n+1), (n.choose (4*k) : ℚ)*coeff k f := by
  rw [transform, coeff_mul_substitution]
  simp_rw [coeff_geom_param]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The eight-term recurrence, for all indices where every term is defined.
Polynomial arithmetic is in ℤ; subtraction in sequence indices is in ℕ. -/
def claim : Prop :=
  ∀ n : ℕ, 7 ≤ n →
    3 * ((n : ℤ) + 4) * (3 * (n : ℤ) + 4) * (3 * (n : ℤ) + 8) * a n +
    3 * (-63 * (n : ℤ)^3 - 297 * (n : ℤ)^2 - 349 * (n : ℤ) - 60) * a (n - 1) +
    3 * (189 * (n : ℤ)^3 + 270 * (n : ℤ)^2 - 229 * (n : ℤ) - 140) * a (n - 2) +
    15 * (-63 * (n : ℤ)^3 + 117 * (n : ℤ)^2 + 44 * (n : ℤ) - 64) * a (n - 3) +
    (689 * (n : ℤ)^3 - 5372 * (n : ℤ)^2 + 6946 * (n : ℤ) - 1288) * a (n - 4) +
    ((n : ℤ) - 4) * (201 * (n : ℤ)^2 + 2767 * (n : ℤ) - 3011) * a (n - 5) -
    ((n : ℤ) - 5) * (579 * (n : ℤ) + 257) * ((n : ℤ) - 4) * a (n - 6) +
    229 * ((n : ℤ) - 5) * ((n : ℤ) - 6) * ((n : ℤ) - 4) * a (n - 7) = 0

private theorem literal_certificate :
    L (PowerSeries.mk (fun n => (a n : ℚ))) =
      PowerSeries.C 384*(1-PowerSeries.X)^3 := by
  have hs : PowerSeries.mk (fun n => (a n : ℚ)) =
      transform (PowerSeries.mk b) := by
    ext n
    rw [PowerSeries.coeff_mk, transform_coefficients]
    simp only [PowerSeries.coeff_mk]
    exact binomial_counting n
  rw [hs]
  exact explicit_series_certificate

private theorem result_of_certificate (A : (PowerSeries ℚ))
    (counting : ∀ n, coeff n A = (a n : ℚ))
    (certificate : L A = C 384*(1-X)^3) : claim := by
  intro n hn
  have h := coeff_L A n hn
  rw [certificate, forcing_zero n hn] at h
  simp only [recurrence, counting] at h
  exact_mod_cast h.symm

theorem result : claim :=
  result_of_certificate
    (PowerSeries.mk (fun n => (a n : ℚ)))
    (fun n => PowerSeries.coeff_mk n _)
    literal_certificate


end
end D5.S1.Recurrence.MatharA379464.Result
