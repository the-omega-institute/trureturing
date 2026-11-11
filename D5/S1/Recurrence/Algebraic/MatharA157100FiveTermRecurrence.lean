/- GID: D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence
   mirror-E: none(waiver:formal-power-series-proof)
   anchors: []
   utility: none
   digest: The five-term recurrence for the Catalan transform A157100. -/

import D5.S1.Recurrence.A308815DFiniteRecurrence

/-! The coefficient convention is the offset-zero generating function in OEIS A157100.
The source omits the onset; n ≥ 4 is its maximal well-formed offset-zero interpretation.
Polynomial scalars are rational; lagged sequence indices use natural subtraction.
-/

/-
admission_basis: open-problem-resolution (#29385)
proof_shape: bind-only for inhomogeneous and result; escape_witness: none.
The new definitions A, a and claim are consumed by result.
The private inhomogeneous identity is consumed by result.
Direct frozen dependencies:
  D5/S1/Recurrence/A308815DFiniteRecurrence.euler_coeff.
The original cat_ode in that same owner is exposed without changing its statement
or proof; inhomogeneous is its new live consumer. Its owner requires canonical
repinning after independent pre-freeze review.
-/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence

open PowerSeries
open D5.S1.Recurrence.A308815DFiniteRecurrence

/-- The ordinary generating function (1+X)c(X(1-X²)), with c the Catalan series. -/
noncomputable def A : PowerSeries ℚ :=
  (1 + X) * subst (X * (1 - X ^ 2))
    (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))

/-- The source sequence, starting at index zero, represented over the rationals. -/
noncomputable def a (n : ℕ) : ℚ := coeff n A

/-- The literal five-term identity on every well-formed offset-zero index. -/
def claim : Prop := ∀ n : ℕ, 4 ≤ n →
  ((n : ℚ) + 1) * a n + (-5 * (n : ℚ) + 1) * a (n - 1) +
    2 * (2 * (n : ℚ) - 1) * a (n - 2) +
    2 * (2 * (n : ℚ) - 7) * a (n - 3) +
    2 * (-2 * (n : ℚ) + 7) * a (n - 4) = 0

private theorem inhomogeneous :
    (1 - 5 * X + 4 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4) *
        (X * derivative (R := ℚ) A) +
      (1 - 4 * X + 6 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) * A =
      1 - 3 * X ^ 2 := by
  let t : PowerSeries ℚ := X * (1 - X ^ 2)
  have ht : HasSubst t := HasSubst.X'.mul_left
  have h := congrArg (substAlgHom (R := ℚ) ht) cat_ode
  simp only [map_add, map_mul, map_sub, map_one, map_ofNat, substAlgHom_X,
    coe_substAlgHom] at h
  dsimp [A]
  rw [Derivation.leibniz, derivative_subst ht]
  dsimp [t] at h ⊢
  simp only [map_add, map_sub, derivative_one, derivative_X, derivative_pow,
    Derivation.leibniz, smul_eq_mul, add_zero, zero_add, mul_one, one_mul,
    Nat.add_sub_cancel, Nat.cast_ofNat]
  linear_combination (1 - 3 * X ^ 2) * h

theorem result : claim := by
  intro n hn
  have h := congrArg (coeff n) inhomogeneous
  have hex :
      (1 - 5 * X + 4 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4) *
          (X * derivative (R := ℚ) A) +
        (1 - 4 * X + 6 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) * A =
      (X * derivative A + A) +
        C (-5) * (X ^ 1 * (X * derivative A)) + C (-4) * (X ^ 1 * A) +
        C 4 * (X ^ 2 * (X * derivative A)) + C 6 * (X ^ 2 * A) +
        C 4 * (X ^ 3 * (X * derivative A)) + C (-2) * (X ^ 3 * A) +
        C (-4) * (X ^ 4 * (X * derivative A)) + C (-2) * (X ^ 4 * A) := by
    simp only [map_neg, map_ofNat]
    ring
  rw [hex] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', euler_coeff] at h
  simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
    ite_eq_left (show 3 ≤ n by omega), ite_eq_left hn] at h
  have h2 : n ≠ 2 := by omega
  have h0 : n ≠ 0 := by omega
  simp only [coeff_one, ite_eq_right h0, coeff_ofNat_mul, coeff_X_pow,
    ite_eq_right h2, mul_zero, sub_zero] at h
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub hn, Nat.cast_one, Nat.cast_ofNat] at h
  dsimp [a]
  linear_combination h

end D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
