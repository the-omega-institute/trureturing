/- GID: D5/S3/Arith/CMJet/Prime
   generality: G
   mirror-B: none(waiver:cm-jet-native-arithmetic)
   mirror-E: none(waiver:cm-jet-native-arithmetic)
   anchors: []
   utility: none
   digest: In odd characteristic the p-fold derivative is scalar, and inert primes force it to vanish. -/

import D5.S3.Arith.CMJet.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic

/-! The restricted derivative over an odd prime field, and its vanishing at inert primes. -/

noncomputable section

namespace D5.S3.Arith.CMJet

open Polynomial Finset Function
open scoped Polynomial BigOperators

variable {A : Type*} [CommRing A]

set_option maxHeartbeats 800000 in
/-- Iterated Leibniz, with the same binomial recurrence as for polynomial derivatives. -/
lemma iter_mul (n : ℕ) (u v : Curve A) :
    iter n (u * v) =
      ∑ k ∈ range (n + 1), n.choose k • (iter (n - k) u * iter k v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hshift :
          (∑ k ∈ range (n + 1), n.choose k • (iter (n - k + 1) u * iter k v)) =
          (∑ k ∈ range (n + 1), n.choose (k + 1) • (iter (n - k) u * iter (k + 1) v)) +
            iter (n + 1) u * v := by
        rw [sum_range_succ' _ n, Nat.choose_zero_right, Nat.sub_zero, iter_zero, one_nsmul]
        congr 1
        rw [sum_range_succ, Nat.choose_succ_self, zero_nsmul, add_zero]
        apply sum_congr rfl
        intro k hk
        have h := mem_range.mp hk
        rw [show n - (k + 1) + 1 = n - k by omega]
      calc
        iter (n + 1) (u * v) =
            D A (∑ k ∈ range (n + 1), n.choose k • (iter (n - k) u * iter k v)) := by
          rw [iter_succ, ih]
        _ = (∑ k ∈ range (n + 1), n.choose k • (iter (n - k + 1) u * iter k v)) +
            ∑ k ∈ range (n + 1), n.choose k • (iter (n - k) u * iter (k + 1) v) := by
          simp only [map_sum, map_nsmul, Derivation.leibniz, smul_eq_mul, ← iter_succ,
            smul_add, sum_add_distrib, mul_comm, add_comm]
        _ = ∑ k ∈ range (n + 2), (n + 1).choose k •
            (iter ((n + 1) - k) u * iter k v) := by
          rw [hshift, sum_range_succ' _ (n + 1), Nat.choose_zero_right, Nat.sub_zero,
            iter_zero, one_nsmul]
          simp only [Nat.choose_succ_succ, Nat.succ_sub_succ, add_nsmul, sum_add_distrib]
          ac_rfl

variable {p : ℕ} [Fact p.Prime]

/-- In characteristic \(p\), all interior binomial coefficients vanish. -/
def primeIter (p : ℕ) [Fact p.Prime] : Derivation (ZMod p) (Curve (ZMod p)) (Curve (ZMod p)) :=
  Derivation.mk' (iter p) (by
    intro u v
    have hp : p.Prime := Fact.out
    have hp₁ : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    rw [iter_mul, sum_range_succ, Nat.choose_self, Nat.sub_self, iter_zero, one_nsmul]
    have hshift (f : ℕ → Curve (ZMod p)) :
        (∑ k ∈ range p, f k) = (∑ k ∈ range (p-1), f (k+1)) + f 0 := by
      simpa only [hp₁] using (sum_range_succ' f (p-1))
    rw [hshift, Nat.choose_zero_right, Nat.sub_zero, iter_zero, one_nsmul]
    have hzero : (∑ k ∈ range (p - 1), p.choose (k + 1) •
        (iter (p - (k + 1)) u * iter (k + 1) v)) = 0 := by
      apply sum_eq_zero
      intro k hk
      have hkp : k + 1 < p := by have := mem_range.mp hk; omega
      have hz : (↑(p.choose (k + 1)) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 (hp.dvd_choose_self (by omega) hkp)
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), hz, zero_smul]
    rw [hzero, zero_add]
    simp only [smul_eq_mul]
    ring)

@[simp] lemma primeIter_apply (z : Curve (ZMod p)) : primeIter p z = iter p z := rfl

lemma W_derivative : (W A).derivative = -4 * X ^ 3 := by
  simp only [W, derivative_sub, derivative_one, derivative_X_pow]
  norm_num [Polynomial.C_ofNat]

lemma poly_smul (a : A) (f : A[X]) : a • poly f = poly (a • f) := by
  ext <;> simp

lemma yPoly_smul (a : A) (f : A[X]) : a • yPoly f = yPoly (a • f) := by
  ext <;> simp

/-- The degree, the equation of the curve and commutation with \(D\) force a constant multiplier. -/
theorem prime_iter_scalar (hp₂ : 2 < p) (hodd : p % 2 = 1) :
    ∃ h : ZMod p, (∀ z : Curve (ZMod p), iter p z = h • D (ZMod p) z) ∧
      h = ((Q^[p / 2] (X : (ZMod p)[X])).derivative).coeff 0 := by
  let F : (ZMod p)[X] := (Q^[p / 2] (X : (ZMod p)[X])).derivative
  let E := primeIter p
  have hpodd : p = 2 * (p / 2) + 1 := by omega
  have hx : E (x (ZMod p)) = yPoly F := by
    change iter p (poly X) = _
    calc
      iter p (poly (X : (ZMod p)[X])) = iter (2 * (p / 2) + 1) (poly (X : (ZMod p)[X])) :=
        congrArg (fun n => iter n (poly (X : (ZMod p)[X]))) hpodd
      _ = _ := by rw [iter_succ, iter_even_poly, D_poly]
  have hy : E (y (ZMod p)) = poly (W (ZMod p) * F.derivative - 2 * X^3 * F) := by
    calc
      E (y (ZMod p)) = iter p (iter 1 (x (ZMod p))) := by rw [primeIter_apply, iter_one, D_x]
      _ = iter (p + 1) (x (ZMod p)) := (iter_add _ _ _).symm
      _ = D (ZMod p) (E (x (ZMod p))) := iter_succ _ _
      _ = _ := by rw [hx, D_yPoly]
  have hrel :
      (2 : (ZMod p)[X]) * (W (ZMod p) * F.derivative - 2 * X^3 * F) =
        (W (ZMod p)).derivative * F := by
    have h := congrArg E (y_sq (A := ZMod p))
    rw [pow_two, E.leibniz, ← poly_aeval, E.map_aeval, poly_aeval, hx, hy] at h
    have hi := congrArg QuadraticAlgebra.im h
    simp [smul_eq_mul, y] at hi
    linear_combination hi
  have h2 : (2 : (ZMod p)[X]) ≠ 0 := by
    intro h
    have h' : (2 : ZMod p) = 0 := by
      simpa [Polynomial.coeff_ofNat_zero] using
        congrArg (fun f : (ZMod p)[X] => f.coeff 0) h
    exact (Nat.not_dvd_of_pos_of_lt (by decide) hp₂) ((ZMod.natCast_eq_zero_iff 2 p).mp h')
  have hW : W (ZMod p) ≠ 0 := by
    intro h
    have := congrArg (fun f : (ZMod p)[X] => f.coeff 0) h
    simpa [W, coeff_X_pow] using this
  have hF' : F.derivative = 0 := by
    have hh : (2 : (ZMod p)[X]) * W (ZMod p) * F.derivative = 0 := by
      rw [W_derivative] at hrel
      linear_combination hrel
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero h2 hW)
  have hF : F = C (F.coeff 0) := by
    ext n
    cases n with
    | zero => simp
    | succ n =>
        rw [coeff_C, if_neg (Nat.succ_ne_zero _)]
        by_cases hn : n + 1 < p
        · have h := congrArg (fun f : (ZMod p)[X] => f.coeff n) hF'
          rw [coeff_derivative, coeff_zero] at h
          have hcast : (↑n : ZMod p) + 1 ≠ 0 := by
            intro hz
            have hz' : (↑(n + 1) : ZMod p) = 0 := by simpa using hz
            exact Nat.not_dvd_of_pos_of_lt (by omega) hn
              ((ZMod.natCast_eq_zero_iff _ _).mp hz')
          exact (mul_eq_zero.mp h).resolve_right hcast
        · dsimp [F]
          rw [coeff_derivative, Q_iter_X_degree (p / 2) _ (by omega), zero_mul]
  refine ⟨F.coeff 0, ?_, rfl⟩
  have heqX : E (x (ZMod p)) = F.coeff 0 • D (ZMod p) (x (ZMod p)) := by
    rw [hx, D_x, y, yPoly_smul, Polynomial.smul_eq_C_mul, mul_one, ← hF]
  have heqY : E (y (ZMod p)) = F.coeff 0 • D (ZMod p) (y (ZMod p)) := by
    calc
      E (y (ZMod p)) = D (ZMod p) (E (x (ZMod p))) := by
        rw [hy, hx, D_yPoly]
      _ = _ := by rw [heqX, Derivation.map_smul, D_x]
  have heqPoly (f : (ZMod p)[X]) : E (poly f) = F.coeff 0 • D (ZMod p) (poly f) := by
    simp only [← poly_aeval, E.map_aeval, (D (ZMod p)).map_aeval, heqX,
      smul_comm _ (F.coeff 0)]
  intro z
  change E z = _
  calc
    E z = E (poly z.re + y (ZMod p) * poly z.im) := congrArg E (pair_decompose z)
    _ = F.coeff 0 • D (ZMod p) (poly z.re + y (ZMod p) * poly z.im) := by
      simp only [map_add, Derivation.leibniz, heqPoly, heqY, smul_add]
      rw [smul_comm (y (ZMod p)), smul_comm (poly z.im)]
    _ = F.coeff 0 • D (ZMod p) z :=
      congrArg (fun w => F.coeff 0 • D (ZMod p) w) (pair_decompose z).symm

/-- For \(p\equiv 3\bmod 4\), the coefficient that could give a scalar is zero. -/
theorem inert_iter_zero (hp : p % 4 = 3) (z : Curve (ZMod p)) : iter p z = 0 := by
  obtain ⟨h, hall, hh⟩ := prime_iter_scalar (p := p) (by omega) (by omega)
  have hx : (Q^[p / 2] (X : (ZMod p)[X])).coeff 1 = 0 :=
    by simpa using (Q_iter_monomial_support (A := ZMod p) (p / 2) 1 1 (by omega))
  rw [hall, hh, coeff_derivative, hx, zero_mul, zero_smul]

end D5.S3.Arith.CMJet
