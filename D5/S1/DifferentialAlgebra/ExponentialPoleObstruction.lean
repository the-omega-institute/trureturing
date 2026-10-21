/- GID: D5/S1/DifferentialAlgebra/ExponentialPoleObstruction
   generality: G
   mirror-B: D5/B/S1/DifferentialAlgebra/ExponentialPoleObstruction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.FieldDivision, mathlib/module/Mathlib.FieldTheory.RatFunc.AsPolynomial, mathlib/module/Mathlib.RingTheory.Derivation.Basic, mathlib/module/Mathlib.Tactic.FieldSimp, mathlib/module/Mathlib.Tactic.Ring, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: The exponential differential field has no rational primitive of u/(2-u). -/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace D5.S1.DifferentialAlgebra.ExponentialPoleObstruction

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Clearing the denominator of a rational primitive gives an impossible polynomial identity. -/
theorem polynomial_obstruction (d : Derivation ℤ K[X] K[X])
    (hdX : d X = X) (p q : K[X]) (hq : q ≠ 0) (hpq : IsCoprime p q) :
    (2 - X) * (d p * q - p * d q) ≠ X * q ^ 2 := by
  intro h
  have hq2 : q.eval 2 = 0 := by
    have he := congrArg (Polynomial.eval (2 : K)) h
    simp only [eval_mul, eval_sub, eval_ofNat, eval_X, eval_pow, sub_self, zero_mul] at he
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp he.symm).resolve_left (by norm_num))
  have hp2 : p.eval 2 ≠ 0 := by
    intro hp2
    obtain ⟨a, b, hab⟩ := hpq
    have he := congrArg (Polynomial.eval (2 : K)) hab
    simpa [hp2, hq2] using he
  obtain ⟨s, hs, hns⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq 2
  have hs2 : s.eval 2 ≠ 0 := by
    intro hz
    exact hns (dvd_iff_isRoot.mpr hz)
  have hm : q.rootMultiplicity 2 ≠ 0 := by
    intro hm
    rw [hs] at hq2
    simp only [hm, pow_zero, one_mul] at hq2
    exact hs2 hq2
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hqfac : q = (X - 2) ^ (n + 1) * s := by
    simpa only [hn, Nat.succ_eq_add_one, C_ofNat] using hs
  have hd2 : d (2 : K[X]) = 0 := by
    rw [show (2 : K[X]) = 1 + 1 by norm_num]
    simp only [map_add, Derivation.map_one_eq_zero, add_zero]
  have hdf : d (X - 2) = X := by rw [map_sub, hdX, hd2, sub_zero]
  have hdq : d q = (n + 1 : K[X]) * (X - 2) ^ n * X * s +
      (X - 2) ^ (n + 1) * d s := by
    rw [hqfac, Derivation.leibniz, Derivation.leibniz_pow, hdf]
    simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hf : (X - 2 : K[X]) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (by simpa only [C_ofNat] using (X_sub_C_ne_zero (2 : K)))
  have hc :
      -d p * (X - 2) * s + p * (n + 1 : K[X]) * X * s +
          p * (X - 2) * d s = X * (X - 2) ^ (n + 1) * s ^ 2 := by
    apply mul_left_cancel₀ hf
    calc
      (X - 2) ^ (n + 1) *
          (-d p * (X - 2) * s + p * (n + 1 : K[X]) * X * s +
            p * (X - 2) * d s) =
          (2 - X) * (d p * q - p * d q) := by
            rw [hdq, hqfac]
            simp only [pow_succ]
            ring
      _ = X * q ^ 2 := h
      _ = (X - 2) ^ (n + 1) * (X * (X - 2) ^ (n + 1) * s ^ 2) := by
        rw [hqfac]
        ring
  have he := congrArg (Polynomial.eval (2 : K)) hc
  have hnK : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_X, eval_ofNat, eval_pow,
    eval_natCast, eval_one, sub_self, mul_zero, zero_mul, neg_zero, zero_add, add_zero,
    zero_pow (Nat.succ_ne_zero n)] at he
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hp2 hnK) (by norm_num)) hs2) he

/-- The obstruction persists under an injective differential evaluation into an arbitrary field. -/
theorem rational_expression_obstruction {L : Type*} [Field L]
    (d : Derivation ℤ K[X] K[X]) (hdX : d X = X)
    (D : Derivation ℤ L L) (j : K[X] →+* L) (hj : Function.Injective j)
    (hcompat : ∀ p : K[X], D (j p) = j (d p))
    (p q : K[X]) (hq : q ≠ 0) (hpq : IsCoprime p q) :
    D (j p / j q) ≠ j X / (2 - j X) := by
  intro hh
  have hqj : j q ≠ 0 := fun hz => hq (hj (by simpa using hz))
  have hx : (2 - j X : L) ≠ 0 := by
    have hxP : (2 - X : K[X]) ≠ 0 := by
      simpa only [neg_sub, C_ofNat] using
        neg_ne_zero.mpr (X_sub_C_ne_zero (2 : K))
    intro hz
    apply hxP
    apply hj
    simpa only [map_sub, map_ofNat, map_zero] using hz
  rw [Derivation.leibniz_div, hcompat, hcompat] at hh
  simp only [smul_eq_mul] at hh
  have hcross :
      (2 - j X) * (j (d p) * j q - j p * j (d q)) =
        j X * j q ^ 2 := by
    field_simp [hqj, hx] at hh
    convert hh using 1 <;> ring
  apply polynomial_obstruction d hdX p q hq hpq
  apply hj
  simpa only [map_mul, map_sub, map_ofNat, map_pow] using hcross

noncomputable local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

/-- A derivation restricting to a polynomial derivation with `d u = u` cannot integrate
`u / (2-u)` in the rational function field. -/
theorem no_rational_primitive (d : Derivation ℤ K[X] K[X])
    (hdX : d X = X) (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (hcompat : ∀ p : K[X], D (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (d p)) (h : RatFunc K) :
    D h ≠ RatFunc.X / (2 - RatFunc.X) := by
  intro heq
  have hh : D (algebraMap K[X] (RatFunc K) h.num /
      algebraMap K[X] (RatFunc K) h.denom) = RatFunc.X / (2 - RatFunc.X) := by
    simpa only [RatFunc.num_div_denom] using heq
  have hne := rational_expression_obstruction (K := K) (L := RatFunc K) d hdX D
    (algebraMap K[X] (RatFunc K)) (RatFunc.algebraMap_injective K) hcompat
    h.num h.denom h.denom_ne_zero (RatFunc.isCoprime_num_denom h)
  apply hne
  simpa only [RatFunc.algebraMap_X] using hh

#print axioms no_rational_primitive

end D5.S1.DifferentialAlgebra.ExponentialPoleObstruction
