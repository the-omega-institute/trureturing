/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/PolynomialWeights
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream polynomial-weight support for Euler products. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/FiniteField/PolynomialWeights.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField.CharacterAPI

/-!
# Multiplicative weights on monic polynomials

The two Euler-product arguments in the manuscript use the coefficient convention

`P = X ^ r + a₁ X ^ (r - 1) + a₂ X ^ (r - 2) + ⋯`.

Mathlib's `Polynomial.nextCoeff` is `a₁`.  We define `secondCoeff P` as coefficient two of
`P.reverse`; this is `a₂` when `2 ≤ r` and is zero in degrees zero and one.  Polynomial
reversal then turns both product identities into the ordinary formulas for coefficients zero,
one, and two of a product.
-/

open Polynomial

namespace LanglandsFirstMainLemma

universe u v

/-- The multiplicative submonoid of monic polynomials. -/
def MonicPolynomial (R : Type u) [Semiring R] : Submonoid R[X] where
  carrier := {p | p.Monic}
  one_mem' := monic_one
  mul_mem' hp hq := hp.mul hq

/-- A multiplicative weight on monic polynomials. -/
abbrev MonicWeight (R : Type u) (M : Type v) [Semiring R] [Monoid M] :=
  MonicPolynomial R →* M

namespace MonicWeight

/-- Construct a monic-polynomial weight from a function on all polynomials which is
multiplicative on monic inputs. -/
def ofFun {R : Type u} {M : Type v} [Semiring R] [Monoid M]
    (w : R[X] → M) (w_one : w 1 = 1)
    (w_mul : ∀ p q : R[X], p.Monic → q.Monic → w (p * q) = w p * w q) :
    MonicWeight R M where
  toFun p := w p
  map_one' := w_one
  map_mul' p q := w_mul p q p.property q.property

@[simp]
theorem ofFun_apply {R : Type u} {M : Type v} [Semiring R] [Monoid M]
    (w : R[X] → M) (w_one) (w_mul) (p : MonicPolynomial R) :
    ofFun w w_one w_mul p = w p :=
  rfl

end MonicWeight

section Coefficients

variable {R : Type u} [CommSemiring R]

/-- The coefficient two places below the leading coefficient, with value zero for polynomials
of degree less than two.  For a monic polynomial this is the manuscript's `a₂`. -/
noncomputable def secondCoeff (p : R[X]) : R :=
  p.reverse.coeff 2

/-- At degree at least two, `secondCoeff` is the expected coefficient counted down from the
leading term. -/
theorem secondCoeff_eq_coeff_of_two_le (p : R[X]) (hp : 2 ≤ p.natDegree) :
    secondCoeff p = p.coeff (p.natDegree - 2) := by
  rw [secondCoeff, coeff_reverse, revAt_le hp]

/-- The low-degree convention in the manuscript: `a₂ = 0` in degree one (and also in
degree zero). -/
theorem secondCoeff_eq_zero_of_natDegree_lt_two (p : R[X]) (hp : p.natDegree < 2) :
    secondCoeff p = 0 := by
  exact coeff_eq_zero_of_natDegree_lt ((reverse_natDegree_le p).trans_lt hp)

@[simp]
theorem secondCoeff_one : secondCoeff (1 : R[X]) = 0 := by
  exact secondCoeff_eq_zero_of_natDegree_lt_two 1 (by simp)

@[simp]
theorem nextCoeff_one : (1 : R[X]).nextCoeff = 0 := by
  rw [← C_1, nextCoeff_C_eq_zero]

/-- The first coefficient of a product of monic polynomials is the sum of the first
coefficients.  This is the project-facing form of Mathlib's `Polynomial.Monic.nextCoeff_mul`. -/
theorem monic_firstCoeff_mul {p q : R[X]} (hp : p.Monic) (hq : q.Monic) :
    (p * q).nextCoeff = p.nextCoeff + q.nextCoeff :=
  hp.nextCoeff_mul hq

/-- If monic `p` and `q` have first two coefficients `a₁,a₂` and `b₁,b₂`, then
the second coefficient of their product is `a₂ + b₂ + a₁ b₁`. -/
theorem monic_secondCoeff_mul {p q : R[X]} (hp : p.Monic) (hq : q.Monic) :
    secondCoeff (p * q) =
      secondCoeff p + secondCoeff q + p.nextCoeff * q.nextCoeff := by
  nontriviality R
  rw [secondCoeff, reverse_mul]
  · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [secondCoeff, hp.leadingCoeff, hq.leadingCoeff, Finset.sum_range_succ]
    ac_rfl
  · simp [hp.leadingCoeff, hq.leadingCoeff]

end Coefficients

section GaussWeight

variable {k : Type u} [Field k]

/-- The polynomial weight in the Euler-product proof of the Hasse--Davenport lift:
`w(P) = χ((-1)^deg(P) P(0)) ψ(-a₁(P))`. -/
noncomputable def gaussPolynomialWeight
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) : MonicWeight k ℂ :=
  MonicWeight.ofFun
    (fun p ↦ χ ((-1 : k) ^ p.natDegree * p.coeff 0) * ψ (-p.nextCoeff))
    (by simp)
    (by
      intro p q hp hq
      rw [hp.natDegree_mul hq, mul_coeff_zero, hp.nextCoeff_mul hq, pow_add]
      rw [show
        ((-1 : k) ^ p.natDegree * (-1) ^ q.natDegree) * (p.coeff 0 * q.coeff 0) =
          ((-1 : k) ^ p.natDegree * p.coeff 0) *
            ((-1 : k) ^ q.natDegree * q.coeff 0) by ring]
      rw [map_mul, show -(p.nextCoeff + q.nextCoeff) =
        -p.nextCoeff + -q.nextCoeff by ring, ψ.map_add_eq_mul]
      ring)

@[simp]
theorem gaussPolynomialWeight_apply (χ : FiniteMulChar k) (ψ : FiniteAddChar k)
    (p : MonicPolynomial k) :
    gaussPolynomialWeight χ ψ p =
      χ ((-1 : k) ^ (p : k[X]).natDegree * (p : k[X]).coeff 0) *
        ψ (-(p : k[X]).nextCoeff) :=
  rfl

end GaussWeight

section HasseWeight

variable {k : Type u} [Field k]

/-- A nowhere-zero function satisfying Hasse's quadratic-refinement law takes the value one
at zero. -/
theorem hasseFunction_zero (φ : k → ℂ) (ψ : FiniteAddChar k)
    (hφ_ne : ∀ x, φ x ≠ 0)
    (hφ_add : ∀ x y, φ (x + y) = φ x * φ y * ψ (x * y)) :
    φ 0 = 1 := by
  have h := hφ_add 0 0
  simp only [zero_add, zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  apply mul_left_cancel₀ (hφ_ne 0)
  simpa only [mul_one] using h.symm

/-- The polynomial weight in the Hasse-function Euler product:
`w(P) = φ(-a₁(P)) ψ(-a₂(P))`.  Its hypotheses are precisely the nowhere-zero and
quadratic-refinement assumptions in the manuscript. -/
noncomputable def hassePolynomialWeight (φ : k → ℂ) (ψ : FiniteAddChar k)
    (hφ_ne : ∀ x, φ x ≠ 0)
    (hφ_add : ∀ x y, φ (x + y) = φ x * φ y * ψ (x * y)) :
    MonicWeight k ℂ :=
  MonicWeight.ofFun
    (fun p ↦ φ (-p.nextCoeff) * ψ (-secondCoeff p))
    (by simp [hasseFunction_zero φ ψ hφ_ne hφ_add])
    (by
      intro p q hp hq
      rw [hp.nextCoeff_mul hq, monic_secondCoeff_mul hp hq]
      rw [show -(p.nextCoeff + q.nextCoeff) =
        -p.nextCoeff + -q.nextCoeff by ring, hφ_add]
      rw [show (-p.nextCoeff) * (-q.nextCoeff) =
        p.nextCoeff * q.nextCoeff by ring]
      rw [show -(secondCoeff p + secondCoeff q + p.nextCoeff * q.nextCoeff) =
        -secondCoeff p + (-secondCoeff q + -(p.nextCoeff * q.nextCoeff)) by ring]
      rw [ψ.map_add_eq_mul, ψ.map_add_eq_mul]
      have hcancel :
          ψ (p.nextCoeff * q.nextCoeff) * ψ (-(p.nextCoeff * q.nextCoeff)) = 1 := by
        rw [← ψ.map_add_eq_mul]
        simp
      calc
        φ (-p.nextCoeff) * φ (-q.nextCoeff) * ψ (p.nextCoeff * q.nextCoeff) *
              (ψ (-secondCoeff p) *
                (ψ (-secondCoeff q) * ψ (-(p.nextCoeff * q.nextCoeff)))) =
            (φ (-p.nextCoeff) * ψ (-secondCoeff p)) *
              (φ (-q.nextCoeff) * ψ (-secondCoeff q)) *
                (ψ (p.nextCoeff * q.nextCoeff) *
                  ψ (-(p.nextCoeff * q.nextCoeff))) := by ring
        _ = (φ (-p.nextCoeff) * ψ (-secondCoeff p)) *
              (φ (-q.nextCoeff) * ψ (-secondCoeff q)) := by rw [hcancel, mul_one])

@[simp]
theorem hassePolynomialWeight_apply (φ : k → ℂ) (ψ : FiniteAddChar k)
    (hφ_ne : ∀ x, φ x ≠ 0)
    (hφ_add : ∀ x y, φ (x + y) = φ x * φ y * ψ (x * y))
    (p : MonicPolynomial k) :
    hassePolynomialWeight φ ψ hφ_ne hφ_add p =
      φ (-(p : k[X]).nextCoeff) * ψ (-secondCoeff (p : k[X])) :=
  rfl

end HasseWeight

end LanglandsFirstMainLemma
