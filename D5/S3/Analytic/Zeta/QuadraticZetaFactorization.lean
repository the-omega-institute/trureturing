/- GID: D5/S3/Analytic/Zeta/QuadraticZetaFactorization
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/QuadraticZetaFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convergent prime-ideal regrouping and the prime imaginary quadratic zeta factorization. -/

import D5.S3.Arith.QuadraticFields.QuadraticPrimeSplitting
import D5.S3.Analytic.Zeta.PrimeQuadraticLValues
import D5.S3.Analytic.Zeta.NumberField.ZetaProductFactorization
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.Sigma.Basic

namespace D5.S3.Analytic.Zeta.QuadraticZetaFactorization

open scoped BigOperators NumberField

noncomputable section

local instance (ℓ : Nat.Primes) : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩

/-- Nonzero maximal-order prime ideals, partitioned by their actual contraction to Z.
This equivalence includes ramified primes. -/
def primeIdealsOverEquiv (K : Type*) [Field K] [NumberField K] :
    (Σ ℓ : Nat.Primes, Ideal.primesOver (Ideal.span {(ℓ : ℤ)}) (𝓞 K)) ≃
      {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} where
  toFun q := ⟨q.2.1, q.2.2.1,
    Ideal.ne_bot_of_mem_primesOver
      (by simpa only [ne_eq, Ideal.span_singleton_eq_bot, Int.natCast_eq_zero]
        using q.1.2.ne_zero) q.2.2⟩
  invFun P := by
    letI : P.1.IsPrime := P.2.1
    letI : NeZero P.1 := ⟨P.2.2⟩
    exact ⟨⟨Ideal.absNorm (P.1.under ℤ), Nat.absNorm_under_prime P.1⟩,
      ⟨P.1, P.2.1, Int.liesOver_span_absNorm P.1⟩⟩
  left_inv q := by
    have hℓ : Ideal.absNorm (q.2.1.under ℤ) = (q.1 : ℕ) := by
      letI := q.2.2.2
      rw [← Ideal.over_def (p := Ideal.span {(q.1 : ℤ)}) (P := q.2.1),
        Ideal.absNorm_span_natCast]
      simp
    exact Sigma.subtype_ext (Subtype.ext hℓ) rfl
  right_inv P := Subtype.ext rfl

/-- Genuine convergent regrouping of the Dedekind Euler product by rational primes.
`HasProd` is required here: a bare equality of `tprod` expressions does not justify it. -/
theorem hasProd_rationalPrime_factors (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun ℓ : Nat.Primes =>
      ∏ P : Ideal.primesOver (Ideal.span {(ℓ : ℤ)}) (𝓞 K),
        (1 - (Ideal.absNorm P.1 : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
  classical
  let e := primeIdealsOverEquiv K
  have h := e.hasProd_iff.mpr (Chebotarev.hasProd_primeIdeal_factor K hs)
  apply h.sigma
  intro ℓ
  exact hasProd_fintype _

end

end D5.S3.Analytic.Zeta.QuadraticZetaFactorization

namespace D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary

open scoped BigOperators NumberField
open D5.S3.Analytic.Zeta.PrimeQuadraticLValues

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The actual maximal-order Euler factor, including the factors at two and p. -/
theorem primeIdeal_euler_factor (ℓ : ℕ) [Fact ℓ.Prime] (s : ℂ) :
    (∏ P : Ideal.primesOver (Ideal.span {(ℓ : ℤ)}) (𝓞 (Field p)),
      (1 - (Ideal.absNorm P.1 : ℂ) ^ (-s))⁻¹) =
        (1 - (ℓ : ℂ) ^ (-s))⁻¹ *
          (1 - primeCharacter p ℓ * (ℓ : ℂ) ^ (-s))⁻¹ := by
  classical
  have hnorm (P : Ideal.primesOver (Ideal.span {(ℓ : ℤ)}) (𝓞 (Field p))) :
      (Ideal.absNorm P.1 : ℂ) ^ (-s) =
        ((ℓ : ℂ) ^ (-s)) ^ Ideal.inertiaDeg P.1 ℤ := by
    rw [← Ideal.pow_inertiaDeg ℓ P.1, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  simp_rw [hnorm]
  rw [Finset.prod_inv_distrib, primeIdeal_euler_polynomial p ℓ,
    mul_inv_rev, mul_comm]
  simp [primeCharacter, legendreSym]

/-- Quadratic Dedekind-zeta factorization for the actual number field and actual
Legendre Dirichlet character, proved by convergent local-to-global products. -/
theorem dedekindZeta_eq_riemannZeta_mul_LFunction {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (Field p) s =
      riemannZeta s * DirichletCharacter.LFunction (primeCharacter p) s := by
  have hK := D5.S3.Analytic.Zeta.QuadraticZetaFactorization.hasProd_rationalPrime_factors
    (Field p) hs
  have hχ := (riemannZeta_eulerProduct_hasProd hs).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd (primeCharacter p) hs)
  rw [← DirichletCharacter.LFunction_eq_LSeries (primeCharacter p) hs] at hχ
  apply hK.unique
  convert hχ using 1
  funext ℓ
  letI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  exact primeIdeal_euler_factor p ℓ s

end D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary
