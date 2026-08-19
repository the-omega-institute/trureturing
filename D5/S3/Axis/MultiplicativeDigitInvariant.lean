/- GID: D5/S3/Axis/MultiplicativeDigitInvariant
   generality: I
   mirror-B: D5/B/S3/Axis/MultiplicativeDigitInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The contraction reading is additive on coprimes, signed by digit shape, and splits off zeta. -/

import D5.S1.Deficit.LambdaMinusAdditive
import D5.S1.Deficit.Displacement.ZeckendorfNormSign
import D5.S3.Axis.LambdaMinusDirichletSeries

/- Library-search audit trail (2026-08-19):
   * This module states no new mathematics. Every conjunct below is an existing public
     theorem on `dev`, applied rather than reproved:
     `lambdaMinus_coprime_add`,
     `betaGolden_norm_sign_of_least_zeckendorf_index`,
     `LambdaMinusDirichletSeries.lambda_minus_dirichlet_series`.
   * The reason it exists is the digestion ledger: the source sentence is one atom carrying
     three clauses, and a multi-clause atom is covered only by a conjunction that names all
     of them in one declaration. The three parts were proved separately and never conjoined,
     so nothing in the truth DAG corresponded to the sentence itself.
   * Placed in `D5/S3/Axis` because the Dirichlet conjunct lives there and a module belongs
     at the stratum of its highest dependency; the two additivity and sign conjuncts are S1.
-/

namespace D5.S3.Axis.MultiplicativeDigitInvariant

open scoped ArithmeticFunction LSeries
open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Deficit
open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Deficit.LambdaMinusAdditive
open D5.S1.Deficit.Displacement.ZeckendorfNormSign
open D5.S3.Axis.LambdaMinusDirichletSeries

/-- The contraction reading is a multiplicative digit-structure invariant: it is additive
over coprime factors, its sign is fixed by the parity of the least occupied Zeckendorf
index rather than by magnitude, and its Dirichlet series factors as zeta times the
prime-axis series with every contraction exponent inside the unit window. -/
theorem lambda_minus_is_a_multiplicative_digit_invariant :
    (∀ m n : ℕ, Nat.Coprime m n →
        lambdaMinus (m * n) =
          lambdaMinus m + lambdaMinus n) ∧
      (∀ v k : ℕ, 0 < v → k ∈ wdigits v →
        (∀ j ∈ wdigits v, k ≤ j) →
          (0 < norm (betaGolden v) ↔ Even k) ∧
            (norm (betaGolden v) < 0 ↔ Odd k)) ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n : ℕ => (lambdaMinus n : ℂ)) s =
            riemannZeta s * lambdaMinusAxisSeries s ∧
          ∀ v : ℕ, |betaContraction v| < 1 :=
  ⟨fun _ _ h => lambdaMinus_coprime_add h,
    fun _ _ hv hk hmin =>
      betaGolden_norm_sign_of_least_zeckendorf_index hv hk hmin,
    fun s hs => lambda_minus_dirichlet_series s hs⟩

#print axioms lambda_minus_is_a_multiplicative_digit_invariant

end D5.S3.Axis.MultiplicativeDigitInvariant
