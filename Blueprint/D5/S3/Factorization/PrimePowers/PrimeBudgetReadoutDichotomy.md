# Prime Budget Readout Dichotomy

## Abstract

Prime budgets separate horizontal CRT factors from vertical precision maps.

**Theorem 1.1 (Different primes decompose horizontally by CRT).**

$$\forall B: PrimeBudget, HorizontalPrimeDecomposition(B).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.horizontal_prime_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A PrimeBudget consists of a finite support, an exponent map, a primality proof on the support, and positivity of every supported exponent.

The proof applies finite_crt_join directly to the support and exponent fields. The product is a dependent product of residue rings; no tensor-product object is introduced.

The empty and singleton supports are included. The imported CRT lemma permits zero exponents, while PrimeBudget intentionally excludes them to represent the source definition.

**Theorem 1.2 (One prime carries compatible precision projections).**

$$\forall p \in \mathbb{N}, VerticalPrimeInverseSystem(p).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.vertical_prime_inverse_system` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named primePowerReadout casts one integer into ZMod of p to the k. When the lower exponent is at most the upper exponent, primePowerProjection is Mathlib's ZMod.castHom.

ZMod.castHom_self and ZMod.castHom_comp prove the identity and composition laws. ZMod.cast_intCast proves that every integer readout commutes with reduction of precision.

These laws are the requested inverse-system compatibility data. No inverse-limit object is required, and no primality premise is used in the vertical direction.

**Theorem 1.3 (Horizontal CRT and vertical filtration hold together).**

$$\forall B: PrimeBudget,\\{}HorizontalPrimeDecomposition(B) \land \forall p \in S_{B}, VerticalPrimeInverseSystem(p).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.horizontal_vertical_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive prime budget, the existing CRT decomposition holds and every supported prime has the compatible vertical system. This is the single bundled structure principle.

**Lemma 1.4 (Precision order is necessary for natural projections).**

$$\neg\operatorname{Nonempty}(\operatorname{ZMod}(2) \to \operatorname{ZMod}(4)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.precision_order_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is no unital ring homomorphism from ZMod 2 to ZMod 4: two is zero in the source but nonzero in the target. Thus a projection cannot in general run from lower precision to higher precision.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.horizontal_prime_decomposition`
- Truth anchor: `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.horizontal_vertical_dichotomy`
- Truth anchor: `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.precision_order_is_necessary`
- Truth anchor: `D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.vertical_prime_inverse_system`
- Dependency: [D5/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness](BoundedIntegerCrtCompleteness.md)
- Dependency: [D5/S3/Factorization/PrimePowers/FiniteCrtJoin](FiniteCrtJoin.md)
