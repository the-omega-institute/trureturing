# The complete uniform corrected-Euler power family

## Abstract

The complete uniform corrected-Euler power family

The parameter s is an integer. The contract uses all s>=2 and every positive natural index. The internal integer weight uses s.toNat; weight_cast proves equality with the requested rational integer power for every s>=0, including zero. All appearances of s.toNat-1 and s.toNat*(r-1)-r represent the corresponding nonnegative integer exponents on their stated domains. The actual F is exp(sum over n>=1 of (n^s-a_s(n))*X^n/n). Its integer coefficients f are extracted independently from the canonical Euler series and then identified with the actual rational coefficients. Su, Theorems 7.1-7.2, owns the known square-weight conclusions; the supplied note attributed to Haobo Ma and Wenlin Zhang motivates the uniform extension. The note's authorship and literature novelty of the all-s extension are unverified. Bala owns the cited universal-shift theorem for A082579, which is outside this module.

**Definition 1.1 (weight).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.weight`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer recursion uses the natural representative of the nonnegative integer weight. Negative parameters are not asserted to model negative-power integrality.

**Definition 1.2 (a).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.a`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction is the generic bounded residue for the integer power weight.

**Definition 1.3 (c).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.c`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive-index Euler exponents are the generic recursively constructed integer ledger.

**Definition 1.4 (F).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.F`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the literal rational formal exponential with integer power parameter s. Its logarithmic input has constant coefficient zero.

**Definition 1.5 (IsPowerCorrection).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.IsPowerCorrection`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.IsPowerCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate states exactly the positive-index bounds and integrality of that literal exponential, with no prescribed value at zero.

**Theorem 1.6 (weight cast).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.weight_cast`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.weight_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative integer s and every natural n, the cast integer weight is exactly the rational integer power n^s. This discharges the domain correspondence.

**Theorem 1.7 (correction spec).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic integer-weight construction supplies boundedness and actual exponential integrality.

**Theorem 1.8 (correction exists unique).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_exists_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Existence and uniqueness hold on every positive index for every integer s>=0. Whole-function uniqueness is deliberately absent because the entry at zero is unused.

**Theorem 1.9 (euler representation).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.euler_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.euler_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer Euler series, indexed by part size i+1, maps to the actual rational exponential. The separate HasProd theorem in the canonical owner proves it is an actual infinite Euler product.

**Theorem 1.10 (exponent bounds).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction bounds the proper-divisor ghost between zero and the proper-divisor power sum. The additive-n divisor budget and the correction interval force the new exponent to be a positive integer, at most n^(s-1).

**Theorem 1.11 (correction prime power).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_prime_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generalized original owner induction treats every prime including two and every positive power. At the first prime power the representative is p-1; at higher powers both weights vanish modulo p^r because s>=2.

**Theorem 1.12 (exponent prime).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting actual divisor ghosts at p and one gives p*c_s(p)=p^s-p. Integer cancellation yields p^(s-1)-1.

**Theorem 1.13 (exponent prime power).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At r>=2, the equal corrections cancel. The exponent s*(r-1)-r is nonnegative on the complete stated domain; exact power algebra and cancellation yield the displayed formula.

**Definition 1.14 (f).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.f`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are ordinary integer coefficients of the canonical Euler series. They are not defined by a recurrence or a requested partition count.

**Theorem 1.15 (coefficient eq).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping the actual integer Euler series into rationals identifies f_s(n) with coefficient n of F_s.

**Definition 1.16 (ColouredPartition).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartition`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The independent finite generic coloured carrier is specialized to (c_s(d)).toNat. Positive-index exponent bounds prove this natural colour count faithfully equals the integer exponent at every occurring part.

**Theorem 1.17 (coefficient cardinality).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent carrier counts the actual coefficients. The proof transports nonnegative Euler exponents to natural colours and consumes the generic cardinality correspondence.

For every integer s, including negative parameters, f_s(0)=1 follows directly from the definitions. Set b(i)=c_s(i+1). By `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.eulerSeries`, f_s(0) is coefficient zero of ledgerProduct b 0. The definition `D5/S1/Recurrence/Witt/PrimitiveEulerLedger.ledgerProduct` makes this the product over the empty range, hence the constant series one, whose coefficient zero is one. This argument concerns the integer Euler series and requires neither nonnegative s nor an assertion about negative-power integrality.

For every integer s>=0 and every natural n, the same actual coefficients satisfy the integer identity n*f_s(n)=sum over 1<=j<=n of (j^(s.toNat)-a_s(j))*f_s(n-j). Apply `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_recurrence` with g(m)=((weight(s,m)-a_s(m)):Q). Its exponentialSum g is F_s because weight_cast identifies the integer weight with the rational integer power. The equality `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_eq` identifies every rational coefficient with the cast of f_s. Injectivity of the integer-to-rational cast gives the displayed integer identity; replacing j by k+1 gives exactly the sum over k in range n. At n=0 both sides are zero. The reusable recurrence itself extracts coefficients from `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponential_sum_equation`: the positive-degree ghost series has coefficient g(j), the derivative contributes n times coefficient n, and multiplication gives the finite convolution. This is a consequence of the generic supplier and the coefficient correspondence, without defining f_s recursively.

**Theorem 1.18 (coefficient positive).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corrected ghost n^s-a_s(n) is strictly positive for s>=2 and n>0. The general exponential positivity theorem therefore applies to the actual f_s.

**Theorem 1.19 (coefficient monotone).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference (n+1)^s-n^s is at least n+1 for s>=2 and n>=1. The correction bounds make corrected ghosts increasing, with first ghost one. The general convolution comparison proves nondecreasing f_s.

**Theorem 1.20 (correction boundary).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At weights zero and one, the bounded positive-index corrections are respectively zero and n-1. Their literal corrected ghosts equal one. Uniqueness comes from the same generic construction.

**Theorem 1.21 (F boundary).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.F_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.F_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both actual boundary exponentials equal the inverse of one minus X. Coefficient induction proves exp(sum X^n/n) has every coefficient one; the formal geometric-series identity identifies its inverse. At weight one and prime-square index p^2, the correction is p^2-1, so the constant prime-power formula starts at weight two. For J_s(n)=sum over d dividing n of mu(n/d)*d^s, the generic Mobius identity at weight(s) gives n*c_s(n)=J_s(n)-sum over d dividing n of mu(n/d)*a_s(d). The generic logarithmic estimate at the same weight gives |c_s(n)-J_s(n)/n|<=1+log(n) for every positive n.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_recurrence`
- Truth anchor: `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.eulerSeries`
- Truth anchor: `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponential_sum_equation`
- Truth anchor: `D5/S1/Recurrence/Witt/PrimitiveEulerLedger.ledgerProduct`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartition`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.F`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.F_boundary`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.IsPowerCorrection`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.a`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.c`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_cardinality`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_eq`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_eq`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_monotone`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_positive`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_boundary`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_exists_unique`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_prime_power`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_spec`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.euler_representation`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_bounds`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime_power`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.f`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.weight`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.weight_cast`
- Dependency: [D5/S1/Recurrence/Witt/BoundedEulerCorrection](../../../S1/Recurrence/Witt/BoundedEulerCorrection.md)
- Dependency: [D5/S1/Recurrence/Witt/EulerExponentialCoefficients](../../../S1/Recurrence/Witt/EulerExponentialCoefficients.md)
- Dependency: [D5/S3/Arith/Congruence/BoundedPowerCorrection](BoundedPowerCorrection.md)
- Dependency: [D5/S3/Arith/Divisors/ProperDivisorPowerBudget](../Divisors/ProperDivisorPowerBudget.md)
- Dependency: [D5/S3/Combinatorics/Partitions/ColouredEulerLedger](../../Combinatorics/Partitions/ColouredEulerLedger.md)
