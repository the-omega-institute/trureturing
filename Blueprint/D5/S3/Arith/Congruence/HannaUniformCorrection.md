# The complete uniform corrected-Euler power family

## Abstract

The complete uniform corrected-Euler power family

The parameter s is an integer. The contract uses all s>=2 and every positive natural index. The internal integer weight uses s.toNat; weight_cast proves equality with the requested rational integer power for every s>=0, including zero. All appearances of s.toNat-1 and s.toNat*(r-1)-r represent the corresponding nonnegative integer exponents on their stated domains. The actual F is exp(sum over n>=1 of (n^s-a_s(n))*X^n/n). Its integer coefficients f are extracted independently from the canonical Euler series and then identified with the actual rational coefficients. Su, Theorems 7.1-7.2, owns the known square-weight conclusions; the supplied 4 November 2026 note by Haobo Ma and Wenlin Zhang motivates the uniform extension. Literature novelty of the all-s extension is unverified. Bala owns the cited universal-shift theorem for A082579, which is outside this module.

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

For s>=0, map_Z_to_Q(eulerSeries(i ↦ c_s(i+1)))=F_s. Apply HannaDiagonalGhostPowerIntegrality.euler_series_exponential with the positive-index identity weight(s,n)-a_s(n)=divisorGhost(c_s,n), supplied by BoundedEulerCorrection.correction_equation. At divisors d>0, (d-1)+1=d. The integer Euler object has the actual HasProd property by the arbitrary-integer-sequence application derived in the owning HannaDiagonalGhostPowerIntegrality Scribe.

**Theorem 1.9 (correction prime power).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_prime_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generalized original owner induction treats every prime including two and every positive power. At the first prime power the representative is p-1; at higher powers both weights vanish modulo p^r because s>=2.

**Theorem 1.10 (exponent prime).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting actual divisor ghosts at p and one gives p*c_s(p)=p^s-p. Integer cancellation yields p^(s-1)-1.

**Theorem 1.11 (exponent bounds).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prime indices use exponent_prime directly. On composite indices, strong induction bounds the proper-divisor ghost between zero and the proper-divisor power sum. The additive-n divisor budget and the correction interval force the new exponent to be a positive integer, at most n^(s-1).

For every integer s>=2, every prime p including 2, and r>=1, a_s(p^r)=p-1. Apply HannaPrimePowerCorrection.bounded_power_corrections with exponent s.toNat. Its interval premise is correction_spec; its divisibility premise follows from divisor_ghost_gauss(c_s) and correction_equation at consecutive prime powers.

For every s>=2 and prime p, c_s(p)=p^(s.toNat-1)-1. Subtract divisorGhost(c_s,1) from divisorGhost(c_s,p). The difference is p*c_s(p); a_s(1)=0 and a_s(p)=p-1. Thus p*c_s(p)=p^s-p, and cancellation by the positive integer p gives the formula.

For every s>=2, prime p and r>=2, c_s(p^r)=p^(s.toNat*(r-1)-r)*(p^s.toNat-1). Consecutive prime-power divisor ghosts differ by p^r*c_s(p^r); the corrections are both p-1. Their difference is therefore p^(r*s.toNat)-p^((r-1)*s.toNat). Since r<=s.toNat*(r-1), factor and cancel the nonzero p^r. No negative natural exponent is used.

**Definition 1.12 (f).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.f`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are ordinary integer coefficients of the canonical Euler series. They are not defined by a recurrence or a requested partition count.

For s>=0 and every n>=0, (f_s(n):Q)=coeff_n(F_s), by applying coeff_n to the Euler/exponential equality and using coeff_map. The integers f are extracted from the existing Euler series independently of this equality.

**Definition 1.13 (Independent finite coloured partitions).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartitionWithColors`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartitionWithColors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any colors:N->N and degree n, take the sigma over p:Nat.Partition n of the dependent product over distinct parts d of Sym(Fin(colors(d)), multiplicity_p(d)). This finite carrier is defined independently of any Euler or exponential coefficient and allows zero colours.

**Definition 1.14 (The corrected-power coloured carrier).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartition`

*Formalization.* `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Substitute colors(d)=(c_s(d)).toNat into the independent generic carrier. The definition applies at every natural degree, including zero.

For every colors:N->N and every n:N, the integer coefficient of eulerSeries(i -> colors(i+1)) at n equals Nat.card(ColouredPartitionWithColors(colors,n)). Compute the latter by Fintype.card_sigma and Fintype.card_pi. Sym.card_sym_fin_eq_multichoose gives the sum over partitions p of the product over its distinct parts d of multichoose(colors(d),multiplicity_p(d)). Nat.Partition.coeff_genFun identifies this with the coefficient of the weighted partition generating function. Nat.Partition.hasProd_genFun supplies its actual infinite product. For each positive part size d, PrimitiveEulerLedger.coeff_eulerFactor and Ring.choose_neg' identify the local coefficient at N with multichoose(colors(d),N/d) when d divides N, and zero otherwise; the two sign factors cancel. ColouredOddMultiplicity.local_factor_of_coeff reconstructs the same local factor from these coefficients. Uniqueness of HasProd, using the arbitrary-integer Euler-product application in the owning HannaDiagonalGhostPowerIntegrality Scribe, identifies the two series and proves the coefficient/cardinality equality. All colours and all degrees are quantified: zero colours are permitted, degree zero has the unique empty partition, and colors(0) is unused because every actual part size is positive.

For every integer s>=2 and every n>=0, f_s(n)=Nat.card(ColouredPartition(s,n)). At each d=i+1, exponent_bounds gives c_s(d)>=1, so Int.toNat_of_nonneg identifies the integer image of the natural colour count with c_s(d). Substitution into the preceding all-colours/all-degrees derivation gives exactly f_s(n), including degree zero. This is an application of the existing cardinality and product formulas, not an additional retained theorem or a new combinatorial proof.

For every integer s, f_s(0)=1. At degree zero, the defining Euler series is ledgerProduct at the empty prefix; its constant coefficient is one.

For s>=0 and n>=0, n*f_s(n)=sum_{k=0}^{n-1}((k+1)^s.toNat-a_s(k+1))*f_s(n-(k+1)). Apply EulerExponentialCoefficients.coefficient_recurrence to g(n)=weight(s,n)-a_s(n), use weight_cast and the Euler/exponential coefficient equality, and reflect the rational equality through the injective integer cast. The n=0 sum is empty.

For s>=2, f_s(n)>0 for every n>=0. On positive indices m, m^s>=m>a_s(m), so g(m)=m^s-a_s(m)>0. Apply EulerExponentialCoefficients.coefficient_positive and transport through the actual coefficient equality; degree zero is one.

For s>=2, f_s is nondecreasing on all natural indices. The first corrected ghost is g(1)=1. For n>=1, write m^s=m*m^(s-1), use n^(s-1)<=(n+1)^(s-1) and (n+1)^(s-1)>=n+1 to get (n+1)^s-n^s>=n+1. Together with 0<=a_s(n)<n and 0<=a_s(n+1)<n+1 this gives g(n)<=g(n+1). EulerExponentialCoefficients.coefficient_monotone then applies, followed by coefficient transport.

**Theorem 1.15 (correction boundary).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At weights zero and one, the bounded positive-index corrections are respectively zero and n-1. Their literal corrected ghosts equal one. Uniqueness comes from the same generic construction.

**Theorem 1.16 (F boundary).**

Lean statement: `D5/S3/Arith/Congruence/HannaUniformCorrection.F_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaUniformCorrection.F_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both actual boundary exponentials equal the inverse of one minus X. Coefficient induction proves exp(sum X^n/n) has every coefficient one; the formal geometric-series identity identifies its inverse. At weight one and prime-square index p^2, the correction is p^2-1, so the constant prime-power formula starts at weight two. For J_s(n)=sum over d dividing n of mu(n/d)*d^s, the generic Mobius identity at weight(s) gives n*c_s(n)=J_s(n)-sum over d dividing n of mu(n/d)*a_s(d). The generic logarithmic estimate at the same weight gives |c_s(n)-J_s(n)/n|<=1+log(n) for every positive n.

## References

- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartition`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.ColouredPartitionWithColors`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.F`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.F_boundary`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.IsPowerCorrection`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.a`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.c`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_boundary`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_exists_unique`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_prime_power`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.correction_spec`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_bounds`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.exponent_prime`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.f`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.weight`
- Truth anchor: `D5/S3/Arith/Congruence/HannaUniformCorrection.weight_cast`
- Dependency: [D5/S1/Recurrence/Witt/BoundedEulerCorrection](../../../S1/Recurrence/Witt/BoundedEulerCorrection.md)
- Dependency: [D5/S1/Recurrence/Witt/EulerExponentialCoefficients](../../../S1/Recurrence/Witt/EulerExponentialCoefficients.md)
- Dependency: [D5/S3/Arith/Congruence/BoundedPowerCorrection](BoundedPowerCorrection.md)
- Dependency: [D5/S3/Arith/Divisors/ProperDivisorPowerBudget](../Divisors/ProperDivisorPowerBudget.md)
