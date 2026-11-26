# Weighted factorial gcds and residue-degree norm complements

## Abstract

Simultaneous floor minima, universal weighted factorial certificates, and actual ideal norms.

Nonnegative weights preserve the prime-power minima of a composition. The key is simultaneous attainment for every power of one rational prime. For number fields the relevant weights come from the residue degrees of actual prime ideals, and the complementary weights are nonnegative by the degree formula. The full-ring factorial terminology refers to the prime-ideal Euler formula of Bhargava and Chabert-Cahen; a p-ordering construction is not an additional object here.

**Theorem 1.1 (Weighted factorials are nonzero).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedValue_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedValue_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every weightedValue is a finite product of powers of positive rational primes. It is nonzero for every cutoff, natural weight array and argument, including empty prime sets and zero weights. This ensures the compact factorial quotients have positive denominators.

**Theorem 1.2 (Weighted tails are nonzero).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every weightedTail is nonzero for all H,M and natural weights. No inequality M<=H is required for this finite prime-power product.

**Theorem 1.3 (Factorization of a finite prime-power product).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.prime_product_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.prime_product_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set P of primes and any natural exponent function e, the exponent at p of the product of q^e(q) over q in P is e(p) if p belongs to P and zero otherwise.

**Theorem 1.4 (The exact weighted tail exponent).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p in primesLE(H), the p-exponent of weightedTail(H,M,c) is the sum over 0<=j<=H of c(p,j) times floorMinimum(H,M,p^(j+1)).

**Theorem 1.5 (Constant coefficients raise the ordinary tail to a power).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all H,M,d, weightedTail(H,M,constant d)=tailLCM(H,M)^d. This follows by comparison of the exact prime exponents, with zero exponents for primes above H.

**Theorem 1.6 (Adding weights multiplies the tails).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_add`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all H,M and natural arrays c,c-prime, the product of their weighted tails equals the weighted tail of their pointwise sum. Together with the constant-coefficient identity, a partition c+c-prime=d yields a product of tails equal to tailLCM(H,M)^d.

**Theorem 1.7 (The actual Euler ideal norm at a finite cutoff).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.fullRingFactorialIdeal_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.fullRingFactorialIdeal_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every number field K and n<=H, the absolute norm of fullRingFactorialIdeal(K,n) is weightedValue(H,normWeight(K),n). The original Euler ideal uses floor(n/(NP)^j); the residue-degree reindexing and the cutoff identity supply this equality.

**Theorem 1.8 (The actual integer complement).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.complement_eq_weightedValue`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.complement_eq_weightedValue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every number field K and n<=H, normComplement(K,n) is weightedValue(H,degree(K)-normWeight(K),n). Thus the natural-number division (n!)^degree(K)/absNorm(fullRingFactorialIdeal(K,n)) is exact. The norm factor is positive, and multiplication by this complement recovers (n!)^degree(K).

**Definition 1.9 (Floor profile).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.floorProfile`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.floorProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite tuple a and a positive modulus q, sum floor(a(i)/q) over all parts.

**Definition 1.10 (Composition floor minimum).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.floorMinimum`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.floorMinimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For M<=H, write Q(q)=max(0,floor(H/q)-M). Natural subtraction implements this truncation.

**Definition 1.11 (Weighted prime exponent).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedExponent`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index j starts at zero and represents the modulus p^(j+1). Sum c(p,j)*floor(n/p^(j+1)) for 0<=j<=H.

**Definition 1.12 (Weighted factorial).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedValue`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For inputs n<=H, take the product over rational primes p<=H of p raised to the weighted exponent. Every omitted prime or power has zero floor contribution, so a finite cutoff represents arbitrary natural coefficient arrays.

**Definition 1.13 (Weighted composition product).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedProduct`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the weighted factorials of the entries of a finite tuple, using the same cutoff and coefficients for every entry.

**Definition 1.14 (Weighted tail).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the product over primes p<=H of p raised to sum c(p,j)*Q(p^(j+1)) for 0<=j<=H.

**Definition 1.15 (Rational prime ideal).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ideal (p) of the integers.

**Theorem 1.16 (A rational prime generates a nonzero ideal).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal_ne_bot`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal_ne_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If p is a rational prime, its integer cast is nonzero, so the principal ideal (p) is nonzero.

**Theorem 1.17 (The rational prime ideal is prime).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal_isPrime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal_isPrime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primality of p in the natural numbers gives primality of its integer cast and hence of the ideal (p). These facts identify the actual primes above p.

**Definition 1.18 (Primes over a rational prime).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.primesAbove`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.primesAbove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a number field K, use the actual finite set of prime ideals of its ring of integers above (p).

**Definition 1.19 (Residue-degree norm weights).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.normWeight`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.normWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the exponent j+1, sum the residue degree f(P) over primes P above p for which f(P) divides j+1. These are the coefficients obtained from NP=p^f(P).

**Definition 1.20 (Euler ideal in rational coordinates).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.residueFactorialIdeal`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.residueFactorialIdeal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply P raised to sum of floor(n/p^(j+1)) over indices for which f(P) divides j+1. The outer rational primes satisfy p<=H and the indices satisfy j<=H. This is an ideal of the actual ring of integers.

**Definition 1.21 (Full-ring Euler factorial ideal).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.fullRingFactorialIdeal`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.fullRingFactorialIdeal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each rational prime p<=n and each prime ideal P above p, use the exponent sum floor(n/(NP)^(j+1)) for 0<=j<=n. This finite prime-ideal Euler product is the full-ring factorial presentation. The comparison with rational coordinates reindexes j+1 by multiples of the actual residue degree, and increasing the cutoff above n leaves the ideal unchanged.

**Definition 1.22 (Integral norm complement).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.normComplement`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.normComplement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Divide (n!)^d by the absolute norm of the Euler factorial ideal, where d=[K:Q]. The norm and complement theorem proves exact divisibility and identifies this quotient with the complementary weights d-c(p,j).

**Theorem 1.23 (One composition for every power of a fixed prime).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.simultaneous_floor_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.simultaneous_floor_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S consist of the (M+1)-tuples of natural numbers summing to H-M, with M<=H. For every fixed rational prime p, one a in S satisfies sum floor(a(i)/p^j)=Q(p^j) for every j>=1. The quotient-remainder identity bounds each sum below by Q. The existing factorial gcd theorem supplies a composition attaining the sum of these lower bounds. Equality of finite sums of ordered natural coordinates forces equality in every coordinate. Powers beyond the finite cutoff contribute zero. A different rational prime may require a different composition.

**Theorem 1.24 (Exact weighted composition gcd).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weighted_composition_gcd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weighted_composition_gcd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every array of natural coefficients c, the gcd over S of the weighted composition products equals the weighted tail. Every composition gives the coordinatewise lower bounds. For each prime p the simultaneous composition attains all of its weighted bounds, including when some or all coefficients vanish. Primewise divisibility in both directions proves the exact natural-number equality. No single composition is asserted to minimize all rational primes simultaneously.

**Theorem 1.25 (Ordinary factorial certificates are universal).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.exact_certificate_is_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.exact_certificate_is_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a finite subfamily of S whose ordinary factorial products have gcd tailLCM(H,M). Then the same C has the exact weighted gcd for every natural coefficient array. For each p, if all members had strictly larger p-valuation than the tail, the next power of p would divide their gcd, a contradiction. A member attaining the ordinary valuation saturates every p-power floor bound, so it also attains every nonnegative weighted bound.

**Theorem 1.26 (A prime-counting bound for a universal family).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.exists_small_universal_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.exists_small_universal_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set t=floor(H/(M+1)). There is a family C of size at most pi(t)+1 that is exact for ordinary factorials and for every natural weighting. One composition has every entry at most t; the residue bound H mod (M+1)<=M proves its feasibility. Add one p-specific composition for each prime p<=t. These members attain the small-prime valuations. For p>t the bounded composition has valuation zero. Duplicate compositions can only reduce the cardinality. The argument includes t=0, M=H, and H=M=0.

**Theorem 1.27 (Actual ideal norms and complementary composition gcds).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.number_field_norm_and_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.number_field_norm_and_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual number field K, the residue-degree weights satisfy c(p,j)<=d. Indeed c(p,j)<=sum f(P)<=sum e(P)f(P)=d. The Euler ideal has absolute norm equal to the weighted factorial: multiplicativity of the ideal norm gives NP=p^f(P), and exchanging the finite sums gives precisely the divisibility-indexed weights. The local reindexing and cutoff comparison identify this with the Euler product using floor(n/(NP)^j). The quotient (n!)^d/NF(n) is the weighted factorial with coefficients d-c(p,j), so it is an integer. The two composition gcds are their respective weighted tails, and their product is tailLCM(H,M)^d. The proof uses common rational-prime compositions; it never moves the ideal norm through a gcd. This statement uses the Euler-product presentation of the full-ring factorial. It does not identify the weighted tail with the norm of a product of intersections of all integral ideals of bounded norm.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.complement_eq_weightedValue`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.exact_certificate_is_universal`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.exists_small_universal_certificate`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.floorMinimum`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.floorProfile`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.fullRingFactorialIdeal`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.fullRingFactorialIdeal_norm`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.normComplement`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.normWeight`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.number_field_norm_and_complement`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.prime_product_factorization`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.primesAbove`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal_isPrime`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.rationalPrimeIdeal_ne_bot`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.residueFactorialIdeal`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.simultaneous_floor_minimum`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedExponent`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedProduct`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_add`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_constant`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_factorization`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedTail_ne_zero`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedValue`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weightedValue_ne_zero`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd.weighted_composition_gcd`
- Dependency: [D5/S3/Arith/FactorialRatio/CompactFactorialGcd](../CompactFactorialGcd.md)
- Dependency: [D5/S3/Arith/FactorialRatio/RankOneLCMGcd](../RankOneLCMGcd.md)
