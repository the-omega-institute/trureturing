# Completeness of the bounded candidate table

## Abstract

Completeness of the bounded candidate table

**Definition 1.1 (The counted predecessor set).**

$$candidatePredecessors = \operatorname{candidateFilter}\left(\operatorname{factoredMultiples}\left(\operatorname{toFinset}\left(allPrimes\right), bound, 2\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage.candidatePredecessors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

This finite set contains the positive even predecessors at most one million whose quotient by two uses primes at most 97 and whose candidate test succeeds.

**Theorem 1.2 (Exact candidate test on primes).**

$$\forall q \in \mathbb{N},\; \operatorname{Prime}\left(q\right) \Rightarrow \left(\operatorname{candidate}\left(q - 1\right) = true \Leftrightarrow \operatorname{notPowerOfTwo}\left(q - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage.candidate_of_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For a prime q, the candidate test succeeds exactly when q-1 is not a power of two. Fermat's little theorem supplies its congruence and primality excludes the listed trial divisors. No size bound or smoothness assumption is needed.

**Theorem 1.3 (Exact bounded candidate coverage).**

$$\forall T \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{all}\left(validEntry, T\right) = true \Rightarrow \left(\operatorname{Nodup}\left(\operatorname{map}\left(entryValue, T\right)\right) \Rightarrow \left(\operatorname{smoothSum}\left(candidateWeight, allPrimes, bound, 2\right) \le \operatorname{length}\left(T\right) \Rightarrow \left(\forall q \in \mathbb{N},\; \left(\exists e \in \mathbb{N},\; \operatorname{member}\left(e, T\right) \land \operatorname{entryValue}\left(e\right) = q\right) \Leftrightarrow \left(q - 1 \le bound \land \left(\operatorname{candidate}\left(q - 1\right) = true \land \operatorname{member}\left(q - 1, \operatorname{smoothNumbers}\left(98\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage.prime_mem_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For every list T whose entries pass validEntry, whose values are distinct, and whose length is at least smoothSum(candidateWeight,allPrimes,bound,2), a natural number q has a labelled entry exactly when q-1 is at most one million, the candidate test succeeds, and q-1 is 98-smooth. Smoothness already forces q to be at least two. The general recursive count turns inclusion into equality. Validity gives inclusion, distinctness converts length to cardinality, and the count inequality excludes omissions. Without validity spurious entries are possible; without distinctness repeated entries can fill the length bound while omitting a candidate; without the count bound a proper sublist need not cover every candidate. Candidate success is not a primality certificate.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage.candidatePredecessors`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage.candidate_of_prime`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage.prime_mem_table`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState](CertificateState.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration](Enumeration.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip](Strip.md)
