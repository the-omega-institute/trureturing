# Least Prime-Modulus Periods of Even-Index Fubini Numbers

## Abstract

The positive even-index Fubini sequence has the conjectured least period at every prime.

The source is OEIS A249938, revision 76, COMMENTS and FORMULA blocks, an electronic entry without page numbers. Its finite formula is: a(n) = Sum_{k=0..2*n} k! * Stirling2(2*n, k) for n>=0. The example explicitly uses n>0. Here p is a natural prime and n ranges over natural numbers, so the sequence argument n+1 expresses exactly the positive indices.

StirlingTransformTotientPeriod.T at weight one and argument 2*n is the integer sum of k! times Nat.stirlingSecond (2*n) k, for k from zero through 2*n. IsLeastPositivePeriodMod p w L means 0<L, equality of the ZMod p reductions of w(n+L) and w(n) for every natural n, and L at most every positive t with that same equality for every n. Nat.card counts the subtype of nonzero squares, including 1 for p=2. The slashes in the subtype are Lean's subtype separator. The arrow in the function is a typed lambda.

**Definition 1.1 (Provvedi's prime-modulus assertion).**

$$claim = (\forall (p : \mathbb{N}), \operatorname{Nat}.\operatorname{Prime}\left(p\right) \implies \operatorname{SomerUniformSubsequenceRefutation}.\operatorname{IsLeastPositivePeriodMod}\left(p, (\operatorname{fun} (n : \mathbb{N}) \mapsto \operatorname{StirlingTransformTotientPeriod}.\operatorname{T}\left((\operatorname{fun} (\mathord{\cdot} : \mathbb{N}) \mapsto 1), 2 \cdot \left(n + 1\right)\right)), \operatorname{Nat}.\operatorname{card}\left(\{x : \operatorname{ZMod}\left(p\right) // x \neq 0 \land \operatorname{IsSquare}\left(x\right)\}\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/ProvvediEvenFubiniLeastPrimePeriod.claim` (`✓ std3`).

*Citation.* Federico Provvedi; Paul D. Hanna (2020). *OEIS A249938, even-index Fubini numbers: prime-modulus least periods*. URL: <https://oeis.org/A249938>.

*Commentary.*

This sequence is a periodic sequence modulo m, and if m is the k-th prime, the periods of {a(n)} over k-th prime is the sequence of the number of nonzero quadratic residues modulo k-th prime, for all k>0. The prime clause is expressed with the positive-index sequence and the cardinality of nonzero squares. The composite-modulus clause and the separate divisibility-by-288 conjecture are outside this proposition. The centered dot denotes Lean's anonymous binder _.

**Theorem 1.2 (The exact least positive period).**

$$\forall (p : \mathbb{N}), \operatorname{Nat}.\operatorname{Prime}\left(p\right) \implies \operatorname{SomerUniformSubsequenceRefutation}.\operatorname{IsLeastPositivePeriodMod}\left(p, (\operatorname{fun} (n : \mathbb{N}) \mapsto \operatorname{StirlingTransformTotientPeriod}.\operatorname{T}\left((\operatorname{fun} (\mathord{\cdot} : \mathbb{N}) \mapsto 1), 2 \cdot \left(n + 1\right)\right)), \operatorname{Nat}.\operatorname{card}\left(\{x : \operatorname{ZMod}\left(p\right) // x \neq 0 \land \operatorname{IsSquare}\left(x\right)\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/ProvvediEvenFubiniLeastPrimePeriod.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Federico Provvedi; Paul D. Hanna (2020). *OEIS A249938, even-index Fubini numbers: prime-modulus least periods*. URL: <https://oeis.org/A249938>.

*Commentary.*

Pair opposite residues in the finite exponential representation. The square frequency (i+1)^2 has weight 2^(-(i+1))+2^i, which vanishes exactly when 4^(i+1)=-2. For p at least 7, three disjoint cyclic translates bound the vanishing weights by a third of all frequencies; both weights survive at p=5. Vandermonde uniqueness and a polynomial root bound then force every positive period to be at least (p-1)/2. The same number is a period. At p=2 and p=3 the positive-index sequences are constant 1 and constant 0, respectively, and their least positive period is one. The centered dot denotes Lean's anonymous binder _.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/ProvvediEvenFubiniLeastPrimePeriod.claim`
- Truth anchor: `D5/S1/Recurrence/Periodic/ProvvediEvenFubiniLeastPrimePeriod.result`
- Dependency: [D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation](SomerUniformSubsequenceRefutation.md)
- Dependency: [D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod](StirlingTransformTotientPeriod.md)
