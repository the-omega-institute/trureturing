# Hanna's pentagonal partition parity

## Abstract

The literal pentagonal unit equation and Hanna's ordinary-partition parity assertion.

Paul D. Hanna's OEIS A361552 defines an integral formal unit A by 2*x = sum over every integer k of x^(k*(3*k+1)/2) times (A^(3*k)-A^(-(3*k+1))). The conjecture states that for every integer n at least one its coefficient is even, and its integer half has the parity of the ordinary partitions of n-1.

PowerSeries denotes formal series, X its variable, and the superscript unit group makes all negative powers defined. A coefficient window is an interval of integer summation indices. The topology is the product topology of coefficients; no analytic convergence is involved. The symbol val is Units.val, unit(F,G) is the unit with value F and inverse G after its two inverse laws have been supplied, mk builds a series from its coefficients, intCast casts a natural number to the integers, and ediv is integer division. NatPartition is Nat.Partition and card is Fintype.card. Integer coefficient division and remainder occur only after evenness has been proved.

**Definition 1.1 (The exact pentagonal exponent).**

$$\forall k: \mathbb{Z}, \operatorname{exponent}\left(k\right) = \operatorname{pentagonal}\left(-(k)\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.exponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

Mathlib's pentagonal number at -k is k*(3*k+1)/2. Its exact multiplication-by-two identity proves integrality; the natural value is nonnegative and is at least the absolute value of k.

**Definition 1.2 (The complete integer-index summand).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(R\right)\right), \forall k: \mathbb{Z}, \operatorname{term}\left(A, k\right) = ((X)^{\operatorname{exponent}\left(k\right)}) \cdot ((\operatorname{val}\left((A)^{(3) \cdot (k)}\right)) - (\operatorname{val}\left((A)^{-(((3) \cdot (k)) + (1))}\right)))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.term` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

Both powers are powers of the same integral unit. The exponent bound forces each monomial separately to vanish at degree N outside [-N,N].

**Definition 1.3 (The full sum by coefficient windows).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(R\right)\right), \operatorname{bilateral}\left(A\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \sum_{k \in \operatorname{Icc}\left(-(\operatorname{intCast}\left(n\right)), \operatorname{intCast}\left(n\right)\right)} (\operatorname{coeff}\left(n, \operatorname{term}\left(A, k\right)\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.bilateral` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

At each degree this window contains every possibly nonzero integer summand. The HasSum clause below identifies it with the entire bilateral sum.

**Definition 1.4 (The original equation).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(R\right)\right), \operatorname{Original}\left(A\right) \iff \operatorname{bilateral}\left(A\right) = (2) \cdot (X)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.Original` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

The equation imposes no initial constant coefficient. Its degree-zero term is 1-A inverse, forcing that coefficient to be one.

**Definition 1.5 (The constructed integral series).**

$$\begin{aligned}\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(R\right)\right), \operatorname{nonzeroSum}\left(A\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \sum_{k \in \operatorname{erase}\left(\operatorname{Icc}\left(-(\operatorname{intCast}\left(n\right)), \operatorname{intCast}\left(n\right)\right), 0\right)} (\operatorname{coeff}\left(n, \operatorname{term}\left(A, k\right)\right)))\right)\\\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \operatorname{approximation}\left(R, 0\right) = 1\\\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \forall d: \mathbb{N}, \operatorname{approximation}\left(R, (d) + (1)\right) = \operatorname{step}\left(\operatorname{approximation}\left(R, d\right)\right)\\\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(R\right)\right), \operatorname{step}\left(A\right) = \operatorname{unit}\left(\operatorname{invOfUnit}\left(((1) - ((2) \cdot (X))) + (\operatorname{nonzeroSum}\left(A\right)), 1\right), ((1) - ((2) \cdot (X))) + (\operatorname{nonzeroSum}\left(A\right))\right)\\\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \operatorname{generatingSeries}\left(R\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{coeff}\left(n, \operatorname{val}\left(\operatorname{approximation}\left(R, (n) + (1)\right)\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

Remove the zero-index term and call the rest S(A). The iteration sends a unit A to the reciprocal of 1-2*X+S(A), whose constant coefficient is one. Agreement through degree d-1 improves through degree d. The nth coefficient is read after n+1 iterations starting at the unit one. Stabilization proves the original equation and equality with every other original unit solution.

**Definition 1.6 (The inhabited unit solution).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)] \operatorname{generatingUnit}\left(R\right) = \operatorname{unit}\left(\operatorname{generatingSeries}\left(R\right), \operatorname{invOfUnit}\left(\operatorname{generatingSeries}\left(R\right), 1\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.generatingUnit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

The constructed series has constant coefficient one. Its inverse is the formal invOfUnit at that constant unit; both inverse laws are kernel proofs.

**Definition 1.7 (Ordinary partitions).**

$$\forall n: \mathbb{N}, \operatorname{partitionCount}\left(n\right) = \operatorname{card}\left(\operatorname{NatPartition}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.partitionCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

Nat.Partition n consists of ordinary positive-part partitions of n. Its cardinality at zero is one.

**Definition 1.8 (The partition generating function).**

$$\operatorname{partitionSeries} = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{intCast}\left(\operatorname{partitionCount}\left(n\right)\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.partitionSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

The coefficients are these ordinary cardinalities cast to integers. The product supplier Nat.Partition.hasProd_powerSeriesMk_card_restricted is applied at predicate True. Euler's pentagonal product and the geometric-factor inverse prove that this series is the reciprocal of pentagonalSeries over the integers.

**Theorem 1.9 (The partition series is the pentagonal reciprocal).**

$$(\operatorname{pentagonalSeries}\left(\mathbb{Z}\right)) \cdot (\operatorname{partitionSeries}) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.partition_reciprocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

Euler's product and the geometric factors show that pentagonalSeries over the integers multiplied by the ordinary partition series is one.

**Definition 1.10 (The integer-index coefficients).**

$$\forall n: \mathbb{Z}, \operatorname{a}\left(n\right) = \operatorname{ifThenElse}\left(0 \le n, \operatorname{coeff}\left(\operatorname{toNat}\left(n\right), \operatorname{generatingSeries}\left(\mathbb{Z}\right)\right), 0\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

At a nonnegative integer n this reads the coefficient at n.toNat. Negative indices are zero; the stated parity range starts at one.

**Definition 1.11 (All clauses of the original-domain assertion).**

$$\operatorname{LiteralResolution} \iff ((\forall k: \mathbb{Z}, (\operatorname{intCast}\left(\operatorname{exponent}\left(k\right)\right) = \operatorname{ediv}\left((k) \cdot (((3) \cdot (k)) + (1)), 2\right)) \land ((0 \le \operatorname{intCast}\left(\operatorname{exponent}\left(k\right)\right)) \land ((2) \cdot (\operatorname{intCast}\left(\operatorname{exponent}\left(k\right)\right)) = (k) \cdot (((3) \cdot (k)) + (1))))) \land ((\forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(\mathbb{Z}\right)\right), \forall N: \mathbb{N}, \forall k: \mathbb{Z}, (\neg (k \in \operatorname{Icc}\left(-(\operatorname{intCast}\left(N\right)), \operatorname{intCast}\left(N\right)\right))) \implies ((\operatorname{coeff}\left(N, ((X)^{\operatorname{exponent}\left(k\right)}) \cdot (\operatorname{val}\left((A)^{(3) \cdot (k)}\right))\right) = 0) \land (\operatorname{coeff}\left(N, ((X)^{\operatorname{exponent}\left(k\right)}) \cdot (\operatorname{val}\left((A)^{-(((3) \cdot (k)) + (1))}\right))\right) = 0))) \land ((\forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(\mathbb{Z}\right)\right), \operatorname{HasSum}\left((k: \mathbb{Z} \mapsto \operatorname{term}\left(A, k\right)), \operatorname{bilateral}\left(A\right)\right)) \land ((\operatorname{Original}\left(\operatorname{generatingUnit}\left(\mathbb{Z}\right)\right)) \land ((\forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(\mathbb{Z}\right)\right), (\operatorname{Original}\left(A\right)) \implies ((\operatorname{constantCoeff}\left(\operatorname{val}\left(A\right)\right) = 1) \land ((A = \operatorname{generatingUnit}\left(\mathbb{Z}\right)) \land (\forall n: \mathbb{Z}, (1 \le n) \implies ((2 \mid \operatorname{coeff}\left(\operatorname{toNat}\left(n\right), \operatorname{val}\left(A\right)\right)) \land (\operatorname{ediv}\left(\operatorname{coeff}\left(\operatorname{toNat}\left(n\right), \operatorname{val}\left(A\right)\right), 2\right) \bmod 2 = \operatorname{intCast}\left(\operatorname{partitionCount}\left(\operatorname{toNat}\left((n) - (1)\right)\right)\right) \bmod 2)))))) \land ((\operatorname{partitionCount}\left(0\right) = 1) \land (\forall n: \mathbb{Z}, (0 \le n) \implies (\operatorname{a}\left(n\right) = \operatorname{coeff}\left(\operatorname{toNat}\left(n\right), \operatorname{generatingSeries}\left(\mathbb{Z}\right)\right)))))))))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.LiteralResolution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

The clauses give exponent validity, local finiteness of both monomials, the whole bilateral HasSum, integral unit existence, forced constant coefficient one, uniqueness among every original unit solution, all positive integer indices, the unique empty partition, and the signed-index correspondence.

**Theorem 1.12 (The literal partition-parity assertion).**

$$(\forall k: \mathbb{Z}, (\operatorname{intCast}\left(\operatorname{exponent}\left(k\right)\right) = \operatorname{ediv}\left((k) \cdot (((3) \cdot (k)) + (1)), 2\right)) \land ((0 \le \operatorname{intCast}\left(\operatorname{exponent}\left(k\right)\right)) \land ((2) \cdot (\operatorname{intCast}\left(\operatorname{exponent}\left(k\right)\right)) = (k) \cdot (((3) \cdot (k)) + (1))))) \land ((\forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(\mathbb{Z}\right)\right), \forall N: \mathbb{N}, \forall k: \mathbb{Z}, (\neg (k \in \operatorname{Icc}\left(-(\operatorname{intCast}\left(N\right)), \operatorname{intCast}\left(N\right)\right))) \implies ((\operatorname{coeff}\left(N, ((X)^{\operatorname{exponent}\left(k\right)}) \cdot (\operatorname{val}\left((A)^{(3) \cdot (k)}\right))\right) = 0) \land (\operatorname{coeff}\left(N, ((X)^{\operatorname{exponent}\left(k\right)}) \cdot (\operatorname{val}\left((A)^{-(((3) \cdot (k)) + (1))}\right))\right) = 0))) \land ((\forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(\mathbb{Z}\right)\right), \operatorname{HasSum}\left((k: \mathbb{Z} \mapsto \operatorname{term}\left(A, k\right)), \operatorname{bilateral}\left(A\right)\right)) \land ((\operatorname{Original}\left(\operatorname{generatingUnit}\left(\mathbb{Z}\right)\right)) \land ((\forall A: \operatorname{Units}\left(\operatorname{PowerSeries}\left(\mathbb{Z}\right)\right), (\operatorname{Original}\left(A\right)) \implies ((\operatorname{constantCoeff}\left(\operatorname{val}\left(A\right)\right) = 1) \land ((A = \operatorname{generatingUnit}\left(\mathbb{Z}\right)) \land (\forall n: \mathbb{Z}, (1 \le n) \implies ((2 \mid \operatorname{coeff}\left(\operatorname{toNat}\left(n\right), \operatorname{val}\left(A\right)\right)) \land (\operatorname{ediv}\left(\operatorname{coeff}\left(\operatorname{toNat}\left(n\right), \operatorname{val}\left(A\right)\right), 2\right) \bmod 2 = \operatorname{intCast}\left(\operatorname{partitionCount}\left(\operatorname{toNat}\left((n) - (1)\right)\right)\right) \bmod 2)))))) \land ((\operatorname{partitionCount}\left(0\right) = 1) \land (\forall n: \mathbb{Z}, (0 \le n) \implies (\operatorname{a}\left(n\right) = \operatorname{coeff}\left(\operatorname{toNat}\left(n\right), \operatorname{generatingSeries}\left(\mathbb{Z}\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a361552-literal-partition-parity` (proved) by `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a361552-literal-partition-parity","declaration_gid":"D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A361552: implicit pentagonal unit series and partition parity*. URL: <https://oeis.org/A361552>.

*Commentary.*

Map the original unit equation to characteristic two and use uniqueness to obtain A=1 there. Thus A=1+2*B with integral B defined by exact coefficient division. In characteristic four this unit squares to one. Reducing integer powers modulo two and multiplying Euler signs by two gives 2*(B*pentagonalSeries-X)=0 modulo four. Coefficientwise integer divisibility 4 divides 2*c implies 2 divides c; no nonunit cancellation is made in characteristic four. The ordinary-partition reciprocal then gives B=X*partitionSeries modulo two. The identity n.toNat=(n-1).toNat+1 for n at least one completes the integer-index coefficient statement.

## References

- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.LiteralResolution`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.Original`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.a`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.bilateral`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.exponent`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.generatingUnit`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.partitionCount`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.partitionSeries`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.partition_reciprocal`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.result`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.term`
