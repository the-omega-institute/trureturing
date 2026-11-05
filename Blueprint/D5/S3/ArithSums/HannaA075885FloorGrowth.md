# Hanna's A075885 root limit

## Abstract

Hanna's floor-prefix sum has the positive root limit specified by its logarithmic series.

The maximal prefix product bounds the sum from below. Multiplying that product by n+1 bounds the sum from above. Their normalized logarithms have the same limit because log(n+1)/n tends to zero. Counting floor quotients and dominated convergence evaluate this limit.

**Definition 1.1 (The sum of prefixes).**

$$\forall n \in \mathbb{N}, \operatorname{a}\left(n\right) = 1 + \sum_{m \in \operatorname{Finset}.\operatorname{Icc}\left(1, n\right)} (\prod_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, m\right)} (\operatorname{Nat}.\operatorname{div}\left(n, k\right)))$$

*Formalization.* `D5/S3/ArithSums/HannaA075885FloorGrowth.a` (`✓ std3`).

*Citation.* Paul D. Hanna; OEIS Foundation Inc. (2002). *OEIS A075885 revision 28: Hanna's floor-prefix root-limit conjecture*. URL: <https://oeis.org/A075885>.

*Commentary.*

OEIS A075885 revision 28, FORMULA (unpaginated): "a(n) = 1 + Sum_{m=1..n} Product_{k=1..m} floor(n/k)." The indices and values are natural numbers. Nat.div is integer division, hence floor(n/k) for positive k. Finset.Icc includes both endpoints. The outer empty sum gives a(0)=1, and the source example gives a(5)=46.

**Definition 1.2 (The source logarithmic series).**

$$\forall j \in \mathbb{N}, \operatorname{logSummand}\left(j\right) = \frac{\operatorname{Real}.\operatorname{log}\left((j: \mathbb{R}) + 1\right)}{((j: \mathbb{R}) + 1) \cdot ((j: \mathbb{R}) + 2)}$$

*Formalization.* `D5/S3/ArithSums/HannaA075885FloorGrowth.logSummand` (`✓ std3`).

*Citation.* Paul D. Hanna; OEIS Foundation Inc. (2002). *OEIS A075885 revision 28: Hanna's floor-prefix root-limit conjecture*. URL: <https://oeis.org/A075885>.

*Commentary.*

OEIS A075885 revision 28, COMMENT (unpaginated): "Conjecture: limit a(n)^(1/n) = L where L = 2.200161058099... is the geometric mean of Luroth expansions, where log(L) = Sum_{n>=1} log(n)/(n*(n+1)) = 0.7885305659115... (cf. A085361)." The source index is j+1, so j ranges over all natural numbers. All divisions in this formula are real divisions; its denominator is positive.

**Definition 1.3 (Hanna's conjecture).**

$$claim = (\exists L \in \mathbb{R}, (0 < L) \land (\operatorname{HasSum}\left((fun (j: \mathbb{N}) \mapsto \operatorname{logSummand}\left(j\right)), \operatorname{Real}.\operatorname{log}\left(L\right)\right)) \land (\operatorname{Filter}.\operatorname{Tendsto}\left((fun (n: \mathbb{N}) \mapsto (\operatorname{a}\left(n + 1\right): \mathbb{R})^{\frac{1}{(n: \mathbb{R}) + 1}}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(L\right)\right)))$$

*Formalization.* `D5/S3/ArithSums/HannaA075885FloorGrowth.claim` (`✓ std3`).

*Citation.* Paul D. Hanna; OEIS Foundation Inc. (2002). *OEIS A075885 revision 28: Hanna's floor-prefix root-limit conjecture*. URL: <https://oeis.org/A075885>.

*Commentary.*

OEIS A075885 revision 28, COMMENT (unpaginated): "Conjecture: limit a(n)^(1/n) = L where L = 2.200161058099... is the geometric mean of Luroth expansions, where log(L) = Sum_{n>=1} log(n)/(n*(n+1)) = 0.7885305659115... (cf. A085361)." L is required to be positive. HasSum requires convergence of the logarithmic series, with its source index shifted from one to j+1. The root index n+1 ranges over exactly the positive integers; the exponent is real and the base is the real image of a(n+1). The decimals identify the source constant and are not extra numerical assertions.

**Theorem 1.4 (The positive limit and its exact logarithm).**

$$\exists L \in \mathbb{R}, (0 < L) \land (\operatorname{HasSum}\left((fun (j: \mathbb{N}) \mapsto \operatorname{logSummand}\left(j\right)), \operatorname{Real}.\operatorname{log}\left(L\right)\right)) \land (\operatorname{Filter}.\operatorname{Tendsto}\left((fun (n: \mathbb{N}) \mapsto (\operatorname{a}\left(n + 1\right): \mathbb{R})^{\frac{1}{(n: \mathbb{R}) + 1}}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(L\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaA075885FloorGrowth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna; OEIS Foundation Inc. (2002). *OEIS A075885 revision 28: Hanna's floor-prefix root-limit conjecture*. URL: <https://oeis.org/A075885>.

*Commentary.*

The logarithm of the full product is a finite sum of logarithmic increments weighted by floor quotients. The quotient ratios converge pointwise and the reciprocal-product series is a summable majorant. Finite summation by parts identifies the sum with the source series. The sum/product bounds then give convergence of normalized logarithms, and continuity of Real.exp gives the real root limit.

## References

- Truth anchor: `D5/S3/ArithSums/HannaA075885FloorGrowth.a`
- Truth anchor: `D5/S3/ArithSums/HannaA075885FloorGrowth.claim`
- Truth anchor: `D5/S3/ArithSums/HannaA075885FloorGrowth.logSummand`
- Truth anchor: `D5/S3/ArithSums/HannaA075885FloorGrowth.result`
- Dependency: [D5/S3/Arith/Coding/ResidueCodeDynamicRange](../Arith/Coding/ResidueCodeDynamicRange.md)
- Dependency: [D5/S3/ArithSums/A400361PillaiMean](A400361PillaiMean.md)
