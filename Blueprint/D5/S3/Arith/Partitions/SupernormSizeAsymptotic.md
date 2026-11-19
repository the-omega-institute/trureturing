# Reciprocal supernorms in the size ensemble

## Abstract

Reciprocal prime supernorms over all partitions of size n have leading term exp(gamma)/n.

Nat denotes the nonnegative integers and Real the real numbers. A partition of n is an unordered multiset of positive parts whose sum is n. The source is Lagarias and Sun, arXiv:2308.15303v1: equation (3.1) defines the size ensemble, and Conjecture 3.5 states its asymptotic.

**Definition 1.1 (Primes attached to positive parts).**

$$\forall k \in \operatorname{Nat},\; \operatorname{partPrime}\left(k\right) = \operatorname{Nat}.\operatorname{nth}\left(\operatorname{Nat}.\operatorname{Prime}, \operatorname{Nat}.\operatorname{sub}\left(k, 1\right)\right)$$

*Formalization.* `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.partPrime` (`✓ std3`).

*Citation.* Jeffrey C. Lagarias and Chenyang Sun (2024). *Asymptotics of reciprocal supernorm partition statistics*. DOI: [10.1007/s11139-024-00893-8](https://doi.org/10.1007/s11139-024-00893-8). URL: <https://arxiv.org/abs/2308.15303v1>.

*Commentary.*

Nat.nth numbers the primes from zero, and Nat.sub is truncated natural subtraction. Thus partPrime(k) is the k-th prime for every positive k, with partPrime(1)=2. Its value at zero is also two. The source's separate convention p_0=1 is immaterial because a partition has no zero part.

**Definition 1.2 (The supernorm of a partition).**

$$\forall n \in \operatorname{Nat},\; \forall p \in \operatorname{Nat}.\operatorname{Partition}\left(n\right),\; \operatorname{supernorm}\left(p\right) = \operatorname{Multiset}.\operatorname{prod}\left(\operatorname{Multiset}.\operatorname{map}\left(\operatorname{partPrime}, \operatorname{parts}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.supernorm` (`✓ std3`).

*Citation.* Jeffrey C. Lagarias and Chenyang Sun (2024). *Asymptotics of reciprocal supernorm partition statistics*. DOI: [10.1007/s11139-024-00893-8](https://doi.org/10.1007/s11139-024-00893-8). URL: <https://arxiv.org/abs/2308.15303v1>.

*Commentary.*

Multiset.map retains every occurrence of a part, and Multiset.prod multiplies all mapped occurrences. A repeated part contributes its prime with the same multiplicity. The empty product is one.

**Definition 1.3 (The complete fixed-size weight).**

$$\forall n \in \operatorname{Nat},\; \operatorname{Wsize}\left(n\right) = \sum_{p: \operatorname{Nat}.\operatorname{Partition}\left(n\right)} \frac{1}{(\operatorname{supernorm}\left(p\right): \operatorname{Real})}$$

*Formalization.* `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.Wsize` (`✓ std3`).

*Citation.* Jeffrey C. Lagarias and Chenyang Sun (2024). *Asymptotics of reciprocal supernorm partition statistics*. DOI: [10.1007/s11139-024-00893-8](https://doi.org/10.1007/s11139-024-00893-8). URL: <https://arxiv.org/abs/2308.15303v1>.

*Commentary.*

The sum contains every partition of exactly n once. The denominator is the natural supernorm cast to Real. All prime factors are positive, so this is precisely the source's reciprocal supernorm weight.

**Theorem 1.4 (The size asymptotic).**

$$\operatorname{Tendsto}\left((\operatorname{fun}(n: \operatorname{Nat}) \mapsto (n: \operatorname{Real}) \cdot \operatorname{Wsize}\left(n\right)), \operatorname{atTop}, \operatorname{nhds}\left(\operatorname{Real}.\operatorname{exp}\left(\operatorname{Real}.\operatorname{eulerMascheroniConstant}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.result` (`✓ std3`). ∎

*Resolves.* `Problems/lagarias-sun-2024-supernorm-size-asymptotic` (proved) by `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lagarias-sun-2024-supernorm-size-asymptotic","declaration_gid":"D5/S3/Arith/Partitions/SupernormSizeAsymptotic.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jeffrey C. Lagarias and Chenyang Sun (2024). *Asymptotics of reciprocal supernorm partition statistics*. DOI: [10.1007/s11139-024-00893-8](https://doi.org/10.1007/s11139-024-00893-8). URL: <https://arxiv.org/abs/2308.15303v1>.

*Commentary.*

The function n times Wsize(n) tends to exp(gamma) along all natural indices tending to infinity, where gamma is Euler's constant. Since exp(gamma) is positive, this is equivalent to Wsize(n) asymptotic to exp(gamma)/n, exactly Conjecture 3.5. No monotonicity of the individual weights is assumed. Finite geometric products and their energy moments bound the cumulative mass A_n between E_m(1-m/n) and E_n, where E_m is the product of (1-1/p_j)^(-1) for 1<=j<=m. Taking m=floor(n/log n), Mertens' product theorem and the prime number theorem give A_n/log n tending to exp(gamma). Marking repeated parts and deleting them gives the positive convolution n Wsize(n)=sum_{j=1}^n b_j Wsize(n-j), with b_j=sum_{d|j} d/p_d^(j/d). Its proper-divisor remainder is at most 2 times the divisor count divided by j, hence b_j log j tends to one. A uniform estimate on the half window gives the main term. Strong induction bounds n Wsize(n), and Cesaro averaging makes the remaining half convolution tend to zero.

## References

- Truth anchor: `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.Wsize`
- Truth anchor: `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.partPrime`
- Truth anchor: `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.result`
- Truth anchor: `D5/S3/Arith/Partitions/SupernormSizeAsymptotic.supernorm`
- Dependency: [D5/S3/Arith/Divisors/DivisorSubpower](../Divisors/DivisorSubpower.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder](../Robin/PriceRecord/PrimeBoundarySecondOrder.md)
- Dependency: [D5/S3/Combinatorics/Partitions/OverpartitionThreshold](../../Combinatorics/Partitions/OverpartitionThreshold.md)
- Dependency: [D5/S3/Combinatorics/Partitions/PositiveEnergyPartition](../../Combinatorics/Partitions/PositiveEnergyPartition.md)
