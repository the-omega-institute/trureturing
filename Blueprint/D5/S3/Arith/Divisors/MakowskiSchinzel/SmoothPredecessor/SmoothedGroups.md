# Grouped bound from arbitrary checked inputs

## Abstract

Grouped bound from arbitrary checked inputs

**Theorem 1.1 (The finite prefix and unbounded smooth tail).**

$$\forall E \in \operatorname{List}\left(\mathbb{N}\right),\; \forall t \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall z \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{all}\left(validEntry, E\right) = true \Rightarrow \left(\operatorname{Nodup}\left(\operatorname{map}\left(entryValue, E\right)\right) \Rightarrow \left(\left(\forall i \in \mathbb{N},\; \operatorname{PairwiseLe}\left(\operatorname{groupValues}\left(i, E\right)\right)\right) \Rightarrow \left(\operatorname{smoothSum}\left(candidateWeight, allPrimes, bound, 2\right) \le \operatorname{length}\left(E\right) \Rightarrow \left(\operatorname{map}\left(tailData, oddPrimes\right) = t \Rightarrow \left(\operatorname{stepTable}\left(t, E, initialState\right) = \operatorname{some}\left(z\right) \Rightarrow \left(\operatorname{finalOk}\left(t, z\right) = true \Rightarrow \left(\forall Q \in \operatorname{Finset}\left(\mathbb{N}\right),\; \left(\forall q \in \mathbb{N},\; \operatorname{member}\left(q, Q\right) \Rightarrow \operatorname{member}\left(\operatorname{subOne}\left(q\right), \operatorname{smoothNumbers}\left(98\right)\right)\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; \operatorname{member}\left(q, Q\right) \Rightarrow \left(\left(\operatorname{subOne}\left(q\right) \le bound \Rightarrow \operatorname{candidate}\left(\operatorname{subOne}\left(q\right)\right) = true\right) \land \left(bound < \operatorname{subOne}\left(q\right) \Rightarrow \left(\operatorname{Odd}\left(q\right) \land \operatorname{NotPowerOfTwo}\left(\operatorname{subOne}\left(q\right)\right)\right)\right)\right)\right) \Rightarrow \prod_{q \in Q} \frac{q}{\operatorname{subOne}\left(q\right)} \le \prod_{p \in \operatorname{toFinset}\left(oddPrimes\right)} \operatorname{geom}\left(p, \sum_{q \in Q} \operatorname{factorization}\left(\operatorname{subOne}\left(q\right), p\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/SmoothedGroups.smooth_group_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any encoded list E, tail constants t and final states z, assume all entries pass validEntry, successor values have no repetitions, and the values within each label group are nondecreasing. Assume also that the recursive candidate count is at most length(E), t is the map of tailData on oddPrimes, the run from initialState reaches z, and finalOk(t,z) passes. Let Q have 98-smooth predecessors, successful candidate tests below bound, and odd successors with non-power-of-two predecessors above bound. Then Q satisfies the displayed grouped product bound. No primality of Q is assumed. Validity, absence of repetitions and count give complete bounded coverage; the tail map identifies the constants in the run; the run and final test control all group prefixes. Smoothness, oddness and the non-power-of-two condition give the large-predecessor labels. Missing any of these inputs leaves the corresponding step unsupported. The conclusion does not recover the supplied certificate: it holds for Q empty even when a chosen input list fails its checks.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/SmoothedGroups.smooth_group_product`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage](FiniteCoverage.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/LocalGroup](LocalGroup.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/TailConstants](TailConstants.md)
- Dependency: [D5/S3/Arith/Robin/PaddingRatio](../../../Robin/PaddingRatio.md)
- Dependency: [D5/S3/Factorization/JordanCototientRecordLimitInfinity](../../../../Factorization/JordanCototientRecordLimitInfinity.md)
