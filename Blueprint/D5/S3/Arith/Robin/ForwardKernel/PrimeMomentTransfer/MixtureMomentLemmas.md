# Finite-mixture moment comparisons

## Abstract

Finite algebraic moment data and biased-cube mixture identities apply at arbitrary order.

**Definition 1.1 (Finite algebraic moment data).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.FifthData`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.FifthData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A datum consists of a finite decidable index type, a commutative real algebra, a real linear functional, an indexed algebra family, and four real parameters a,b,H,L. Both underlying types are in universe zero; positivity is a hypothesis of the implication below.

**Theorem 1.2 (An arbitrary-order collision bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.inj_sum_product_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.inj_sum_product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r be positive and let N be at least r. For r real coefficient families on N indices bounded in absolute value by one, removing noninjective assignments from the product of coefficient sums changes its value by at most choose(r,2) N^(r-1). The number of omitted assignments is N^r minus the descending factorial. Its recurrence bounds the next-order error by N times the previous error plus r N^r; the binomial recursion gives the stated constant.

**Theorem 1.3 (The whole label set).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subsetDistinct_univ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subsetDistinct_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary k, evaluating the subset distinct-index moment on all labels in Fin k recovers the original ordered distinct-index moment by reindexing its canonical enumeration.

**Theorem 1.4 (Unit-weight moments of any finite mixture).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subset_unit_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subset_unit_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite real bias values and weights, let m_j be the weighted j-th bias moment. For a label subset U of cardinality j, the unit-weight distinct-index moment equals m_j divided by (sqrt(N))^j, multiplied by the descending factorial of N of length j. The formula counts the injective assignments and does not require positive weights.

**Theorem 1.5 (The two-label formula).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.distinct_pair_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.distinct_pair_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite bias mixture and real coefficient families f and h on N indices, the two-label distinct moment is m_2/N times ((sum f)(sum h) minus sum(f h)). The off-diagonal sum removes precisely the equal-index assignments.

**Theorem 1.6 (Two-label subsets of any finite label type).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subset_pair_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subset_pair_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a two-element label subset e and arbitrary real coefficient families g, its distinct moment is m_2/N times (the product over i in e of sum_d g_i(d), minus sum_d of the product over i in e of g_i(d)). Reindexing the two labels gives the preceding two-label formula.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.FifthData`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.distinct_pair_formula`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.inj_sum_product_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subsetDistinct_univ`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subset_pair_formula`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas.subset_unit_moment`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture](BiasedCubeMixture.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra](PairingDefectAlgebra.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion](QuadraticFourthExpansion.md)
