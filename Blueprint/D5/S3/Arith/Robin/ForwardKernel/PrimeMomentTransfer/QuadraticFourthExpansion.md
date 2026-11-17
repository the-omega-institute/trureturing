# Fourth-order expansion

## Abstract

The fourth moment of finite coefficient sums expands according to index multiplicity.

**Theorem 1.1 (Two distinct indices).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion.sum_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion.sum_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type with decidable equality and every real function F of two indices, the sum of F(x(0),x(1)) over injective functions x from the two-element type equals the iterated sum of F(d,e) over all ordered pairs of unequal indices d,e.

**Theorem 1.2 (Expansion under a quadratic relation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion.quadratic_fourth_moment_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion.quadratic_fourth_moment_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the index type be finite, let A be a commutative real algebra, and let ell be a real linear functional with ell(1)=1. Assume ell(Y_d)=0 and Y_d^2=a*Y_d+b for every index d. For any four real coefficient functions f,g,h,q, the fourth moment equals the ordered distinct-index fourth moment, plus a times the six distinct third moments formed by multiplying one pair of coefficients, plus a^2 times the three distinct second moments formed by two pairs, plus (a^2-2b) times the four triple/singleton second moments, plus (a^2*b-2b^2) times indexSum(f*g*h*q), plus b times the six terms indexSum(f_i*f_j)*distinctIndexMoment(f_k,f_l), plus b^2 times the three products indexSum(f_i*f_j)*indexSum(f_k*f_l).

The fifteen equality patterns of an ordered four-tuple give the five multiplicity types. In a pair and two singletons, summing the repeated index away from the two singleton indices gives indexSum(f_i*f_j) minus its values at those two indices. Each triple/singleton term is subtracted three times. The quadratic relation evaluates the remaining two-pair, triple/singleton, and quadruple contributions. No positivity, independence, or nonempty-index assumption is required.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion.quadratic_fourth_moment_expansion`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion.sum_two`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns](IndexEqualityPatterns.md)
- Dependency: [D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection](../../../../Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.md)
- Dependency: [D5/S3/Zeros/LeeYang/TreePairStability](../../../../Zeros/LeeYang/TreePairStability.md)
