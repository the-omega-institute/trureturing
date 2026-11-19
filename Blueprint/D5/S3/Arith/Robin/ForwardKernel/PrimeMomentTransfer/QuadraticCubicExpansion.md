# Quadratic and cubic moment expansions

## Abstract

Second and third moments of centered algebra elements satisfying a common quadratic relation.

Let the index type be finite, A a commutative real algebra, and ell a real linear functional with ell(1)=1. Suppose ell(Y(d))=0 and Y(d)^2=a*Y(d)+b for every index d. For real coefficient functions, indexSum is their sum, quadraticFamilyMoment is ell applied to the product of the weighted sums, and distinctIndexMoment is the sum over ordered injective tuples. Neither positivity nor independence is assumed; the finite index type may be empty.

**Theorem 1.1 (The second moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion.quadratic_second_moment_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion.quadratic_second_moment_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any f and g, quadraticFamilyMoment(f,g)=distinctIndexMoment(f,g)+b*indexSum(f*g). Split the ordered pairs into distinct indices and equal indices. The quadratic relation and centering give ell(Y(d)^2)=b, which evaluates the diagonal.

**Theorem 1.2 (The third moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion.quadratic_third_moment_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion.quadratic_third_moment_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any f, g and h, quadraticFamilyMoment(f,g,h)=distinctIndexMoment(f,g,h) +a*(distinctIndexMoment(f*g,h)+distinctIndexMoment(f*h,g)+distinctIndexMoment(g*h,f))+a*b*indexSum(f*g*h). The three-index equality classification separates distinct triples, the three choices of a repeated pair, and the triple diagonal. The quadratic relation reduces each repeated-pair contribution to a times its ordered distinct-pair sum, because the remaining first moment is zero. The same relation gives ell(Y(d)^3)=a*b and hence the final diagonal term.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion.quadratic_second_moment_eq`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion.quadratic_third_moment_eq`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns](IndexEqualityPatterns.md)
