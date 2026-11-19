# Lemma 498.2: quadratic fourth-order pairing defect

## Abstract

Lemma 498.2 expresses the fourth-order pairing defect under a quadratic relation.

**Theorem 1.1 (The fourth-order pairing defect).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthDefect.quadratic_fourth_pairing_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthDefect.quadratic_fourth_pairing_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family Y in a commutative real algebra and a real linear functional ell, assume ell(1)=1, ell(Y_d)=0, and Y_d^2=a*Y_d+b. For arbitrary real coefficient functions f,g,h,q, subtract the three products of second moments from their fourth moment. The result equals the distinct-index fourth moment minus the three products of distinct-index second moments, plus a times the six third-moment terms with one coefficient pair multiplied, plus a^2 times the three second-moment terms with two coefficient pairs, plus (a^2-2b) times the four triple/singleton second moments, plus (a^2*b-2b^2)*indexSum(f*g*h*q). This is identity (498.5).

The raw fourth expansion supplies the multiplicity contributions. In each covariance product, substitute quadraticFamilyMoment(u,v)=distinctIndexMoment(u,v)+b*indexSum(u*v). The six mixed indexSum*distinctIndexMoment terms and three products of indexSum sums cancel exactly. The distinct sums count ordered injective tuples without a factorial factor. This is an algebraic identity and does not assume a probability measure, positivity of ell, or independence.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthDefect.quadratic_fourth_pairing_defect`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion](QuadraticCubicExpansion.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion](QuadraticFourthExpansion.md)
