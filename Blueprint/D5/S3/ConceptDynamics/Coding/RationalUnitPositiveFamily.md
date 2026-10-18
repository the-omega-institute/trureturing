# A positive family from given rational matrix units

## Abstract

Arbitrary given rational augmentation-ideal matrix units admit one strictly positive integral family with exact positive uniformizing depths and exact rectangular exchange distances.

**Theorem 1.1 (Synchronized positive factors in the given realization).**

Lean statement: `D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily.theorem26_2`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily.theorem26_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite nontrivial group of order q, and let n and d be positive integers. In the original n by n rational group-matrix ring, suppose that the given units e(a,b) satisfy e(a,b)e(c,f)=delta(b,c)e(a,f), every entry has augmentation zero, and e(1,1) is nonzero. No relation d<=n, involution condition, or ambient-identity condition on the diagonal sum is assumed. The Lean indices start at zero; zero extension serves only to write finite sums in these same matrices.

For 1<=t<=d, set N(t)=sum over 1<=a<t of e(a,a+1) and P(t)=sum over 1<=a<t of e(a,a). Choose one positive integer c clearing every coefficient of every given unit. Choose one positive integer K strictly exceeding the absolute values of all coefficients of cN(t) and cP(t), simultaneously for the whole family. Let u be the sum of all group elements and let J be the n by n matrix with every entry one.

$W = \operatorname{smul}\left(K, J \cdot u\right)$

$\operatorname{R}\left(t\right) = W + \operatorname{smul}\left(c, \operatorname{P}\left(t\right)\right)$

$\operatorname{S}\left(t\right) = W + \operatorname{smul}\left(c, \operatorname{N}\left(t\right)\right)$

$\operatorname{B}\left(t\right) = \operatorname{power}\left(W, 2\right) + \operatorname{smul}\left(\operatorname{power}\left(c, 2\right), \operatorname{N}\left(t\right)\right)$

All the displayed R(t), S(t) and B(t) have strictly positive integer group coefficients. The formulas are identities after the injective natural-to-rational coefficient map; hence the factors and endpoints are actual matrices over the natural group ring in the given realization.

The unit relations give P(t)N(t)=N(t) and N(t)P(t)=N(t-1). Augmentation zero kills both cross terms with W. Consequently, for 2<=t<=d, the same two positive factors satisfy the two adjacent product identities.

$\operatorname{R}\left(t\right) \cdot \operatorname{S}\left(t\right) = \operatorname{B}\left(t\right)$

$\operatorname{S}\left(t\right) \cdot \operatorname{R}\left(t\right) = \operatorname{B}\left(t - 1\right)$

$\operatorname{power}\left(W, 2\right) = \operatorname{smul}\left(q \cdot n \cdot \operatorname{power}\left(K, 2\right), J \cdot u\right)$

$\operatorname{augmentation}\left(\operatorname{B}\left(t\right)\right) = \operatorname{smul}\left(\operatorname{power}\left(q, 2\right) \cdot n \cdot \operatorname{power}\left(K, 2\right), J\right)$

For 1<=j<t, induction in the original matrix ring gives N(t)^j=sum over 1<=a<=t-j of e(a,a+j). The t-th power is zero. Multiplying the j-th power on the left by e(1,1) selects e(1,j+1), which is nonzero because its product with e(j+1,1) is e(1,1). This proves exact depth t without imposing that the sum of the units is the ambient identity. For t=1, N(1)=0 has least positive depth one; no claim about its zeroth power is needed.

Quotient the rational group algebra by its ideal of uniform elements. The quotient kills W and preserves every nonzero positive power of the augmentation-zero shift, since augmentation together with this quotient is injective. The nonzero scalar c squared preserves the exact depth. Uniformity of a natural group matrix is equivalent to vanishing in this quotient, so its least positive uniformizing exponent is exactly t.

$\operatorname{tau}\left(\operatorname{B}\left(t\right)\right) = t$

The adjacent factors construct chains in either direction, including an empty chain for t=r. For every competing rectangular exchange chain, map every vertex and factor through the same quotient and apply the general rectangular nilpotence-depth barrier. It bounds the two endpoint depths in both directions, so its length is at least the absolute depth difference. Intermediate dimensions are unrestricted, including zero wherever the chain interface permits it. The cases n=1, d=1 and either endpoint t=1 remain in scope.

$\operatorname{minimumExchangeLength}\left(\operatorname{B}\left(t\right), \operatorname{B}\left(r\right)\right) = \operatorname{dist}\left(t, r\right)$

This construction chooses a new common positive baseline for the supplied units. It does not embed an arbitrary previously fixed inert matrix into the family.

**Theorem 1.2 (The construction preserves supplied constants).**

Lean statement: `D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily.positiveFamily_with_constants`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily.positiveFamily_with_constants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the given rational augmentation-ideal matrix units, supply positive integers c,K and integer group matrices Z(a,b) whose rational casts equal c times e(a,b). Assume the absolute integer coefficients of both truncated sums from Z are strictly below K for every t<=d. The construction produces F with F.c=c and F.K=K, retaining every clause of PositiveFamily: exact factors, positivity, augmentation, positive tau, and rectangular exchange minima.

This is the original construction with its clearing and positivity inputs exposed at its original owner. The existing theorem26_2 prepares those inputs by its original common-denominator and finite-maximum arguments and consumes this result. The supplied constants are never replaced by newly chosen ones. A specialization to c=K=card(H) still requires the actual clearing and bound proofs; existence alone does not identify them.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily.positiveFamily_with_constants`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily.theorem26_2`
- Dependency: [D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy](InertGroupBlockConjugacy.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange](InvolutionUniformExchange.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier](RectangularNilpotenceBarrier.md)
