# Coherent rational time from infinite multiplicity

## Abstract

Infinite isotypic multiplicity permits a single coherent rational-time action on the complete family.

Let H be an arbitrary group, iota an arbitrary index type, X:iota->Type a dependent family and A_i:ReturnAtlas H (X i) complete signed return charts. The universes of H, iota and the fibers may vary independently. The charts have positive natural periods d_i and arbitrary holonomies h_i. Isotypic A i j means d_i=d_j and there is b:H satisfying b*h_j=h_i*b. Its actual class is the subtype {j:iota | Isotypic A i j}. Assume every such class is infinite, with no countability restriction on the class or index type. The empty family is permitted.

Write T=jointTime A and D_a=jointDeck A a on Sigma X. Multiplicative Rational is the multiplicative type synonym for the additive rational group: its identity is ofAdd(0), and ofAdd(1) is the unit of time, not the group identity. MonoidHom into Perm means an actual group homomorphism, including its identity and composition laws; negative times therefore act by inverse permutations.

**Theorem 1.1 (One rational action with the prescribed time-one map).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall iota \in Type, X \in \operatorname{Map}\left(iota, Type\right), A \in \operatorname{DependentReturnAtlases}\left(H, X\right),\; (\forall i \in iota,\; \operatorname{Infinite}\left(\operatorname{IsotypicClass}\left(A, i\right)\right)) \implies \exists rho \in \operatorname{MonoidHom}\left(\operatorname{Multiplicative}\left(Rational\right), \operatorname{Perm}\left(\operatorname{Sigma}\left(X\right)\right)\right),\; ((\forall q \in \operatorname{Multiplicative}\left(Rational\right), a \in H, x \in \operatorname{Sigma}\left(X\right),\; \operatorname{apply}\left(\operatorname{apply}\left(rho, q\right), \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), x\right)\right) = \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), \operatorname{apply}\left(\operatorname{apply}\left(rho, q\right), x\right)\right)) \land (\operatorname{apply}\left(rho, \operatorname{ofAdd}\left(1\right)\right) = \operatorname{jointTime}\left(A\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalTimeAction.exists_rational_time_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists rho:Multiplicative Rational ->* Perm(Sigma X) such that for every q:Multiplicative Rational, a:H and x:Sigma X, rho(q)(D_a(x))=D_a(rho(q)(x)), and the underlying function of rho(ofAdd(1)) is exactly T. This is one homomorphism for all rational times, not a separate choice of an nth root for each positive n. No nilpotence, commutativity, divisibility or root-existence assumption is made on H or on the holonomies.

For a permutation U of a carrier Y, use the rational phase P={r:Rational | 0<=r and r<1}. The fractional suspension sends (r,y) at rational time q to (fract(r+q),U^floor(r+q)(y)). The floor is the signed integer floor, and powers are integer powers of the permutation, including negative exponents. The identity floor(fract(a)+b)+floor(a)=floor(a+b) supplies the exact carry in the homomorphism law. At time 1 the phase is unchanged and y becomes U(y). Every map commuting with U also commutes with its signed powers, and hence its phasewise lift commutes with the whole suspension.

The phase P is countable and nonempty. For every infinite actual isotypic index class C, infinite_block_equiv gives C equivalent to C times P: multiplication by a nonzero countable cardinal preserves every infinite cardinal. After swapping the factors, this absorbs the suspension phase into the existing multiplicity. It requires no countable enumeration of C.

Quotient iota by isotypy and choose one representative chart in each occurring class. The chartGauge equivalence identifies every chart in that class with its representative, intertwining time and all deck maps by the actual holonomy-conjugacy witness. The sigma-fiber equivalence separates the quotient class and its actual indices. Absorb P only into this index factor; the representative-carrier time permutation fixes the index. Assemble its suspension over all classes and conjugate the resulting permutation homomorphism through the complete dependent equivalence back to Sigma X. The transported time-one function is precisely jointTime, and all rational times commute with the original jointDeck maps.

The proof uses classical choice for quotient representatives, holonomy gauges and cardinal equivalences. It proves an algebraic action; no topology, continuity, real-time extension or physical realization is asserted. The construction gives coherent roots by a rational group action and therefore strengthens the separately chosen finite-order roots supplied by the earlier arbitrary-index root criterion. No literature-priority claim is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalTimeAction.exists_rational_time_action`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion](FiniteOrbitRootCriterion.md)
