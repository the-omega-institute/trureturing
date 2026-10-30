# Coprime roots and a finite holonomy obstruction

## Abstract

Square and cube roots can coexist without a sixth root in an explicit finite nonabelian group.

**Definition 1.1 (The actual semidirect product).**

$$H = \operatorname{SemidirectProduct}\left(\operatorname{QuaternionGroup}\left(2\right), \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(9\right)\right), rho\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write Q8={1,-1,i,-i,j,-j,k,-k} and C9=<t>. In Mathlib coordinates i=a(1), j=xa(0), k=xa(3), and -1=a(2). The automorphism alpha cycles i to j, j to k, and k to i. Its complete coordinate map is a(0)->a(0), a(1)->xa(0), a(2)->a(2), a(3)->xa(2), xa(0)->xa(3), xa(1)->a(3), xa(2)->xa(1), xa(3)->a(1). Its inverse is alpha squared. The action rho sends ofAdd(r) to alpha raised to the least nonnegative representative of r in ZMod 9. Multiplication is (q,t^r)(s,t^u)=(q*alpha^r(s),t^(r+u)). The upstream QuaternionGroup and SemidirectProduct group structures supply associativity, identity and inverses; this construction does not replace Q8 by a new multiplication table. The public Fintype instance is transported from Q8 times C9 using SemidirectProduct.equivProd.

**Definition 1.2 (The order-six holonomy).**

$$h = \operatorname{pair}\left(\operatorname{a}\left(2\right), \operatorname{ofAdd}\left(3\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Thus h=(-1,t^3). The specified square root is (i,t^6), and the specified cube root is (-1,t). All coordinates are elements of the actual semidirect product H.

**Definition 1.3 (Coprime-root sufficiency at this element).**

$$claim = ((\exists x \in H,\; x^{2} = h) \implies (((\exists x \in H,\; x^{3} = h) \implies (\exists x \in H,\; x^{6} = h))))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion says that existence of a square root and existence of a cube root of this h imply existence of a sixth root in the same group H. There are no assumptions of commutativity or of compatibility between the two roots.

**Theorem 1.4 (Failure of coprime-root sufficiency).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both antecedents hold, using (i,t^6) and (-1,t). Evaluation of the actual semidirect-product sixth power for every one of its 72 elements proves that none equals h. The finite calculation is checked by the Lean kernel with decide; it uses neither native_decide nor a compiler-trust axiom. This refutes the asserted sufficiency rather than assuming a root obstruction as a premise.

**Theorem 1.5 (The exact finite nonabelian obstruction).**

$$((\operatorname{NatCard}\left(H\right) = 72) \land (((\operatorname{orderOf}\left(h\right) = 6) \land (((\operatorname{pair}\left(\operatorname{a}\left(1\right), \operatorname{ofAdd}\left(6\right)\right)^{2} = h) \land (((\operatorname{pair}\left(\operatorname{a}\left(2\right), \operatorname{ofAdd}\left(1\right)\right)^{3} = h) \land (((\forall x \in H,\; x^{6} \neq h) \land (\exists x \in H, y \in H,\; \operatorname{mul}\left(x, y\right) \neq \operatorname{mul}\left(y, x\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.finite72_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The group has exactly 72 elements, h has exact order six, the displayed elements have square and cube equal to h, every sixth power differs from h, and there exist noncommuting elements. The cardinality follows from SemidirectProduct.card and QuaternionGroup.card. Exact order is proved by h^6=1 and the five positive smaller powers differing from 1. The two noncommuting elements can be chosen as (i,1) and (j,1), so noncommutativity already occurs inside the embedded upstream Q8.

**Theorem 1.6 (The universal root-degree spectrum).**

$$\forall q \in Nat,\; (\exists x \in H,\; x^{q} = h) \iff (((\operatorname{gcd}\left(q, 36\right) = 1) \lor (((\operatorname{gcd}\left(q, 36\right) = 2) \lor (\operatorname{gcd}\left(q, 36\right) = 3)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.root_degree_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree q, including zero, h has a qth root exactly when gcd(q,36) is 1, 2 or 3. Every element x of this same H satisfies x^12=1 or x^18=1, hence x^36=1; this bound does not assert that an element of order 36 exists. In any group with common exponent bound N, the qth-power image equals the gcd(q,N)th-power image. Divisibility gives one inclusion. For the other, choose integers A,B with Aq+BN=gcd(q,N): a gcd(q,N)th root y gives the qth root y^A, since y^N=1. Only powers of one element are combined, so ambient commutativity is unnecessary. For N=36, h itself and the displayed square and cube roots realize gcd values 1, 2 and 3. A fourth root would force h^9=1, and a ninth root would force h^4=1; both fail for this h. Sixth roots are already excluded. Every divisor of 36 outside 1,2,3 is divisible by 4,6 or 9, so these obstructions exhaust all natural degrees. The finite divisor calculation does not restrict q to a finite range. At degree zero every zeroth power is 1, whereas h is not 1 and gcd(0,36)=36. This is a classification of root existence, with no root-count formula or priority claim.

For return-chart arithmetic, take positive exponent k=6, period d=1 and holonomy h. The prospective block equation at a divisor ell of 6 asks for b^(6/ell)=h. The verified cube root supplies ell=2, the verified square root supplies ell=3, and h itself supplies ell=6. The missing sixth root excludes ell=1. Thus the permitted divisor lengths are exactly 2,3,6, whose additive monoid is {0} union {n>=2}: every even n>=2 is a sum of twos, and every odd n>=3 is three plus a sum of twos. Their gcd is one, yet multiplicity one is absent. This arithmetic explains why a gcd condition loses finite multiplicity information. The group theorem proves the concrete root facts only; interpreting that monoid as a complete classification of finite atlas families additionally requires the general finite-family theorem and its hypotheses. No such atlas-family classification is assumed or proved here.

The construction is repository-derived, using the classical quaternion group and semidirect-product operations provided by pinned Mathlib. QuaternionGroup is attributed upstream to Julian Kuelshammer and SemidirectProduct to Chris Hughes, under Mathlib's Apache 2.0 license. The quaternion-group background is also described in Groupprops, Quaternion group, https://groupprops.subwiki.org/wiki/Quaternion_group. The Q8-by-C9 semidirect-product family also occurs in the Math StackExchange question Semi directProduct and Maximal subgroup in gap, https://math.stackexchange.com/questions/291350/semi-directproduct-and-maximal-subgroup-in-gap; that question concerns maximal subgroups, rather than the root assertion here. No priority, minimal-order, or exhaustive literature-absence claim is made for this finite counterexample.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.H`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.finite72_obstruction`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.h`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.result`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.root_degree_spectrum`
