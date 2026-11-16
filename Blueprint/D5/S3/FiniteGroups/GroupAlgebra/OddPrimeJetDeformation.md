# The original additive group and its higher jets

## Abstract

Odd-prime higher-jet representations and a trace obstruction to ordinary translations.

Let p be any odd prime, F=ZMod p, and K/F any finite-dimensional field extension of degree r at least two. The universe of K is independent of that of F. Let q:K→K be F-linear with q(1)=0. Put V=K[t] of degree less than p and E=Multiplicative K, the multiplicative type synonym of the original additive group of K. Let D be formal differentiation on V. Since D^p=0 and j! is invertible in K for j<p, exp(A) denotes the finite sum of A^j/j! for 0≤j<p.

**Definition 1.1 (The infinitesimal higher jet).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.jetOperator`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.jetOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The K-linear operator L_x=xD+q(x)D^(p−1) acts on the actual truncated polynomial space. The parameter q is only F-linear. For j≥2, L_x^j=x^j D^j, because every mixed term has derivative order at least p. In particular L_x^p=0.

**Definition 1.2 (The representation of the original group).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.originalRepresentation`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.originalRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define rho_x=exp(L_x), viewed as an F-linear endomorphism of V. It equals U_x+q(x)D^(p−1), where U_x=sum_(j<p) x^j D^j/j!. The ordinary Taylor composition identity gives U_(x+y)=U_x U_y; moreover U_x D^(p−1)=D^(p−1)=D^(p−1) U_x. Additivity of q then gives rho_(x+y)=rho_x rho_y and rho_0=1. Thus this is an actual Representation F E V, rather than an action of its image group.

**Definition 1.3 (Ordinary polynomial translations).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.ordinaryRepresentation`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.ordinaryRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary representation is the case q=0. Its action is exactly f(t)↦f(t+x), not just a named formal exponential: comparison on the monomial basis, using the iterated-derivative formula and the binomial theorem, identifies U_x with Mathlib's actual Taylor map.

**Theorem 1.4 (Cyclic projectivity, global obstruction, and trace inequivalence).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.full_family`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.full_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such p,K,q the theorem states that rho is faithful; every restriction to an original cyclic subgroup H≤E, including the trivial subgroup, is projective over F[H]; the common invariants are exactly the constant polynomials; the full group norm is zero; the full F[E]-module is not projective; and dim_F V=p*r. It also states the exact ordinary-translation identity. Finally, if trace_(K/F)(q(a)) is nonzero for some a, then for every group automorphism phi:E≃*E and every merely F-linear equivalence P:V≃V, the equations P(rho_g v)=tau_(phi(g))(P v) cannot hold for all g and v.

Faithfulness follows by applying rho_x to t: the result is t+x. For nontrivial cyclic H, every nonidentity generator x has order p. The polynomial h_x(z)=sum_(j<p) x^j z^j/j!−1+q(x)z^(p−1) has constant coefficient zero and first coefficient x. Its value at D is rho_x−1. The public truncated-polynomial cyclic criterion therefore gives projectivity, since K is an F-vector space and x is a unit. The actual Cp action is transported to the original subgroup H along its generator isomorphism. The trivial subgroup is treated separately through F[H]≃F.

These are cyclic directions of the original additive group. The parent cyclic generator is 1+h_x(D)=rho_x, not 1+L_x. No assertion about arbitrary shifted directions or arbitrary one-parameter subalgebras replaces the cyclic statement. In particular, the family illustrates why testing original cyclic subgroups does not imply projectivity for the entire group.

Constants are fixed. A polynomial expression in the powers of rho_1 recovers L_1=D, so every common invariant lies in ker D. In degree less than p, the nonzero coefficients 1,...,p−1 make ker D precisely the constants. For the norm, |K|=p^r and r≥2 imply sum_(x in K) x^j=0 for every j<p. F-linearity also gives sum_x q(x)=0. Summing the explicit exponential expression yields norm(rho)=0. The public p-group projectivity criterion would make the norm surjective onto invariants for a projective module. The nonzero invariant constant 1 makes this impossible. The degreeLT basis and finite-dimensional tower formula give the stated dimension.

The logarithm bridge respects F-linear intertwiners. The prime-field moment identity gives L_x=−sum_(i in F) i^(p−2) rho_(i*x). Each rho_(i*x) is a power of rho_x, so this is a polynomial logarithm on the actual action. A group automorphism phi of E induces an F-linear additive automorphism of K; its scalar compatibility is derived from the ZMod linear-map interface. Applying P to the logarithm yields P L_x=phi(x) D P, with no K-linearity of P.

Put c=phi(1), which is nonzero. The diagonal K-linear equivalence S(t^j)=c^j t^j satisfies S D=c^(-1) D S. Thus P'=S P commutes with D because q(1)=0, and P' L_a=e D P' where e=phi(a)/c. Restrict P' and its inverse to ker D, the constants, to derive an F-linear equivalence P0:K≃K. This equivalence is a consequence of the intertwining equations, not an additional hypothesis.

Use the divided monomials b_j(s)=s*t^j/j!. On b_1(s), the second equation gives P0 M_a=M_e P0, since p>2 makes D^(p−1)b_1(s)=0. On b_(p−1)(s), take the constant coefficient and set T(s)=coeff_0(P'(b_(p−2)(s))). The result is T M_a+P0 M_(q(a))=M_e T. With Q=P0^(-1)T, these equations give M_a Q−Q M_a=M_(q(a)). The public trace identity trace(AB)=trace(BA) makes the left side trace zero; the trace of multiplication by q(a) is the field trace. This contradicts the stated nonzero trace.

The parameter r is not fixed at two and p is not fixed at three. The theorem assumes neither projectivity nor freeness, a Jordan basis, a module equivalence, or K-linearity of an intertwiner. It concerns this explicit family and its trace obstruction; it gives no classification or literature-novelty assertion.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.full_family`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.jetOperator`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.ordinaryRepresentation`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDeformation.originalRepresentation`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/TruncatedPolynomialCyclicCriterion](TruncatedPolynomialCyclicCriterion.md)
