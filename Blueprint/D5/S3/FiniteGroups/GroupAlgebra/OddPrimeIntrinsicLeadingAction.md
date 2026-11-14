# Intrinsic odd-prime leading action

## Abstract

An actual odd-prime elementary-abelian representation yields a normalized commuting action on its existing coinvariants.

**Theorem 1.1 (Top-layer extraction from an actual representation).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeIntrinsicLeadingAction.intrinsic_leading_action`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeIntrinsicLeadingAction.intrinsic_leading_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be an odd prime, K a finite field of characteristic p, and rho an actual K-representation of Multiplicative (Fin r -> ZMod p) on V with r,m positive and finrank K V = p*m. Assume every actual cyclic subgroup restriction is projective and every ordered length-p product of augmentation operators vanishes. For any actual nonidentity anchor h, put D = rho(h)-1 and U = Representation.Coinvariants rho.

For every such rho and every actual h != 1, there exists a ZMod p-linear map A from Fin r -> ZMod p to End_K(U), using the standard prime-field scalar action. It satisfies finrank_K U = m, A(h.toAdd) = 1, IsUnit(A(g)) for every g != 0, and Commute(A(g), A(k)) for all g,k. For all g and all v,w in V, A(g)(q(v)) = q(w) if and only if (rho(ofAdd g)-1)(v) - (rho(h)-1)(w) lies in range((rho(h)-1)^2). The field and vector-space universes are independent.

The cyclic norm criterion gives D^p = 0 and ker D = range D^(p-1). Induction on j derives ker D^j = range D^(p-j) for 0 <= j <= p. Mixed products identify every nonzero range with range D, hence the original coinvariant kernel is range D.

The quotient map q induces eD : U -> ker D by q(v) |-> D^(p-1)v and ng : U -> ker D by q(v) |-> D^(p-2)(rho(g)-1)v. Set A_h(g) = eD^{-1} ng. Additivity is the length-p mixed-product instance; surjectivity follows from range Ng = range D; commutation applies D^(p-3)Ng to the lift error Nk(v)-D(w) in range D^2. The p=3 boundary is handled before subtraction.

The same construction records the intrinsic certification: A_h(g)(qv)=qw exactly when Ng(v)-Nh(w) belongs to range Nh^2. No Toeplitz coordinates, Jordan basis, full-chain identification, field generation, or full-action field conjugacy is assumed or concluded.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeIntrinsicLeadingAction.intrinsic_leading_action`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/FiniteFieldCyclicDimension](FiniteFieldCyclicDimension.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PrimeFieldCyclicProjectivityDimension](PrimeFieldCyclicProjectivityDimension.md)
