# All-parameter native cubic-circulant components

## Abstract

Every component is an explicit Mobius ladder or Cartesian prism, with the exact gcd multiplicity.

Let n be even with n at least four, and let 1 at most a be strictly less than n/2. The graph is the actual circulant on ZMod n with differences a, -a and n/2. Write h=gcd(n,a), ell=n/h and g=gcd(a,n/2). These definitions apply to every admissible parameter pair, including disconnected graphs. The finite-walk coset theorem determines actual component supports. Cyclic generator coordinates then determine their graph type.

**Theorem 1.1 (The complete native decomposition).**

$$\operatorname{NatCard}\left(\operatorname{Components}\left(\operatorname{cubic}\left(n, a\right)\right)\right) = g \land \left(\left(\operatorname{Even}\left(ell\right) \Rightarrow \left(h = g \land \left(\exists m \in \mathrm{Nat},\; ell = \operatorname{mul}\left(2, \operatorname{add}\left(m, 2\right)\right) \land \left(\forall C \in \operatorname{Components}\left(\operatorname{cubic}\left(n, a\right)\right),\; \operatorname{GraphIso}\left(\operatorname{mobius}\left(m\right), \operatorname{componentGraph}\left(C\right)\right)\right)\right)\right)\right) \land \left(\operatorname{Odd}\left(ell\right) \Rightarrow \left(\operatorname{Even}\left(h\right) \land \left(g = \operatorname{NatDiv}\left(h, 2\right) \land \left(\exists r \in \mathrm{Nat},\; ell = \operatorname{add}\left(r, 3\right) \land \left(\forall C \in \operatorname{Components}\left(\operatorname{cubic}\left(n, a\right)\right),\; \operatorname{GraphIso}\left(\operatorname{prism}\left(r\right), \operatorname{componentGraph}\left(C\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CubicCirculant.component_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If ell is even, the antipode is the half-order element of the generator subgroup. Each actual component is therefore M_ell and there are h=g components. If ell is odd, the antipode is outside that subgroup; product coordinates with its order-two subgroup give P_ell. The generator subgroup has odd order, h is even, and there are h/2=g components. Translation constructs the isomorphism to each actual support; none of these graph correspondences is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CubicCirculant.component_decomposition`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum](BinaryRungSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CirculantComponents](CirculantComponents.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower](FiniteDistancePower.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum](MobiusLadderSpectrum.md)
