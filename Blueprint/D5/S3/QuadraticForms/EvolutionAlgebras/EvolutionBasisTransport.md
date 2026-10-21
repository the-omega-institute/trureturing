# Basis transport and the full algebra group

## Abstract

All multiplication automorphisms of an arbitrary finite-dimensional perfect complex evolution algebra obey joint cycle, quotient and block control.

A and B are complex vector spaces with bilinear multiplication mu. Neither associativity nor a multiplicative unit is required. productSpan(mu) is the span of every mu(x,y); perfection means productSpan(mu)=Top. The automorphism group is the single Aut definition of EvolutionAutomorphismControl: all complex LinearEquivs preserving every pair product.

**Definition 1.1 (Transporting the multiplication).**

$$\forall A \in Typeu,\; \forall B \in Typeu,\; \operatorname{ComplexVectorSpace}\left(A\right) \Rightarrow \left(\operatorname{ComplexVectorSpace}\left(B\right) \Rightarrow \left(\forall e \in \operatorname{LinearEquiv}\left(A, B\right),\; \forall mu \in \operatorname{BilinearProduct}\left(A\right),\; \forall x \in B,\; \forall y \in B,\; \operatorname{ApplyProduct}\left(\operatorname{transportProduct}\left(e, mu\right), x, y\right) = \operatorname{e}\left(\operatorname{ApplyProduct}\left(mu, \operatorname{inverse}\left(e, x\right), \operatorname{inverse}\left(e, y\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.transportProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x,y in B, the transported multiplication is e(mu(e inverse(x),e inverse(y))). Bilinearity follows from composition of linear maps.

**Theorem 1.2 (Exact product-span correspondence).**

$$\forall A \in Typeu,\; \forall B \in Typeu,\; \operatorname{ComplexVectorSpace}\left(A\right) \Rightarrow \left(\operatorname{ComplexVectorSpace}\left(B\right) \Rightarrow \left(\forall e \in \operatorname{LinearEquiv}\left(A, B\right),\; \forall mu \in \operatorname{BilinearProduct}\left(A\right),\; \operatorname{map}\left(e, \operatorname{productSpan}\left(mu\right)\right) = \operatorname{productSpan}\left(\operatorname{transportProduct}\left(e, mu\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.product_span_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image under e of the span of all pair products is exactly the span of all transported pair products. Surjectivity of e supplies the reverse inclusion. Since e has zero kernel and full range, perfection is equivalent on the two spaces.

**Definition 1.3 (Conjugacy of the entire automorphism group).**

$$\forall A \in Typeu,\; \forall B \in Typeu,\; \operatorname{ComplexVectorSpace}\left(A\right) \Rightarrow \left(\operatorname{ComplexVectorSpace}\left(B\right) \Rightarrow \left(\forall e \in \operatorname{LinearEquiv}\left(A, B\right),\; \forall mu \in \operatorname{BilinearProduct}\left(A\right),\; \operatorname{GroupEquiv}\left(\operatorname{Aut}\left(mu\right), \operatorname{Aut}\left(\operatorname{transportProduct}\left(e, mu\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.automorphismConjugacy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map sends f to e composed with f composed with e inverse. Its inverse conjugates by e inverse. Both maps preserve multiplication because the transported product is defined on all pairs. They are inverse group homomorphisms; no monomiality, support lift, finiteness or conjugacy premise is inserted.

**Theorem 1.4 (The natural-basis correspondence).**

$$\forall A \in Typeu,\; \operatorname{ComplexVectorSpace}\left(A\right) \Rightarrow \left(\forall n \in NaturalNumbers,\; \forall mu \in \operatorname{BilinearProduct}\left(A\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), Complex, A\right),\; \left(\operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \operatorname{CoordinateBasisNatural}\left(mu, b\right)\right) \land \left(\operatorname{CoordinateBasisNatural}\left(mu, b\right) \Rightarrow \operatorname{NaturalBasisAt}\left(mu, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.natural_basis_transport_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence b.equivFun sends b(i) to the i-th coordinate vector. Products of distinct basis vectors therefore vanish exactly when products of the corresponding coordinate basis vectors vanish.

**Definition 1.5 (The finite-index bridge).**

$$\forall A \in Typeu,\; \operatorname{FiniteDimensionalComplexVectorSpace}\left(A\right) \Rightarrow \left(\forall I \in Typeu,\; \operatorname{Fintype}\left(I\right) \Rightarrow \left(\forall n \in \operatorname{NaturalNumbers}\left(\right),\; \operatorname{finrank}\left(A\right) = n \Rightarrow \left(\forall b \in \operatorname{Basis}\left(I, Complex, A\right),\; \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), Complex, A\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.dimensionBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite index type I and any basis b indexed by I, finrank equals card(I). Given finrank(A)=n, Fintype.equivFinOfCardEq and Basis.reindex produce the n-indexed basis. Its naturality follows by injectivity of the index equivalence. Thus the original natural basis is arbitrary, and the n-dimensional source quantifier is retained.

**Theorem 1.6 (Joint control on the actual algebra group).**

$$\forall A \in Typeu,\; \operatorname{FiniteDimensionalComplexVectorSpace}\left(A\right) \Rightarrow \left(\forall I \in Typeu,\; \operatorname{Fintype}\left(I\right) \Rightarrow \left(\forall n \in \operatorname{NaturalNumbers}\left(\right),\; \operatorname{finrank}\left(A\right) = n \Rightarrow \left(\forall mu \in \operatorname{BilinearProduct}\left(A\right),\; \forall b \in \operatorname{Basis}\left(I, Complex, A\right),\; \operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \left(\operatorname{productSpan}\left(mu\right) = Top \Rightarrow \left(\operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right) \land \operatorname{card}\left(\operatorname{Aut}\left(mu\right)\right) \le \operatorname{cycleWeight}\left(\operatorname{beta}\left(\operatorname{SupportOfCoordinateProduct}\left(mu, b, n\right)\right)\right) \cdot \operatorname{card}\left(\operatorname{centralizer}\left(\operatorname{beta}\left(\operatorname{SupportOfCoordinateProduct}\left(mu, b, n\right)\right)\right)\right) \cdot \operatorname{BlockFactorialProduct}\left(\operatorname{SupportOfCoordinateProduct}\left(mu, b, n\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.finite_and_joint_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

First transport along the reindexed basis and prove coordinate perfection and naturality. The coordinate algebra group is finite, and the group conjugacy transfers that actual finiteness before Nat.card is used. Let R be the support of the transported product, P its least successor-compatible quotient, beta the induced permutation, and B_q the original vertices in quotient class q. The bound is product_c(2^card(c)-1) times card(centralizer_Sym(P)(beta)) times product_q(card(B_q)!). The cycles c partition P, not the n original vertices. Singleton cycles contribute one. Exact diagonal assignment descent and cycle-root realization supply the first factor. The actual kernel of the block action injects into the product of the symmetric groups of B_q; it may be nontrivial. No support-surjectivity or faithful quotient-action hypothesis is used. The neutral n=0 case is included.

This joint control concerns the full source family in Conjecture 3 of Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1. It does not assert the conjecture's sharp maximum or attainment. The partition maximum, six small dimensions, factorial tail and absorption, coefficient-one cyclic-family attainment, and final upper-bound-plus-attainment assembly remain further mathematical requirements.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.automorphismConjugacy`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.dimensionBasis`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.finite_and_joint_bound`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.natural_basis_transport_iff`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.product_span_transport`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.transportProduct`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl](EvolutionAutomorphismControl.md)
