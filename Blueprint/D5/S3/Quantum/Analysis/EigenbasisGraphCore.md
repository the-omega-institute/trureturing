# Eigenbasis Graph and Finite Core

## Abstract

Weighted coefficients describe the genuine closure graph and its simultaneous finite core.

**Theorem 1.1 (The actual finite operator determines the weighted graph).**

$$\forall H \in CompleteComplexInnerProductSpace, I \in Type, e \in \operatorname{HilbertBasis}\left(I, H\right), T \in \operatorname{LinearPartialOperator}\left(H\right), lambda \in I \to \mathbb{R}, x \in H, y \in H,\; \left(\operatorname{domain}\left(T\right) = \operatorname{span}\left(\operatorname{range}\left(e\right)\right) \land \left(\forall j \in I,\; T\left(e\left(j\right)\right) = lambda\left(j\right) \cdot e\left(j\right)\right)\right) \Rightarrow \left(\left(\operatorname{GraphMember}\left(\operatorname{closure}\left(T\right), x, y\right) \Leftrightarrow \left(\forall j \in I,\; \operatorname{inner}\left(e\left(j\right), y\right) = lambda\left(j\right) \cdot \operatorname{inner}\left(e\left(j\right), x\right)\right)\right) \land \left(\left(\left(\forall j \in I,\; \operatorname{inner}\left(e\left(j\right), y\right) = lambda\left(j\right) \cdot \operatorname{inner}\left(e\left(j\right), x\right)\right) \Rightarrow \left(\exists u \in \operatorname{Finset}\left(I\right) \to \operatorname{domain}\left(T\right),\; \left(\forall F \in \operatorname{Finset}\left(I\right),\; u\left(F\right) = \operatorname{sum}\left(\left(\operatorname{inner}\left(e\left(j\right), x\right) \cdot e\left(j\right)\right)_{j \in F}\right)\right) \land \left(\left(\forall F \in \operatorname{Finset}\left(I\right),\; T\left(u\left(F\right)\right) = \operatorname{sum}\left(\left(lambda\left(j\right) \cdot \operatorname{inner}\left(e\left(j\right), x\right) \cdot e\left(j\right)\right)_{j \in F}\right)\right) \land \left(\operatorname{Tendsto}\left(\left(u\left(F\right)\right)_{F \in \operatorname{Finset}\left(I\right)}, x\right) \land \operatorname{Tendsto}\left(\left(T\left(u\left(F\right)\right)\right)_{F \in \operatorname{Finset}\left(I\right)}, y\right)\right)\right)\right)\right) \land \left(\operatorname{DomainMember}\left(\operatorname{closure}\left(T\right), x\right) \Leftrightarrow \operatorname{MemL2}\left(\left(lambda\left(j\right) \cdot \operatorname{inner}\left(e\left(j\right), x\right)\right)_{j \in I}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/EigenbasisGraphCore.eigenbasis_graph_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any complete complex inner product space, e a Hilbert basis with arbitrary index type I, and T a complex linear partial operator whose domain is exactly the algebraic span of e. Assume T sends e of i to lambda of i times e of i, with arbitrary real lambda. K is the genuine closure of T. Write c of i of x for the inner product of e of i with x.

For every x and y in H, the pair x and y belongs to the actual graph of K exactly when c of i of y equals lambda of i times c of i of x for every i. The domain of K consists exactly of vectors whose weighted coefficient family is square summable. The operator is not defined by that family.

Under the coefficient condition, let F range over finite subsets of I directed by inclusion. The vectors u of F are the finite sums of c of i of x times e of i over F. They lie in the actual domain of T. Their actual T images are the sums of lambda of i times c of i of x times e of i over the same F. The vectors converge to x and the images converge to y.

Hilbert expansion gives the two limits. Each finite pair is in the actual graph of T, so their product limit is in its graph closure. Symmetry of the self-adjoint closure gives the converse coefficient condition. Zero and repeated eigenvalues are allowed; no division by an energy is used.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/EigenbasisGraphCore.eigenbasis_graph_coefficients`
- Dependency: [D5/S3/Quantum/Analysis/EigenbasisClosure](EigenbasisClosure.md)
