# Selfadjoint topological Schur

## Abstract

A selfadjoint operator in the commutant of a topologically irreducible operator set is scalar.

**Theorem 1.1 (Scalarity from closed invariant subspaces).**

$$\forall H \in \operatorname{Type}\left(\right),\; \operatorname{ComplexHilbert}\left(H\right) \Rightarrow \left(\forall S \in \operatorname{Set}\left(\operatorname{BoundedOperators}\left(H\right)\right),\; \forall y \in \operatorname{BoundedOperators}\left(H\right),\; \left(\operatorname{IsTopologicallyIrreducible}\left(S\right) \land \left(\operatorname{IsSelfAdjoint}\left(y\right) \land \left(\forall T \in \operatorname{BoundedOperators}\left(H\right),\; \operatorname{Member}\left(T, S\right) \Rightarrow \operatorname{Commute}\left(y, T\right)\right)\right)\right) \Rightarrow \left(\exists r \in \operatorname{Real}\left(\right),\; y = \operatorname{algebraMap}\left(\operatorname{Real}\left(\right), \operatorname{BoundedOperators}\left(H\right), r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/TopologicalSchur.exists_eq_algebraMap_of_isSelfAdjoint_of_commute` (`✓ std3`). ∎

*Citation.* Keisuke Suzuki (2025). *Selfadjoint Schur lemma for topologically irreducible bounded operators*. URL: <https://github.com/kencyke/quantum-system/blob/5d67fe8030eaf1bdaf081e2acfcbe3fbaecfda7c/QuantumSystem/ForMathlib/Analysis/InnerProductSpace/InvariantSubspace.lean>.

*Commentary.*

H is any complete complex inner-product space, including the zero space. S is any set of bounded complex-linear operators. Topological irreducibility requires each closed complex-linear S-invariant subspace to be zero or all of H. If the bounded selfadjoint operator y commutes with every member of S, it is a real multiple of the identity. No finite-dimensional or algebraic irreducibility premise is imposed.

This is the immutable upstream theorem of Keisuke Suzuki cited below. The continuous functional calculus would separate distinct spectral points by two nonzero operators with disjoint support. The kernel of one is then a nontrivial proper closed S-invariant subspace. Thus the spectrum has one point, which yields the real scalar. The upstream definition and proof are reused with their original declaration names and license.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/TopologicalSchur.exists_eq_algebraMap_of_isSelfAdjoint_of_commute`
