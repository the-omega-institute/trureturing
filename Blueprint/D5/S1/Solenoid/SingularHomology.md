# Singular Homology of the Universal Solenoid

## Abstract

Every positive-degree ordinary singular homology group of the universal solenoid is zero, proved through genuine continuous lifts of all singular simplices.

**Theorem 1.1 (Normalized real parameter on a simply connected source).**

$$\forall A, \operatorname{SimplyConnectedSpace}\left(A\right), \operatorname{LocallyPathConnectedSpace}\left(A\right), \forall f: \operatorname{ContinuousMap}\left(A, Sigma\right), \forall a0: A, \exists! r: \operatorname{ContinuousMap}\left(A, R\right), \operatorname{r}\left(a0\right)=0, \forall a, \operatorname{f}\left(a\right)=\operatorname{realFlow}\left(\operatorname{r}\left(a\right)\right)+\operatorname{f}\left(a0\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/SingularHomology.exists_unique_normalized_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be simply connected and locally path-connected, let f be a continuous map from A to the universal solenoid, and choose a basepoint a0. The circle covering supplies a continuous real lift of the visible projection of f minus f(a0), normalized to zero at a0. The remaining difference lies in the hidden kernel. Every modulus-m coordinate of that difference is m-torsion, hence lies in a finite discrete subset of the circle. Connectedness makes every such coordinate constant, and its value at a0 is zero. The real-flow injectivity theorem gives uniqueness. This result is used on the live proof path of the singular homology calculation below.

**Theorem 1.2 (Positive-degree integral singular homology vanishes).**

$$\forall n: N, n\neq0 \implies \operatorname{singularHomology}\left(Sigma, Z, n\right)=0.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/SingularHomology.singular_homology_positive_is_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write B for the set of path components, equipped with a new discrete topology, and choose one solenoid point xb in each component. The map q from B times the real line sends (b,t) to realFlow(t) plus xb. The existing path-orbit classification and real-flow injectivity make q a continuous bijection. The proof does not identify the quotient topology on path components with this discrete topology.

Apply normalized source lifting to every finite-dimensional standard simplex. Each singular simplex in the solenoid lifts to a continuous map into B times the real line. Injectivity of q makes the lift unique. The actual natural transformation obtained by applying TopCat.toSSet to q is therefore bijective in every degree and hence an isomorphism of simplicial sets; its face and degeneracy compatibility comes from the singular functor itself.

On the resolution B times the real line, multiplying the real coordinate by 1-s gives a homotopy from the identity to the section-projection composite through B. Mathlib's homotopy invariance and positive-degree vanishing for totally disconnected spaces then prove the integral singular homology object is zero. The target is ordinary singular homology in positive degrees; the path-component contribution in degree zero is retained. Cech invariants require a separate calculation. The existing recurrence theorem proves that realFlow is not an embedding.

This is a formal calculation using standard covering-space and singular-homology mathematics, with no claim of a new mathematical theorem. The library contribution is the proved bridge from the project's inverse-limit dynamical carrier to genuine singular simplices and categorical homology.

## References

- Truth anchor: `D5/S1/Solenoid/SingularHomology.exists_unique_normalized_lift`
- Truth anchor: `D5/S1/Solenoid/SingularHomology.singular_homology_positive_is_zero`
- Dependency: [D5/S1/Dynamics/UniversalSolenoidCoordinate](../Dynamics/UniversalSolenoidCoordinate.md)
- Dependency: [D5/S1/Solenoid/PathOrbitClassification](PathOrbitClassification.md)
- Dependency: [D5/S1/Solenoid/RealFlowInjectivity](RealFlowInjectivity.md)
