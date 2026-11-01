# The eleven-vertex torsion seed for Question 32

## Abstract

An explicit order-two class in the integral finite-chain homology of the eleven-vertex seed.

This is a consumed necessary component in the counterexample route for Carnero Bravo, arXiv:2505.06457v2 Question 32, not Question 35 and not another solved original problem. The mathematical statement is integral finite-chain torsion.

The graph, oriented simplices, integral chain and detecting cocycle are displayed in the Lean module. The source supplies finite proofs by decide and algebraic proofs, without native_decide, proof placeholders or custom axioms.

**Definition 1.1 (The project's actual independence complex).**

$$seedComplex=\operatorname{independenceComplex}\left(G_0\right)$$

*Formalization.* `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedComplex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

H is the graph on Fin 11 decoded from the graph6 payload of JEhbtj{rve?, and G0 is its complement. This exact classical graph6 seed appears in Adamaszek, Small flag complexes with torsion (2012), arXiv:1208.3892v1; the explicit Lean proof here is local. seedComplex is exactly FiniteGraphVertexSubstitution.independenceComplex G0. Its eventual realization is FiniteConeCollapse.realization applied to its underlying pre-abstract complex.

**Definition 1.2 (The complete increasing edge basis).**

$$edgeSimplexEquiv: \operatorname{Fin}\left(32\right) \equiv EdgeSimplex$$

*Formalization.* `D5/S3/Geometry/IndependenceComplexTorsionSeed.edgeSimplexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

There is a bijection from Fin 32 to the pairs (a,b) with a less than b and {a,b} an actual face of seedComplex. The retained edge table supplies the bijection, including its injectivity and exhaustiveness. The differential uses this actual simplex enumeration.

**Definition 1.3 (The complete increasing triangle basis).**

$$triangleSimplexEquiv: \operatorname{Fin}\left(24\right) \equiv TriangleSimplex$$

*Formalization.* `D5/S3/Geometry/IndependenceComplexTorsionSeed.triangleSimplexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

There is a bijection from Fin 24 to the triples (a,b,c) with a less than b less than c and {a,b,c} an actual face of seedComplex. The retained triangle table supplies this bijection, which the triangle boundary uses.

**Theorem 1.4 (The alternating boundaries form a complex).**

$$d_1 \circ d_2=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeed.d1_comp_d2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

d1.comp d2 = 0. Here C0 = Fin 11 to Z, C1 = Fin 32 to Z and C2 = Fin 24 to Z. An oriented edge [a,b] has boundary [b]-[a], and [a,b,c] has boundary [b,c]-[a,c]+[a,b]. Finite reduction checks every triangle column; linearity handles all integral triangle chains.

**Definition 1.5 (The finite degree-one homology object).**

$$seedChainComplex=\operatorname{moduleCatMk}\left(d_2, d_1\right)$$

*Formalization.* `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedChainComplex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

seedChainComplex is ShortComplex.moduleCatMk d2 d1 d1_comp_d2. Its homology is Mathlib's ShortComplex.homology in ModuleCat Z. These are all actual degree-zero, degree-one and degree-two ordered simplicial chains of seedComplex; higher chains do not change ker(d1)/im(d2). No identification with geometric singular homology is assumed.

**Theorem 1.6 (The displayed vector is a cycle).**

$$d_1(z)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeed.d1_z` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

d1 z = 0, where z = [0,3]-[0,7]-[1,3]+[1,5]+[5,7] in the enumerated oriented edge basis.

**Theorem 1.7 (The retained double bounds integrally).**

$$d_2(boundingChain)=2\cdot z$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeed.d2_boundingChain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

d2 boundingChain = (2 : N) times z. The 24 retained integer coefficients of boundingChain, in triangle-table order, are 0,1,1,-1,1,-1,-1,0,-1,-1,1,1,-1,1,-1,1,1,-1,-1,1,0,0,1,1.

**Theorem 1.8 (The extended mod-two cocycle kills all boundaries).**

$$\forall c: \operatorname{Fin}\left(24\right) \to \mathbb{Z}, \operatorname{detector}\left(d_2(c)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeed.detector_d2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every c : C2, detector (d2 c) = 0. The integer-linear detector to ZMod 2 uses the supplied 22 non-tree cocycle values, with zero on the ten retained tree edges. Its extension values are proved in the type of extendedCocycle; no spanning-tree hypothesis is needed for the non-boundary argument.

**Theorem 1.9 (The cocycle detects the cycle).**

$$\operatorname{detector}\left(z\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeed.detector_z` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

detector z = 1 in ZMod 2.

**Theorem 1.10 (The cycle is not a boundary).**

$$\neg (z \in \operatorname{range}\left(d_2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeed.z_not_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

z is not in LinearMap.range d2. If z were d2 c, applying the mod-two detector would give one equal to zero.

**Definition 1.11 (The displayed class in categorical homology).**

$$seedClass=\operatorname{cycleClassMap}\left(seedChainComplex, z\right)$$

*Formalization.* `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

seedClass : seedChainComplex.homology is cycleClassMap seedChainComplex applied to the concrete cycle (z,d1_z). The class map uses the inverse of Mathlib's exact moduleCatHomologyIso, so no bespoke quotient comparison is left implicit.

**Theorem 1.12 (Nonzero two-torsion).**

$$seedClass \neq 0 \land 2\cdot seedClass=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedClass_nonzero_killed_by_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

seedClass is nonzero and (2 : N) times seedClass is zero. This finite-chain torsion statement is the intended component consumed by the full Question 32 obstruction.

**Theorem 1.13 (Exact additive order two).**

$$\operatorname{addOrderOf}\left(seedClass\right)=2$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedClass_addOrderOf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

addOrderOf seedClass = 2. This follows from the nonzero class killed by the prime two. It makes no classification assertion about the other homology classes.

Still required is an actual comparison isomorphism from seedChainComplex.homology to integral singular H1 of TopCat.of of the subtype of FiniteConeCollapse.realization seedComplex.toPreAbstractSimplicialComplex. The graph S(G,H) singular-suspension result, its 31326 genuine iterations, transport to the 93999-vertex induced king graph in the 9337 by 9061 grid, and the torsion-free sphere-wedge obstruction are outside this module. No large independence complex is enumerated, and no full topology verification or literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.d1_comp_d2`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.d1_z`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.d2_boundingChain`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.detector_d2`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.detector_z`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.edgeSimplexEquiv`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedChainComplex`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedClass`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedClass_addOrderOf`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedClass_nonzero_killed_by_two`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.seedComplex`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.triangleSimplexEquiv`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeed.z_not_boundary`
- Dependency: [D5/S3/Geometry/FiniteGraphVertexSubstitution](FiniteGraphVertexSubstitution.md)
- Dependency: [D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology](../HomologicalAlgebra/DetectedOrderTwoHomology.md)
