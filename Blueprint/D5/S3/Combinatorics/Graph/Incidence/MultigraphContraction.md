# Multigraph Contraction on Rational Cycles

## Abstract

Nonloop contraction of an edge-indexed directed multigraph preserves rational signed-incidence cycles by surviving-coordinate restriction.

Let G be EssentialWordRealization.DirectedMultigraph V E. E is finite, while V may be arbitrary. Distinct edge IDs remain distinct even when their endpoints agree. No connectedness, simplicity, cyclic vertex order, or condition on bridges is imposed.

**Definition 1.1 (The actual rational boundary).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.boundary`

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

incidence G v f is the rational cast of the existing integer signedIncidence G.source G.target v f. Its sign is head minus tail. boundary G is multiplication by this matrix on E-indexed rational coefficients; CycleSpace G is its kernel. Every loop has zero boundary, including loops retained after contraction.

**Definition 1.2 (Delete one edge and identify its endpoints).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.contract`

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.contract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For e with source(e) different from target(e), Surviving e is the subtype of original edge IDs f different from e. ContractedVertex G e is the subtype of vertices different from target(e). vertexMap sends target(e) to source(e) and fixes every other vertex. contract G e h has the same existing DirectedMultigraph structure with source and target obtained by composing the original endpoint maps with vertexMap. All isolated vertices other than the removed endpoint persist. Parallel edges retain their IDs, and an edge joining the identified vertices becomes a loop rather than disappearing.

**Theorem 1.3 (Endpoint fibers and the cycle equivalence).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableEq}\left(E\right)] [\operatorname{Fintype}\left(E\right)], \forall G: \operatorname{DirectedMultigraph}\left(V, E\right), \forall e: E, \forall h: \operatorname{source}\left(G, e\right) \neq \operatorname{target}\left(G, e\right), {\forall w: V, \forall v: \operatorname{ContractedVertex}\left(G, e\right), \operatorname{vertexMap}\left(G, e, h, w\right) = v \iff w = \operatorname{val}\left(v\right) \lor {w = \operatorname{target}\left(G, e\right) \land \operatorname{val}\left(v\right) = \operatorname{source}\left(G, e\right)}} \land \exists Phi: \operatorname{LinearEquiv}\left(\mathbb{Q}, \operatorname{CycleSpace}\left(G\right), \operatorname{CycleSpace}\left(\operatorname{contract}\left(G, e, h\right)\right)\right), {\forall z: \operatorname{CycleSpace}\left(G\right), \forall f: \operatorname{Surviving}\left(e\right), \operatorname{coeff}\left(\operatorname{apply}\left(Phi, z\right), f\right) = \operatorname{coeff}\left(z, \operatorname{val}\left(f\right)\right)} \land {\forall z: \operatorname{CycleSpace}\left(\operatorname{contract}\left(G, e, h\right)\right), \operatorname{coeff}\left(\operatorname{inverse}\left(Phi, z\right), e\right) = -\operatorname{residual}\left(G, e, \operatorname{val}\left(z\right), \operatorname{target}\left(G, e\right)\right)} \land {\forall z: \operatorname{CycleSpace}\left(\operatorname{contract}\left(G, e, h\right)\right), \forall f: \operatorname{Surviving}\left(e\right), \operatorname{coeff}\left(\operatorname{inverse}\left(Phi, z\right), \operatorname{val}\left(f\right)\right) = \operatorname{coeff}\left(z, f\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.nonloop_contraction_cycle_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, coeff(z,f) means the underlying cycle coefficient z.val f; inverse(Phi,z) means Phi.symm z. LinearEquiv(Q,A,B) denotes a Q-linear equivalence. The fiber identity identifies precisely the two selected endpoints and no other vertices. The forward equivalence literally restricts surviving coordinates. Its inverse preserves each surviving coefficient and reconstructs the deleted coefficient as the negative original target-row residual. residual G e x v is the sum, over surviving IDs f, of incidence G v f times x(f).

The contracted boundary at a vertex other than the merged source is its original surviving-edge boundary. At the merged source it is the sum of the original source and target residuals. On a full cycle the removed edge contributes minus its coefficient at the source and plus its coefficient at the target, so restriction has zero contracted boundary. Conversely the target balance fixes the removed coefficient, and the merged balance then proves the source balance. These identities prove both inverse laws. The argument includes bridges, loops, parallel edges, empty surviving edge types, and arbitrary additional isolated vertices.

This supplies the cycle-space transport step in the common-contraction argument of the caller-supplied completed marked-four-loop proof, Section Half-edge rule and the homology calculation, proof.tex SHA256 7723959228b1445082f506550b1473155eb8210a27f8025e7a56d1a669663d82. The primary mathematical source is Kuperberg, arXiv:2608.11334v1, oddvas.tex. Cyclic-order signs, actual AS/IHX/CL relation maps, cohomology, coefficient duality, socket gluing, and the marked odd two-color four-loop Jacobi quotient require further arguments.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.boundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.contract`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.nonloop_contraction_cycle_equiv`
- Dependency: [D5/S3/ConceptDynamics/Coding/EssentialWordRealization](../../../ConceptDynamics/Coding/EssentialWordRealization.md)
- Dependency: [D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity](../../../Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.md)
