# Cohomology and Coefficient Transport for Multigraph Contraction

## Abstract

Actual rational graph cohomology transports by evacuation of one nonloop edge coefficient, inverse transpose to cycle contraction.

Let G be the existing DirectedMultigraph V E, with arbitrary vertex type V and finite edge type E. The boundary, incidence, vertexMap, contract and cycleEquiv are those of MultigraphContraction. Fix an edge ID e with source(e) different from target(e). Put F = Surviving e and W = ContractedVertex G e. No connectedness, simplicity or condition on bridges is imposed. Loops and parallel surviving IDs persist; isolated vertices remain except for the contracted target, and F may be empty.

**Definition 1.1 (Actual coboundaries and their quotient).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.coboundary`

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.coboundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coboundary G sends a vertex function k to the edge function f ↦ k(target(f)) − k(source(f)). Cohomology G is the native rational vector-space quotient (E → Q) / range(coboundary G). Write d(G,k) for this coboundary and class(G,a) for the quotient projection. The values of a vertex function at isolated vertices have no effect on its coboundary.

**Definition 1.2 (Evacuation and zero extension).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.evacuate`

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.evacuate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(G,e,a) denotes evacuate G e a, whose surviving coordinate f is a(f.val) − a(e) incidence G (target(e)) f.val. J(e,b) denotes extend e b: its e coordinate is zero and each surviving coordinate is b. Both are rational linear maps. The incidence sign is head minus tail.

**Theorem 1.3 (Evacuation restricts the vertex potential).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableEq}\left(E\right)] , \forall G: \operatorname{DirectedMultigraph}\left(V, E\right), \forall e: E, \forall h: \operatorname{source}\left(G, e\right) \neq \operatorname{target}\left(G, e\right), \forall k: {V} \to \mathbb{Q}, \operatorname{A}\left(G, e, \operatorname{d}\left(G, k\right)\right) = \operatorname{d}\left(\operatorname{contract}\left(G, e, h\right), \operatorname{restrictVertices}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.evacuate_coboundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a vertex w, the restricted potential evaluated at vertexMap(w) is k(w) minus (k(target(e)) − k(source(e))) times the indicator of w = target(e). Subtracting this identity at the two surviving endpoints gives the displayed coboundary transport.

**Theorem 1.4 (Zero extension pulls the potential back).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableEq}\left(E\right)] , \forall G: \operatorname{DirectedMultigraph}\left(V, E\right), \forall e: E, \forall h: \operatorname{source}\left(G, e\right) \neq \operatorname{target}\left(G, e\right), \forall k: {\operatorname{ContractedVertex}\left(G, e\right)} \to \mathbb{Q}, \operatorname{J}\left(e, \operatorname{d}\left(\operatorname{contract}\left(G, e, h\right), k\right)\right) = \operatorname{d}\left(G, \operatorname{compose}\left(k, \operatorname{vertexMap}\left(G, e, h\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.extend_coboundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoints of e have the same image under vertexMap, so the pulled-back coboundary vanishes on e. On each surviving edge, the identity is the definition of the contracted endpoint maps.

**Theorem 1.5 (One composite is exactly the identity).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableEq}\left(E\right)] , \forall G: \operatorname{DirectedMultigraph}\left(V, E\right), \forall e: E, \forall b: {\operatorname{Surviving}\left(e\right)} \to \mathbb{Q}, \operatorname{A}\left(G, e, \operatorname{J}\left(e, b\right)\right) = b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.evacuate_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero extension has no deleted coefficient to evacuate; every surviving coordinate is fixed.

**Theorem 1.6 (The other composite has an exact coboundary correction).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableEq}\left(E\right)] , \forall G: \operatorname{DirectedMultigraph}\left(V, E\right), \forall e: E, {\operatorname{source}\left(G, e\right) \neq \operatorname{target}\left(G, e\right)} \to \forall a: {E} \to \mathbb{Q}, \operatorname{J}\left(e, \operatorname{A}\left(G, e, a\right)\right) - a = \operatorname{d}\left(G, \operatorname{targetCorrection}\left(G, e, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.extend_evacuate_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

targetCorrection(G,e,a)(w) is −a(e) times the indicator of w = target(e). Its coboundary is −a(e) at e and −a(e) incidence G (target(e)) f at every surviving edge f. Thus J A(a) and a define the same cohomology class.

**Definition 1.7 (The native quotient linear equivalence).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomologyEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomologyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cohomologyEquiv G e h, written Psi(G,e,h), is a rational linear equivalence Cohomology G ≃ Cohomology (contract G e h). Mathlib Submodule.mapQ descends A and J using their actual coboundary transport laws. A J = id gives one inverse law, and the target correction gives the other modulo range(coboundary G). No quotient relation or equivalence is assumed.

**Theorem 1.8 (Both representative computation rules).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableEq}\left(E\right)] , \forall G: \operatorname{DirectedMultigraph}\left(V, E\right), \forall e: E, \forall h: \operatorname{source}\left(G, e\right) \neq \operatorname{target}\left(G, e\right), {\forall a: {E} \to \mathbb{Q}, \operatorname{apply}\left(\operatorname{Psi}\left(G, e, h\right), \operatorname{class}\left(G, a\right)\right) = \operatorname{class}\left(\operatorname{contract}\left(G, e, h\right), \operatorname{A}\left(G, e, a\right)\right)} \land {\forall b: {\operatorname{Surviving}\left(e\right)} \to \mathbb{Q}, \operatorname{inverse}\left(\operatorname{Psi}\left(G, e, h\right), \operatorname{class}\left(\operatorname{contract}\left(G, e, h\right), b\right)\right) = \operatorname{class}\left(G, \operatorname{J}\left(e, b\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomologyEquiv_representatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original representative is evacuated by A; every contracted representative is extended by J with zero at the deleted coordinate. These formulas hold on the native quotients without choosing representatives.

**Theorem 1.9 (Finite-endpoint annihilation with arbitrary vertices).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)]  [\operatorname{Fintype}\left(E\right)], \forall G: \operatorname{DirectedMultigraph}\left(V, E\right), \forall k: {V} \to \mathbb{Q}, \forall z: \operatorname{CycleSpace}\left(G\right), \operatorname{edgePair}\left(\operatorname{d}\left(G, k\right), \operatorname{val}\left(z\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.coboundary_annihilates_cycles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

edgePair(a,z) is the finite sum over edge IDs f of a(f) z(f). Let S be the union of the finite source and target images. Interchanging finite sums gives edgePair(d(G,k),z) = sum over w in S of k(w) boundary(G,z)(w). Every boundary coordinate vanishes for z in CycleSpace G. There is no sum over all vertices and no Fintype V hypothesis.

**Definition 1.10 (Evaluation on the actual cohomology quotient).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomologyPairing`

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomologyPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib dotProductEquiv identifies edge functions with their coordinate functionals. Restriction to CycleSpace G gives cycleEvaluation G. The annihilation identity permits Submodule.liftQ to define cohomologyPairing G, a rational linear map from Cohomology G to the linear dual of CycleSpace G. Write pairing(G,a,z) for its value. It is independent of the cohomology representative and linear in both entries.

**Theorem 1.11 (Inverse-transpose coefficient naturality in both directions).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableEq}\left(E\right)] [\operatorname{Fintype}\left(E\right)], \forall G: \operatorname{DirectedMultigraph}\left(V, E\right), \forall e: E, \forall h: \operatorname{source}\left(G, e\right) \neq \operatorname{target}\left(G, e\right), {\forall a: {E} \to \mathbb{Q}, \forall z: \operatorname{CycleSpace}\left(G\right), \operatorname{pairing}\left(G, \operatorname{class}\left(G, a\right), z\right) = \operatorname{edgePair}\left(a, \operatorname{val}\left(z\right)\right)} \land {\forall a: \operatorname{Cohomology}\left(G\right), \forall z: \operatorname{CycleSpace}\left(\operatorname{contract}\left(G, e, h\right)\right), \operatorname{pairing}\left(\operatorname{contract}\left(G, e, h\right), \operatorname{apply}\left(\operatorname{Psi}\left(G, e, h\right), a\right), z\right) = \operatorname{pairing}\left(G, a, \operatorname{inverse}\left(\operatorname{cycleEquiv}\left(G, e, h\right), z\right)\right)} \land {\forall b: \operatorname{Cohomology}\left(\operatorname{contract}\left(G, e, h\right)\right), \forall z: \operatorname{CycleSpace}\left(G\right), \operatorname{pairing}\left(G, \operatorname{inverse}\left(\operatorname{Psi}\left(G, e, h\right), b\right), z\right) = \operatorname{pairing}\left(\operatorname{contract}\left(G, e, h\right), b, \operatorname{apply}\left(\operatorname{cycleEquiv}\left(G, e, h\right), z\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomology_pairing_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write Phi = cycleEquiv G e h. Its inverse has deleted coefficient −residual G e z.val (target(e)), and its surviving coefficients are z. Splitting the edge sum into e and the surviving IDs gives edgePair(A(a),z) = edgePair(a,Phi.symm(z)); the deleted term is −a(e) residual G e z.val (target(e)). The representative rules and annihilation descend this identity to cohomology. Applying it to J(b) and Phi(z) gives the reverse direction. This supplies actual coefficient transport for endpoint nonloop contraction. It does not establish perfect duality, cyclic AS signs, IHX or CL relation maps, socket gluing, or the complete four-loop Jacobi quotient.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.coboundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.coboundary_annihilates_cycles`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomologyEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomologyEquiv_representatives`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomologyPairing`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.cohomology_pairing_naturality`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.evacuate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.evacuate_coboundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.evacuate_extend`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.extend_coboundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.extend_evacuate_sub`
- Dependency: [D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction](MultigraphContraction.md)
