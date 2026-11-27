# Sharpness of the chordal Banach reconstruction constant

## Abstract

Finite connected chordal graphs force real Banach reconstruction errors arbitrarily close to four.

Write Skew(V,g) for skew symmetry on every ordered pair of vertices, and Flat(G,g) for the condition that the norm of the sum of the first two oriented gains minus the third gain is at most one on every ordered triangle of G. Write Error(g,p,u,v) for the norm of the gain on the oriented edge from u to v minus the potential difference p(v) minus p(u).

**Theorem 1.1 (Errors approach four).**

$$\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] \exists G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{Chordal}\left(G\right)) \land ((\operatorname{Connected}\left(G\right)) \land (\exists E \in \mathrm{Type},\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{CompleteSpace}\left(E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] \exists g \in V \to \left(V \to E\right),\; (\operatorname{Skew}\left(V, g\right)) \land ((\operatorname{Flat}\left(G, g\right)) \land (\forall p \in V \to E,\; \exists u \in V,\; \exists v \in V,\; (\operatorname{Adj}\left(G, u, v\right)) \land (4-e \leq \operatorname{Error}\left(g, p, u, v\right))))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour.exists_chordal_banach_gain_lower_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Build a finite graph by attaching complete blocks along the union of nested surviving subsets of the last several blocks. The surviving subsets form a clique. A deepest vertex on any cycle of length at least four therefore has adjacent cycle neighbours. The construction includes every permitted retention choice and multiple copies of each descendant history.

On oriented chains use the supremum of absolute evaluations by cochains bounded by three on edges and by one on triangles. Signed coordinate evaluations bound the chain mass by three times this norm. The supported chains of boundary zero form a finite-dimensional real Banach space. Rooted paths correct the edge generators into cycles, and changing a potential adds a cycle to each rooted path chain.

Translate the chain potentials by their mean over the root block and average over graph symmetries. Project to ancestral spines. The norm error of changing the projection is controlled by the mass in a single descendant copy, which tends to zero as the number of copies grows. The remaining changes in retention ages and the effect of distinguishing a parent vertex are controlled by the ratio of the retained sizes.

On the band of ages, centered residue indicators give a skew triangle-flat cochain for each residue. An edge of the full width in its residue path contributes two minus two over the width. Two distinguished vertices add two to the ideal band expression. The refinement estimates bound the difference between that expression and the evaluation of the actual residual. The potential terms telescope on each residue path and cancel between residues. Increasing the width, the number of full-width steps, and the retention and copy parameters gives the stated lower bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour.exists_chordal_banach_gain_lower_four`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](Dirac.md)
