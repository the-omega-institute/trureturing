# Unbounded healing displacement

## Abstract

A tree of triangles forces arbitrarily many displaced apices before a stuck tight set can augment.

**Definition 1.1 (Two-colour frustration).**

$$\forall V \in \operatorname{Type}_{0},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{frustration}\left(G\right) = \operatorname{sInf}\left(\{ \operatorname{card}\left(\operatorname{Finset.filter}\left((\lambda e: \operatorname{Sym2}\left(V\right) \mapsto \exists u \in V,\; \exists v \in V,\; (e = \operatorname{Sym2.mk}\left(u, v\right)) \land (c\left(u\right) = c\left(v\right))), \operatorname{edgeFinset}\left(G\right)\right)\right) \mid c: V \to \operatorname{Bool} \}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.frustration` (`✓ std3`).

*Citation.* Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon, Changyeon Won (2026). *Coordination three heals, coordination four is hard: the antiferromagnetic Potts model with a costly third state*. DOI: [10.48550/arXiv.2610.41277](https://doi.org/10.48550/arXiv.2610.41277). URL: <https://arxiv.org/html/2610.41277v1>.

*Commentary.*

For a finite vertex type V with decidable equality and a simple graph G with decidable adjacency, mono(G,c) consists of the unordered edges {u,v} of G for which c(u)=c(v). Each edge is counted once. The infimum over all total Boolean colourings is the attained minimum, including the empty graph. Boolean values represent the source's states 1 and 2. This is Appendix B's frustration invariant.

**Definition 1.2 (Deletion potential).**

$$\forall V \in \operatorname{Type}_{0},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall X \in \operatorname{Finset}\left(V\right),\; \operatorname{phi}\left(G, X\right) = \operatorname{card}\left(X\right) + \operatorname{frustration}\left(\operatorname{induce}\left(G, \{ v: V \mid \neg (v \in X) \}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.phi` (`✓ std3`).

*Citation.* Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon, Changyeon Won (2026). *Coordination three heals, coordination four is hard: the antiferromagnetic Potts model with a costly third state*. DOI: [10.48550/arXiv.2610.41277](https://doi.org/10.48550/arXiv.2610.41277). URL: <https://arxiv.org/html/2610.41277v1>.

*Commentary.*

X is a finite vertex set. Deletion is the actual induced simple graph on the subtype of all vertices outside X; it retains every edge whose two endpoints survive. The cardinality term counts removed vertices.

**Definition 1.3 (Independent tight sets).**

$$\forall V \in \operatorname{Type}_{0},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall X \in \operatorname{Finset}\left(V\right),\; \operatorname{Tight}\left(G, X\right) = \left((\operatorname{IsIndepSet}\left(G, (X: \operatorname{Set}\left(V\right))\right)) \land (\operatorname{phi}\left(G, X\right) = \operatorname{frustration}\left(G\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.Tight` (`✓ std3`).

*Citation.* Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon, Changyeon Won (2026). *Coordination three heals, coordination four is hard: the antiferromagnetic Potts model with a costly third state*. DOI: [10.48550/arXiv.2610.41277](https://doi.org/10.48550/arXiv.2610.41277). URL: <https://arxiv.org/html/2610.41277v1>.

*Commentary.*

Tightness includes independence and the equality of the deletion potential to the original frustration. It does not mean a maximum independent set or a tight set of maximum cardinality.

**Definition 1.4 (Tight independent augmentation).**

$$\forall V \in \operatorname{Type}_{0},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall X \in \operatorname{Finset}\left(V\right),\; \operatorname{Augmentable}\left(G, X\right) = \left((\operatorname{Tight}\left(G, X\right)) \land (\exists v \in V,\; (\neg (v \in X)) \land (\operatorname{Tight}\left(G, \operatorname{insert}\left(v, X\right)\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.Augmentable` (`✓ std3`).

*Citation.* Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon, Changyeon Won (2026). *Coordination three heals, coordination four is hard: the antiferromagnetic Potts model with a costly third state*. DOI: [10.48550/arXiv.2610.41277](https://doi.org/10.48550/arXiv.2610.41277). URL: <https://arxiv.org/html/2610.41277v1>.

*Commentary.*

The new vertex lies outside X. The enlarged set must be both independent and tight; the definition also requires the original set to be tight.

**Definition 1.5 (Stuck tight sets).**

$$\forall V \in \operatorname{Type}_{0},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall X \in \operatorname{Finset}\left(V\right),\; \operatorname{Stuck}\left(G, X\right) = \left((\operatorname{Tight}\left(G, X\right)) \land (\neg (\operatorname{Augmentable}\left(G, X\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.Stuck` (`✓ std3`).

*Citation.* Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon, Changyeon Won (2026). *Coordination three heals, coordination four is hard: the antiferromagnetic Potts model with a costly third state*. DOI: [10.48550/arXiv.2610.41277](https://doi.org/10.48550/arXiv.2610.41277). URL: <https://arxiv.org/html/2610.41277v1>.

*Commentary.*

A stuck set is tight and admits no independent tight augmentation, exactly as in the constructive version of Appendix B.

**Definition 1.6 (The uniform displacement assertion).**

$$\operatorname{claim} = \left(\exists C \in \mathbb{N},\; \forall V \in \operatorname{Type}_{0},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] (\operatorname{Connected}\left(G\right)) \Rightarrow ((\forall v \in V,\; \operatorname{degree}\left(G, v\right) \le 3) \Rightarrow ((\neg (\operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(G, \operatorname{completeGraph}\left(\operatorname{Fin}\left(4\right)\right)\right)\right))) \Rightarrow (\forall S \in \operatorname{Finset}\left(V\right),\; (\operatorname{Stuck}\left(G, S\right)) \Rightarrow ((1 \le \operatorname{frustration}\left(\operatorname{induce}\left(G, \{ v: V \mid \neg (v \in S) \}\right)\right)) \Rightarrow (\exists T \in \operatorname{Finset}\left(V\right),\; (\operatorname{Augmentable}\left(G, T\right)) \land ((\operatorname{card}\left(T\right) = \operatorname{card}\left(S\right)) \land (\operatorname{card}\left((S \setminus T)\right) \le C)))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.claim` (`✓ std3`).

*Citation.* Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon, Changyeon Won (2026). *Coordination three heals, coordination four is hard: the antiferromagnetic Potts model with a costly third state*. DOI: [10.48550/arXiv.2610.41277](https://doi.org/10.48550/arXiv.2610.41277). URL: <https://arxiv.org/html/2610.41277v1>.

*Commentary.*

The constant C is a natural number common to every finite simple graph on a universe-zero vertex type. The type is equipped with Fintype and DecidableEq and the adjacency is decidable. The graph is connected, every degree is at most three, and there is no graph isomorphism to the complete graph on Fin 4. Every stuck tight S with residual frustration at least one must have an augmentable tight T of the same cardinality with at most C vertices of S absent from T. This is the displacement consequence of a uniform stage bound in Section VIII(1).

**Theorem 1.7 (No uniform displacement bound).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result` (`✓ std3`). ∎

*Resolves.* `Problems/choi-yoo-kim-kwon-won-2026-healing-chain-unbounded` (refuted) by `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"choi-yoo-kim-kwon-won-2026-healing-chain-unbounded","declaration_gid":"D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon, Changyeon Won (2026). *Coordination three heals, coordination four is hard: the antiferromagnetic Potts model with a costly third state*. DOI: [10.48550/arXiv.2610.41277](https://doi.org/10.48550/arXiv.2610.41277). URL: <https://arxiv.org/html/2610.41277v1>.

*Commentary.*

Fix any proposed C and put h=C+1 and B=3·2^h−2. The vertices are pairs of a block in Fin B and a port in Fin 3. Every block is a triangle. Root port b joins the apex of block b+1. At each positive block u, ports 1 and 2 join the apices of blocks 2u+2 and 2u+3 whenever those blocks exist. These are exactly the complete rooted triangle trees of height h, with three children at the root and two at each other internal block. Distinct incoming bridges have distinct parent ports, by parity and the separation of the root children 1,2,3 from later children. Every vertex therefore has its two triangle neighbours and at most one bridge neighbour. Parent descent proves connectedness. There are 3B≥12 vertices, so the graph is not K4. Every Boolean colouring leaves a monochromatic edge in each triangle, and the block indices make these edges distinct. For the matching upper bound, give every apex a shade and both other ports its opposite. The root shade is false; the first child's shade is true and the other two children's shades are false. Below them each child inherits its parent's shade. Every bridge is bichromatic and the only monochromatic edge in each triangle is its port-1 to port-2 edge. Thus fr(G)=B. Let S contain every positive block's apex. It is independent and has B−1 vertices. Deleting S removes every bridge and leaves the root triangle and B−1 isolated edges. Colour those edges properly and the root with one monochromatic edge; hence fr(G−S)=1 and S is tight. Every root vertex is adjacent to a child apex in S, and every remaining nonroot port is adjacent to its own apex in S. Consequently S has no independent augmentation and is stuck. If T is augmentable and |T|=B−1, its augmentation R has B vertices and is independent. The projection from R to blocks is injective; equal finite cardinalities make it surjective. Thus R meets each triangle exactly once. Its root selection excludes a child's apex. The selected vertex of that child is then a port and excludes the next child's apex. For a positive block u whose selected port is nonzero, induction constructs k+1 distinct missing apices whenever 2^k(u+3)≤B+2: the child c=2u+r(u)+1 satisfies u<c and c+3≤2(u+3), preserving the induction bound. The first child has u≤3, so k=C is available. The resulting C+1 apices are outside R and therefore outside T, contradicting |S∖T|≤C. No residual-frustration formula for arbitrary deletion sets is needed. The source's component-dependent healing theorem remains consistent with this family. A tested set after j chain exchanges and one test exchange loses at most j+1 vertices of the original S. Any absolute stage bound would therefore give an absolute displacement bound, which the theorem refutes. This implication concerns the number of exchanges; zero-based stage labels differ by one and do not change unboundedness.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.Augmentable`
- Truth anchor: `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.Stuck`
- Truth anchor: `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.Tight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.frustration`
- Truth anchor: `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.phi`
- Truth anchor: `D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result`
