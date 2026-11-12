# An irrational purely imaginary independence root

## Abstract

A finite graph with an irrational purely imaginary independence root.

Brown and Cameron, A note on purely imaginary independence roots, arXiv:2001.08881v2, DOI 10.1016/j.disc.2020.112113, Question 2 on printed page 11, ask whether a graph can have an independence root bi with irrational real b. The polynomial counts every independent vertex subset by cardinality, with the empty subset contributing one. There is no prescribed graph order, connectivity, independence number, or lower bound on the modulus.

**Definition 1.1 (The recursive tagged carrier).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.Copies`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.Copies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every type α : Type and every natural n, Copies α n is defined recursively by Copies α 0 = Empty and Copies α (n+1) = α ⊕ Copies α n. The sum tags distinguish successive copies, including the separate empty terminal type. No finiteness assumption is required to define this carrier.

The instance copiesFintype supplies Fintype (Copies α n) for every n when α has a Fintype instance. At zero it uses the Fintype instance of Empty; at a successor it installs copiesFintype at n and uses the sum instance on α ⊕ Copies α n. The instance copiesDecidableEq likewise supplies DecidableEq (Copies α n) from DecidableEq α, using Empty at zero and the recursive sum instance at a successor. These instances introduce no restriction on n.

**Definition 1.2 (Joining every tagged copy).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.joinedCopies`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.joinedCopies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any α : Type and G : SimpleGraph α, joinedCopies G n is a SimpleGraph (Copies α n), defined for all natural n by joinedCopies G 0 = ⊥ on Empty and joinedCopies G (n+1) = join G (joinedCopies G n). Here join is the graph on the tagged sum with all cross edges and the original edges within each side. Thus every distinct pair of copies is completely joined, while every individual copy retains G. The definition requires no finite-domain or decidability hypothesis.

**Definition 1.3 (The four-clique carrier).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.FourCliqueVertices`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.FourCliqueVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public type abbreviation is FourCliqueVertices := ((Fin 4 ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 4. Its left-associated sum tags distinguish the four four-element vertex sets.

**Definition 1.4 (Four disjoint complete graphs).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.fourCliques`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.fourCliques` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph fourCliques : SimpleGraph FourCliqueVertices is defined by (((⊤ : SimpleGraph (Fin 4)) ⊕g ⊤) ⊕g ⊤) ⊕g ⊤. Each top graph is complete on its own Fin 4 carrier; ⊕g is the disjoint graph sum, so there are no edges between the four summands.

**Definition 1.5 (The complete witness carrier).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.Vertex`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public type abbreviation is Vertex := (FourCliqueVertices ⊕ Copies (Fin 2) 34) ⊕ Fin 44. The parenthesized sum retains the four-clique carrier, the thirty-four tagged pairs, and the final forty-four-element carrier as distinct parts.

**Definition 1.6 (A graph with 128 vertices).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.graph`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let A be the disjoint union of four complete graphs on four vertices. Join A, thirty-four blocks each consisting of two isolated vertices, and a complete graph on forty-four vertices. Distinct join blocks are completely adjacent. The total order is 16+68+44=128. The tagged vertex type and its equivalence to Fin 128 describe actual finite simple undirected graphs.

**Definition 1.7 (Transport to Fin 128).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.finGraph`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.finGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph finGraph : SimpleGraph (Fin 128) is defined by graph.map (Fintype.equivFinOfCardEq vertex_card).toEmbedding. The internal proof vertex_card establishes Fintype.card Vertex = 128. Fintype.equivFinOfCardEq vertex_card is therefore an equivalence Vertex ≃ Fin 128; graph.map transports edges along its underlying embedding. This specifies the actual graph used in the existential conclusion on the standard finite domain.

**Theorem 1.8 (The native integer polynomial).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.native_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.native_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty independent subset belongs to exactly one join block. Within A, each of the four cliques contributes either no vertex or one of four vertices, giving (1+4X)^4. Each isolated pair contributes 2X+X^2 beyond the empty subset; the forty-four-clique contributes 44X. Thus the actual independent-subset sum is (1+4X)^4+34(2X+X^2)+44X = 1+128X+130X^2+256X^3+256X^4 = (1+2X^2)(1+128X+128X^2). The degree is exactly four. For every natural k, the number of independent k-subsets is 1, 128, 130, 256, 256 for k=0,1,2,3,4 respectively, and zero for every k greater than four. These counts are cardinalities of filtered actual configuration families.

**Theorem 1.9 (Existence with irrational imaginary part).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.result`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. I. Brown and Ben Cameron (2020). *A note on purely imaginary independence roots*. DOI: [10.1016/j.disc.2020.112113](https://doi.org/10.1016/j.disc.2020.112113). URL: <https://arxiv.org/abs/2001.08881v2>.

*Commentary.*

There exist n, a simple graph G on Fin n, and an irrational real b such that the complex evaluation of the native integer independence polynomial of G at i*b equals zero. Take n=128 and b=1/sqrt(2). Irrationality follows from irrationality of sqrt(2) and preservation of irrationality under inversion. Since (i*b)^2=-1/2, the factor 1+2X^2 vanishes exactly. Relabeling preserves the full independent-subset sum.

The construction answers the unrestricted existential question. It gives no minimum-order claim and no claim that every irrational purely imaginary number is an independence root. The source's separate restriction on square roots of rationals greater than one does not exclude b^2=1/2.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.Copies`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.FourCliqueVertices`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.Vertex`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.finGraph`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.fourCliques`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.graph`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.joinedCopies`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.native_polynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.result`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration](../../Combinatorics/Graph/LinearForests/TwoPathConcentration.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/PartitionJoin](PartitionJoin.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling](PartitionRelabeling.md)
