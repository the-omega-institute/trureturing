# Connected encoder classes and powers of three

## Abstract

The commuting order-three rotations of the matched input-pivot pairs act freely on each connected class of normalized encoders. Each class therefore has cardinality divisible by 3^k.

**Definition 1.1 (Adding one input row to another).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; \forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{addInputRow}\left(G, i, j\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left(\operatorname{fun} (x y: \operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{match} x,y \operatorname{with} \begin{aligned}|\operatorname{Sum}.\operatorname{inl}\left(a\right),\operatorname{Sum}.\operatorname{inr}\left(o\right) \mapsto \operatorname{if} a = i \operatorname{then} \operatorname{Xor}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, \operatorname{Sum}.\operatorname{inl}\left(i\right), \operatorname{Sum}.\operatorname{inr}\left(o\right)\right), \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, \operatorname{Sum}.\operatorname{inl}\left(j\right), \operatorname{Sum}.\operatorname{inr}\left(o\right)\right)\right) \operatorname{else} \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, x, y\right)\\|\operatorname{Sum}.\operatorname{inr}\left(o\right),\operatorname{Sum}.\operatorname{inl}\left(a\right) \mapsto \operatorname{if} a = i \operatorname{then} \operatorname{Xor}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, \operatorname{Sum}.\operatorname{inl}\left(i\right), \operatorname{Sum}.\operatorname{inr}\left(o\right)\right), \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, \operatorname{Sum}.\operatorname{inl}\left(j\right), \operatorname{Sum}.\operatorname{inr}\left(o\right)\right)\right) \operatorname{else} \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, x, y\right)\\|x,y \mapsto \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, x, y\right)\end{aligned})\right)$$

*Formalization.* `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.addInputRow` (`✓ std3`).

*Citation.* Andrey Boris Khesin, Alexander M. Li (2024). *Equivalence Classes of Quantum Error-Correcting Codes*. DOI: [10.48550/arXiv.2406.12083](https://doi.org/10.48550/arXiv.2406.12083). URL: <https://arxiv.org/abs/2406.12083v1>.

*Commentary.*

Conjecture 6.3, p. 17: “4. Performing row operations on the adjacency matrix of input to output edges.” Section 6, p. 18: “Operation 4 consists of adding rows of the adjacency matrix between input and output nodes in modulo 2.” Input vertices are Sum.inl and output vertices are Sum.inr. The row indexed by j is added to row i with Xor; all other edges are retained. SimpleGraph.fromRel removes loops and symmetrizes the displayed relation.

**Definition 1.2 (Elementary encoder operations).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; \begin{aligned}\forall v \in \operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right),\; \operatorname{Step}\left(G, \operatorname{SimpleGraph}.\operatorname{fromRel}\left(\operatorname{fun} (x y: \operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{Xor}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, x, y\right), (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, v, x\right)) \land (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, v, y\right))\right))\right)\right)\\\forall sigma \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Step}\left(G, \operatorname{SimpleGraph}.\operatorname{map}\left(\operatorname{Equiv}.\operatorname{toEmbedding}\left(\operatorname{Equiv}.\operatorname{sumCongr}\left(\operatorname{Equiv}.\operatorname{refl}\left(\operatorname{Fin}\left(k\right)\right), sigma\right)\right), G\right)\right)\\\forall tau \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{Step}\left(G, \operatorname{SimpleGraph}.\operatorname{map}\left(\operatorname{Equiv}.\operatorname{toEmbedding}\left(\operatorname{Equiv}.\operatorname{sumCongr}\left(tau, \operatorname{Equiv}.\operatorname{refl}\left(\operatorname{Fin}\left(n\right)\right)\right)\right), G\right)\right)\\\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; (\neg (i = j)) \Rightarrow (\operatorname{Step}\left(G, \operatorname{addInputRow}\left(G, i, j\right)\right))\\\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{Step}\left(G, \operatorname{SimpleGraph}.\operatorname{deleteEdges}\left(G, \left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Sum}.\operatorname{inl}\left(i\right), \operatorname{Sum}.\operatorname{inl}\left(j\right)\right)\right\}\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.Step` (`✓ std3`).

*Citation.* Andrey Boris Khesin, Alexander M. Li (2024). *Equivalence Classes of Quantum Error-Correcting Codes*. DOI: [10.48550/arXiv.2406.12083](https://doi.org/10.48550/arXiv.2406.12083). URL: <https://arxiv.org/abs/2406.12083v1>.

*Commentary.*

Conjecture 6.3, p. 17, lists: “1. Local complementing about any vertex of the graph. 2. Permuting the output vertices. 3. Permuting the input vertices. 4. Performing row operations on the adjacency matrix of input to output edges. 5. Removing an input-input edge. 6. Applying local operations on the output edges.” Definition 2.7, p. 6: “By performing a local complementation about vertex v, all edges connecting two vertices in N(v) are toggled.” Step is the inductive relation generated by the five displayed constructors. Operation 6 acts on the removed local Clifford decorations. Permutations act by graph map along Equiv.sumCongr, with each embedding coerced to its underlying function; the row indices in a row operation must be distinct. Sym2.mk forms an unordered pair.

**Definition 1.3 (Renormalizing operations).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; \begin{aligned}\forall sigma \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{RenormStep}\left(G, \operatorname{SimpleGraph}.\operatorname{map}\left(\operatorname{Equiv}.\operatorname{toEmbedding}\left(\operatorname{Equiv}.\operatorname{sumCongr}\left(\operatorname{Equiv}.\operatorname{refl}\left(\operatorname{Fin}\left(k\right)\right), sigma\right)\right), G\right)\right)\\\forall tau \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{RenormStep}\left(G, \operatorname{SimpleGraph}.\operatorname{map}\left(\operatorname{Equiv}.\operatorname{toEmbedding}\left(\operatorname{Equiv}.\operatorname{sumCongr}\left(tau, \operatorname{Equiv}.\operatorname{refl}\left(\operatorname{Fin}\left(n\right)\right)\right)\right), G\right)\right)\\\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; (\neg (i = j)) \Rightarrow (\operatorname{RenormStep}\left(G, \operatorname{addInputRow}\left(G, i, j\right)\right))\\\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{RenormStep}\left(G, \operatorname{SimpleGraph}.\operatorname{deleteEdges}\left(G, \left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Sum}.\operatorname{inl}\left(i\right), \operatorname{Sum}.\operatorname{inl}\left(j\right)\right)\right\}\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.RenormStep` (`✓ std3`).

*Citation.* Andrey Boris Khesin, Alexander M. Li (2024). *Equivalence Classes of Quantum Error-Correcting Codes*. DOI: [10.48550/arXiv.2406.12083](https://doi.org/10.48550/arXiv.2406.12083). URL: <https://arxiv.org/abs/2406.12083v1>.

*Commentary.*

Section 7, p. 19: “To fix this, we first employ operation 5 from Conjecture 6.3 to set all input-input edges to 0.” It continues: “Operation 2 is used to put the pivots back into their fixed positions, so they once again correspond to their input vertices.” RenormStep is the inductive relation generated by operations 2–5; its four constructors are displayed in full.

**Definition 1.4 (Normalized labelled encoders).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; (\operatorname{Normalized}\left(G\right)) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \neg (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, \operatorname{Sum}.\operatorname{inl}\left(i\right), \operatorname{Sum}.\operatorname{inl}\left(j\right)\right))) \land ((\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (\operatorname{val}\left(j\right) < k) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, \operatorname{Sum}.\operatorname{inl}\left(i\right), \operatorname{Sum}.\operatorname{inr}\left(j\right)\right)) \Leftrightarrow (\operatorname{val}\left(j\right) = \operatorname{val}\left(i\right)))) \land (\forall j \in \operatorname{Fin}\left(n\right),\; \forall l \in \operatorname{Fin}\left(n\right),\; (\operatorname{val}\left(j\right) < k) \Rightarrow ((\operatorname{val}\left(l\right) < k) \Rightarrow (\neg (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, \operatorname{Sum}.\operatorname{inr}\left(j\right), \operatorname{Sum}.\operatorname{inr}\left(l\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.Normalized` (`✓ std3`).

*Citation.* Andrey Boris Khesin, Alexander M. Li (2024). *Equivalence Classes of Quantum Error-Correcting Codes*. DOI: [10.48550/arXiv.2406.12083](https://doi.org/10.48550/arXiv.2406.12083). URL: <https://arxiv.org/abs/2406.12083v1>.

*Commentary.*

Claim 6.4, p. 19: “To find the distinct encoders in an equivalence class of the set of Clifford codes, it is sufficient to find the distinct encoders in the equivalence class satisfying the following constraints:” The list reads: “The input-output adjacency matrix is in RREF.” “The pivot nodes are the lowest-numbered output nodes, and they are ordered to match the order of the input nodes.” “Local Clifford gates on the free output edges are all removed, leaving only output Z nodes with phase 0.” “Diagrams with pivot-pivot edges are not included.” Inputs are Fin(k); outputs are Fin(n). The first k outputs are pivots with the identity input-pivot block. There are no input-input or pivot-pivot edges. The diagram has no local Clifford decorations.

**Definition 1.5 (An operation followed by renormalization).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; \forall H \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; (\operatorname{NormalizedStep}\left(G, H\right)) \Leftrightarrow ((\operatorname{Normalized}\left(G\right)) \land ((\operatorname{Normalized}\left(H\right)) \land (\exists Z \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; (\operatorname{Step}\left(G, Z\right)) \land (\operatorname{Relation}.\operatorname{ReflTransGen}\left(\operatorname{RenormStep}, Z, H\right)))))$$

*Formalization.* `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.NormalizedStep` (`✓ std3`).

*Citation.* Andrey Boris Khesin, Alexander M. Li (2024). *Equivalence Classes of Quantum Error-Correcting Codes*. DOI: [10.48550/arXiv.2406.12083](https://doi.org/10.48550/arXiv.2406.12083). URL: <https://arxiv.org/abs/2406.12083v1>.

*Commentary.*

Section 7, p. 19: “The code takes an integer representation, say n, of an encoder graph, performs one operation from Conjecture 6.3 on the encoder graph, then merges the disjoint sets of n and the integer representing the resulting encoder graph.” The two endpoints are normalized; an intermediate graph Z is reached by Step and then a finite, possibly empty sequence of RenormStep operations. Relation.ReflTransGen represents that sequence.

**Definition 1.6 (Number of normalized graphs in a class).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{classSize}\left(G\right) = \operatorname{Nat}.\operatorname{card}\left(\{H: \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right) // (\operatorname{Normalized}\left(H\right)) \land (\operatorname{Relation}.\operatorname{EqvGen}\left(\operatorname{NormalizedStep}, G, H\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.classSize` (`✓ std3`).

*Citation.* Andrey Boris Khesin, Alexander M. Li (2024). *Equivalence Classes of Quantum Error-Correcting Codes*. DOI: [10.48550/arXiv.2406.12083](https://doi.org/10.48550/arXiv.2406.12083). URL: <https://arxiv.org/abs/2406.12083v1>.

*Commentary.*

Section 7, p. 19: “The variable edges’ values in the adjacency matrix are made into a single integer using a binary representation.” The source counts distinct labelled normalized adjacency matrices. Nat.card counts the subtype of normalized graphs H in the Relation.EqvGen closure of NormalizedStep from G; it does not quotient graphs by isomorphism.

**Definition 1.7 (Khesin–Li Conjecture 7.1).**

$$(claim) \Leftrightarrow (\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; (0 < k) \Rightarrow ((k < n) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; (\operatorname{Normalized}\left(G\right)) \Rightarrow ((\forall H \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; (\operatorname{Normalized}\left(H\right)) \Rightarrow ((\operatorname{Relation}.\operatorname{EqvGen}\left(\operatorname{NormalizedStep}, G, H\right)) \Rightarrow (\operatorname{SimpleGraph}.\operatorname{Connected}\left(H\right)))) \Rightarrow (3^{k} \mid \operatorname{classSize}\left(G\right))))))$$

*Formalization.* `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.claim` (`✓ std3`).

*Citation.* Andrey Boris Khesin, Alexander M. Li (2024). *Equivalence Classes of Quantum Error-Correcting Codes*. DOI: [10.48550/arXiv.2406.12083](https://doi.org/10.48550/arXiv.2406.12083). URL: <https://arxiv.org/abs/2406.12083v1>.

*Commentary.*

Conjecture 7.1 (arXiv:2406.12083v1, p. 20): “For positive integers n > k, the equivalence classes of [n,k] codes with a single connected component have sizes divisible by 3^k.” Here 0 < k and k < n express the positive integers. The carrier is SimpleGraph(Sum(Fin(k),Fin(n))). Normalized fixes the pivot positions and the three fixed adjacency blocks. Every normalized H in the equivalence class is required to be connected, as in the source's figures. The cardinality counts labelled normalized graphs.

**Theorem 1.8 (Divisibility by 3^k).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; (0 < k) \Rightarrow ((k < n) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; (\operatorname{Normalized}\left(G\right)) \Rightarrow ((\forall H \in \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right)\right),\; (\operatorname{Normalized}\left(H\right)) \Rightarrow ((\operatorname{Relation}.\operatorname{EqvGen}\left(\operatorname{NormalizedStep}, G, H\right)) \Rightarrow (\operatorname{SimpleGraph}.\operatorname{Connected}\left(H\right)))) \Rightarrow (3^{k} \mid \operatorname{classSize}\left(G\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrey Boris Khesin, Alexander M. Li (2024). *Equivalence Classes of Quantum Error-Correcting Codes*. DOI: [10.48550/arXiv.2406.12083](https://doi.org/10.48550/arXiv.2406.12083). URL: <https://arxiv.org/abs/2406.12083v1>.

*Commentary.*

For each input u and its matched pivot p, complement first at u and then at p. On their free-output adjacency rows this sends (b,c) to (c,b xor c), an order-three rotation. Local complementations at different pairs commute because the corresponding vertices are nonadjacent. If both rows vanished, u and p would form an isolated component; connectedness and k < n exclude this. Every nonidentity coordinate rotation therefore moves each class member. The free action of the product of k cyclic groups of order three partitions the class into equal orbits of size 3^k. The orbit decomposition in Mathlib gives the divisibility.

## References

- Truth anchor: `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.Normalized`
- Truth anchor: `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.NormalizedStep`
- Truth anchor: `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.RenormStep`
- Truth anchor: `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.Step`
- Truth anchor: `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.addInputRow`
- Truth anchor: `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.claim`
- Truth anchor: `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.classSize`
- Truth anchor: `D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.result`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Cuts](../../Combinatorics/Graph/Brooks/Cuts.md)
- Dependency: [D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition](../Algebra/GeneralizedCHSHGroupDecomposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph](../Entanglement/GraphStateMonogamyForbiddenSubgraph.md)
