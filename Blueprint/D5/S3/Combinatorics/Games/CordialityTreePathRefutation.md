# A Tree Exceeds the Path in the Cordiality Game

## Abstract

A tree on ten vertices forces discrepancy at least three, while Admirable can hold the path on ten vertices to discrepancy at most one.

**Definition 1.1 (Unlabelled vertices).**

$$\forall (n:\mathbb N), \forall (A:\operatorname{Finset}(\operatorname{Fin}(n))), \forall (B:\operatorname{Finset}(\operatorname{Fin}(n))), \operatorname{free}(A, B)=\operatorname{Finset}.\operatorname{univ}\setminus (A\cup B)$$

*Formalization.* `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.free` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The disjoint sets A and B record the vertices already labelled zero and one. Their complement consists of the legal next moves.

**Definition 1.2 (Edges labelled one).**

$$\forall (n:\mathbb N), \forall (G:\operatorname{SimpleGraph}(\operatorname{Fin}(n))), [\operatorname{DecidableRel}(G.\operatorname{Adj})] \forall (A:\operatorname{Finset}(\operatorname{Fin}(n))), \operatorname{e1}(G, A)=G.\operatorname{edgeFinset}.\operatorname{filter}(fun (e:\operatorname{Sym2}(\operatorname{Fin}(n))) \mapsto \exists (u:\operatorname{Fin}(n)), (u\in e)\land (\exists (v:\operatorname{Fin}(n)), (v\in e)\land ((u\in A)\land (\neg (v\in A))))).\operatorname{card}$$

*Formalization.* `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.e1` (`✓ std3`).

*Citation.* Elliot Krop; Aryan Mittal; Michael C. Wigal (2024). *The Cordiality Game and the Game Cordiality Number*. DOI: [10.1007/s00373-024-02798-1](https://doi.org/10.1007/s00373-024-02798-1). URL: <https://arxiv.org/abs/2403.18060v1>.

*Commentary.*

Section 1, page 2: "The labels on edges are then determined by the sum of incident vertex labels modulo 2." Vertices are Fin n. A is the zero-labelled set, so the filter counts each undirected edge with oppositely labelled endpoints once.

**Definition 1.3 (Edges labelled zero).**

$$\forall (n:\mathbb N), \forall (G:\operatorname{SimpleGraph}(\operatorname{Fin}(n))), [\operatorname{DecidableRel}(G.\operatorname{Adj})] \forall (A:\operatorname{Finset}(\operatorname{Fin}(n))), \operatorname{e0}(G, A)=G.\operatorname{edgeFinset}.\operatorname{card}-\operatorname{e1}(G, A)$$

*Formalization.* `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.e0` (`✓ std3`).

*Citation.* Elliot Krop; Aryan Mittal; Michael C. Wigal (2024). *The Cordiality Game and the Game Cordiality Number*. DOI: [10.1007/s00373-024-02798-1](https://doi.org/10.1007/s00373-024-02798-1). URL: <https://arxiv.org/abs/2403.18060v1>.

*Commentary.*

Section 1, page 2: "In other words, after all the vertices are labeled, if we let e₀ be the number of edges labeled by 0 and e₁ be the number of edges labeled by 1, then we define the discrepancy to be d = |e₁ − e₀|." Subtraction here is natural-number subtraction. Every edge has exactly one of the two labels.

**Definition 1.4 (Terminal discrepancy).**

$$\forall (n:\mathbb N), \forall (G:\operatorname{SimpleGraph}(\operatorname{Fin}(n))), [\operatorname{DecidableRel}(G.\operatorname{Adj})] \forall (A:\operatorname{Finset}(\operatorname{Fin}(n))), \operatorname{discrepancy}(G, A)=\operatorname{Int}.\operatorname{natAbs}((\operatorname{e1}(G, A):\mathbb Z)-(\operatorname{e0}(G, A):\mathbb Z))$$

*Formalization.* `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.discrepancy` (`✓ std3`).

*Citation.* Elliot Krop; Aryan Mittal; Michael C. Wigal (2024). *The Cordiality Game and the Game Cordiality Number*. DOI: [10.1007/s00373-024-02798-1](https://doi.org/10.1007/s00373-024-02798-1). URL: <https://arxiv.org/abs/2403.18060v1>.

*Commentary.*

Section 1, page 2: "then we define the discrepancy to be d = |e₁ − e₀|. Then Admirable attempts to minimize d and Impish attempts to maximize d." The two counts are coerced from naturals to integers before subtraction. At a terminal state B is the complement of A.

**Definition 1.5 (Backward induction).**

$$\forall (n:\mathbb N), \forall (G:\operatorname{SimpleGraph}(\operatorname{Fin}(n))), [\operatorname{DecidableRel}(G.\operatorname{Adj})] \forall (A:\operatorname{Finset}(\operatorname{Fin}(n))), \forall (B:\operatorname{Finset}(\operatorname{Fin}(n))), \operatorname{gameValue}(G, A, B)=if (\operatorname{free}(A, B)=\emptyset) then \operatorname{discrepancy}(G, A) else if (A.\operatorname{card}=B.\operatorname{card}) then (\operatorname{free}(A, B).\operatorname{attach}.\operatorname{image}(fun v \mapsto \operatorname{gameValue}(G, \operatorname{Finset}.\operatorname{insert}(v.1, A), B))).\operatorname{min}' else (\operatorname{free}(A, B).\operatorname{attach}.\operatorname{image}(fun v \mapsto \operatorname{gameValue}(G, A, \operatorname{Finset}.\operatorname{insert}(v.1, B)))).\operatorname{max}'$$

*Formalization.* `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.gameValue` (`✓ std3`).

*Citation.* Elliot Krop; Aryan Mittal; Michael C. Wigal (2024). *The Cordiality Game and the Game Cordiality Number*. DOI: [10.1007/s00373-024-02798-1](https://doi.org/10.1007/s00373-024-02798-1). URL: <https://arxiv.org/abs/2403.18060v1>.

*Commentary.*

Section 1, page 2: "Admirable labels selected vertices by 0 and Impish labels selected vertices by 1." The initial state is empty and Admirable moves first. Equal cardinals mean Admirable moves and takes the minimum; otherwise Impish takes the maximum. The recursion decreases the number of unlabelled vertices. Nonempty-set proof arguments to min' and max' are implicit in the display. Strong induction proves that either player's guaranteed discrepancy bounds this value.

**Definition 1.6 (Game cordiality number).**

$$\forall (n:\mathbb N), \forall (G:\operatorname{SimpleGraph}(\operatorname{Fin}(n))), [\operatorname{DecidableRel}(G.\operatorname{Adj})] \operatorname{cg}(G)=\operatorname{gameValue}(G, \emptyset, \emptyset)$$

*Formalization.* `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.cg` (`✓ std3`).

*Citation.* Elliot Krop; Aryan Mittal; Michael C. Wigal (2024). *The Cordiality Game and the Game Cordiality Number*. DOI: [10.1007/s00373-024-02798-1](https://doi.org/10.1007/s00373-024-02798-1). URL: <https://arxiv.org/abs/2403.18060v1>.

*Commentary.*

Section 1, page 2: "We define the game cordiality number, c_g(G), to be the value of d when both players play optimally. Further, to prove our claimed bounds, we create a variant of the cordiality game where Impish starts rather than Admirable." Thus cg is the Admirable-starts value.

**Definition 1.7 (The tree–path conjecture).**

$$\operatorname{claim}\iff \forall (n:\mathbb N), \forall (T:\operatorname{SimpleGraph}(\operatorname{Fin}(n))), [\operatorname{DecidableRel}(T.\operatorname{Adj})] [\operatorname{DecidableRel}(\operatorname{SimpleGraph}.\operatorname{pathGraph}(n).\operatorname{Adj})] T.\operatorname{IsTree}\longrightarrow \operatorname{cg}(T)\le \operatorname{cg}(\operatorname{SimpleGraph}.\operatorname{pathGraph}(n))$$

*Formalization.* `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.claim` (`✓ std3`).

*Citation.* Elliot Krop; Aryan Mittal; Michael C. Wigal (2024). *The Cordiality Game and the Game Cordiality Number*. DOI: [10.1007/s00373-024-02798-1](https://doi.org/10.1007/s00373-024-02798-1). URL: <https://arxiv.org/abs/2403.18060v1>.

*Commentary.*

Section 3, Conjecture 3.2, page 9: "For any tree T of order n, c_g(T) ≤ c_g(P_n)." The encoding uses every natural n and every SimpleGraph on Fin n. IsTree is Mathlib's tree predicate. The two anonymous DecidableRel arguments express decidability of the adjacency relations and preserve this quantification.

**Theorem 1.8 (A ten-vertex counterexample).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Elliot Krop; Aryan Mittal; Michael C. Wigal (2024). *The Cordiality Game and the Game Cordiality Number*. DOI: [10.1007/s00373-024-02798-1](https://doi.org/10.1007/s00373-024-02798-1). URL: <https://arxiv.org/abs/2403.18060v1>.

*Commentary.*

Take the tree with edges {i,i+1} for i from zero through six, together with {0,8} and {0,9}. Explicit walks establish connectivity, and its nine edges establish that it is a tree. Impish pairs (0,4), (1,5), (2,6), (3,7), and (8,9), responding to each Admirable move with its partner. The pairing is legal and preserves disjointness. Every terminal transversal has discrepancy at least three. Strong induction transfers that bound to the minimax value. For the path on ten vertices, an explicit finite strategy table and its recursive soundness theorem bound the value above by one. The conjectured comparison would therefore imply three is at most one.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.cg`
- Truth anchor: `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.discrepancy`
- Truth anchor: `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.e0`
- Truth anchor: `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.e1`
- Truth anchor: `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.free`
- Truth anchor: `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.gameValue`
- Truth anchor: `D5/S3/Combinatorics/Games/CordialityTreePathRefutation.result`
- Dependency: [D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap](../../StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.md)
