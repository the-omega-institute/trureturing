# The negativity of randomized graph states is not monotone

## Abstract

Wu, Rossi, Kampermann, Severini, Kwek, Macchiavello and Bruss (arXiv:1403.3828, Section V) ask whether the negativity of a randomized graph state, across any bipartition, increases monotonically with the probability p that each edge is present. It does not: for the complete bipartite graph K_(3,3) and the bipartition into its two parts, the negativity is larger than 1/2 at p = 97/100 and at most 1/2 at p = 1.

**Definition 1.1 (Controlled-Z phases).**

$$\forall n : \mathbb{N}, \forall a : \operatorname{Fin}\left(n\right), \forall b : \operatorname{Fin}\left(n\right), \forall x : \operatorname{Qubits}\left(n\right), \operatorname{czPhase}\left(\operatorname{s}\left(a, b\right), x\right) = (-1)^{\operatorname{x}\left(a\right) \cdot \operatorname{x}\left(b\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.czPhase` (`✓ std3`).

*Citation.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

The n qubits are indexed by Fin(n) and the computational basis by the maps x from Fin(n) to {0, 1}. The controlled-Z gate on the edge {a, b} is diagonal in this basis, with entry (-1)^(x(a) x(b)) at the basis state x.

**Definition 1.2 (The product state).**

$$\forall n : \mathbb{N}, \forall x : \operatorname{Qubits}\left(n\right), \operatorname{plusState}\left(n, x\right) = (\frac{1}{\sqrt{2}})^{n}$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.plusState` (`✓ std3`).

*Citation.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

The state |+>^n has every computational-basis amplitude equal to 2^(-n/2).

**Definition 1.3 (Graph states).**

$$\forall n : \mathbb{N}, \forall F : \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right), \forall x : \operatorname{Qubits}\left(n\right), \operatorname{graphState}\left(F, x\right) = (\prod_{e \in F} \operatorname{czPhase}\left(e, x\right)) \cdot \operatorname{plusState}\left(n, x\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.graphState` (`✓ std3`).

*Citation.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

The graph state of an edge set F is the product of the controlled-Z gates of its edges applied to |+>^n. These gates are diagonal, so the amplitude at x is the product of their phases at x times the amplitude of |+>^n.

**Definition 1.4 (Randomized graph states).**

$$\forall n : \mathbb{N}, \forall G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \forall p : \mathbb{R}, \operatorname{rgState}\left(G, p\right) = \sum_{F \subseteq \operatorname{edgeFinset}\left(G\right)} p^{\operatorname{card}\left(F\right)} \cdot (1 - p)^{\operatorname{card}\left(\operatorname{edgeFinset}\left(G\right) \setminus F\right)} \cdot \operatorname{vecMulVec}\left(\operatorname{graphState}\left(F\right), \operatorname{star}\left(\operatorname{graphState}\left(F\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.rgState` (`✓ std3`).

*Citation.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

Each edge of G is present independently with probability p. The randomized graph state is the mixture, over the subsets F of the edge set of G, of the projections onto the graph states of F, with weights p^|F| (1 - p)^(|E(G)| - |F|).

**Definition 1.5 (Partial transposition).**

$$\forall n : \mathbb{N}, \forall A : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), \forall M : \mathbb{C}^{\operatorname{Qubits}\left(n\right) \times \operatorname{Qubits}\left(n\right)}, \forall x : \operatorname{Qubits}\left(n\right), \forall y : \operatorname{Qubits}\left(n\right), \operatorname{entry}\left(\operatorname{partialTranspose}\left(A, M\right), x, y\right) = \operatorname{entry}\left(M, \operatorname{piecewise}\left(A, y, x\right), \operatorname{piecewise}\left(A, x, y\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.partialTranspose` (`✓ std3`).

*Citation.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

The partial transposition on the qubits in A exchanges the A parts of the row and column labels: the entry of M^Gamma_A at (x, y) is the entry of M at the row label with A part from y and remaining part from x, and the column label with A part from x and remaining part from y. Here piecewise(A, u, v) is the label that agrees with u on A and with v elsewhere (Mathlib Finset.piecewise).

**Definition 1.6 (Negativity).**

$$\forall n : \mathbb{N}, \forall A : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), \forall \rho : \mathbb{C}^{\operatorname{Qubits}\left(n\right) \times \operatorname{Qubits}\left(n\right)}, \operatorname{negativity}\left(A, \rho\right) = \frac{\operatorname{traceNorm}\left(\operatorname{partialTranspose}\left(A, \rho\right)\right) - 1}{2}$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.negativity` (`✓ std3`).

*Citation.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

The negativity across the bipartition A versus its complement is (||rho^Gamma_A|| - 1)/2, with the trace norm ||X|| = Re Tr sqrt(X^* X) of the existing finite trace-distance module.

**Definition 1.7 (The question).**

$$(claim) \Leftrightarrow (\forall n : \mathbb{N}, \forall G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \forall A : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), \forall p : \mathbb{R}, \forall q : \mathbb{R}, (0 \le p) \Rightarrow ((p \le q) \Rightarrow ((q \le 1) \Rightarrow (\operatorname{negativity}\left(A, \operatorname{rgState}\left(G, p\right)\right) \le \operatorname{negativity}\left(A, \operatorname{rgState}\left(G, q\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.claim` (`✓ std3`).

*Citation.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

The paper reports monotone negativity for the complete graphs and the star graphs with at most 4 vertices and states that it is an open question whether the monotonic behaviour of the negativity in p is a common feature of all randomized graph states, the negativity being evaluated with respect to all bipartitions. The displayed statement reads the question as a universal statement over finite simple graphs on Fin(n), subsets A of the vertices and 0 <= p <= q <= 1.

**Definition 1.8 (The graph K_(3,3)).**

$$\forall a : \operatorname{Fin}\left(6\right), \forall b : \operatorname{Fin}\left(6\right), (\operatorname{Adj}\left(k33, a, b\right)) \Leftrightarrow (\neg (a\equiv b\pmod{2}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.k33` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

The complete bipartite graph on Fin(6) whose parts are the even and the odd vertices.

**Definition 1.9 (One part of K_(3,3)).**

$$partA = \ \{0, 2, 4\ \}$$

*Formalization.* `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.partA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

The part A is the set of even vertices.

**Theorem 1.10 (The answer is negative).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-2014-randomized-graph-negativity-monotonicity` (refuted) by `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-2014-randomized-graph-negativity-monotonicity","declaration_gid":"D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß (2014). *Randomized Graph States and their Entanglement Properties*. DOI: [10.1103/PhysRevA.89.052335](https://doi.org/10.1103/PhysRevA.89.052335). URL: <https://arxiv.org/abs/1403.3828v3>.

*Commentary.*

Expanding the product over the edges, the entry of the randomized state of a graph at (x, y) is 2^(-n) times the product over its edges of p c + (1 - p), where c = 1 if x and y have equal products x(a) x(b) on the edge and c = -1 otherwise. For K_(3,3) with the bipartition into its parts A = {0, 2, 4} and B = {1, 3, 5}, the entries of the partial transpose X_p are therefore (1 - 2p)^d / 64, with d the number of edges on which the two exchanged labels disagree. At p = 1 let u_00 and u_11 be the indicators of even and odd parity on A, times 1 and times the sign (-1)^|x_B| on B respectively, and let w and v be the difference and the sum of the indicator of even parity on A times (-1)^|x_B| and the indicator of odd parity on A. Entry by entry, X_1 + (1/128) w w^T equals (1/64)(u_00 u_00^T + u_11 u_11^T) + (1/128) v v^T. Both sides are sums of positive semidefinite rank-one terms, so by the triangle inequality ||X_1|| is at most the trace of the right side plus the trace of (1/128) w w^T, that is 3/2 + 1/2 = 2, and the negativity at p = 1 is at most 1/2. At p = 97/100, fourteen pairwise orthogonal integer vectors u_j of length 64 give the projection P = sum_j u_j u_j^T / |u_j|^2 and the unitary I - 2P; the trace norm is at least Re Tr((I - 2P) X_(97/100)) = 1 - 2 sum_j u_j^T X u_j / |u_j|^2, and this exact rational number is larger than 2. So the negativity at p = 97/100 exceeds 1/2, which contradicts monotonicity between p = 97/100 and q = 1.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.czPhase`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.graphState`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.k33`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.negativity`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.partA`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.partialTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.plusState`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.rgState`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
