# An order-19 counterexample to the broom spectral-ratio conjecture

## Abstract

At order nineteen the broom with seven star leaves has larger Laplacian ratio than the broom with eight.

**Definition 1.1 (Ordered Laplacian eigenvalues).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left((G).\operatorname{Adj}\right)] \forall i \in \operatorname{Fin}\left(n\right),\; \forall h \in ((G).\operatorname{lapMatrix}\left(\mathrm{Real}\right)).\operatorname{IsHermitian},\; \forall e \in (n = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Fin}\left(n\right)\right)),\; \operatorname{lapEig}\left(G, i\right) = h.\operatorname{eigenvalues}_{0}\left(\operatorname{Fin}.\operatorname{cast}\left(e, i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.lapEig` (`✓ std3`).

*Citation.* Zhen Lin; Jiajia Wang; Min Cai (2023). *The Laplacian spectral ratio of connected graphs*. DOI: [10.48550/arXiv.2302.10491](https://doi.org/10.48550/arXiv.2302.10491). URL: <https://arxiv.org/abs/2302.10491v1>.

*Commentary.*

Page 2 states: “The Laplacian matrix of G with n vertices, denoted by L(G), is given by L(G) = D(G) − A(G), where A(G) is the adjacency matrix and D(G) is the diagonal matrix of its vertex degrees. And the largest and second smallest Laplacian eigenvalues of G are called the Laplacian spectral radius and algebraic connectivity of G, denoted by µ1(G) and µn−1(G).” The index i is zero based, so lapEig G i represents µᵢ₊₁(G). In the formula h is any Hermitian proof and e is any proof identifying the two finite index sizes; proof irrelevance makes these choices immaterial. The eigenvalues are in nonincreasing order.

**Definition 1.2 (Laplacian spectral ratio).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left((G).\operatorname{Adj}\right)] \operatorname{spectralRatio}\left(G\right) = \operatorname{ite}\left(2 \le n, \frac{\operatorname{lapEig}\left(G, \langle0\rangle\right)}{\operatorname{lapEig}\left(G, \langle(n-2)\rangle\right)}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.spectralRatio` (`✓ std3`).

*Citation.* Zhen Lin; Jiajia Wang; Min Cai (2023). *The Laplacian spectral ratio of connected graphs*. DOI: [10.48550/arXiv.2302.10491](https://doi.org/10.48550/arXiv.2302.10491). URL: <https://arxiv.org/abs/2302.10491v1>.

*Commentary.*

Page 2 states: “The Laplacian spectral ratio of a connected graph G with n vertices is defined as R_L(G) = µ1(G)/µn−1(G).” The numerator has index zero and the denominator index n - 2. The value below order two is zero. Indices in the two-or-more branch carry the inequalities required by Fin; subtraction is natural-number subtraction.

**Definition 1.3 (Broom tree).**

$$\forall n \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \operatorname{broom}\left(n, t\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\lambda (i j : \operatorname{Fin}\left(n\right)) \mapsto (((\operatorname{val}\left(i\right) = 0) \land ((1 \le \operatorname{val}\left(j\right)) \land (\operatorname{val}\left(j\right) \le t+1))) \lor ((t+1 \le \operatorname{val}\left(i\right)) \land (\operatorname{val}\left(i\right)+1 = \operatorname{val}\left(j\right)))))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.broom` (`✓ std3`).

*Citation.* Zhen Lin; Jiajia Wang; Min Cai (2023). *The Laplacian spectral ratio of connected graphs*. DOI: [10.48550/arXiv.2302.10491](https://doi.org/10.48550/arXiv.2302.10491). URL: <https://arxiv.org/abs/2302.10491v1>.

*Commentary.*

Page 13 states: “A broom tree B_n^t, shown in Figure 2, is a tree obtained from the path P_{n−t−1} and the star K_{1,t} by joining one pendant vertex of P_{n−t−1} and the center of K_{1,t} by an edge.” Figure 2 labels the center v0, the star leaves v1 through vt, and the path v_{t+1} through v_{n−1}. SimpleGraph.fromRel symmetrizes the displayed relation and removes loops. The coercion val takes a Fin vertex to its natural-number value.

**Definition 1.4 (The proposed broom parameter).**

$$\forall n \in \mathrm{Nat},\; \operatorname{conjParam}\left(n\right) = \operatorname{ite}\left(\operatorname{Nat}.\operatorname{mod}\left(n, 2\right) = 1, \operatorname{Nat}.\operatorname{div}\left((n-3), 2\right), \operatorname{Nat}.\operatorname{div}\left((n-4), 2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.conjParam` (`✓ std3`).

*Citation.* Zhen Lin; Jiajia Wang; Min Cai (2023). *The Laplacian spectral ratio of connected graphs*. DOI: [10.48550/arXiv.2302.10491](https://doi.org/10.48550/arXiv.2302.10491). URL: <https://arxiv.org/abs/2302.10491v1>.

*Commentary.*

Page 16 states: “Let T be a tree with n ≥ 8 vertices. Then R_L(K_{1,n−1}) ≤ R_L(T) ≤ R_L(B_n^{(n−3)/2}) if n is odd; R_L(B_n^{(n−4)/2}) if n is even. The left (right) equality holds if and only if T = K_{1,n−1} (T = B_n^{(n−3)/2} or T = B_n^{(n−4)/2}).” The expression uses Nat.mod and Nat.div, with natural-number subtraction. At n = 19 the parameter is eight.

**Definition 1.5 (Conjecture 5.4).**

$$\operatorname{claim} = (\forall n \in \mathrm{Nat},\; (8 \le n) \Rightarrow (\forall T \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left((T).\operatorname{Adj}\right)] ((T).\operatorname{IsTree}) \Rightarrow ((\operatorname{spectralRatio}\left(\operatorname{SimpleGraph}.\operatorname{starGraph}\left(\langle0\rangle\right)\right) \le \operatorname{spectralRatio}\left(T\right)) \land ((\operatorname{spectralRatio}\left(T\right) \le \operatorname{spectralRatio}\left(\operatorname{broom}\left(n, \operatorname{conjParam}\left(n\right)\right)\right)) \land (((\operatorname{spectralRatio}\left(T\right) = \operatorname{spectralRatio}\left(\operatorname{SimpleGraph}.\operatorname{starGraph}\left(\langle0\rangle\right)\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(T, \operatorname{SimpleGraph}.\operatorname{starGraph}\left(\langle0\rangle\right)\right)\right))) \land ((\operatorname{spectralRatio}\left(T\right) = \operatorname{spectralRatio}\left(\operatorname{broom}\left(n, \operatorname{conjParam}\left(n\right)\right)\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(T, \operatorname{broom}\left(n, \operatorname{conjParam}\left(n\right)\right)\right)\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.claim` (`✓ std3`).

*Citation.* Zhen Lin; Jiajia Wang; Min Cai (2023). *The Laplacian spectral ratio of connected graphs*. DOI: [10.48550/arXiv.2302.10491](https://doi.org/10.48550/arXiv.2302.10491). URL: <https://arxiv.org/abs/2302.10491v1>.

*Commentary.*

Page 16 states: “Let T be a tree with n ≥ 8 vertices. Then R_L(K_{1,n−1}) ≤ R_L(T) ≤ R_L(B_n^{(n−3)/2}) if n is odd; R_L(B_n^{(n−4)/2}) if n is even. The left (right) equality holds if and only if T = K_{1,n−1} (T = B_n^{(n−3)/2} or T = B_n^{(n−4)/2}).” The formula includes both inequalities and both equality characterizations. Graph equality in the characterizations means isomorphism; Nonempty records existence of that isomorphism. The anonymous bracket specifies decidability of adjacency.

**Theorem 1.6 (Refutation at order nineteen).**

$$\neg (\forall n \in \mathrm{Nat},\; (8 \le n) \Rightarrow (\forall T \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left((T).\operatorname{Adj}\right)] ((T).\operatorname{IsTree}) \Rightarrow ((\operatorname{spectralRatio}\left(\operatorname{SimpleGraph}.\operatorname{starGraph}\left(\langle0\rangle\right)\right) \le \operatorname{spectralRatio}\left(T\right)) \land ((\operatorname{spectralRatio}\left(T\right) \le \operatorname{spectralRatio}\left(\operatorname{broom}\left(n, \operatorname{conjParam}\left(n\right)\right)\right)) \land (((\operatorname{spectralRatio}\left(T\right) = \operatorname{spectralRatio}\left(\operatorname{SimpleGraph}.\operatorname{starGraph}\left(\langle0\rangle\right)\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(T, \operatorname{SimpleGraph}.\operatorname{starGraph}\left(\langle0\rangle\right)\right)\right))) \land ((\operatorname{spectralRatio}\left(T\right) = \operatorname{spectralRatio}\left(\operatorname{broom}\left(n, \operatorname{conjParam}\left(n\right)\right)\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(T, \operatorname{broom}\left(n, \operatorname{conjParam}\left(n\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhen Lin; Jiajia Wang; Min Cai (2023). *The Laplacian spectral ratio of connected graphs*. DOI: [10.48550/arXiv.2302.10491](https://doi.org/10.48550/arXiv.2302.10491). URL: <https://arxiv.org/abs/2302.10491v1>.

*Commentary.*

The tree broom 19 7 has spectral ratio strictly larger than broom 19 8. The upper Rayleigh inequality for its real Laplacian follows from RHLinalg.hermForm_le_of_eigenvalues_le with threshold equal to the largest ordered eigenvalue. A rational vector orthogonal to constants gives µ18(B₁₉⁷) < 35467/1000000, and a second rational vector gives 9018480/1000000 < µ1(B₁₉⁷). Positive rational LDL transpose factorizations give 39388/1000000 < µ18(B₁₉⁸) and µ1(B₁₉⁸) < 10014270/1000000. The integer products satisfy 355176114090 < 355219890240, so 10014270/39388 < 9018480/35467. Specializing the proposed upper bound to this tree contradicts those inequalities. This refutes the conjunction and does not refute its separate star lower bound.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.broom`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.conjParam`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.lapEig`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.spectralRatio`
