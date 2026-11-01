# The ternary replica collapse for four-party stabilizer states

## Abstract

For a normalized pure qubit stabilizer state, ternary replica contractions are positive real numbers. Their four-party genuine multi-entropy is determined by the tripartite information.

Akella and Gadde, Renyi multi-entropy of graph states and the n to 1 limit, arXiv:2610.27080v1, Section II Eqs. (7)-(9) and Appendix A, give an odd-replica rank formula that also implies this n=3 four-party relation. For the three nonzero F4 labels, diagonal rescaling makes the rank depend only on their equality partition. The entropy normalization here retains n^{-(q-2)}, which their Eq. (2) explicitly omits. The partition counts then give the coefficient 1/9. This is a structural formal proof and reusable library growth for an existing conclusion, with no new unique-solve or global-priority claim. The resolution slug below preserves the existing project resolution; the open counting question in arXiv:2607.06050v2 Section 6 is a source-text statement, not a current no-other-proof certificate.

**Definition 1.1 (Shifting a replica coordinate).**

$$\forall (n : \mathbb{N}), \forall (q : \mathbb{N}), \forall (c : \operatorname{Fin}\left(q\right)), \forall (r : (\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(n\right))), \operatorname{shift}\left(n, q, c, r\right) = (i : \operatorname{Fin}\left((q - 1)\right)) \mapsto \operatorname{ite}\left((i : \mathbb{N}) = (c : \mathbb{N}), \operatorname{r}\left(i\right) + 1, \operatorname{r}\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.shift` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Replica labels are functions Fin(q - 1) to Z/nZ. The shift adds one at the coordinate whose natural index equals the colour c. Colour q - 1 has no such coordinate and acts as the identity. Natural differences such as q - 1 and q - 2 in these formulas use truncated subtraction.

**Definition 1.2 (Contracting the replicas).**

$$\forall (n : \mathbb{N}), \forall (q : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (N : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{Z}\left(n, q, col, \psi\right) = \sum_{(x : ((\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(n\right)) \to (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))))} \prod_{(r : (\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(n\right)))} \operatorname{star}\left(\psi(\operatorname{x}\left(r\right))\right) \cdot \psi(((u : \operatorname{Fin}\left(N\right)) \mapsto \operatorname{x}\left(\operatorname{shift}\left(n, q, \operatorname{col}\left(u\right), r\right), u\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

A configuration x assigns a binary N-qubit string to each replica label r. The conjugated amplitude is evaluated at x(r); the other amplitude takes qubit u from the replica shifted by its colour col(u). Summing the product gives the computational-basis contraction of Appendix A.

**Definition 1.3 (Ternary replica translation vector).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (u : \operatorname{Fin}\left(N\right)), \operatorname{delta}\left(col, u\right) = (i : \operatorname{Fin}\left((q - 1)\right)) \mapsto \operatorname{ite}\left((i : \mathbb{N}) = (\operatorname{col}\left(u\right) : \mathbb{N}), 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

For a colouring col : Fin N to Fin q, delta(col, u) is the standard basis vector in (Z/3Z)^{q-1} at coordinate col(u) when col(u) < q - 1, and zero when col(u) = q - 1, so shift(3, q, col(u), r) = r + delta(col, u).

**Theorem 1.4 (Scalar homogeneity of the replica contraction).**

$$\forall (N : \mathbb{N}), \forall (n : \mathbb{N}), \forall (q : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \forall (c : \mathbb{C}), \operatorname{Z}\left(n, q, col, c \cdot \psi\right) = (\operatorname{star}\left(c\right) \cdot c)^{n^{(q - 1)}} \cdot \operatorname{Z}\left(n, q, col, \psi\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Scaling a pure state amplitude by c in C multiplies each of the n^{q-1} replica factors by star(c) * c, scaling Z(n, q, col, c * psi) by (star(c) * c)^{n^{q-1}}.

**Theorem 1.5 (Replica contraction at index one).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{Z}\left(1, q, col, \psi\right) = (\sum_{(x : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} : \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

At replica index n = 1 the replica group (Z/1Z)^{q-1} has a unique element on which every shift acts trivially, reducing Z(1, q, col, psi) to the cast of the squared Hilbert norm sum_x ||psi(x)||^2.

**Theorem 1.6 (Invariance under product unitaries and scalars).**

$$\forall (N : \mathbb{N}), \forall (n : \mathbb{N}), \forall (q : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \forall (U : (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))), (\forall (u : \operatorname{Fin}\left(N\right)), U(u) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \Rightarrow (\forall (c : \mathbb{C}), \operatorname{Z}\left(n, q, col, c \cdot \operatorname{mulVec}\left(\operatorname{tensorOp}\left(U\right), \psi\right)\right) = \operatorname{Z}\left(n, q, col, c \cdot \psi\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z_local_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Applying a tensor product tensorOp(U) of single-qubit unitaries U(u) commutes with replica coordinate permutations on each qubit wire and cancels against its adjoint in the replica inner product, leaving Z(n, q, col, c * (tensorOp(U) * psi)) equal to Z(n, q, col, c * psi).

**Theorem 1.7 (Squared modulus of a normalized local-unitary graph amplitude).**

$$\forall (N : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), \forall (U : (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))), (\forall (u : \operatorname{Fin}\left(N\right)), U(u) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \Rightarrow (\forall (c : \mathbb{C}), (\sum_{(x : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)))} \left\lVert (c \cdot \operatorname{mulVec}\left(\operatorname{tensorOp}\left(U\right), \operatorname{graphAmp}\left(A\right)\right))(x) \right\rVert^{2} = 1) \Rightarrow (\operatorname{star}\left(c\right) \cdot c = (2^{N})^{-1}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.graph_scalar_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Because the unnormalized graph amplitude graphAmp(A) has 2^N unit-modulus entries and product unitaries preserve the squared norm via Z_local_scalar and Z_one at (n, q) = (1, 1), unit Hilbert norm of c * (tensorOp(U) * graphAmp(A)) forces star(c) * c = (2^N)^{-1}.

**Theorem 1.8 (Ternary graph contraction as a reciprocal power of two).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), (\forall (u : \operatorname{Fin}\left(N\right)), \forall (v : \operatorname{Fin}\left(N\right)), A(u, v) = A(v, u)) \Rightarrow (\forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (P : \operatorname{Finset}\left((\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(3\right))\right)), (\neg(0 \in P) \land (\forall (t : (\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(3\right))), (t \neq 0) \Rightarrow (t \in P \Leftrightarrow \neg(-t \in P)))) \Rightarrow (((2^{N})^{-1})^{3^{(q - 1)}} \cdot \operatorname{Z}\left(3, q, col, \operatorname{graphAmp}\left(A\right)\right) = (2^{\sum_{t \in P} \operatorname{rank}\left(\operatorname{C}\left(A, \operatorname{delta}\left(col\right), t\right)\right)})^{-1}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.graph_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

For any symmetric binary matrix A, colouring col : Fin N to Fin q, and opposite-pair representative set P of nonzero vectors in (Z/3Z)^{q-1}, the ternary quadratic normal form splits the unnormalized graph contraction into one zero-mode factor 2^N and |P| bilinear blocks of size 2^(2N - rank C_t); multiplying by ((2^N)^{-1})^{3^{q-1}} yields 2^{-sum_{t in P} rank C(A, delta(col), t)}.

**Theorem 1.9 (Existence of opposite-mode representatives).**

$$\forall (d : \mathbb{N}), \exists (P : \operatorname{Finset}\left((\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right))\right)), \neg(0 \in P) \land (\forall (t : (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right))), (t \neq 0) \Rightarrow (t \in P \Leftrightarrow \neg(-t \in P)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.representatives_exist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Ordering (Z/3Z)^d by an equivalence to Fin(3^d) and selecting those vectors strictly preceding their negation produces a finite set P avoiding 0 and containing, for every nonzero t, either t or -t but not both.

**Definition 1.10 (The normalized multi-entropy).**

$$\forall (n : \mathbb{N}), \forall (q : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (N : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{S}\left(n, q, col, \psi\right) = \frac{1}{(1 - (n : \mathbb{R}))} \cdot \frac{1}{(n : \mathbb{R})^{(q - 2)}} \cdot \operatorname{log}\left(\operatorname{Re}\left(\frac{\operatorname{Z}\left(n, q, col, \psi\right)}{\operatorname{Z}\left(1, q, col, \psi\right)^{n^{(q - 1)}}}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.S` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The normalization divides Z(n,q,col,psi) by the indicated power of Z(1,q,col,psi). The logarithm is applied to the real part of the quotient, with the prefactors specified in Appendix A. The casts of n to R appear explicitly.

**Theorem 1.11 (Replica-three multi-entropy from a reciprocal-power contraction).**

$$\forall (N : \mathbb{N}), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), (\sum_{(x : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1) \Rightarrow (\forall (q : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), \forall (P : \operatorname{Finset}\left((\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(3\right))\right)), (\operatorname{Z}\left(3, q, col, \psi\right) = (2^{\sum_{t \in P} \operatorname{rank}\left(\operatorname{C}\left(A, \operatorname{delta}\left(col\right), t\right)\right)})^{-1}) \Rightarrow (\operatorname{S}\left(3, q, col, \psi\right) = \frac{\operatorname{log}\left(2\right)}{2 \cdot 3^{(q - 2)}} \cdot \sum_{t \in P} \operatorname{rank}\left(\operatorname{C}\left(A, \operatorname{delta}\left(col\right), t\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.entropy_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

When psi has unit squared norm so Z(1, q, col, psi) = 1 and Z(3, q, col, psi) equals the reciprocal of 2^{sum_{t in P} rank C(A, delta(col), t)}, substituting into S(3, q, col, psi) evaluates the real logarithm to -(sum_{t in P} rank C_t) log 2 and cancels 1/(1 - 3) = -1/2 to give (log 2 / (2 * 3^{q-2})) sum_{t in P} rank C(A, delta(col), t).

**Definition 1.12 (Four cuts minus three cuts).**

$$\forall (n : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (N : \mathbb{N}), \forall (party : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{I3}\left(n, party, \psi\right) = \operatorname{S}\left(n, 2, (([0, 0, 0, 1] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 0, 1, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 1, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([1, 0, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) - (\operatorname{S}\left(n, 2, (([0, 0, 1, 1] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 1, 0, 1] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 1, 1, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.I3` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Label A, B, C, D by 0, 1, 2, 3. Each displayed tuple is a function from Fin 4 to the stated colour set, composed with party. In order, the four positive terms are ABC:D, ABD:C, ACD:B and BCD:A; the three subtracted terms are AB:CD, AC:BD and AD:BC. This is the Renyi tripartite information I_{3,n} in Eq. (1) of the paper.

**Definition 1.13 (The genuine four-party combination).**

$$\forall (n : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (a : \mathbb{R}), \forall (N : \mathbb{N}), \forall (party : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{GM4}\left(n, a, party, \psi\right) = \operatorname{S}\left(n, 4, party, \psi\right) - \frac{1}{3} \cdot (\operatorname{S}\left(n, 3, (([0, 0, 1, 2] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([0, 1, 0, 2] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([0, 1, 2, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([1, 0, 0, 2] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([1, 0, 2, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([1, 2, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right)) + \frac{1}{3} \cdot (\operatorname{S}\left(n, 2, (([0, 0, 0, 1] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 0, 1, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 1, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([1, 0, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right)) - a \cdot \operatorname{I3}\left(n, party, \psi\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.GM4` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The six three-colour tuples merge AB, AC, AD, BC, BD and CD, respectively. Their entropies have coefficient -1/3, while the four singleton cuts have coefficient 1/3. The remaining term is -a times the tripartite information, for an arbitrary real parameter a, as in Section 2 of the paper.

**Definition 1.14 (Positivity and the n = 3 collapse).**

$$claim \Leftrightarrow (\forall (N : \mathbb{N}), \forall (party : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{StabilizedBy}\left(pauliSet, \psi\right) \Rightarrow ((\sum_{(x : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1) \Rightarrow ((\forall (q : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), 0 < \operatorname{Re}\left(\operatorname{Z}\left(3, q, col, \psi\right)\right) \land (\operatorname{Im}\left(\operatorname{Z}\left(3, q, col, \psi\right)\right) = 0)) \land (\forall (a : \mathbb{R}), \operatorname{GM4}\left(3, a, party, \psi\right) = -(a - \frac{1}{9}) \cdot \operatorname{I3}\left(3, party, \psi\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.claim` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The proposition quantifies over every qubit count, every assignment to four labelled parties and every amplitude. Its two assumptions are Pauli stabilization and unit squared norm. The first conclusion includes every colour count and colouring and asserts both strict positivity of the real part and a zero imaginary part. The second conclusion is Eq. (3) for every real a, with I3 interpreted as I_{3,3}. Empty parties are allowed.

**Theorem 1.15 (The stabilizer collapse).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result` (`✓ std3`). ∎

*Resolves.* `Problems/akella-2026-stabilizer-multi-entropy-n3-collapse` (proved) by `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"akella-2026-stabilizer-multi-entropy-n3-collapse","declaration_gid":"D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

A stabilizer state is a scalar multiple of a local-unitary image of the unnormalized graphAmp Gamma, which has 2^N entries of modulus one, hence squared Hilbert norm 2^N. For arbitrary N including 0, odd n >= 3, q >= 2, colouring col : Fin N to Fin q, binary matrix Gamma and local unitaries U, if psi = c * (tensorOp U * graphAmp Gamma) has unit squared Hilbert norm, tensor unitarity preserves Hilbert norm, so normalization fixes star c * c = (2^N)^{-1}. Local-unitary invariance and homogeneity reduce Z(n,q,col,psi) to (((2^N)^{-1})^{n^{q-1}}) Z(n,q,col,graphAmp Gamma). At n = 3, the graph replica translation form decomposes into bilinear blocks indexed by opposite nonzero Fourier modes. Each block contributes the inverse power of two determined by its rank, giving positive real contractions whose ranks depend only on the equality partition of the party colours. TernaryPartitionCounting supplies the generic merger transport and weighted counting identity consumed here, while TernaryPartitionOrbit classifies nonzero anchored modes modulo sign by their equality partitions. With four labels, the finite partition coefficients 1, -1, 2 and 1 for the full term, six pair mergers, four singleton cuts and three balanced cuts cancel at every induced two- or three-block partition, yielding GM4(3, a, party, psi) = -(a - 1/9) I3(3, party, psi) without settling other replica indices.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.GM4`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.I3`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.S`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z_local_scalar`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z_one`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z_smul`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.delta`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.entropy_formula`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.graph_count`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.graph_scalar_norm`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.representatives_exist`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.shift`
- Dependency: [D5/S3/Combinatorics/Partitions/TernaryPartitionCounting](../../Combinatorics/Partitions/TernaryPartitionCounting.md)
- Dependency: [D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm](../../QuadraticForms/TernaryTranslationQuadraticNormalForm.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../Information/BinaryStabilizerGraphNormalForm.md)
