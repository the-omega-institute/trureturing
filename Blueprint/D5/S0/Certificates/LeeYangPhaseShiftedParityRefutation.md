# The odd-sector spectral minimum need not be the second eigenvalue

## Abstract

A pi-flux four-cycle refutes the phase-shifted parity conjecture.

**Definition 1.1 (The two-qubit interaction).**

$$\forall n: \mathbb{N}, \forall p: \operatorname{Fin}\left(n\right), \forall q: \operatorname{Fin}\left(n\right), \forall z: \mathbb{C}, \operatorname{hpq}\left(p, q, z\right) = (\lambda y: (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(2\right), (\lambda x: (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(2\right), \operatorname{ite}\left((\forall k: \operatorname{Fin}\left(n\right), (k \ne p) \Rightarrow ((k \ne q) \Rightarrow (y\left(k\right) = x\left(k\right)))), \operatorname{ite}\left(((x\left(p\right) = 0) \land ((x\left(q\right) = 0) \land ((y\left(p\right) = 0) \land (y\left(q\right) = 0)))), 1, 0\right) + \operatorname{ite}\left(((x\left(p\right) = 0) \land ((x\left(q\right) = 0) \land ((y\left(p\right) = 1) \land (y\left(q\right) = 1)))), z, 0\right) + \operatorname{ite}\left(((x\left(p\right) = 1) \land ((x\left(q\right) = 1) \land ((y\left(p\right) = 0) \land (y\left(q\right) = 0)))), \operatorname{starRingEnd}\left(\mathbb{C}\right)\left(z\right), 0\right) + \operatorname{ite}\left(((x\left(p\right) = 1) \land ((x\left(q\right) = 1) \land ((y\left(p\right) = 1) \land (y\left(q\right) = 1)))), ((\operatorname{Complex.normSq}\left(z\right): \mathbb{R}): \mathbb{C}), 0\right), 0\right)))$$

*Formalization.* `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.hpq` (`✓ std3`).

*Citation.* Benjamin Wong; Sergey Bravyi; David Gosset; Yinchen Liu (2026). *Lee-Yang tensors and Hamiltonian complexity*. DOI: [10.48550/arXiv.2602.03605](https://doi.org/10.48550/arXiv.2602.03605). URL: <https://arxiv.org/abs/2602.03605v1>.

*Commentary.*

Section 5.6, p. 26: “Define a two-qubit operator h(z) = |00⟩⟨00| + z|11⟩⟨00| + z*|00⟩⟨11| + |z|²|11⟩⟨11|, where z ∈ ℂ.” Computational basis states are functions Fin n → Fin 2. The matrix entry with row y and column x vanishes unless all other qubits agree. The complex conjugate is starRingEnd ℂ applied to z, and Complex.normSq z is cast through ℝ to ℂ.

**Definition 1.2 (The phase-shifted Hamiltonian).**

$$\forall n: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), [\operatorname{DecidableRel}\left(\operatorname{G.Adj}\right)], \forall s: \mathbb{R}, \forall \theta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(n\right)) \to \mathbb{R}, \operatorname{H}\left(G, s, \theta\right) = -(\operatorname{Finset.sum}\left(\operatorname{Finset.univ}, (\lambda p: \operatorname{Fin}\left(n\right), \operatorname{Finset.sum}\left(\operatorname{Finset.univ}, (\lambda q: \operatorname{Fin}\left(n\right), \operatorname{ite}\left(((p < q) \land (\operatorname{G.Adj}\left(p, q\right))), \operatorname{hpq}\left(p, q, (s: \mathbb{C}) \cdot \operatorname{Complex.exp}\left(((\theta\left(p, q\right): \mathbb{R}): \mathbb{C}) \cdot \operatorname{Complex.I}\right)\right), 0\right))\right))\right))$$

*Formalization.* `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.H` (`✓ std3`).

*Citation.* Benjamin Wong; Sergey Bravyi; David Gosset; Yinchen Liu (2026). *Lee-Yang tensors and Hamiltonian complexity*. DOI: [10.48550/arXiv.2602.03605](https://doi.org/10.48550/arXiv.2602.03605). URL: <https://arxiv.org/abs/2602.03605v1>.

*Commentary.*

Section 5.6, p. 26: “A phase-shifted EPR-like Hamiltonian is defined as H_s(θ) = −Σ_{(p,q)∈E} h_{p,q}(se^{iθ_{p,q}}), (77) where s ∈ [0,1] and θ_{p,q} ∈ [0,2π) are arbitrary edge-dependent angles (phase shifts). Setting θ_{p,q} = 0 gives the original EPR-like Hamiltonian H_s.” Each undirected edge is counted once, using p < q. Real angles supply representatives in the exponential. Complex.I is the imaginary unit.

**Definition 1.3 (Eigenvalues in increasing order).**

$$\forall \iota: \operatorname{Type}, [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall M: \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right), \operatorname{eigAsc}\left(M\right) = (\operatorname{if} h: \operatorname{Matrix.IsHermitian}\left(M\right) \operatorname{then} \operatorname{Multiset.sort}\left(\operatorname{Multiset.map}\left(\operatorname{Matrix.IsHermitian.eigenvalues}\left(h\right), \operatorname{Finset.univ.val}\right), (\lambda a: \mathbb{R}, (\lambda b: \mathbb{R}, a \le b))\right) \operatorname{else} [])$$

*Formalization.* `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.eigAsc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Wong; Sergey Bravyi; David Gosset; Yinchen Liu (2026). *Lee-Yang tensors and Hamiltonian complexity*. DOI: [10.48550/arXiv.2602.03605](https://doi.org/10.48550/arXiv.2602.03605). URL: <https://arxiv.org/abs/2602.03605v1>.

*Commentary.*

For a Hermitian matrix, sort the multiset of Matrix.IsHermitian.eigenvalues in increasing order, retaining multiplicity. Return the empty list for a matrix that is not Hermitian. The proof h in the conditional selects the Hermitian eigenvalues.

**Definition 1.4 (Conjecture 2 with arbitrary edge phases).**

$$\operatorname{claim} = (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), [\operatorname{DecidableRel}\left(\operatorname{G.Adj}\right)], (\operatorname{SimpleGraph.Connected}\left(G\right)) \Rightarrow (\forall s: \mathbb{R}, (0 \le s) \Rightarrow ((s < 1) \Rightarrow (\forall \theta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(n\right)) \to \mathbb{R}, \operatorname{List.getD}\left(\operatorname{eigAsc}\left(\operatorname{H}\left(G, s, \theta\right)\right), 1, 0\right) = \operatorname{List.getD}\left(\operatorname{eigAsc}\left(\operatorname{Matrix.submatrix}\left(\operatorname{H}\left(G, s, \theta\right), (\operatorname{Subtype.val}: (\{x: (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(2\right) \mid \operatorname{Odd}\left(\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((\lambda k: \operatorname{Fin}\left(n\right), x\left(k\right) = 1), \operatorname{Finset.univ}\right)\right)\right)\}) \to (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(2\right)), \operatorname{Subtype.val}\right)\right), 0, 0\right))))))$$

*Formalization.* `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.claim` (`✓ std3`).

*Citation.* Benjamin Wong; Sergey Bravyi; David Gosset; Yinchen Liu (2026). *Lee-Yang tensors and Hamiltonian complexity*. DOI: [10.48550/arXiv.2602.03605](https://doi.org/10.48550/arXiv.2602.03605). URL: <https://arxiv.org/abs/2602.03605v1>.

*Commentary.*

Conjecture 2, Section 5.5, p. 24: “Suppose n ≥ 2, s ∈ [0, 1), and the interaction graph is connected. Then the second smallest eigenvalue of H_s coincides with the smallest eigenvalue of H_s restricted to the odd-weight subspace.” Section 5.6, p. 26: “We leave as an open question whether Conjectures 1,2,3 hold for phase-shifted EPR-like Hamiltonians.” This proposition extends Conjecture 2 to every phase function. List.getD uses zero-based indices: index one is the second eigenvalue with multiplicity and index zero is the odd-sector minimum. Matrix.submatrix restricts to the odd-weight computational basis.

**Theorem 1.5 (A four-cycle refutes the extension).**

$$\neg (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), [\operatorname{DecidableRel}\left(\operatorname{G.Adj}\right)], (\operatorname{SimpleGraph.Connected}\left(G\right)) \Rightarrow (\forall s: \mathbb{R}, (0 \le s) \Rightarrow ((s < 1) \Rightarrow (\forall \theta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(n\right)) \to \mathbb{R}, \operatorname{List.getD}\left(\operatorname{eigAsc}\left(\operatorname{H}\left(G, s, \theta\right)\right), 1, 0\right) = \operatorname{List.getD}\left(\operatorname{eigAsc}\left(\operatorname{Matrix.submatrix}\left(\operatorname{H}\left(G, s, \theta\right), (\operatorname{Subtype.val}: (\{x: (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(2\right) \mid \operatorname{Odd}\left(\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((\lambda k: \operatorname{Fin}\left(n\right), x\left(k\right) = 1), \operatorname{Finset.univ}\right)\right)\right)\}) \to (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(2\right)), \operatorname{Subtype.val}\right)\right), 0, 0\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Wong; Sergey Bravyi; David Gosset; Yinchen Liu (2026). *Lee-Yang tensors and Hamiltonian complexity*. DOI: [10.48550/arXiv.2602.03605](https://doi.org/10.48550/arXiv.2602.03605). URL: <https://arxiv.org/abs/2602.03605v1>.

*Commentary.*

Take s = 3/5 and the cycle with edges {0,1}, {0,3}, {1,2}, {2,3}. The phase on {0,3} is π and the other phases are zero. Two distinct full-space eigenvalues are below −5/2, while every odd-sector eigenvalue is above −5/2. The odd matrix satisfies 25M² + 68M + 18I = 0; two explicit full-space eigenvectors give eigenvalues −(67 + √1989)/25 and −(35 + √901)/25. Sorting with multiplicity therefore puts the second full-space eigenvalue strictly below the odd-sector minimum. This conclusion concerns the phase-shifted extension; it leaves Conjecture 2 for zero phases unresolved.

## References

- Truth anchor: `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.H`
- Truth anchor: `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.claim`
- Truth anchor: `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.eigAsc`
- Truth anchor: `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.hpq`
- Truth anchor: `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.result`
