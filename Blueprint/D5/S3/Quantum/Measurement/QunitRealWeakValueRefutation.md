# Real weak values outside the projector span for qutrits

## Abstract

For the standard basis of C^3 and the real orthonormal basis given by the columns of (1/3)[[1, 2, 2], [2, 1, -2], [2, -2, 1]], every pair of basis vectors is distinct and nonorthogonal, and the traceless Hermitian matrix M = E_01 + E_10 has all nine weak values real, while M is not in the real span of the traceless projectors of the two bases. This refutes the conjecture of J. M. Farinholt, A. Ghazarians and J. E. Troupe (arXiv:1512.02113) that all weak values of a traceless observable are real exactly when it lies in that span.

**Definition 1.1 (Weak values).**

$$\forall n : \mathbb{N}, \forall \phi : \operatorname{Fin}\left(n\right) \to \mathbb{C}, \forall \psi : \operatorname{Fin}\left(n\right) \to \mathbb{C}, \forall M : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{weakValue}\left(\phi, \psi, M\right) = \frac{\sum_{k} \sum_{l} \overline{\psi_{k}} \cdot M_{kl} \cdot \phi_{l}}{\sum_{k} \overline{\psi_{k}} \cdot \phi_{k}}$$

*Formalization.* `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.weakValue` (`✓ std3`).

*Citation.* Jacob M. Farinholt; Alexander Ghazarians; James E. Troupe (2015). *The Geometry of Qubit Weak Values*. DOI: [10.48550/arXiv.1512.02113](https://doi.org/10.48550/arXiv.1512.02113). URL: <https://arxiv.org/abs/1512.02113v2>.

*Commentary.*

For a pre-selected state phi and a post-selected state psi of C^n and an n x n matrix M, the weak value is <psi|M|phi> / <psi|phi>, with the bar denoting complex conjugation (star in Lean).

**Definition 1.2 (Orthonormal bases).**

$$\forall n : \mathbb{N}, \forall b : \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{C}), \operatorname{IsONB}\left(b\right) \Leftrightarrow (\forall i : \operatorname{Fin}\left(n\right), \forall j : \operatorname{Fin}\left(n\right), \sum_{k} \overline{b_{ik}} \cdot b_{jk} = \operatorname{ite}\left(i = j, 1, 0\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.IsONB` (`✓ std3`).

*Citation.* Jacob M. Farinholt; Alexander Ghazarians; James E. Troupe (2015). *The Geometry of Qubit Weak Values*. DOI: [10.48550/arXiv.1512.02113](https://doi.org/10.48550/arXiv.1512.02113). URL: <https://arxiv.org/abs/1512.02113v2>.

*Commentary.*

A family b_0, ..., b_(n-1) of vectors of C^n, written b_ik for the k-th coordinate of b_i, is an orthonormal basis when <b_i|b_j> is 1 for i = j and 0 otherwise.

**Definition 1.3 (Traceless projectors).**

$$\forall n : \mathbb{N}, \forall v : \operatorname{Fin}\left(n\right) \to \mathbb{C}, \forall a : \operatorname{Fin}\left(n\right), \forall c : \operatorname{Fin}\left(n\right), \operatorname{tracelessProj}\left(v\right)_{ac} = v_{a} \cdot \overline{v_{c}} - \operatorname{ite}\left(a = c, \frac{1}{n}, 0\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.tracelessProj` (`✓ std3`).

*Citation.* Jacob M. Farinholt; Alexander Ghazarians; James E. Troupe (2015). *The Geometry of Qubit Weak Values*. DOI: [10.48550/arXiv.1512.02113](https://doi.org/10.48550/arXiv.1512.02113). URL: <https://arxiv.org/abs/1512.02113v2>.

*Commentary.*

The traceless part of the projector onto v is |v><v| - I/n, whose (a, b) entry is v_a times the conjugate of v_b, minus 1/n on the diagonal.

**Definition 1.4 (The real span of the two bases).**

$$\forall n : \mathbb{N}, \forall \phi : \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{C}), \forall \psi : \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{C}), \operatorname{realSpan}\left(\phi, \psi\right) = \operatorname{span}_{\mathbb{R}}\{\operatorname{tracelessProj}\left(\phi_{i}\right), \operatorname{tracelessProj}\left(\psi_{j}\right) : i, j \in \operatorname{Fin}\left(n\right)\}$$

*Formalization.* `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.realSpan` (`✓ std3`).

*Citation.* Jacob M. Farinholt; Alexander Ghazarians; James E. Troupe (2015). *The Geometry of Qubit Weak Values*. DOI: [10.48550/arXiv.1512.02113](https://doi.org/10.48550/arXiv.1512.02113). URL: <https://arxiv.org/abs/1512.02113v2>.

*Commentary.*

R(phi, psi) is the real linear span, inside the complex n x n matrices viewed as a real vector space, of the 2n traceless projectors of the two bases. All of them are traceless Hermitian, so this is the paper's span inside the space S of traceless Hermitian matrices.

**Definition 1.5 (The conjecture).**

$$claim \Leftrightarrow (\forall n : \mathbb{N}, \forall \phi : \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{C}), \forall \psi : \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{C}), ((2 \le n) \land \left((\operatorname{IsONB}\left(\phi\right)) \land \left((\operatorname{IsONB}\left(\psi\right)) \land \left(((\forall i : \operatorname{Fin}\left(n\right), \forall j : \operatorname{Fin}\left(n\right), \sum_{k} \overline{\psi_{jk}} \cdot \phi_{ik} \ne 0)) \land \forall i : \operatorname{Fin}\left(n\right), \forall j : \operatorname{Fin}\left(n\right), \phi_{i} \ne \psi_{j}\right)\right)\right)) \Rightarrow \forall M : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), ((M^{*} = M) \land \operatorname{tr}\left(M\right) = 0) \Rightarrow \left((\forall i : \operatorname{Fin}\left(n\right), \forall j : \operatorname{Fin}\left(n\right), \operatorname{Im}\left(\operatorname{weakValue}\left(\phi_{i}, \psi_{j}, M\right)\right) = 0) \Leftrightarrow (M \in \operatorname{realSpan}\left(\phi, \psi\right))\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.claim` (`✓ std3`).

*Citation.* Jacob M. Farinholt; Alexander Ghazarians; James E. Troupe (2015). *The Geometry of Qubit Weak Values*. DOI: [10.48550/arXiv.1512.02113](https://doi.org/10.48550/arXiv.1512.02113). URL: <https://arxiv.org/abs/1512.02113v2>.

*Commentary.*

For every n >= 2 and all orthonormal bases phi, psi of C^n such that every pair (phi_i, psi_j) is distinct and nonorthogonal, a traceless Hermitian matrix M has all weak values W(phi_i, psi_j, M) real exactly when M lies in R(phi, psi). The paper requires phi_0 and psi_0 to be distinct and nonorthogonal and defines weak values for distinct, nonorthogonal pairs; assuming this for every pair, so that every weak value in the statement is defined, only weakens the claim.

**Theorem 1.6 (A qutrit counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/farinholt-2015-qunit-real-weak-values` (refuted) by `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"farinholt-2015-qunit-real-weak-values","declaration_gid":"D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jacob M. Farinholt; Alexander Ghazarians; James E. Troupe (2015). *The Geometry of Qubit Weak Values*. DOI: [10.48550/arXiv.1512.02113](https://doi.org/10.48550/arXiv.1512.02113). URL: <https://arxiv.org/abs/1512.02113v2>.

*Commentary.*

Take n = 3, phi_i the standard basis vectors and psi_j the j-th column of O = (1/3)[[1, 2, 2], [2, 1, -2], [2, -2, 1]], an orthogonal matrix, so both families are orthonormal bases; the overlap <psi_j|phi_i> is the entry O_ij, never 0, and no phi_i equals a psi_j. For M = E_01 + E_10 the nine weak values are 2, 1/2, -1, 1/2, 2, -1, 0, 0, 0 (in the order (i, j) = (0, 0), (0, 1), ...), all real. If M were a real combination of the six traceless projectors, the off-diagonal entries (0, 1), (0, 2), (1, 2) would come only from the psi projectors and give (2 b_0 + 2 b_1 - 4 b_2)/9 = 1, (2 b_0 - 4 b_1 + 2 b_2)/9 = 0 and (4 b_0 - 2 b_1 - 2 b_2)/9 = 0; the last two force b_0 = b_1 = b_2, and then the first reads 0 = 1.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.IsONB`
- Truth anchor: `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.realSpan`
- Truth anchor: `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.tracelessProj`
- Truth anchor: `D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.weakValue`
