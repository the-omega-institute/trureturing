# Negative H-eigenvalues of reflected Steiner forms

## Abstract

The star with 47 leaves has a negative real H-eigenvalue for the last-reflected Steiner form at every even order at least four.

**Definition 1.1 (Steiner distance of an ordered tuple).**

$$\operatorname{steinerEntry}\left(h, t\right) = \min \{ \left|\operatorname{E}\left(H\right)\right| \mid H \subseteq G, H.Connected, \forall (a : \operatorname{Fin}\left(k\right)), \operatorname{t}\left(a\right) \in \operatorname{V}\left(H\right) \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.steinerEntry` (`✓ std3`).

*Citation.* Joshua Cooper; Zhibin Du (2025). *Determinants of Steiner Distance Hypermatrices*. DOI: [10.48550/arXiv.2505.10501](https://doi.org/10.48550/arXiv.2505.10501). URL: <https://arxiv.org/abs/2505.10501v1>.

*Commentary.*

On printed page 1, Cooper and Du define Steiner distance by minimizing the number of edges in a connected subgraph containing all the specified vertices. In a tree the minimum is the size of the unique minimal subtree spanning those vertices. An ordered tuple may repeat vertices, so repetitions constrain the same vertex and add no edges. The subgraph H is a connected subgraph of G and |E(H)| counts its undirected edges once. The proof h of connectedness of G ensures the minimum exists.

**Definition 1.2 (Steiner multilinear form).**

$$\operatorname{steinerForm}\left(h, z\right) = \sum_{t : \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right)} \operatorname{steinerEntry}\left(h, t\right) \cdot \prod_{a : \operatorname{Fin}\left(k\right)} z_{a}\left(\operatorname{t}\left(a\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.steinerForm` (`✓ std3`).

*Citation.* Joshua Cooper; Zhibin Du (2025). *Determinants of Steiner Distance Hypermatrices*. DOI: [10.48550/arXiv.2505.10501](https://doi.org/10.48550/arXiv.2505.10501). URL: <https://arxiv.org/abs/2505.10501v1>.

*Commentary.*

The sum on printed page 1 ranges over all ordered k-tuples of vertices, including repeated indices. There is one coordinate factor from each input slot, and the natural edge count is cast to a real coefficient.

**Definition 1.3 (Reflection through the all-ones line).**

$$\operatorname{reflect}\left(x, i\right) = \frac{2 \sum_{j : \operatorname{Fin}\left(n\right)} \operatorname{x}\left(j\right)}{n} - \operatorname{x}\left(i\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.reflect` (`✓ std3`).

*Citation.* Joshua Cooper; Zhibin Du (2025). *Determinants of Steiner Distance Hypermatrices*. DOI: [10.48550/arXiv.2505.10501](https://doi.org/10.48550/arXiv.2505.10501). URL: <https://arxiv.org/abs/2505.10501v1>.

*Commentary.*

Lemma 4.2 on printed page 8 gives the reflection through the span of the all-ones vector. The term twice the mean is the same at every vertex. The map fixes constant vectors and reverses vectors with coordinate sum zero.

**Definition 1.4 (First-slot contraction of the last-reflected form).**

$$\operatorname{reflectedRow}\left(h, m, x, i\right) = \operatorname{steinerForm}\left(h, z\right),\quad z = (e_{i}, (x)_{a : \operatorname{Fin}\left(m\right)}, \operatorname{reflect}\left(x\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.reflectedRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joshua Cooper; Zhibin Du (2025). *Determinants of Steiner Distance Hypermatrices*. DOI: [10.48550/arXiv.2505.10501](https://doi.org/10.48550/arXiv.2505.10501). URL: <https://arxiv.org/abs/2505.10501v1>.

*Commentary.*

Printed page 9 defines C₁ at order four by applying the reflection in the last slot of the Steiner form. The same placement defines the higher-order form here. The slot vector z starts with the vertex basis vector eᵢ, followed by m copies of the real vector x and then the reflected x. The order is m + 2.

**Definition 1.5 (Real H-eigenpair equations).**

$$\operatorname{IsHEigenpair}\left(h, m, x, lam\right) \Leftrightarrow (x \ne 0 \land (\forall (i : \operatorname{Fin}\left(n\right)), \operatorname{reflectedRow}\left(h, m, x, i\right) = lam \cdot \operatorname{x}\left(i\right)^{m + 1}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.IsHEigenpair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joshua Cooper; Zhibin Du (2025). *Determinants of Steiner Distance Hypermatrices*. DOI: [10.48550/arXiv.2505.10501](https://doi.org/10.48550/arXiv.2505.10501). URL: <https://arxiv.org/abs/2505.10501v1>.

*Commentary.*

The vector x is real and nonzero, and lam is real. Each first-slot row equals the eigenvalue times the corresponding coordinate raised to the power m + 1, which is one less than the tensor order.

**Definition 1.6 (Cooper and Du’s positivity question).**

$$claim \Leftrightarrow (\forall (n : \mathbb{N}), \forall (k : \mathbb{N}), 3 \leq n \Rightarrow 4 \leq k \Rightarrow \operatorname{Even}\left(k\right) \Rightarrow (\forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (hG : G.IsTree), \forall (x : \operatorname{Fin}\left(n\right) \to \mathbb{R}), \forall (lam : \mathbb{R}), \operatorname{IsHEigenpair}\left(hG.connected, (k - 2), x, lam\right) \Rightarrow 0 < lam))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.claim` (`✓ std3`).

*Citation.* Joshua Cooper; Zhibin Du (2025). *Determinants of Steiner Distance Hypermatrices*. DOI: [10.48550/arXiv.2505.10501](https://doi.org/10.48550/arXiv.2505.10501). URL: <https://arxiv.org/abs/2505.10501v1>.

*Commentary.*

After Proposition 4.5 on printed page 10, Cooper and Du report computational evidence for diagonal positive definiteness of the quartic C₁. They ask whether the H-eigenvalues of C₁ are all positive and whether this extends to all even orders. The claim adopts the first-slot convention and requires strict positivity for every real H-eigenpair on every finite simple tree with at least three vertices at each even order k at least four. The tree proof hG supplies the connectedness argument. Relabelling the paper’s vertices by Fin n preserves both the Steiner entries and the eigenpair equations.

**Theorem 1.7 (A fixed star gives a negative H-eigenvalue at every even order at least four).**

$$\forall (k : \mathbb{N}), 4 \leq k \Rightarrow \operatorname{Even}\left(k\right) \Rightarrow \exists (x : \operatorname{Fin}\left(48\right) \to \mathbb{R}) (lam : \mathbb{R}), lam < 0 \land \operatorname{IsHEigenpair}\left(hStar, (k - 2), x, lam\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.star_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Cooper; Zhibin Du (2025). *Determinants of Steiner Distance Hypermatrices*. DOI: [10.48550/arXiv.2505.10501](https://doi.org/10.48550/arXiv.2505.10501). URL: <https://arxiv.org/abs/2505.10501v1>.

*Commentary.*

Cooper and Du’s last-slot reflection and positivity question motivate this construction. For each natural even order k ≥ 4, the theorem gives a nonzero real vector x on the same star K₁,₄₇ with centre 0 on Fin 48 and a real eigenvalue lam < 0. The eigenpair may depend on k. In the formula, hStar is (isTree_starGraph (0 : Fin 48)).connected. The first-slot contraction has k − 2 copies of x between the basis vector and the reflected x.

On the star with 47 leaves, the minimal subtree uses exactly the leaf edges whose cuts the tuple crosses. In the multilinear sum, each cut contributes the product of the whole-vertex slot sums minus the two products of slot sums restricted to its sides. Give all leaves coordinate −1 and the centre coordinate s + 47. The contraction then has a single centre value and a common leaf value.

Eliminating the eigenvalue from the two row equations gives a continuous polynomial in s. It is positive at 24/23 and negative at 2 for every even order k at least four. The intermediate value theorem gives a zero. There the contribution from a leaf’s own cut is positive, so the balance forces the common contribution from the other cuts to be negative. The centre equation gives a negative eigenvalue, and the balance equation gives the leaf equation.

The corresponding Reg registration is Reg.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner.registration. Its parameter coordinates are k followed by x, its real state is lam, and its Boolean readout decides the displayed IsHEigenpair predicate. The registration law retains the two premises on k, the two existential binders, and lam < 0.

**Theorem 1.8 (The order-four instance refutes claim).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Cooper; Zhibin Du (2025). *Determinants of Steiner Distance Hypermatrices*. DOI: [10.48550/arXiv.2505.10501](https://doi.org/10.48550/arXiv.2505.10501). URL: <https://arxiv.org/abs/2505.10501v1>.

*Commentary.*

Apply star_negative at k = 4. The star on Fin 48 satisfies the size and tree hypotheses of claim, which would make the supplied eigenvalue strictly positive. The witness has a strictly negative eigenvalue, giving ¬ claim.

At every even order k ≥ 4, multilinearity in the first slot expresses the diagonal value at the star witness as the sum of each coordinate times its first-slot row. The row equations give lam times the sum of the kth powers of the coordinates, which is negative because x is nonzero and lam < 0. The symmetric polarization has the same diagonal polynomial, and scaling the witness so its kth powers sum to one preserves the sign. The polynomial therefore attains a negative minimum on that compact constraint set. The constraint gradient is nonzero there. By symmetry the polynomial gradient is k times the row contraction, so the Lagrange multiplier equation gives an H-eigenpair. Contracting with the minimizing vector identifies its eigenvalue with the negative minimum. Proposition 4.5 gives diagonal positivity for the quartic sum C₁ + C₃.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.IsHEigenpair`
- Truth anchor: `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.reflect`
- Truth anchor: `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.reflectedRow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.star_negative`
- Truth anchor: `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.steinerEntry`
- Truth anchor: `D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.steinerForm`
