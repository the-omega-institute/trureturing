# The cyclic stable-marriage arc-lemma upper bound

## Abstract

For n >= 1, every complete matching in the cyclic Hollow-Shell profile has at most floor((n - 1)^2 / 4) blocking pairs.

**Definition 1.1 (The man's cyclic rank).**

$$\forall n \in \mathbb{N},\; \forall g \in \operatorname{Fin}\left(n\right),\; \forall h \in \operatorname{Fin}\left(n\right),\; \operatorname{rM}\left(g, h\right) = \operatorname{emod}\left(\operatorname{ofNat}\left(\operatorname{val}\left(h\right)\right) - \operatorname{ofNat}\left(\operatorname{val}\left(g\right)\right), \operatorname{ofNat}\left(n\right)\right) + 1$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.rM` (`✓ std3`).

*Citation.* Yoshiteru Ishida (2026). *A Quadratic Lower Bound for the Shield Number of the Stable Marriage Problem: Rearrangement, Extremal Construction, and Biclique Realizability*. DOI: [10.48550/arXiv.2609.17418](https://doi.org/10.48550/arXiv.2609.17418). URL: <https://arxiv.org/abs/2609.17418v1>.

*Commentary.*

Equation (1), Section 1.1, p. 2: "r_M(g, h) = (h − g) mod n + 1, r_W(h, g) = n − (h − g) mod n". Men and women both have carrier Fin(n), with labels 0 through n - 1. The function val reads a Fin label and ofNat embeds a natural number into the integers. The operator emod is integer Euclidean remainder, exactly the source's mod n; smaller ranks are preferred.

**Definition 1.2 (The woman's cyclic rank).**

$$\forall n \in \mathbb{N},\; \forall h \in \operatorname{Fin}\left(n\right),\; \forall g \in \operatorname{Fin}\left(n\right),\; \operatorname{rW}\left(h, g\right) = \operatorname{ofNat}\left(n\right) - \operatorname{emod}\left(\operatorname{ofNat}\left(\operatorname{val}\left(h\right)\right) - \operatorname{ofNat}\left(\operatorname{val}\left(g\right)\right), \operatorname{ofNat}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.rW` (`✓ std3`).

*Citation.* Yoshiteru Ishida (2026). *A Quadratic Lower Bound for the Shield Number of the Stable Marriage Problem: Rearrangement, Extremal Construction, and Biclique Realizability*. DOI: [10.48550/arXiv.2609.17418](https://doi.org/10.48550/arXiv.2609.17418). URL: <https://arxiv.org/abs/2609.17418v1>.

*Commentary.*

Equation (1), Section 1.1, p. 2: "r_M(g, h) = (h − g) mod n + 1, r_W(h, g) = n − (h − g) mod n". The argument order of rW is woman h, then man g. Both label casts and the integer remainder are displayed explicitly.

**Definition 1.3 (A blocking pair).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall g \in \operatorname{Fin}\left(n\right),\; \forall h \in \operatorname{Fin}\left(n\right),\; \operatorname{blocks}\left(p, g, h\right) \Leftrightarrow ((\operatorname{rM}\left(g, h\right) < \operatorname{rM}\left(g, p\left(g\right)\right)) \land (\operatorname{rW}\left(h, g\right) < \operatorname{rW}\left(h, \operatorname{symm}\left(p\right)\left(h\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.blocks` (`✓ std3`).

*Citation.* Yoshiteru Ishida (2026). *A Quadratic Lower Bound for the Shield Number of the Stable Marriage Problem: Rearrangement, Extremal Construction, and Biclique Realizability*. DOI: [10.48550/arXiv.2609.17418](https://doi.org/10.48550/arXiv.2609.17418). URL: <https://arxiv.org/abs/2609.17418v1>.

*Commentary.*

Section 1.1, p. 1: "A complete matching µ (a bijection from men to women) has a blocking pair (m_i, w_j) if m_i prefers w_j to µ(m_i) and w_j prefers m_i to µ^{−1}(w_j)". The letter p denotes the Lean matching μ, represented by Equiv.Perm(Fin(n)); g is a man and h a woman. The displayed function symm(p) is the inverse bijection. Both comparisons are strict, so a matched pair never blocks.

**Definition 1.4 (The blocking-pair count).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{B}\left(p\right) = \operatorname{card}\left(\{x: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right) \mid \operatorname{blocks}\left(p, \operatorname{fst}\left(x\right), \operatorname{snd}\left(x\right)\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.B` (`✓ std3`).

*Citation.* Yoshiteru Ishida (2026). *A Quadratic Lower Bound for the Shield Number of the Stable Marriage Problem: Rearrangement, Extremal Construction, and Biclique Realizability*. DOI: [10.48550/arXiv.2609.17418](https://doi.org/10.48550/arXiv.2609.17418). URL: <https://arxiv.org/abs/2609.17418v1>.

*Commentary.*

Section 1.1, p. 1: "write B_S(µ) for their number in instance S and β(S) = max_µ B_S(µ)". Here S is the cyclic profile. The displayed finite comprehension is precisely Finset.univ.filter on Fin(n) × Fin(n), and card is its natural-number cardinality. The functions fst and snd read the man and woman of the ordered pair x. Each ordered man-woman pair is counted once.

**Definition 1.5 (The open arc-lemma upper-bound statement).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall p \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{B}\left(p\right) \le \operatorname{NatDiv}\left((n - 1)^{2}, 4\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.claim` (`✓ std3`).

*Citation.* Yoshiteru Ishida (2026). *A Quadratic Lower Bound for the Shield Number of the Stable Marriage Problem: Rearrangement, Extremal Construction, and Biclique Realizability*. DOI: [10.48550/arXiv.2609.17418](https://doi.org/10.48550/arXiv.2609.17418). URL: <https://arxiv.org/abs/2609.17418v1>.

*Commentary.*

Section 7.1, p. 8: "This statement does not assert that µ∗ is maximum-blocking; that is exactly the open arc-lemma upper-bound problem." Conclusion, p. 10: "It does not claim the exact Shield-Core equality for general n, a universal Hall-feasible biclique theorem, or the general upper bound β(C_n) ≤ ⌊(n − 1)²/4⌋." Because β is the maximum over all complete matchings, this upper bound says that every permutation p has the displayed bound. The size n ranges over natural numbers with 1 ≤ n. The subtraction n - 1 is natural subtraction; NatDiv(a, 4) is natural-number division, namely floor(a/4), rather than a rational fraction.

**Theorem 1.6 (The cyclic upper bound).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split matched edges into U = {i : i ≤ p(i)} and W = {i : p(i) < i}, of sizes k and q. The cyclic rank comparisons divide blocking pairs into inversions within U, inversions within W, and mixed pairs. Across every cut t, the number of edges starting below t and ending at or above t equals the number going the other way, since p permutes the labels below t. Applying this balance at p(j) + 1 bounds the U inversions by mixed nesting pairs; applying it at w bounds the W inversions plus q by another disjoint class of mixed pairs. These two classes and the mixed blocking pairs partition W × U, giving B(p) + q ≤ qk. Since k + q = n and (k - q - 1)^2 ≥ 0, we get 4 B(p) ≤ (n - 1)^2 and therefore claim. The conclusion concerns the cyclic profile; the minimum over all preference profiles is a separate question.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.B`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.blocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.rM`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.rW`
- Truth anchor: `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.result`
