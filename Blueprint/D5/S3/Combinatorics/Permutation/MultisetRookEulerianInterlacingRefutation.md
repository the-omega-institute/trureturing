# A counterexample to multiset rook-Eulerian interlacing

## Abstract

Multiset rook-Eulerian interlacing fails on a six-row Ferrers board.

A board is a weakly increasing function l on zero-based positions Fin(n). Content a on Fin(k) specifies the multiplicity of the positive letter c+1. Lists encode the source words in their original order. When the content sum is n, their length is n. Polynomial.Splits over the real field is used directly for real-rootedness; by Mathlib's splits_iff_card_roots it is equivalent to roots.card = natDegree, with multiplicity.

**Definition 1.1 (Words with fixed content fitting a Ferrers board).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall l \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall a \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; \operatorname{W}\left(l, a\right) = \operatorname{filter}\left(\operatorname{toFinset}\left(\mathit{permutations}'\left(\operatorname{flatMap}\left(\operatorname{finRange}\left(k\right), (c:\operatorname{Fin}\left(k\right))\mapsto\operatorname{replicate}\left(\operatorname{a}\left(c\right), \operatorname{val}\left(c\right) + 1\right)\right)\right)\right), (w:\operatorname{List}\left(\mathbb{N}\right))\mapsto\forall i \in \operatorname{Fin}\left(n\right),\; 0 < \operatorname{getD}\left(w, \operatorname{val}\left(i\right), 0\right) \land \operatorname{getD}\left(w, \operatorname{val}\left(i\right), 0\right) \le \operatorname{l}\left(i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.W` (`✓ std3`).

*Citation.* Per Alexandersson, Aryaman Jal, and Maena Quemener (2025). *Real-rootedness of rook-Eulerian polynomials*. DOI: [10.48550/arXiv.2502.05939](https://doi.org/10.48550/arXiv.2502.05939). URL: <https://arxiv.org/abs/2502.05939v1>.

*Commentary.*

Section 3.3, page 11: ‘Let α = (α₁, . . . , αₖ) be non-negative integers with total sum n, and let λ and μ be integer partitions such that λᵢ > μᵢ for all i. We let W(λ/μ, α) be all words with αᵢ entries equal to i, such that μᵢ < wᵢ ≤ λᵢ for all i = 1, 2, . . . , n.’ Here μ is zero. The defining expression constructs the list containing a(c) copies of c+1, enumerates its permutations by the existing List.permutations' operation, removes duplicate lists, and retains precisely the row inequalities. List.mem_permutations' identifies membership with permutation of that content list. No word order is identified: only repeated enumeration of the same word is removed. getD(w,i,0) is list lookup with default zero; every queried position exists when the content sum is n.

**Definition 1.2 (Strict adjacent ascents).**

$$\forall w \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{asc}\left(w\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{range}\left(\operatorname{length}\left(w\right) - 1\right), (i:\mathbb{N})\mapsto\operatorname{getD}\left(w, i, 0\right) < \operatorname{getD}\left(w, i + 1, 0\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.asc` (`✓ std3`).

*Citation.* Per Alexandersson, Aryaman Jal, and Maena Quemener (2025). *Real-rootedness of rook-Eulerian polynomials*. DOI: [10.48550/arXiv.2502.05939](https://doi.org/10.48550/arXiv.2502.05939). URL: <https://arxiv.org/abs/2502.05939v1>.

*Commentary.*

Section 2, page 4: ‘if w₁w₂ . . . wℓ is a word, then i is an ascent of the word if wᵢ < wᵢ₊₁.’ The zero-based index set is range(length(w) minus one). Subtraction in this natural-valued expression is truncated, including at the empty word.

**Definition 1.3 (The full polynomial).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall l \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall a \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; \operatorname{R}\left(l, a\right) = \sum_{w\in\operatorname{W}\left(l, a\right)}X^{\operatorname{asc}\left(w\right)}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.R` (`✓ std3`).

*Citation.* Per Alexandersson, Aryaman Jal, and Maena Quemener (2025). *Real-rootedness of rook-Eulerian polynomials*. DOI: [10.48550/arXiv.2502.05939](https://doi.org/10.48550/arXiv.2502.05939). URL: <https://arxiv.org/abs/2502.05939v1>.

*Commentary.*

Section 3.3, page 11, equation (10): R(λ/μ, α; t) := Σ_{w ∈ W(λ/μ, α)} t^{asc(w)}. X is the real polynomial indeterminate; summation is over distinct words.

**Definition 1.4 (The first-letter refined polynomial).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall l \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall a \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{Rj}\left(l, a, j\right) = \sum_{w\in\operatorname{filter}\left(\operatorname{W}\left(l, a\right), (u:\operatorname{List}\left(\mathbb{N}\right))\mapsto\operatorname{getD}\left(u, 0, 0\right) = j\right)}X^{\operatorname{asc}\left(w\right)}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.Rj` (`✓ std3`).

*Citation.* Per Alexandersson, Aryaman Jal, and Maena Quemener (2025). *Real-rootedness of rook-Eulerian polynomials*. DOI: [10.48550/arXiv.2502.05939](https://doi.org/10.48550/arXiv.2502.05939). URL: <https://arxiv.org/abs/2502.05939v1>.

*Commentary.*

Section 3.3, page 11, equation (11): Rⱼ(λ/μ, α; t) := Σ_{w ∈ W(λ/μ, α), w₁=j} t^{asc(w)}. The first letter is getD(w,0,0), without an ascent shift. Examples 25–26 use λ = 22233 and α = (2,2,1): twelve fitting words give t³ + 8t² + 3t.

**Definition 1.5 (Interlacing with multiplicity).**

$$\forall f \in \mathbb{R}[X],\; \forall g \in \mathbb{R}[X],\; \operatorname{Interlaces}\left(f, g\right) = \left(0 < \operatorname{leadingCoeff}\left(f\right) \land \left(0 < \operatorname{leadingCoeff}\left(g\right) \land \left(\operatorname{Splits}\left(f\right) \land \left(\operatorname{Splits}\left(g\right) \land \left(\left(\forall x \in \mathbb{R},\; x \in \operatorname{roots}\left(f\right) \Rightarrow x \le 0\right) \land \left(\left(\forall x \in \mathbb{R},\; x \in \operatorname{roots}\left(g\right) \Rightarrow x \le 0\right) \land \left(\left(\operatorname{natDegree}\left(g\right) = \operatorname{natDegree}\left(f\right) \lor \operatorname{natDegree}\left(g\right) = \operatorname{natDegree}\left(f\right) + 1\right) \land \left(\forall i \in \mathbb{N},\; i < \operatorname{card}\left(\operatorname{roots}\left(f\right)\right) \Rightarrow \left(\operatorname{getD}\left(\operatorname{sort}\left(\operatorname{roots}\left(f\right), (\mathord{\cdot} \ge \mathord{\cdot})\right), i, 0\right) \le \operatorname{getD}\left(\operatorname{sort}\left(\operatorname{roots}\left(g\right), (\mathord{\cdot} \ge \mathord{\cdot})\right), i, 0\right) \land \left(i + 1 < \operatorname{card}\left(\operatorname{roots}\left(g\right)\right) \Rightarrow \operatorname{getD}\left(\operatorname{sort}\left(\operatorname{roots}\left(g\right), (\mathord{\cdot} \ge \mathord{\cdot})\right), i + 1, 0\right) \le \operatorname{getD}\left(\operatorname{sort}\left(\operatorname{roots}\left(f\right), (\mathord{\cdot} \ge \mathord{\cdot})\right), i, 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.Interlaces` (`✓ std3`).

*Citation.* Per Alexandersson, Aryaman Jal, and Maena Quemener (2025). *Real-rootedness of rook-Eulerian polynomials*. DOI: [10.48550/arXiv.2502.05939](https://doi.org/10.48550/arXiv.2502.05939). URL: <https://arxiv.org/abs/2502.05939v1>.

*Commentary.*

Definition 8, page 6: ‘Let f and g be polynomials with positive leading coefficients and real, non-positive zeros, aᵢ and bᵢ, respectively. We say that f interlaces g, and we write f ≼ g if ⋯ ≤ a₃ ≤ b₃ ≤ a₂ ≤ b₂ ≤ a₁ ≤ b₁ ≤ 0. Note that deg(f) = deg(g) or deg(f) + 1 = deg(g).’ roots is Mathlib's root multiset; sort(roots, (· >= ·)) orders it decreasingly without dropping repeated zeros. The two comparisons use zero-based i. They are exactly aᵢ₊₁ ≤ bᵢ₊₁ and, where it exists, bᵢ₊₂ ≤ aᵢ₊₁. Positive leading coefficients exclude the zero polynomial; Splits makes the multiset lengths equal the degrees. The stated degree alternatives make every compared entry valid, so the default zero in getD is never used.

**Definition 1.6 (Conjecture 28, including both clauses).**

$$\mathit{claim} = \left(\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall l \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall a \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; \forall h \in (0 < n),\; \operatorname{Monotone}\left(l\right) \Rightarrow \left(\sum_{c\in\operatorname{Fin}\left(k\right)}\operatorname{a}\left(c\right) = n \Rightarrow \left(\operatorname{Splits}\left(\operatorname{R}\left(l, a\right)\right) \land \left(\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; 1 \le q \Rightarrow \left(q < p \Rightarrow \left(p \le \operatorname{l}\left(\langle0,h\rangle\right) \Rightarrow \left(\operatorname{Rj}\left(l, a, p\right) \ne 0 \Rightarrow \left(\operatorname{Rj}\left(l, a, q\right) \ne 0 \Rightarrow \operatorname{Interlaces}\left(\operatorname{Rj}\left(l, a, p\right), \operatorname{Rj}\left(l, a, q\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.claim` (`✓ std3`).

*Citation.* Per Alexandersson, Aryaman Jal, and Maena Quemener (2025). *Real-rootedness of rook-Eulerian polynomials*. DOI: [10.48550/arXiv.2502.05939](https://doi.org/10.48550/arXiv.2502.05939). URL: <https://arxiv.org/abs/2502.05939v1>.

*Commentary.*

Conjecture 28, page 12: ‘For Ferrers boards, the polynomial R(λ, α; t) is real-rooted. Moreover, Rλ₁(λ, α; t), Rλ₁−1(λ, α; t), . . . , R₂(λ, α; t), R₁(λ, α; t) forms an interlacing sequence.’ Definition 9, page 6: ‘A sequence F = (f₁, . . . , fₙ) of real-rooted polynomials is interlacing if fᵢ ≼ fⱼ for 1 ≤ i < j ≤ n.’ The formula quantifies all positive n, all k, all monotone boards and all contents summing to n. The nonzero hypotheses on both refined polynomials are explicit. Since the sequence runs in decreasing letter order, p > q requires R_p to interlace R_q. The binder h is the proof that n is positive, needed to form the first position ⟨0,h⟩.

**Theorem 1.7 (Refutation on board 333344).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The content (2,2,1,1) on the board (3,3,3,3,4,4) has sixty fitting words. The two relevant refinements are R₁ = 2X⁴ + 15X³ + 7X² = X²(X+7)(2X+1) and R₃ = X³ + 8X² + 3X. Their decreasing roots, with multiplicity, are respectively [0,0,−1/2,−7] and [0,−4+√13,−4−√13]. Since 3 < √13 < 4, the bottom comparison would require −7 ≤ −4−√13, which is false. This refutes the interlacing-sequence clause and hence the conjunction. The universal real-rootedness clause is not decided by this refutation.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.Interlaces`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.R`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.Rj`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.W`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.asc`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.result`
