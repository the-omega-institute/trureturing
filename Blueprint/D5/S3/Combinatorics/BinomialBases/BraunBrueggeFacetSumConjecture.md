# Braun–Bruegge Conjecture 5.1

## Abstract

Braun–Bruegge's symmetric edge-polytope facet-sum conjecture

**Definition 1.1 (The facet sum).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) = \sum_{j \in \operatorname{Finset.range}\left(c + 1\right)} (\operatorname{Nat.choose}\left(c, j\right) \cdot \operatorname{Nat.choose}\left(b, \operatorname{Nat.div}\left(b - c, 2\right) + j\right) \cdot \operatorname{Nat.choose}\left(a, \operatorname{Nat.div}\left(a - c, 2\right) + j\right))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.F` (`✓ std3`).

*Citation.* B. Braun, K. Bruegge (2023). *Facets of Symmetric Edge Polytopes for Graphs with Few Edges*. URL: <https://arxiv.org/abs/2201.13303v4>.

*Commentary.*

Proposition 4.4 states verbatim: “If all the m_i's have the same parity, N(CB(m)) is given by F(m) = Σ_{j=0}^{m_t} C(m_t, j) [Π_{k=1}^{t−1} C(m_k, (m_k − m_t)/2 + j)].” The displayed Lean expression is its t=3 specialization, with Nat.choose and natural floor division.

**Definition 1.2 (The sorted common-parity domain).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right) \Leftrightarrow ((b \le a) \land ((c \le b) \land ((1 \le c) \land ((\operatorname{Nat.mod}\left(a, 2\right) = \operatorname{Nat.mod}\left(b, 2\right)) \land (\operatorname{Nat.mod}\left(b, 2\right) = \operatorname{Nat.mod}\left(c, 2\right))))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.Admissible` (`✓ std3`).

*Citation.* B. Braun, K. Bruegge (2023). *Facets of Symmetric Edge Polytopes for Graphs with Few Edges*. URL: <https://arxiv.org/abs/2201.13303v4>.

*Commentary.*

The source orders the entries so that a≥b≥c, requires positive entries, and requires common parity. The conjunction records exactly those conditions.

**Definition 1.3 (Conjecture 5.1).**

$$(\forall k \in \mathbb{N},\; (2 \le k) \Rightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right)) \Rightarrow ((a + b + c = 2 \cdot k + 1) \Rightarrow (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) \le \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(2 \cdot k - 1, 1, 1\right))))) \land ((\forall k \in \mathbb{N},\; (3 \le k) \Rightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right)) \Rightarrow ((a + b + c = 2 \cdot k - 1 + 1) \Rightarrow (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) \le \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(2 \cdot k - 1 - 3, 2, 2\right))))) \land ((\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right)) \Rightarrow ((3 \le c) \Rightarrow (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) \le \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a + 2, b, c - 2\right)))) \land (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right)) \Rightarrow ((3 \le c) \Rightarrow ((c \le b - 2) \Rightarrow (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) \le \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a + 2, b - 2, c\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.claim` (`✓ std3`).

*Citation.* B. Braun, K. Bruegge (2023). *Facets of Symmetric Edge Polytopes for Graphs with Few Edges*. URL: <https://arxiv.org/abs/2201.13303v4>.

*Commentary.*

Conjecture 5.1 states verbatim: “For n = 2k and k ≥ 2 with x_1 + x_2 + x_3 = n + 1, F(x_1, x_2, x_3) is maximized at F(n − 1, 1, 1). For n = 2k − 1 and k ≥ 3 with x_1 + x_2 + x_3 = n + 1, F(x_1, x_2, x_3) is maximized at F(n − 3, 2, 2). Further, for any x_1 ≥ x_2 ≥ x_3 ≥ 3 all even or all odd positive integers, F(x_1, x_2, x_3) ≤ F(x_1 + 2, x_2, x_3 − 2) and F(x_1, x_2, x_3) ≤ F(x_1 + 2, x_2 − 2, x_3), when the subtraction by 2 will maintain the inequalities on the x_i's.” The four conjuncts encode these assertions with the admissible domain and the stated endpoint conditions.

**Theorem 1.4 (The four assertions hold).**

$$(\forall k \in \mathbb{N},\; (2 \le k) \Rightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right)) \Rightarrow ((a + b + c = 2 \cdot k + 1) \Rightarrow (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) \le \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(2 \cdot k - 1, 1, 1\right))))) \land ((\forall k \in \mathbb{N},\; (3 \le k) \Rightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right)) \Rightarrow ((a + b + c = 2 \cdot k - 1 + 1) \Rightarrow (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) \le \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(2 \cdot k - 1 - 3, 2, 2\right))))) \land ((\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right)) \Rightarrow ((3 \le c) \Rightarrow (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) \le \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a + 2, b, c - 2\right)))) \land (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.Admissible}\left(a, b, c\right)) \Rightarrow ((3 \le c) \Rightarrow ((c \le b - 2) \Rightarrow (\operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a, b, c\right) \le \operatorname{D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.F}\left(a + 2, b - 2, c\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.result` (`✓ std3`). ∎

*Resolves.* `Problems/braun-bruegge-2022-symmetric-edge-polytope-facet-sum-conjecture-5-1` (proved) by `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"braun-bruegge-2022-symmetric-edge-polytope-facet-sum-conjecture-5-1","declaration_gid":"D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* B. Braun, K. Bruegge (2023). *Facets of Symmetric Edge Polytopes for Graphs with Few Edges*. URL: <https://arxiv.org/abs/2201.13303v4>.

*Commentary.*

The proof writes each facet sum as a weighted sum of centered binomial rows. A Vandermonde identity preserves the paired mass under each two-unit transfer. The transfer difference has one sign crossing, and the third centered row is antitone with distance from the center, so the weighted difference is nonnegative. Strong induction then reaches the endpoint triples in both parity classes. Finite computation checks 58,088 admissible triples for 4≤n≤200; the centered-row argument proves the inequalities for arbitrary admissible triples.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.Admissible`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.F`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.claim`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.result`
- Dependency: [D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound](../../Quantum/Contextuality/SymmetricGHZResourceLowerBound.md)
