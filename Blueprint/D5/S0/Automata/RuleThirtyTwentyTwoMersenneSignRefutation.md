# A non-Mersenne exception to the Rule 30/22 sign pattern

## Abstract

Refutes the Rule 30/22 Mersenne sign pattern at row 767.

**Definition 1.1 (Single-seed evolution).**

$$\begin{aligned}(\forall g \in (\mathit{Bool} \to \left(\mathit{Bool} \to \left(\mathit{Bool} \to \mathit{Bool}\right)\right)),\; \forall r \in \mathbb{Z},\; \operatorname{row}\left(g, 0, r\right) = \operatorname{decide}\left(r = 0\right))\\(\forall g \in (\mathit{Bool} \to \left(\mathit{Bool} \to \left(\mathit{Bool} \to \mathit{Bool}\right)\right)),\; \forall m \in \mathbb{N},\; \forall r \in \mathbb{Z},\; \operatorname{row}\left(g, m + 1, r\right) = g\left(\operatorname{row}\left(g, m, r - 1\right), \operatorname{row}\left(g, m, r\right), \operatorname{row}\left(g, m, r + 1\right)\right))\end{aligned}$$

*Formalization.* `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.row` (`✓ std3`).

*Citation.* E. Chan-López and A. Martín-Ruiz (2026). *Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30*. DOI: [10.48550/arXiv.2604.00165](https://doi.org/10.48550/arXiv.2604.00165). URL: <https://arxiv.org/abs/2604.00165v3>.

*Commentary.*

The whole integer lattice evolves synchronously from one active cell at the origin. The arguments of g are the left neighbour, centre and right neighbour, in that order. The value true means an active cell; decide converts a proposition to Bool. Section 3, p. 4, fixes the configuration evolved "from the single-seed initial condition η_0 = δ_0".

**Definition 1.2 (Rule 30).**

$$\forall a \in \mathit{Bool},\; \forall b \in \mathit{Bool},\; \forall c \in \mathit{Bool},\; \operatorname{g30}\left(a, b, c\right) = \operatorname{xor}\left(\operatorname{xor}\left(\operatorname{xor}\left(a, b\right), c\right), \operatorname{and}\left(b, c\right)\right)$$

*Formalization.* `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.g30` (`✓ std3`).

*Citation.* E. Chan-López and A. Martín-Ruiz (2026). *Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30*. DOI: [10.48550/arXiv.2604.00165](https://doi.org/10.48550/arXiv.2604.00165). URL: <https://arxiv.org/abs/2604.00165v3>.

*Commentary.*

Proposition 1, p. 3: "Rule 30, with ANF g30 = a ⊕ b ⊕ c ⊕ bc, is left-permutive but lacks S3 symmetry." Here xor is Bool XOR and and is Bool AND, so they implement addition and multiplication over F2. Boolean exclusive-or is nested to the left as displayed, with the conjunction of the centre and right bits as its final argument.

**Definition 1.3 (Rule 22).**

$$\forall a \in \mathit{Bool},\; \forall b \in \mathit{Bool},\; \forall c \in \mathit{Bool},\; \operatorname{g22}\left(a, b, c\right) = \operatorname{xor}\left(\operatorname{xor}\left(\operatorname{xor}\left(a, b\right), c\right), \operatorname{and}\left(\operatorname{and}\left(a, b\right), c\right)\right)$$

*Formalization.* `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.g22` (`✓ std3`).

*Citation.* E. Chan-López and A. Martín-Ruiz (2026). *Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30*. DOI: [10.48550/arXiv.2604.00165](https://doi.org/10.48550/arXiv.2604.00165). URL: <https://arxiv.org/abs/2604.00165v3>.

*Commentary.*

Equation (1), p. 3: "g22(a, b, c) = a ⊕ b ⊕ c ⊕ abc." Boolean exclusive-or and conjunction are nested to the left as displayed.

**Definition 1.4 (Full-row support cardinality).**

$$\forall g \in (\mathit{Bool} \to \left(\mathit{Bool} \to \left(\mathit{Bool} \to \mathit{Bool}\right)\right)),\; \forall m \in \mathbb{N},\; \operatorname{supportCard}\left(g, m\right) = Set.ncard\left(\{r:\mathbb{Z}\mid\operatorname{row}\left(g, m, r\right) = \mathit{true}\}\right)$$

*Formalization.* `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.supportCard` (`✓ std3`).

*Citation.* E. Chan-López and A. Martín-Ruiz (2026). *Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30*. DOI: [10.48550/arXiv.2604.00165](https://doi.org/10.48550/arXiv.2604.00165). URL: <https://arxiv.org/abs/2604.00165v3>.

*Commentary.*

Definition 2, p. 4: "The support set at time m is the full-row support S_m = {r ∈ Z : η_m(r) = 1}". The same page specifies: "All cardinality statements below refer to the full-row set S_m". This counts every active integer site, including negative sites and the origin, rather than the right-half support. The operator ncard is Set.ncard. Both rules send the all-false neighbourhood to false; induction bounds their support by the finite interval [-m,m].

**Definition 1.5 (The symmetry-breaking deviation).**

$$\forall m \in \mathbb{N},\; \operatorname{eps}\left(m\right) = (\operatorname{supportCard}\left(\mathit{g30}, m\right):\mathbb{Z}) - (\operatorname{supportCard}\left(\mathit{g22}, m\right):\mathbb{Z})$$

*Formalization.* `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.eps` (`✓ std3`).

*Citation.* E. Chan-López and A. Martín-Ruiz (2026). *Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30*. DOI: [10.48550/arXiv.2604.00165](https://doi.org/10.48550/arXiv.2604.00165). URL: <https://arxiv.org/abs/2604.00165v3>.

*Commentary.*

Equation (11), p. 10: "ϵ(m) = |S_m^(30)| − |S_m^(22)|". The formula casts each natural cardinality to the integers before subtraction, preserving negative values. The function eps is the paper's ϵ and uses the two full-row supports.

**Definition 1.6 (The sign-pattern question).**

$$\mathit{claim} = (\forall m \in \mathbb{N},\; 1 \le m \Rightarrow (\operatorname{eps}\left(m\right) \le 0 \Leftrightarrow (\exists k \in \mathbb{N},\; 1 \le k \land m = 2^{k} - 1)))$$

*Formalization.* `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.claim` (`✓ std3`).

*Citation.* E. Chan-López and A. Martín-Ruiz (2026). *Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30*. DOI: [10.48550/arXiv.2604.00165](https://doi.org/10.48550/arXiv.2604.00165). URL: <https://arxiv.org/abs/2604.00165v3>.

*Commentary.*

Remark 3, p. 11: "A direct computation for m ≤ 256 shows that ϵ(m) ≤ 0 precisely at the Mersenne indices m = 2^k − 1, with ϵ = 0 for k ≤ 3 and ϵ < 0 for 4 ≤ k ≤ 8." Section 9, p. 15, asks: "Is the sign pattern of Remark 3 exact for all k?" The proposition extends the 'precisely' biconditional to every natural row index m at least one. The exponent k is a natural number at least one, and the subtraction in 2^k - 1 is natural subtraction. The separate assertion of strict negativity at every Mersenne index with k at least four is not part of this proposition.

**Theorem 1.7 (The sign pattern is false).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* E. Chan-López and A. Martín-Ruiz (2026). *Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30*. DOI: [10.48550/arXiv.2604.00165](https://doi.org/10.48550/arXiv.2604.00165). URL: <https://arxiv.org/abs/2604.00165v3>.

*Commentary.*

At row 767, Rule 30 has 763 active cells and Rule 22 has 768, so eps(767) = -5. But 767 is not a Mersenne index: 512 < 768 < 1024 excludes 768 being a power of two. For a quiescent rule, a light-cone induction proves that the row vanishes outside [-m,m]. A second induction identifies row g m r with bit r+m of the m-fold bitwise step starting at 1, with negative bit positions set to false. The map i ↦ (i : Z)-m identifies the active bits below 2m+1 with the full-row support and preserves cardinality. For Rule 30 the encoded step is the exclusive-or of b shifted left by two bits with the bitwise union of b shifted left by one bit and b. For Rule 22 it is the exclusive-or of b shifted left by two bits, b shifted left by one bit, b, and their three-way bitwise intersection. Evaluating these exact recurrences and counting the 1535 possible bits gives the two cardinalities. This disproves the only-if direction. It does not determine the signs at all Mersenne indices or the recurrence of other exceptions.

## References

- Truth anchor: `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.claim`
- Truth anchor: `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.eps`
- Truth anchor: `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.g22`
- Truth anchor: `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.g30`
- Truth anchor: `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.result`
- Truth anchor: `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.row`
- Truth anchor: `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.supportCard`
