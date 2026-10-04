# The one-tenth synchronous doily game

## Abstract

The classical value of Tony Lau's one-tenth synchronous doily game is exactly 22/25. The proof combines an explicit attaining strategy with the odd parities of ten grids and a bound on the effect of synchronous disagreements.

**Definition 1.1 (The fifteen equations).**

$$vars : \operatorname{Fin}\left(15\right) \to (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(15\right)) = [[0, 3, 6], [1, 3, 7], [2, 3, 8], [0, 4, 9], [1, 4, 10], [2, 4, 11], [0, 5, 12], [1, 5, 13], [2, 5, 14], [6, 11, 13], [10, 12, 8], [14, 7, 9], [6, 10, 14], [11, 12, 7], [13, 8, 9]]$$

*Formalization.* `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.vars` (`✓ std3`).

*Citation.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Table 3, p. 6: “E₀ V₀ + V₃ + V₆ = 0; E₁ V₁ + V₃ + V₇ = 0; E₂ V₂ + V₃ + V₈ = 0; E₃ V₀ + V₄ + V₉ = 0; E₄ V₁ + V₄ + V₁₀ = 0; E₅ V₂ + V₄ + V₁₁ = 0; E₆ V₀ + V₅ + V₁₂ = 0; E₇ V₁ + V₅ + V₁₃ = 0; E₈ V₂ + V₅ + V₁₄ = 0; E₉ V₆ + V₁₁ + V₁₃ = 0; E₁₀ V₁₀ + V₁₂ + V₈ = 0; E₁₁ V₁₄ + V₇ + V₉ = 0; E₁₂ V₆ + V₁₀ + V₁₄ = 1; E₁₃ V₁₁ + V₁₂ + V₇ = 1; E₁₄ V₁₃ + V₈ + V₉ = 1.” The Boolean equation additions are modulo two. The displayed list defines vars : Fin 15 → Fin 3 → Fin 15: its entry at equation e and position i is the variable index in precisely the printed order, including E₁₀ and E₁₁.

**Definition 1.2 (Right-hand-side parity).**

$$\forall e \in \operatorname{Fin}\left(15\right),\; \operatorname{odd}\left(e\right) = \operatorname{decide}\left(12 \le \operatorname{val}\left(e\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.odd` (`✓ std3`).

*Citation.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Table 3, p. 6: “E₀ V₀ + V₃ + V₆ = 0; E₁ V₁ + V₃ + V₇ = 0; E₂ V₂ + V₃ + V₈ = 0; E₃ V₀ + V₄ + V₉ = 0; E₄ V₁ + V₄ + V₁₀ = 0; E₅ V₂ + V₄ + V₁₁ = 0; E₆ V₀ + V₅ + V₁₂ = 0; E₇ V₁ + V₅ + V₁₃ = 0; E₈ V₂ + V₅ + V₁₄ = 0; E₉ V₆ + V₁₁ + V₁₃ = 0; E₁₀ V₁₀ + V₁₂ + V₈ = 0; E₁₁ V₁₄ + V₇ + V₉ = 0; E₁₂ V₆ + V₁₀ + V₁₄ = 1; E₁₃ V₁₁ + V₁₂ + V₇ = 1; E₁₄ V₁₃ + V₈ + V₉ = 1.” The function odd is true exactly at equations 12, 13 and 14; val takes the natural-number value of a finite index. The operator decide converts a decidable proposition into a Boolean.

**Definition 1.3 (Parity-valid answers).**

$$\forall e \in \operatorname{Fin}\left(15\right),\; \forall a \in \operatorname{Fin}\left(3\right) \to Bool,\; \operatorname{sat}\left(e, a\right) \Leftrightarrow (\operatorname{mod}\left(\sum_{i \in \operatorname{Fin}\left(3\right)} \operatorname{toNat}\left(a\left(i\right)\right), 2\right) = \operatorname{toNat}\left(\operatorname{odd}\left(e\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.sat` (`✓ std3`).

*Citation.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Definition 4.1, p. 15: “For p ∈ [0, 1], the p-synchronous (p-sync) doily game is defined as the nonlocal game ([15], [15], {0, 1}³, {0, 1}³, (1 − p)π₁ + pπ₂, R), for π₁ being the uniform distribution over {(j, k) ∈ [15] × [15] : Eⱼ and Eₖ have exactly one variable in common}, (13) π₂ being the uniform distribution over {(j, j) ∈ [15] × [15] : j ∈ [15]}, (14) and R : [15] × [15] × {0, 1}³ × {0, 1}³ → {0, 1} being the function such that R(j, k, a, b) = 1 if and only if a satisfies the parity of Eⱼ, b satisfies the parity of Eₖ and the bits corresponding to any variables shared between Eⱼ and Eₖ in a are the same as those in b.” An answer is any function Fin 3 → Bool. The operator toNat sends false to 0 and true to 1, and mod is natural-number remainder. Thus sat states exactly the Boolean equation's required parity.

**Definition 1.4 (Intersecting questions).**

$$\forall e \in \operatorname{Fin}\left(15\right),\; \forall f \in \operatorname{Fin}\left(15\right),\; \operatorname{meet}\left(e, f\right) \Leftrightarrow ((e \ne f) \land (\operatorname{card}\left(\operatorname{inter}\left(\operatorname{image}\left(\operatorname{vars}\left(e\right), \operatorname{univ}\left(\operatorname{Fin}\left(3\right)\right)\right), \operatorname{image}\left(\operatorname{vars}\left(f\right), \operatorname{univ}\left(\operatorname{Fin}\left(3\right)\right)\right)\right)\right) = 1))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.meet` (`✓ std3`).

*Citation.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Definition 4.1, p. 15: “For p ∈ [0, 1], the p-synchronous (p-sync) doily game is defined as the nonlocal game ([15], [15], {0, 1}³, {0, 1}³, (1 − p)π₁ + pπ₂, R), for π₁ being the uniform distribution over {(j, k) ∈ [15] × [15] : Eⱼ and Eₖ have exactly one variable in common}, (13) π₂ being the uniform distribution over {(j, j) ∈ [15] × [15] : j ∈ [15]}, (14) and R : [15] × [15] × {0, 1}³ × {0, 1}³ → {0, 1} being the function such that R(j, k, a, b) = 1 if and only if a satisfies the parity of Eⱼ, b satisfies the parity of Eₖ and the bits corresponding to any variables shared between Eⱼ and Eₖ in a are the same as those in b.” The finite variable set of an equation is the image of Finset.univ under its vars map. Distinct equations meet when the intersection of those sets has cardinality one. Identical equations share three variables and are excluded. Ordered pairs are counted separately.

**Definition 1.5 (The referee predicate).**

$$\forall e \in \operatorname{Fin}\left(15\right),\; \forall f \in \operatorname{Fin}\left(15\right),\; \forall a \in \operatorname{Fin}\left(3\right) \to Bool,\; \forall b \in \operatorname{Fin}\left(3\right) \to Bool,\; \operatorname{R}\left(e, f, a, b\right) \Leftrightarrow ((\operatorname{sat}\left(e, a\right)) \land ((\operatorname{sat}\left(f, b\right)) \land (\forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{vars}\left(e, i\right) = \operatorname{vars}\left(f, j\right) \Rightarrow a\left(i\right) = b\left(j\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.R` (`✓ std3`).

*Citation.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Definition 4.1, p. 15: “For p ∈ [0, 1], the p-synchronous (p-sync) doily game is defined as the nonlocal game ([15], [15], {0, 1}³, {0, 1}³, (1 − p)π₁ + pπ₂, R), for π₁ being the uniform distribution over {(j, k) ∈ [15] × [15] : Eⱼ and Eₖ have exactly one variable in common}, (13) π₂ being the uniform distribution over {(j, j) ∈ [15] × [15] : j ∈ [15]}, (14) and R : [15] × [15] × {0, 1}³ × {0, 1}³ → {0, 1} being the function such that R(j, k, a, b) = 1 if and only if a satisfies the parity of Eⱼ, b satisfies the parity of Eₖ and the bits corresponding to any variables shared between Eⱼ and Eₖ in a are the same as those in b.” The proposition R represents payoff 1. On a diagonal question the universally quantified shared-position condition requires equality of all three answer bits, as well as both parity conditions.

**Definition 1.6 (Winning probability).**

$$\forall p \in \mathbb{R},\; \forall A \in \operatorname{Fin}\left(15\right) \to (\operatorname{Fin}\left(3\right) \to Bool),\; \forall B \in \operatorname{Fin}\left(15\right) \to (\operatorname{Fin}\left(3\right) \to Bool),\; \operatorname{winProb}\left(p, A, B\right) = (1 - p) \cdot \frac{(\operatorname{card}\left(\operatorname{filter}\left((\Lambda z : \operatorname{Fin}\left(15\right) \times \operatorname{Fin}\left(15\right), \operatorname{R}\left(z.1, z.2, A\left(z.1\right), B\left(z.2\right)\right)), \operatorname{filter}\left((\Lambda q : \operatorname{Fin}\left(15\right) \times \operatorname{Fin}\left(15\right), \operatorname{meet}\left(q.1, q.2\right)), \operatorname{univ}\left(\operatorname{Fin}\left(15\right) \times \operatorname{Fin}\left(15\right)\right)\right)\right)\right) : \mathbb{R})}{(\operatorname{card}\left(\operatorname{filter}\left((\Lambda q : \operatorname{Fin}\left(15\right) \times \operatorname{Fin}\left(15\right), \operatorname{meet}\left(q.1, q.2\right)), \operatorname{univ}\left(\operatorname{Fin}\left(15\right) \times \operatorname{Fin}\left(15\right)\right)\right)\right) : \mathbb{R})} + p \cdot \frac{(\operatorname{card}\left(\operatorname{filter}\left((\Lambda e : \operatorname{Fin}\left(15\right), \operatorname{R}\left(e, e, A\left(e\right), B\left(e\right)\right)), \operatorname{univ}\left(\operatorname{Fin}\left(15\right)\right)\right)\right) : \mathbb{R})}{15}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.winProb` (`✓ std3`).

*Citation.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Definition 4.1, p. 15: “For p ∈ [0, 1], the p-synchronous (p-sync) doily game is defined as the nonlocal game ([15], [15], {0, 1}³, {0, 1}³, (1 − p)π₁ + pπ₂, R), for π₁ being the uniform distribution over {(j, k) ∈ [15] × [15] : Eⱼ and Eₖ have exactly one variable in common}, (13) π₂ being the uniform distribution over {(j, j) ∈ [15] × [15] : j ∈ [15]}, (14) and R : [15] × [15] × {0, 1}³ × {0, 1}³ → {0, 1} being the function such that R(j, k, a, b) = 1 if and only if a satisfies the parity of Eⱼ, b satisfies the parity of Eₖ and the bits corresponding to any variables shared between Eⱼ and Eₖ in a are the same as those in b.” Definition 2.2, p. 2: “For the nonlocal game G = (X, Y, A, B, π, V), a classical deterministic strategy S is any pair of functions S = (A, B) with A : X → A and B : Y → B. A and B will be referred to as Alice’s local strategy and Bob’s local strategy, respectively. Then, the probability that Alice and Bob win G using S is given by the expression Σ_{x∈X, y∈Y} π(x, y)V(x, y, A(x), B(y)). (1)” The first finite set in the fraction is the filter of all ordered intersecting pairs by R; its denominator is the cardinality of all ordered intersecting pairs, computed from Table 3 as 90. The diagonal denominator is 15. Both cardinalities are cast to real numbers, as shown by the displayed typed coercion. The definition extends to real p; the game uses p ∈ [0, 1], and the theorem uses p = 1/10. Answer functions remain unrestricted, including parity-invalid answers.

**Definition 1.7 (The deterministic classical value).**

$$\forall p \in \mathbb{R},\; \operatorname{classicalValue}\left(p\right) = Finset.sup'\left(\operatorname{univ}\left((\operatorname{Fin}\left(15\right) \to (\operatorname{Fin}\left(3\right) \to Bool)) \times (\operatorname{Fin}\left(15\right) \to (\operatorname{Fin}\left(3\right) \to Bool))\right), (\Lambda S : (\operatorname{Fin}\left(15\right) \to (\operatorname{Fin}\left(3\right) \to Bool)) \times (\operatorname{Fin}\left(15\right) \to (\operatorname{Fin}\left(3\right) \to Bool)), \operatorname{winProb}\left(p, S.1, S.2\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.classicalValue` (`✓ std3`).

*Citation.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Section 2, p. 3: “We may then define the classical value and entangled value of a game G as the supremal probability of winning G over all classical strategies and over all entangled strategies, respectively.” The displayed Finset.sup' is taken over the nonempty finite universe of all pairs of functions Fin 15 → Fin 3 → Bool, with S mapped to winProb(p, S.1, S.2). Fintype.ofFinite supplies the complete finite enumeration; it imposes no parity restriction. This finite maximum is the source supremum over every deterministic strategy.

**Definition 1.8 (Lau's candidate value).**

$$claim \Leftrightarrow (\operatorname{classicalValue}\left(\frac{1}{10}\right) = \frac{22}{25})$$

*Formalization.* `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.claim` (`✓ std3`).

*Citation.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Section 5, p. 20: “However, it is possible that for p < 1/7, the value of the p-synchronous doily game is less than 31/35. In particular, if Lemma 4.3 can be improved to state that an optimal asymmetric strategy for the doily game wins on at most 12 of 15 synchronous questions, the 1/10-synchronous doily game would have a classical value of 22/25 < 31/35. The author estimates that this could be checked exhaustively using about three years of continuous work on an RTX 4090 graphics card.” Table 3, p. 6: “E₀ V₀ + V₃ + V₆ = 0; E₁ V₁ + V₃ + V₇ = 0; E₂ V₂ + V₃ + V₈ = 0; E₃ V₀ + V₄ + V₉ = 0; E₄ V₁ + V₄ + V₁₀ = 0; E₅ V₂ + V₄ + V₁₁ = 0; E₆ V₀ + V₅ + V₁₂ = 0; E₇ V₁ + V₅ + V₁₃ = 0; E₈ V₂ + V₅ + V₁₄ = 0; E₉ V₆ + V₁₁ + V₁₃ = 0; E₁₀ V₁₀ + V₁₂ + V₈ = 0; E₁₁ V₁₄ + V₇ + V₉ = 0; E₁₂ V₆ + V₁₀ + V₁₄ = 1; E₁₃ V₁₁ + V₁₂ + V₇ = 1; E₁₄ V₁₃ + V₈ + V₉ = 1.” Definition 4.1, p. 15: “For p ∈ [0, 1], the p-synchronous (p-sync) doily game is defined as the nonlocal game ([15], [15], {0, 1}³, {0, 1}³, (1 − p)π₁ + pπ₂, R), for π₁ being the uniform distribution over {(j, k) ∈ [15] × [15] : Eⱼ and Eₖ have exactly one variable in common}, (13) π₂ being the uniform distribution over {(j, j) ∈ [15] × [15] : j ∈ [15]}, (14) and R : [15] × [15] × {0, 1}³ × {0, 1}³ → {0, 1} being the function such that R(j, k, a, b) = 1 if and only if a satisfies the parity of Eⱼ, b satisfies the parity of Eₖ and the bits corresponding to any variables shared between Eⱼ and Eₖ in a are the same as those in b.” Section 2, pp. 2–3: “For the nonlocal game G = (X, Y, A, B, π, V), a classical deterministic strategy S is any pair of functions S = (A, B) with A : X → A and B : Y → B. A and B will be referred to as Alice’s local strategy and Bob’s local strategy, respectively. Then, the probability that Alice and Bob win G using S is given by the expression Σ_{x∈X, y∈Y} π(x, y)V(x, y, A(x), B(y)). (1)” “We may then define the classical value and entangled value of a game G as the supremal probability of winning G over all classical strategies and over all entangled strategies, respectively.” The equality selects the explicitly named candidate p = 1/10. All fifteen equations, all eight local answers per equation, both independent deterministic strategies, and the ordered-question convention are retained.

**Theorem 1.9 (The exact value).**

$$\operatorname{classicalValue}\left(\frac{1}{10}\right) = \frac{22}{25}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tony Lau (2026). *Beyond the Magic Square Game: Widening the Gap for Two Bell States*. DOI: [10.48550/arXiv.2603.20748](https://doi.org/10.48550/arXiv.2603.20748). URL: <https://arxiv.org/abs/2603.20748v2>.

*Commentary.*

Answer 000 at equations 0 through 11 and 100 at equations 12 through 14, for both players. This wins 78 of the 90 intersecting ordered pairs and every diagonal question, attaining 22/25. For the upper bound, repair invalid parities without losing a won question. Each of the ten odd grids forces a loss in each orientation, and every ordered intersecting pair lies in two grids, so the total intersecting loss L is at least 10. If the players disagree on at most two equations, minority-event counting and parity-valid local flips give L ≥ 12. Writing r for their number of differing equation answers yields 3L + 2r ≥ 36, while 300(1 − winProb) = 3L + 2r. Consequently every strategy has winProb ≤ 22/25, and the explicit strategy attains the finite maximum. The conclusion is at the single parameter 1/10; the full parameter dependence and higher-dimensional games require further results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.R`
- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.classicalValue`
- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.meet`
- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.odd`
- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.sat`
- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.vars`
- Truth anchor: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.winProb`
