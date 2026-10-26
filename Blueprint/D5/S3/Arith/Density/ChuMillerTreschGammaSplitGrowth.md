# Linear Growth for Every Gamma-Label Split

## Abstract

Every prescribed Gamma-label density has a positive increasing linear-growth sequence.

All sequence indices and Diophantine variables are natural numbers, including zero. Nat.div is natural integer division, subtraction in the naturals truncates at zero, and the displayed density ratio uses real division. Sequences start at index zero; prefix counts start at edge one.

**Definition 1.1 (The gcd-reduced Diophantine label).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Gamma}\left(a, b\right) = (\operatorname{if} (\exists x \in \mathbb{N},\; \exists y \in \mathbb{N},\; \operatorname{Nat}.\operatorname{div}\left(a, \operatorname{Nat}.\operatorname{gcd}\left(a, b\right)\right) \cdot x + \operatorname{Nat}.\operatorname{div}\left(b, \operatorname{Nat}.\operatorname{gcd}\left(a, b\right)\right) \cdot y = \operatorname{Nat}.\operatorname{div}\left(((\operatorname{Nat}.\operatorname{div}\left(a, \operatorname{Nat}.\operatorname{gcd}\left(a, b\right)\right) - 1) \cdot (\operatorname{Nat}.\operatorname{div}\left(b, \operatorname{Nat}.\operatorname{gcd}\left(a, b\right)\right) - 1)), 2\right)) \operatorname{then} 0 \operatorname{else} 1)$$

*Formalization.* `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.Gamma` (`✓ std3`).

*Citation.* Hùng Việt Chu, Steven J. Miller, and Garrett Tresch (2025). *Problems Regarding a Pair of Diophantine Equations*. DOI: [10.48550/arXiv.2512.12681](https://doi.org/10.48550/arXiv.2512.12681). URL: <https://arxiv.org/abs/2512.12681v1>.

*Commentary.*

Section 1, pp. 2–3: “Γ : ℕ² → {0, 1} … where Γ(a, b) = 0 if (a/gcd(a, b)) x + (b/gcd(a, b)) y = (a/gcd(a, b) − 1)(b/gcd(a, b) − 1)/2 has the nonnegative integral solution, and Γ(a, b) = 1 if 1 + (a/gcd(a, b)) x + (b/gcd(a, b)) y = (a/gcd(a, b) − 1)(b/gcd(a, b) − 1)/2 has the nonnegative integral solution.” The function Gamma returns 0 when the first equation has a solution in ℕ and 1 otherwise. Theorem 1.1 identifies this latter case with the second equation for positive inputs.

**Definition 1.2 (The inclusive prefix count).**

$$\forall a \in \mathbb{N} \to \mathbb{N},\; \forall N \in \mathbb{N},\; \operatorname{zeroCount}\left(a, N\right) = \operatorname{Finset}.\operatorname{card}\left((\operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} (n: \mathbb{N}) \mapsto \operatorname{Gamma}\left(a\left((n - 1)\right), a\left(n\right)\right) = 0), (\operatorname{Finset}.\operatorname{Icc}\left(1, N\right))\right))\right)$$

*Formalization.* `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.zeroCount` (`✓ std3`).

*Citation.* Hùng Việt Chu, Steven J. Miller, and Garrett Tresch (2025). *Problems Regarding a Pair of Diophantine Equations*. DOI: [10.48550/arXiv.2512.12681](https://doi.org/10.48550/arXiv.2512.12681). URL: <https://arxiv.org/abs/2512.12681v1>.

*Commentary.*

Corollary 2.6, p. 5, counts “#{n ≤ N : Γ(a_{n−1}, a_n) = 0}”. The count zeroCount uses 1 ≤ n ≤ N, so that the first pair is (a 0, a 1) and the prefix contains exactly N edges.

**Definition 1.3 (Polynomial growth for a prescribed split).**

$$(claim) \Leftrightarrow (\forall p \in \mathbb{R},\; (0 \le p) \Rightarrow ((p \le 1) \Rightarrow (\exists a \in \mathbb{N} \to \mathbb{N},\; (\operatorname{StrictMono}\left(a\right)) \land ((\forall n \in \mathbb{N},\; 0 < a\left(n\right)) \land ((\exists k \in \mathbb{N},\; \exists C \in \mathbb{R},\; \forall n \in \mathbb{N},\; (1 \le n) \Rightarrow ((a\left(n\right): \mathbb{R}) \le C \cdot (n: \mathbb{R})^{k})) \land (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (N: \mathbb{N}) \mapsto \frac{(\operatorname{zeroCount}\left(a, N\right): \mathbb{R})}{(N: \mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(p\right)\right)))))))$$

*Formalization.* `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.claim` (`✓ std3`).

*Citation.* Hùng Việt Chu, Steven J. Miller, and Garrett Tresch (2025). *Problems Regarding a Pair of Diophantine Equations*. DOI: [10.48550/arXiv.2512.12681](https://doi.org/10.48550/arXiv.2512.12681). URL: <https://arxiv.org/abs/2512.12681v1>.

*Commentary.*

Section 3.4, p. 11: “As noted in Remark 2.7, the sequence grows exponentially fast (faster than the Fibonacci sequence). Is there a construction involving a strictly increasing sequence that grows slower than the Fibonacci sequence, or perhaps even like n^k for some k?” The real parameter p ranges over [0,1]. The sequence has positive natural entries, a polynomial upper bound from index one, and limiting proportion p of zero-labelled edges.

**Theorem 1.4 (An affirmative answer with exponent one).**

$$\forall p \in \mathbb{R},\; (0 \le p) \Rightarrow ((p \le 1) \Rightarrow (\exists a \in \mathbb{N} \to \mathbb{N},\; (\operatorname{StrictMono}\left(a\right)) \land ((\forall n \in \mathbb{N},\; 0 < a\left(n\right)) \land ((\exists k \in \mathbb{N},\; \exists C \in \mathbb{R},\; \forall n \in \mathbb{N},\; (1 \le n) \Rightarrow ((a\left(n\right): \mathbb{R}) \le C \cdot (n: \mathbb{R})^{k})) \land (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (N: \mathbb{N}) \mapsto \frac{(\operatorname{zeroCount}\left(a, N\right): \mathbb{R})}{(N: \mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(p\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.result` (`✓ std3`). ∎

*Resolves.* `Problems/chu-miller-tresch-2025-gamma-split-linear-growth` (proved) by `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chu-miller-tresch-2025-gamma-split-linear-growth","declaration_gid":"D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hùng Việt Chu, Steven J. Miller, and Garrett Tresch (2025). *Problems Regarding a Pair of Diophantine Equations*. DOI: [10.48550/arXiv.2512.12681](https://doi.org/10.48550/arXiv.2512.12681). URL: <https://arxiv.org/abs/2512.12681v1>.

*Commentary.*

The chains (3,7,17,19,23,43) and (3,23,27,29,33,43), translated by 40k, have respectively five zero-labelled and five one-labelled edges. Their endpoints agree across consecutive translates. The floor increment ⌊(k+1)p⌋−⌊kp⌋ selects a chain for each k. The resulting sequence satisfies 8n ≤ a n + 9 and a n ≤ 8n + 15, while 0 ≤ pN − zeroCount a N < 5. Squeezing the real ratios gives the required limit, including p=0 and p=1. The polynomial bound uses k=1 and C=23. No assertion of optimality of the coefficient is made.

## References

- Truth anchor: `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.Gamma`
- Truth anchor: `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.claim`
- Truth anchor: `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.result`
- Truth anchor: `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.zeroCount`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](../../../S1/Words/Mechanical/MechanicalBalance.md)
