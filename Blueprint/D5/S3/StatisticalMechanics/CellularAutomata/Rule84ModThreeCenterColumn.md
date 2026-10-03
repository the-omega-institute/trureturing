# The Rule 84 center column modulo three

## Abstract

The canonical polynomial lift of Rule 84 from a single seed has center column 1 at time zero and the repeating block (1, 2, 2) at every positive time modulo three. A forward-invariant language of length-seven windows proves the pattern for all time.

**Definition 1.1 (The canonical single-seed orbit).**

$$\begin{aligned}A: \mathbb{N} \to \mathbb{Z} \to \operatorname{ZMod}\left(3\right)\\\forall x \in \mathbb{Z},\; \operatorname{A}\left(0, x\right) = \operatorname{ite}\left(x = 0, 1, 0\right)\\\forall t \in \mathbb{N},\; \forall x \in \mathbb{Z},\; \operatorname{A}\left(t + 1, x\right) = (\operatorname{A}\left(t, x - 1\right) + \operatorname{A}\left(t, x\right) + \operatorname{A}\left(t, x - 1\right) \cdot \operatorname{A}\left(t, x\right)) \cdot (1 + \operatorname{A}\left(t, x + 1\right))\end{aligned}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.A` (`✓ std3`).

*Citation.* Tigran Nersissian (2026). *Diagonal Bases and Diagonal Periods of Elementary Cellular Automata*. DOI: [10.48550/arXiv.2609.25078](https://doi.org/10.48550/arXiv.2609.25078). URL: <https://arxiv.org/abs/2609.25078v1>.

*Commentary.*

Definition 1, page 4 of arXiv:2609.25078v1: "The variables a, b, c are the left, center and right neighbors." "For an initial condition c₀ = (c₀(0), c₀(1), …) placed at x = 0, 1, … on a zero background, write A_{R,c₀}(t, x), t ≥ 0, x ∈ Z, for the orbit under p_R." Here R = 84, the modulus is 3, and c₀ is the single seed δ₀. Time t is a natural number, position x is an integer, and all cell values and polynomial arithmetic lie in ZMod 3. The three inputs at time t are A(t, x − 1), A(t, x), A(t, x + 1), respectively. The displayed ite(condition, u, v) equals u when the condition holds and v otherwise; it gives exactly one nonzero cell at time zero.

**Definition 1.2 (The outstanding Rule 84 pattern).**

$$claim \Leftrightarrow ((\operatorname{A}\left(0, 0\right) = 1) \land (\forall s \in \mathbb{N},\; (\operatorname{A}\left(3 \cdot s + 1, 0\right) = 1) \land ((\operatorname{A}\left(3 \cdot s + 2, 0\right) = 2) \land (\operatorname{A}\left(3 \cdot s + 3, 0\right) = 2))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.claim` (`✓ std3`).

*Citation.* Tigran Nersissian (2026). *Diagonal Bases and Diagonal Periods of Elementary Cellular Automata*. DOI: [10.48550/arXiv.2609.25078](https://doi.org/10.48550/arXiv.2609.25078). URL: <https://arxiv.org/abs/2609.25078v1>.

*Commentary.*

Remark 6, page 12 of arXiv:2609.25078v1: "(The outstanding Rule 84 case) The polynomial of Rule 84 is (a + b + ab)(1 + c). Modulo three, its center column begins 1, 1, 2, 2, 1, 2, 2, … and follows the repeating block (1, 2, 2) after the first entry for the tested times 0 ≤ t < 2048. All center values are also units modulo 9 and 27 on that range, as Corollary 2 predicts. An all-time proof of the observed pattern is not supplied here. If Rule 84 is universal modulo three, it is universal at every power of three; three could not be the sole exceptional modulus." Section 19, page 42: "The classification reduces the remaining single-seed universality question to the eight rules in E at odd primes. The observed Rule 84 pattern modulo three requires an invariant or an all-time recurrence proof. A finite nonzero prefix is insufficient." The encoding states A(0, 0) = 1 and the three values at 3s + 1, 3s + 2 and 3s + 3 for every natural s, so every positive time is included. The entries 1 and 2 denote residues in ZMod 3. Universality at higher powers is a consequence using the source's Corollaries 1–2, outside the displayed claim.

**Theorem 1.3 (The pattern holds for all time).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tigran Nersissian (2026). *Diagonal Bases and Diagonal Periods of Elementary Cellular Automata*. DOI: [10.48550/arXiv.2609.25078](https://doi.org/10.48550/arXiv.2609.25078). URL: <https://arxiv.org/abs/2609.25078v1>.

*Commentary.*

The half-plane x < 0 remains zero by induction on time, since the polynomial vanishes when its left and center inputs are zero. From time 1 onward, every length-seven window starting at x ≥ −5 lies in one of three finite languages, indexed by time modulo three. They have sizes 35, 37 and 38. Every compatible length-nine word maps to a word in the next language. The distinguished window at x = −5 cycles through 0000011, 0000020 and 0000021 at phases 1, 2 and 0; its left input is zero, and its neighboring window controls the right input. Induction preserves both the language membership and this boundary word. Its sixth letter is the value at x = 0, yielding 1, 2 and 2 in the three phases.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.A`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.result`
