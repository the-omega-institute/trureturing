# A Forbidden Zero Pattern in Finch's Ternary Recurrence

## Abstract

At lag 61 the ternary recurrence never attains the proposed fifteen-gap zero run.

**Definition 1.1 (Universal attainment of the upper bound).**

$$claim \Leftrightarrow (\forall k \in \mathbb{N},\; 2 \le k \Rightarrow ((\exists x \in \mathbb{N} \to \operatorname{ZMod}\left(3\right),\; (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(n < k \Rightarrow x\left(n\right) = 0\right)) \land \left(x\left(k\right) = 1 \land (\forall n \in \mathbb{N},\; k + 1 \le n \Rightarrow x\left(n\right) = x\left(n - 1\right) + x\left(n - k\right)^{2})\right)) \land (\forall x \in \mathbb{N} \to \operatorname{ZMod}\left(3\right),\; \left((\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(n < k \Rightarrow x\left(n\right) = 0\right)) \land \left(x\left(k\right) = 1 \land (\forall n \in \mathbb{N},\; k + 1 \le n \Rightarrow x\left(n\right) = x\left(n - 1\right) + x\left(n - k\right)^{2})\right)\right) \Rightarrow \left((k \bmod 4 = 0 \lor k \bmod 4 = 1) \Rightarrow \left(0 < \operatorname{Nat}.\operatorname{div}\left(k - 1, 4\right) \Rightarrow \left(\exists r \in \mathbb{N},\; k + 1 \le r \land \left(1 \le \operatorname{Nat}.\operatorname{div}\left(k - 1, 4\right) \land \left((\forall i \in \mathbb{N},\; i \le \operatorname{Nat}.\operatorname{div}\left(k - 1, 4\right) \Rightarrow x\left(r + 4 \cdot i\right) = 0) \land (\forall n \in \mathbb{N},\; r < n \Rightarrow \left(n < r + 4 \cdot \operatorname{Nat}.\operatorname{div}\left(k - 1, 4\right) \Rightarrow \left(\left(n - r\right) \bmod 4 \ne 0 \Rightarrow x\left(n\right) \ne 0\right)\right))\right)\right)\right)\right)\right))))$$

*Formalization.* `D5/S1/Recurrence/FinchZeroRunsModThree.claim` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. DOI: [10.48550/arXiv.2610.34300](https://doi.org/10.48550/arXiv.2610.34300). URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

Remark 20, p. 8: “Empirical data suggest that Theorem 16 is the best possible. For instance, runs with exactly ⌊(k−1)/4⌋ gaps were observed for k = 245, 297, 333 (where k ≡ 1) and for k = 288, 320, 340 (where k ≡ 0). Proving that such maximal runs always occur would be a nice exercise in experimentation, but maybe a hard one in theory!” The proposition states the universal attainment reading: source sequences exist for every k≥2, and every such sequence attains the bound when k modulo four is zero or one and the gap count is positive. Nat.div is natural-number division, so (k−1) div 4 is the floor in the source. A run has g+1 zeros and g gaps; maximal here refers to attaining the bound, without an extension condition on either endpoint.

**Theorem 1.2 (The universal attainment assertion is false).**

$$\neg (\forall k \in \mathbb{N},\; 2 \le k \Rightarrow ((\exists x \in \mathbb{N} \to \operatorname{ZMod}\left(3\right),\; (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(n < k \Rightarrow x\left(n\right) = 0\right)) \land \left(x\left(k\right) = 1 \land (\forall n \in \mathbb{N},\; k + 1 \le n \Rightarrow x\left(n\right) = x\left(n - 1\right) + x\left(n - k\right)^{2})\right)) \land (\forall x \in \mathbb{N} \to \operatorname{ZMod}\left(3\right),\; \left((\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(n < k \Rightarrow x\left(n\right) = 0\right)) \land \left(x\left(k\right) = 1 \land (\forall n \in \mathbb{N},\; k + 1 \le n \Rightarrow x\left(n\right) = x\left(n - 1\right) + x\left(n - k\right)^{2})\right)\right) \Rightarrow \left((k \bmod 4 = 0 \lor k \bmod 4 = 1) \Rightarrow \left(0 < \operatorname{Nat}.\operatorname{div}\left(k - 1, 4\right) \Rightarrow \left(\exists r \in \mathbb{N},\; k + 1 \le r \land \left(1 \le \operatorname{Nat}.\operatorname{div}\left(k - 1, 4\right) \land \left((\forall i \in \mathbb{N},\; i \le \operatorname{Nat}.\operatorname{div}\left(k - 1, 4\right) \Rightarrow x\left(r + 4 \cdot i\right) = 0) \land (\forall n \in \mathbb{N},\; r < n \Rightarrow \left(n < r + 4 \cdot \operatorname{Nat}.\operatorname{div}\left(k - 1, 4\right) \Rightarrow \left(\left(n - r\right) \bmod 4 \ne 0 \Rightarrow x\left(n\right) \ne 0\right)\right))\right)\right)\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FinchZeroRunsModThree.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. DOI: [10.48550/arXiv.2610.34300](https://doi.org/10.48550/arXiv.2610.34300). URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

At k=61, the recurrence has a source sequence whose packed ternary states start at one and advance by shifting sixty retained digits and appending the quadratic recurrence value. A list of 9685 states contains the initial state and is closed under this transition: its last transition returns to entry 739. Every future state therefore belongs to the list. None has zeros exactly at the multiples of four among its lowest 45 digits. A fifteen-gap run beginning at r≥62 would produce that forbidden pattern in the state after r−17 transitions. This contradicts universal attainment at k=61, where the proposed bound is fifteen. The statement refutes attainment and makes no assertion against the upper bound of Theorem 16.

## References

- Truth anchor: `D5/S1/Recurrence/FinchZeroRunsModThree.claim`
- Truth anchor: `D5/S1/Recurrence/FinchZeroRunsModThree.result`
- Dependency: [D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation](../../S0/Certificates/FinchConjecture23CaptureOffsetRefutation.md)
