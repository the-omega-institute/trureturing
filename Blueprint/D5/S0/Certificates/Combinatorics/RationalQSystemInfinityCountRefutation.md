# Refutation of the rational Q-system infinite-root count

## Abstract

Hou--Jiang--Miao's root-of-unity primitive-count formula is negative at the admissible triple (26,11,1), so it cannot be a natural-number count.

**Definition 1.1 (The proposed primitive-count expression).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{formula}\left(L, M, n\right) = (\operatorname{Nat}.\operatorname{choose}\left(L, M - n\right): \mathbb{Z}) - \sum_{x \in \operatorname{Finset}.\operatorname{range}\left(M - n\right)} (\operatorname{Nat}.\operatorname{choose}\left(L, x\right): \mathbb{Z})$$

*Formalization.* `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.formula` (`✓ std3`).

*Citation.* J. Hou, Y. Jiang, Y. Miao (2024). *Rational Q-systems at Root of Unity I. Closed Chains*. DOI: [10.21468/SciPostPhys.16.5.129](https://doi.org/10.21468/SciPostPhys.16.5.129). URL: <https://arxiv.org/abs/2310.14966>.

*Commentary.*

Appendix C, equation (C.2), page 35: "N^{pri}_{±∞}(L, M, n_±) = \binom{L}{M − n_±} − \sum_{x=0}^{M−n_±−1} \binom{L}{x}, (C.2)". The Lean formula uses Int subtraction after casting each binomial coefficient; Finset.range(M − n) enumerates x = 0 through M − n − 1.

**Definition 1.2 (The admissible root-of-unity scope).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{Admissible}\left(L, M, n\right)) \Leftrightarrow ((\operatorname{Even}\left(L\right)) \land ((1 \le M) \land ((2 \cdot M \le L) \land ((1 \le n) \land ((n \le 2) \land ((n \le M) \land ((L: \mathbb{Z}) \equiv 2 \cdot \left((M: \mathbb{Z}) - (n: \mathbb{Z})\right) (\operatorname{mod} 6))))))))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.Admissible` (`✓ std3`).

*Citation.* J. Hou, Y. Jiang, Y. Miao (2024). *Rational Q-systems at Root of Unity I. Closed Chains*. DOI: [10.21468/SciPostPhys.16.5.129](https://doi.org/10.21468/SciPostPhys.16.5.129). URL: <https://arxiv.org/abs/2310.14966>.

*Commentary.*

The source says: "We focus on the case with no twist, i.e. κ = 1 and η = iπ/3 for simplicity." It then considers even L and primitive states with M ≤ L/2. Equations (3.15)--(3.17) give 0 ≤ n ≤ 2 and, for κ = 1 and ℓ₂ = 3, L ≡ 2(M − n) (mod 6). The displayed predicate also records n ≥ 1 and n ≤ M.

**Definition 1.3 (The natural-valued count claim).**

$$(claim) \Leftrightarrow (\exists N \in \mathbb{N} \to \left(\mathbb{N} \to \left(\mathbb{N} \to \mathbb{N}\right)\right),\; \forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{Admissible}\left(L, M, n\right)) \Rightarrow ((N\left(L, M, n\right): \mathbb{Z}) = \operatorname{formula}\left(L, M, n\right)))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.claim` (`✓ std3`).

*Citation.* J. Hou, Y. Jiang, Y. Miao (2024). *Rational Q-systems at Root of Unity I. Closed Chains*. DOI: [10.21468/SciPostPhys.16.5.129](https://doi.org/10.21468/SciPostPhys.16.5.129). URL: <https://arxiv.org/abs/2310.14966>.

*Commentary.*

Appendix C, equation (C.2), page 35 states verbatim: "Before introducing the algorithm, we make the following conjecture for the number of primitive states with infinite Bethe root(s) by observing the numerical results: N^{pri}_{±∞}(L, M, n_±) = \binom{L}{M − n_±} − \sum_{x=0}^{M−n_±−1} \binom{L}{x}, (C.2), when n_± = n_+ = n_− is a solution to (3.15). When there is no solution to (3.15), N^{pri}_{±∞}(L, M, n_±) = 0." A count of primitive states is a natural number, so (C.2) implies this existential natural-valued claim for the true count.

**Theorem 1.4 (The conjecture is refuted).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hou-jiang-miao-2023-root-of-unity-infinity-count-refutation` (refuted) by `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hou-jiang-miao-2023-root-of-unity-infinity-count-refutation","declaration_gid":"D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

At (L, M, n) = (26, 11, 1), all admissibility clauses hold and the formula evaluates to −346802: binom(26,10) = 5,311,735 while the sum through x = 9 is 5,658,537. A natural-number cast to ℤ is nonnegative, so the displayed negative value contradicts the claim. This refutes (C.2) without modelling Bethe states.

## References

- Truth anchor: `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.Admissible`
- Truth anchor: `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.formula`
- Truth anchor: `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.result`
