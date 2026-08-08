# Diagonal Linear Margin Bound

## Abstract

Finite diagonal listings satisfy a corrected KL-Chernoff linear-margin bound.

**Definition 1.1 (Bernoulli KL divergence).**

Lean statement: `D5/S0/Diagonal/MarginBound.bernoulliKL`

*Formalization.* `D5/S0/Diagonal/MarginBound.bernoulliKL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar Bernoulli divergence is q log(q/p) plus one minus q times log((1-q)/(1-p)). Its local nonnegativity, strict positivity off the diagonal, and continuity are proved on the open unit square.

**Definition 1.2 (Finite margin-failure probability).**

Lean statement: `D5/S0/Diagonal/MarginBound.marginFailureProbability`

*Formalization.* `D5/S0/Diagonal/MarginBound.marginFailureProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The probability is the finite cardinality ratio of listings having some row at Hamming distance below alpha times the address cardinality, divided by the cardinality of all listings.

**Theorem 1.3 (A linear margin has the corrected KL bound).**

$$\operatorname{marginFailureProbability}\left(f, \mathit{alpha}\right) \le \operatorname{card}\left(A\right) \cdot \operatorname{exp}\left(\left(0 - \left(\operatorname{card}\left(A\right) - 1\right)\right) \cdot \operatorname{bernoulliKL}\left(\frac{\mathit{alpha} \cdot \operatorname{card}\left(A\right)}{\operatorname{card}\left(A\right) - 1}, \frac{\operatorname{card}\left(Y\right) - 1}{\operatorname{card}\left(Y\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/MarginBound.linear_margin_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite address and value types with cardinalities at least two, positive alpha, and q less than p, the failure probability is at most the address cardinality times exp(-(card(A)-1) KL(q||p)), where q is alpha card(A)/(card(A)-1) and p is (card(Y)-1)/card(Y). The corrected q is retained in the displayed exponent. The proof combines the frozen minimum-distance tail, a rowwise union bound, the exact binomial moment-generating function, and the KL-Chernoff lower tail.

The limit as the address cardinality tends to infinity and the two-sided concentration of minimum distance density are deferred; neither asymptotic statement is claimed by this finite theorem.

## References

- Truth anchor: `D5/S0/Diagonal/MarginBound.bernoulliKL`
- Truth anchor: `D5/S0/Diagonal/MarginBound.linear_margin_bound`
- Truth anchor: `D5/S0/Diagonal/MarginBound.marginFailureProbability`
- Dependency: [D5/S0/Diagonal/DistanceProfile](DistanceProfile.md)
