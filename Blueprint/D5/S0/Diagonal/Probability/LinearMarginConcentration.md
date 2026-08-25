# Linear Margin and Typical Distance Density

## Abstract

Diagonal listings satisfy the corrected linear-margin bound and concentrate at the typical distance density.

**Theorem 1.1 (Linear margins concentrate at the nonzero-choice density).**

$$\begin{gathered}\forall Y: \operatorname{Type}, f: Y \to Y, alpha \in \mathbb{R},\\{}(\operatorname{Fintype}\left(Y\right) \land 2 \leq \operatorname{card}\left(Y\right) \land 0 < alpha \land alpha < \frac{\operatorname{card}\left(Y\right) - 1}{\operatorname{card}\left(Y\right)}) \Rightarrow\\{}(\forall A: \operatorname{Type}, (\operatorname{Fintype}\left(A\right) \land 2 \leq \operatorname{card}\left(A\right) \land \frac{alpha \cdot \operatorname{card}\left(A\right)}{\operatorname{card}\left(A\right) - 1} < \frac{\operatorname{card}\left(Y\right) - 1}{\operatorname{card}\left(Y\right)}) \Rightarrow \operatorname{marginFailureProbability}\left(f, alpha\right) \leq \operatorname{linearMarginBound}\left(\operatorname{card}\left(Y\right), alpha, \operatorname{card}\left(A\right)\right)) \land\\{}(\lim_{A\to\infty}\operatorname{linearMarginBound}\left(\operatorname{card}\left(Y\right), alpha, A\right)=0) \land\\{}(\lim_{A\to\infty}\operatorname{marginFailureProbability}\left(f, alpha\right)=0) \land\\{}(\forall beta \in \mathbb{R}, (\frac{\operatorname{card}\left(Y\right) - 1}{\operatorname{card}\left(Y\right)} < beta \land beta < 1) \Rightarrow \lim_{A\to\infty}\operatorname{typicalDensityFailureProbability}\left(f, alpha, beta\right)=0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Probability/LinearMarginConcentration.linear_margin_concentration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite value type Y of cardinality at least two, a self-map f, and a lower density alpha strictly between zero and (card(Y)-1)/card(Y), the first conjunct gives the corrected finite KL-Chernoff bound for every finite address type satisfying the displayed threshold restriction.

The second conjunct states that the corrected bound tends to zero. The third states that the actual probability of any row missing the linear margin also tends to zero, which is the asymptotically almost-sure linear escape clause. The fourth quantifies over every upper density between the typical density and one and states two-sided concentration of the minimum-distance density.

The proof directly combines the four frozen diagonal-margin theorems. It introduces no replacement probability, distance, divergence, or carrier.

## References

- Truth anchor: `D5/S0/Diagonal/Probability/LinearMarginConcentration.linear_margin_concentration`
- Dependency: [D5/S0/Diagonal/TypicalDensity](../TypicalDensity.md)
