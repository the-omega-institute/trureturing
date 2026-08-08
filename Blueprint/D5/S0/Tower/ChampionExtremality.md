# Radix Champion Extremality

## Abstract

Integer radix towers have exact odd and even champion arms.

For a radix b, eventualLowerBounds(b) is the set of real r for which there are a real point x and a natural level N such that every Q at least N satisfies r less than or equal to b to the Q times radixDistance(b,Q,x). Its supremum is the supremum over points of the liminf normalized distance, written in the equivalent eventual-tail form used by the Lean declarations.

**Lemma 1.1 (One even-radix step exits the forbidden band).**

$$\forall b \in N,\; \left(b \ge 2 \land \operatorname{Even}\left(b\right)\right) \Rightarrow \left(\forall y \in R,\; \operatorname{radixDistance}\left(b, 0, y\right) > \frac{b}{2 \cdot \left(b + 1\right)} \Rightarrow \operatorname{radixDistance}\left(b, 0, b \cdot y\right) < \frac{b}{2 \cdot \left(b + 1\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ChampionExtremality.one_step_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the nearest-integer distance of y is strictly above the even threshold, multiplying y once by b puts its nearest-integer distance strictly below that threshold. The proof compares to the explicit integers plus or minus b over two and uses the identity b times the threshold equals b over two minus the threshold.

**Theorem 1.2 (The even-radix champion is the half-radix arm).**

$$\forall b \in N,\; \left(b \ge 2 \land \operatorname{Even}\left(b\right)\right) \Rightarrow \operatorname{sSup}\left(\operatorname{eventualLowerBounds}\left(b\right)\right) = \frac{b}{2 \cdot \left(b + 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ChampionExtremality.even_champion_sup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen half-radix arm supplies the lower bound. Any eventual uniform lower bound strictly above it contradicts one-step exit between a tail level and its successor, so the supremum is exactly b divided by two times b plus one.

**Theorem 1.3 (The odd-radix half point has a constant half arm).**

$$\forall b \in N, Q \in N,\; \left(b \ge 2 \land \operatorname{Odd}\left(b\right)\right) \Rightarrow b^{Q} \cdot \operatorname{radixDistance}\left(b, Q, \frac{1}{2}\right) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ChampionExtremality.odd_half_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every power of an odd radix is odd. After scaling the half point, the numerator is therefore one modulo two, so nearest-integer rounding leaves exactly one half at every level, including level zero.

**Theorem 1.4 (The odd-radix champion is one half).**

$$\forall b \in N,\; \left(b \ge 2 \land \operatorname{Odd}\left(b\right)\right) \Rightarrow \operatorname{sSup}\left(\operatorname{eventualLowerBounds}\left(b\right)\right) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/ChampionExtremality.odd_champion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nearest-integer distance is always at most one half, giving the global upper bound. The constant half arm at x equal to one half belongs to the eventual-lower-bound set and attains the bound.

## References

- Truth anchor: `D5/S0/Tower/ChampionExtremality.even_champion_sup`
- Truth anchor: `D5/S0/Tower/ChampionExtremality.odd_champion`
- Truth anchor: `D5/S0/Tower/ChampionExtremality.odd_half_arm`
- Truth anchor: `D5/S0/Tower/ChampionExtremality.one_step_exit`
- Dependency: [D5/S0/Tower/ConstantArms](ConstantArms.md)
