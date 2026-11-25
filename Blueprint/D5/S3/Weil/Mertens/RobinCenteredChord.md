# Signed transfer and two-sided mass approximation

## Abstract

Centered Robin chord quadrature

Write u(t)=t log(t), E(t)=ψ(t)−t, and A(t)=(1+log(t))/(t log(t))². Here A is the activation density and R is the Robin ramp. M(a,b) is the weighted negative mass of the tail of the Chebyshev kernel E(t)/t².

**Theorem 1.1 (The two chord weights have equal scaled mass).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; 1 < a \Rightarrow \left(\left(a \le x \land x \le b\right) \Rightarrow \left(p + q = 1 \Rightarrow \left(p \cdot \operatorname{u}\left(a\right) + q \cdot \operatorname{u}\left(b\right) = \operatorname{u}\left(x\right) \Rightarrow \left(p \cdot \operatorname{u}\left(a\right) \cdot \int_{a}^{x} \operatorname{A}\left(t\right) dt = \operatorname{C}\left(p, a, x\right) \land \left(q \cdot \operatorname{u}\left(b\right) \cdot \int_{x}^{b} \operatorname{A}\left(t\right) dt = \operatorname{C}\left(p, a, x\right) \land \frac{q \cdot (\operatorname{u}\left(b\right) - \operatorname{u}\left(x\right))}{\operatorname{u}\left(x\right)} = \operatorname{C}\left(p, a, x\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinCenteredChord.chord_weight_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write C(p,a,x)=p(u(x)−u(a))/u(x). The primitive −1/u gives the activation mass of each interval. The chord coordinate identity makes the left and right scaled masses agree.

**Theorem 1.2 (Exact signed transfer for every centering constant).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; 2 \le a \Rightarrow \left(\left(a \le x \land x \le b\right) \Rightarrow \left(p + q = 1 \Rightarrow \left(p \cdot \operatorname{u}\left(a\right) + q \cdot \operatorname{u}\left(b\right) = \operatorname{u}\left(x\right) \Rightarrow \left(\forall m \in \mathbb{R},\; \operatorname{R}\left(x\right) - p \cdot \operatorname{R}\left(a\right) - q \cdot \operatorname{R}\left(b\right) = p \cdot \operatorname{u}\left(a\right) \cdot \int_{a}^{x} (\operatorname{E}\left(t\right) - m) \cdot \operatorname{A}\left(t\right) dt - q \cdot \operatorname{u}\left(b\right) \cdot \int_{x}^{b} (\operatorname{E}\left(t\right) - m) \cdot \operatorname{A}\left(t\right) dt\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinCenteredChord.ramp_chord_centered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ramp is minus u times the weighted tail. Subtract the neighboring tails to obtain the two local Chebyshev integrals. Equal scaled masses cancel the contribution of the same constant m on the two sides.

**Theorem 1.3 (The Chebyshev range controls the pointwise error).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall L \in \mathbb{R},\; \forall U \in \mathbb{R},\; 2 \le a \Rightarrow \left(\left(a \le x \land x \le b\right) \Rightarrow \left(0 \le p \Rightarrow \left(0 \le q \Rightarrow \left(p + q = 1 \Rightarrow \left(p \cdot \operatorname{u}\left(a\right) + q \cdot \operatorname{u}\left(b\right) = \operatorname{u}\left(x\right) \Rightarrow \left(\left(\forall t \in \mathbb{R},\; \left(a \le t \land t \le b\right) \Rightarrow \left(L \le \operatorname{E}\left(t\right) \land \operatorname{E}\left(t\right) \le U\right)\right) \Rightarrow \left|\operatorname{R}\left(x\right) - p \cdot \operatorname{R}\left(a\right) - q \cdot \operatorname{R}\left(b\right)\right| \le (U - L) \cdot \operatorname{C}\left(p, a, x\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinCenteredChord.abs_ramp_chord_error_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Center at the lower bound L. Each scaled integral is between zero and (U−L)C(p,a,x), so their signed difference has absolute value at most (U−L)C(p,a,x).

**Theorem 1.4 (Coordinate coefficient and its uniform bound).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; 1 < a \Rightarrow \left(a < b \Rightarrow \left(\left(a \le x \land x \le b\right) \Rightarrow \left(p + q = 1 \Rightarrow \left(p \cdot \operatorname{u}\left(a\right) + q \cdot \operatorname{u}\left(b\right) = \operatorname{u}\left(x\right) \Rightarrow \left(\operatorname{C}\left(p, a, x\right) = \frac{(\operatorname{u}\left(x\right) - \operatorname{u}\left(a\right)) \cdot (\operatorname{u}\left(b\right) - \operatorname{u}\left(x\right))}{\operatorname{u}\left(x\right) \cdot (\operatorname{u}\left(b\right) - \operatorname{u}\left(a\right))} \land \operatorname{C}\left(p, a, x\right) \le \frac{\operatorname{u}\left(b\right) - \operatorname{u}\left(a\right)}{4 \cdot \operatorname{u}\left(a\right)}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinCenteredChord.chord_weight_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Solve the chord coordinate identity for p. The product of the two nonnegative gaps in u is at most one quarter of the square of their sum, and u(x)≥u(a)>0.

**Theorem 1.5 (Two-sided bound for the actual weighted negative mass).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall L \in \mathbb{R},\; \forall U \in \mathbb{R},\; \operatorname{exp}\left(1\right) \le a \Rightarrow \left(a < b \Rightarrow \left(b \le 2 \cdot a \Rightarrow \left(\left(\forall t \in \mathbb{R},\; \left(a \le t \land t \le b\right) \Rightarrow \left(L \le \operatorname{E}\left(t\right) \land \operatorname{E}\left(t\right) \le U\right)\right) \Rightarrow \left|\operatorname{M}\left(a, b\right) - \int_{a}^{b} \operatorname{w}\left(t\right) \cdot \operatorname{max}\left(\operatorname{H}\left(a, b, t\right), 0\right) dt\right| \le \frac{3 \cdot (U - L) \cdot (b - a)^{2}}{4 \cdot a^{2} \cdot \operatorname{sqrt}\left(a\right)}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinCenteredChord.abs_mass_sub_chord_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed a and b put Q(a,b,t)=(u(t)−u(a))/(u(b)−u(a)) and H(a,b,t)=(1−Q(a,b,t))R(a)+Q(a,b,t)R(b). The true mass density is w(t) max(R(t),0), where w(t)=(log(t)/(1+log(t)))/(t sqrt(t)). Taking positive parts contracts the pointwise error. Bound w by 1/(a sqrt(a)), bound the coordinate gap by 3(b−a)log(a), and integrate the resulting bound over the cell.

## References

- Truth anchor: `D5/S3/Weil/Mertens/RobinCenteredChord.abs_mass_sub_chord_le`
- Truth anchor: `D5/S3/Weil/Mertens/RobinCenteredChord.abs_ramp_chord_error_le`
- Truth anchor: `D5/S3/Weil/Mertens/RobinCenteredChord.chord_weight_balance`
- Truth anchor: `D5/S3/Weil/Mertens/RobinCenteredChord.chord_weight_coefficient`
- Truth anchor: `D5/S3/Weil/Mertens/RobinCenteredChord.ramp_chord_centered`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](../../Arith/Robin/ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Weil/Mertens/RobinWeightedRamp](RobinWeightedRamp.md)
