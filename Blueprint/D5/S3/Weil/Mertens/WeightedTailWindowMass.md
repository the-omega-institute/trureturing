# Transport across a finite window

## Abstract

Negative mass under finite weighted-tail inversion

Let Q(k,x) be the tail of k from x to infinity and W(k,x) its tail weighted by (1+log(t))/log(t)^2. Write a(t)=log(t)^2/(1+log(t)), v=a', and E(k,B)=Q(k,B)-a(B)W(k,B). The nonlocal coefficient is K(Y,X,t)=2(sqrt(min(t,X))-sqrt(Y))v(t).

**Theorem 1.1 (The local, nonlocal, and endpoint contributions).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \forall Y \in \mathbb{R},\; \forall X \in \mathbb{R},\; \forall B \in \mathbb{R},\; \forall c \in \mathbb{R},\; 2 \le Y \Rightarrow \left(Y \le X \Rightarrow \left(X \le B \Rightarrow \left(\operatorname{IntegrableOn}\left(k, \operatorname{Ioi}\left(Y\right)\right) \Rightarrow \left(\operatorname{IntegrableOn}\left(g, \operatorname{Icc}\left(Y, B\right)\right) \Rightarrow \left(\left(\forall t \in \mathbb{R},\; \left(Y \le t \land t \le B\right) \Rightarrow 0 \le \operatorname{g}\left(t\right)\right) \Rightarrow \left(\left(\forall t \in \mathbb{R},\; \left(Y \le t \land t \le B\right) \Rightarrow -\operatorname{W}\left(k, t\right) \le \operatorname{g}\left(t\right)\right) \Rightarrow \left(0 \le c \Rightarrow \left(-\operatorname{E}\left(k, B\right) \le c \Rightarrow \int_{Y}^{X} \frac{\operatorname{max}\left(-\operatorname{Q}\left(k, x\right), 0\right)}{\operatorname{sqrt}\left(x\right)} dx \le \int_{Y}^{X} \frac{\operatorname{a}\left(t\right)}{\operatorname{sqrt}\left(t\right)} \cdot \operatorname{g}\left(t\right) dt + \int_{Y}^{B} \operatorname{K}\left(Y, X, t\right) \cdot \operatorname{g}\left(t\right) dt + 2 \cdot (\operatorname{sqrt}\left(X\right) - \operatorname{sqrt}\left(Y\right)) \cdot c\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedTailWindowMass.negative_mass_le_of_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Invert at each x and split off the terminal defect at B. Integrating the nonlocal term over Y ≤ x ≤ X and x ≤ t ≤ B gives K by integrating 1/sqrt(x) from Y to min(t,X). The constant endpoint majorant c is paid over the interval from Y to X.

**Theorem 1.2 (The bound by the weighted negative mass).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall Y \in \mathbb{R},\; \forall X \in \mathbb{R},\; \forall B \in \mathbb{R},\; 2 \le Y \Rightarrow \left(Y \le X \Rightarrow \left(X \le B \Rightarrow \left(\operatorname{IntegrableOn}\left(k, \operatorname{Ioi}\left(Y\right)\right) \Rightarrow \int_{Y}^{X} \frac{\operatorname{max}\left(-\operatorname{Q}\left(k, x\right), 0\right)}{\operatorname{sqrt}\left(x\right)} dx \le \operatorname{F}\left(Y\right) \cdot \operatorname{M}\left(k, Y, B\right) + 2 \cdot (\operatorname{sqrt}\left(X\right) - \operatorname{sqrt}\left(Y\right)) \cdot \operatorname{max}\left(-\operatorname{E}\left(k, B\right), 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedTailWindowMass.negative_mass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write M(k,Y,B) for the integral of (a(t)/sqrt(t)) max(-W(k,t),0) from Y to B and F(Y)=1+2(log(Y)+2)/(log(Y)(1+log(Y))). Use the positive part of -W as the majorant. Its local term can be extended to B, and the kernel K is bounded by (F(Y)-1)a(t)/sqrt(t).

## References

- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailWindowMass.negative_mass_le`
- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailWindowMass.negative_mass_le_of_majorant`
- Dependency: [D5/S3/Weil/Mertens/WeightedTailInverse](WeightedTailInverse.md)
