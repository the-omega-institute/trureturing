# Finite Mangoldt ramps and endpoint bounds

## Abstract

Robin weighted-ramp quadrature

Write u(x)=x log(x) and k(t)=(ψ(t)−t)/t². The Robin ramp is R(x)=u(x)E₂Λ(x)−(ψ(x)−x), where E₂Λ is the centered weighted Mangoldt sum. W(x) is the weighted tail of k, M(c,d) is its weighted negative mass on [c,d], and S(x)=max(R(x),0). The constant γ is Euler's constant, and floor denotes the natural floor.

**Theorem 1.1 (The weighted-tail identity).**

$$\forall x \in \mathbb{R},\; 2 \le x \Rightarrow \operatorname{R}\left(x\right) = -\operatorname{u}\left(x\right) \cdot \operatorname{W}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinWeightedRamp.ramp_eq_neg_weightedTail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiply the complete Mertens ledger by u(x) and cancel the Chebyshev endpoint term.

**Theorem 1.2 (The exact finite ramp sum).**

$$\forall x \in \mathbb{R},\; \forall N \in \mathbb{N},\; 2 \le x \Rightarrow \left(\operatorname{floor}\left(x\right) \le N \Rightarrow \operatorname{R}\left(x\right) = \sum_{2 \le n \land n \le N} \operatorname{Lambda}\left(n\right) \cdot \operatorname{max}\left(\frac{\operatorname{u}\left(x\right)}{\operatorname{u}\left(n\right)} - 1, 0\right) - \operatorname{u}\left(x\right) \cdot (\operatorname{log}\left(\operatorname{log}\left(x\right)\right) + gamma) + x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinWeightedRamp.ramp_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ramp at an integer n contributes only for x greater than n. Monotonicity of u on this range permits a common cutoff N at or above the natural floor of x. The endpoint ramp vanishes when x=n.

**Theorem 1.3 (An upper chord in the x log x coordinate).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \operatorname{exp}\left(1\right) \le a \Rightarrow \left(a < b \Rightarrow \left(b \le 2 \cdot a \Rightarrow \left(\left(a \le x \land x \le b\right) \Rightarrow \left(0 \le p \Rightarrow \left(0 \le q \Rightarrow \left(p + q = 1 \Rightarrow \left(p \cdot \operatorname{u}\left(a\right) + q \cdot \operatorname{u}\left(b\right) = \operatorname{u}\left(x\right) \Rightarrow \operatorname{R}\left(x\right) \le p \cdot \operatorname{R}\left(a\right) + q \cdot \operatorname{R}\left(b\right) + \frac{3 \cdot (b - a)^{2}}{a}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinWeightedRamp.ramp_chord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ramp in the common finite sum is a nonnegative Mangoldt weight times the positive part of an affine function of u. The smooth centering term has a tangent remainder between zero and 3(z−a)²/a for a ≤ z ≤ 2a and a ≥ exp(1). The affine tangent cancels in the chord difference.

**Theorem 1.4 (Endpoint samples bound the mass of a subinterval).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall d \in \mathbb{R},\; \operatorname{exp}\left(1\right) \le a \Rightarrow \left(a < b \Rightarrow \left(b \le 2 \cdot a \Rightarrow \left(a \le c \Rightarrow \left(c \le d \Rightarrow \left(d \le b \Rightarrow \operatorname{M}\left(c, d\right) \le \frac{d - c}{a \cdot \operatorname{sqrt}\left(a\right)} \cdot (\operatorname{S}\left(a\right) + \operatorname{S}\left(b\right) + \frac{3 \cdot (b - a)^{2}}{a})\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinWeightedRamp.mass_le_of_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted negative-mass density is (log(x)/(1+log(x))) S(x)/(x sqrt(x)). Bound the first factor by one, bound S(x) by the endpoint samples and chord allowance, then integrate the resulting constant bound over [c,d].

**Theorem 1.5 (Fourth-power cells with curvature allowance 675).**

$$\forall n \in \mathbb{N},\; 6 \le n \Rightarrow \left(\forall c \in \mathbb{R},\; \forall d \in \mathbb{R},\; n^{4} \le c \Rightarrow \left(c \le d \Rightarrow \left(d \le (n + 1)^{4} \Rightarrow \operatorname{M}\left(c, d\right) \le \frac{d - c}{n^{4}} \cdot (\frac{\operatorname{S}\left(n^{4}\right) + \operatorname{S}\left((n + 1)^{4}\right)}{n^{2}} + 675)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinWeightedRamp.quartic_mass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n ≥ 6 the fourth-power cell has width at most 15n³ and its right endpoint is at most twice the left endpoint. With a=n⁴ the chord allowance is at most 675n² and a sqrt(a)=n⁶. The subinterval length therefore multiplies the normalized samples and allowance by (d−c)/n⁴.

## References

- Truth anchor: `D5/S3/Weil/Mertens/RobinWeightedRamp.mass_le_of_cell`
- Truth anchor: `D5/S3/Weil/Mertens/RobinWeightedRamp.quartic_mass_le`
- Truth anchor: `D5/S3/Weil/Mertens/RobinWeightedRamp.ramp_chord`
- Truth anchor: `D5/S3/Weil/Mertens/RobinWeightedRamp.ramp_eq_neg_weightedTail`
- Truth anchor: `D5/S3/Weil/Mertens/RobinWeightedRamp.ramp_eq_sum`
- Dependency: [D5/S3/Arith/Robin/CompleteMertensPeak](../../Arith/Robin/CompleteMertensPeak.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedTailWindowMass](WeightedTailWindowMass.md)
