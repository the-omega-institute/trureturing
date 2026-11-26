# Two-coordinate loss comparison on a closed disk

## Abstract

Sharp lower comparison of the simplex and cube losses for two coordinates.

**Theorem 1.1 (Exact lower loss coefficients).**

$$\begin{aligned}&\forall R,C\in \mathbb{R},0\le R\Rightarrow (\\&(\forall m\in \mathbb{N},p\in \mathbb{R}^{m},v\in \mathbb{C}^{m\times2},\\&((\forall 1\le i\le m,1\le j\le m,p_{i}p_{j}\ge0)\land (\forall 1\le i\le m,p_{i}\neq0\Rightarrow \forall 1\le k\le 2,\left|v_{ik}\right|\le R))\Rightarrow CL(A,p,v)\le L(B,p,v))\\&\Leftrightarrow \begin{cases}C\le \frac{9(3+R^{2})}{16(2+R^{2})}&R\le1\\C=\frac{3}{4}&R>1\end{cases})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhasePairLossFloor.mixed_lower_coefficient_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here A is the simplex overlap, B is the cube overlap and L is the weighted sum of pairwise deficits. Each coordinate of a relative row is the product of one conjugated coordinate and the corresponding coordinate of another row. The relative coordinates of pairs of nonzero weight have modulus at most the square of the disk radius.

Write x for the mean of the two real parts of a relative row. The difference between the cube deficit and C times the simplex deficit is the sum of three terms.

$$
(1-x)(\frac{3+x}{4}-C\frac{4(2+x)}{9})+\frac{(a_{1}-a_{2})^{2}}{16}+C\frac{(b_{1}+b_{2})^{2}}{9}
$$

The a coordinates are real parts and the b coordinates are imaginary parts. At the displayed coefficient for a radius at most one, the factor multiplying one minus x simplifies to the following nonnegative quotient.

$$
\frac{R^{2}-x}{4(2+R^{2})}
$$

All three terms are nonnegative. The simplex deficit is also nonnegative on these disks, which gives the inequality for every smaller coefficient. At three quarters the first term is the square of one minus x divided by twelve, giving the inequality for arbitrary complex relative coordinates.

A single row of weight one with both coordinates equal to a real t has both relative coordinates equal to t squared. The two square remainders vanish. When the radius is below one, taking t equal to the radius forces the stated upper endpoint on C. At radius one, taking t up to one gives the endpoint three quarters. For a radius greater than one, taking t down to one gives the reverse restriction because one minus t squared changes sign.

For probability weights and unit-modulus coordinates the losses are deficits of mixture purity. The larger disks extend the algebraic comparison to arbitrary complex coordinates within the radius bound.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhasePairLossFloor.mixed_lower_coefficient_iff`
- Dependency: [D5/S3/Quantum/PureState/PhaseProductFidelity](PhaseProductFidelity.md)
