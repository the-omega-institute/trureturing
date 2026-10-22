# CoordinatePoisson

## Abstract

Let n be any finite coordinate type and f a continuous complex function on real coordinate space. Assume f is integrable for coordinate Lebesgue measure, its integer translates have summable sup norms on every compact set, and the integer samples of its negative-exponent Fourier integral are summable. Then sum over integer vectors a of f(a) equals sum over integer vectors k of the integral of exp(-2 pi i sum_j k_j x_j) f(x). The unit cube is an actual fundamental domain for integer translations. Local normal convergence justifies descent to the unit torus and dominated sum-integral interchange; the torus Fourier series reconstructs the value at zero.

**Theorem 1.1 (Coordinate Poisson summation).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] \forall f \in \operatorname{ContinuousMap}\left(n \to \mathbb{R}, \mathbb{C}\right),\; \left(\operatorname{Integrable}\left(f, \operatorname{volume}\left(n \to \mathbb{R}\right)\right) \land \left(\left(\forall K \in \operatorname{Compacts}\left(n \to \mathbb{R}\right),\; \operatorname{Summable}\left((a:n \to \mathbb{Z} \mapsto \left\lVert \operatorname{restrict}\left(\operatorname{comp}\left(f, \operatorname{addRight}\left((i:n \mapsto (a(i):\mathbb{R}))\right)\right), K\right) \right\rVert)\right)\right) \land \operatorname{Summable}\left((k:n \to \mathbb{Z} \mapsto \operatorname{integral}\left((x:n \to \mathbb{R} \mapsto \operatorname{exp}\left(-2 \cdot \pi \cdot \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{sum}\left((i:n \mapsto (k(i):\mathbb{R}) \cdot x(i))\right):\mathbb{C})\right) \cdot f(x)), \operatorname{volume}\left(n \to \mathbb{R}\right)\right))\right)\right)\right) \Rightarrow \operatorname{tsum}\left((a:n \to \mathbb{Z} \mapsto f((i:n \mapsto (a(i):\mathbb{R}))))\right) = \operatorname{tsum}\left((k:n \to \mathbb{Z} \mapsto \operatorname{integral}\left((x:n \to \mathbb{R} \mapsto \operatorname{exp}\left(-2 \cdot \pi \cdot \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{sum}\left((i:n \mapsto (k(i):\mathbb{R}) \cdot x(i))\right):\mathbb{C})\right) \cdot f(x)), \operatorname{volume}\left(n \to \mathbb{R}\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CoordinatePoisson.tsum_eq_tsum_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be any finite coordinate type and f a continuous complex function on real coordinate space. Assume f is integrable for coordinate Lebesgue measure, its integer translates have summable sup norms on every compact set, and the integer samples of its negative-exponent Fourier integral are summable. Then sum over integer vectors a of f(a) equals sum over integer vectors k of the integral of exp(-2 pi i sum_j k_j x_j) f(x). The unit cube is an actual fundamental domain for integer translations. Local normal convergence justifies descent to the unit torus and dominated sum-integral interchange; the torus Fourier series reconstructs the value at zero.

## References

- Truth anchor: `D5/S3/Fourier/CoordinatePoisson.tsum_eq_tsum_integral`
