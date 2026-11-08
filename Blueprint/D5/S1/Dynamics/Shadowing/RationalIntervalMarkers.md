# Rational Interval Markers

## Abstract

Closed-error rational interval pseudo-orbits have a finite middle block of at most three consecutive integer times, with strict boundary behavior.

Let I=[0,1], f(u)=2u/(1+u), and x:Z->I. The predicate ClosedRationalPseudoOrbit(delta,x) means |f(x(k))-x(k+1)|<=delta for every integer k. Both interval endpoints and equality in the error bound are included. Write B={k : 1/3<x(k)<2/3}. The domain follows the closed, bi-infinite pseudo-orbit convention in Alfonso Artigue, Shadowing maps, arXiv:2504.00171v1, Section 2.1. The marker estimates below concern this rational interval map; they are not attributed to that paper.

**Theorem 1.1 (Three consecutive markers and strict cap boundaries).**

$$\begin{aligned}x:\mathbb{Z}\to [0,1], \Delta\in \mathbb{R}, \Delta\le \frac{1}{256},\\(\forall k\in \mathbb{Z}, |\frac{2x(k)}{1+x(k)}-x(k+1)|\le \Delta)\Rightarrow\\B finite\land ncard(B)\le 3\land\\((\forall k\in \mathbb{Z}, x(k)<\frac{1}{3})\lor (\forall k\in \mathbb{Z}, \frac{2}{3}<x(k))\lor\\(\exists l,r\in \mathbb{Z},l\le r\land r-l\le 2\land\\B=[l,r]\land\\(\forall k\in \mathbb{Z}, k<l\Rightarrow x(k)\le \frac{1}{3})\land (\forall k\in \mathbb{Z}, r<k\Rightarrow \frac{2}{3}\le x(k))))\land\\(\forall k\in \mathbb{Z}, x(k)=\frac{1}{3}\Rightarrow k+1\in B)\land\\(\forall k\in \mathbb{Z}, x(k)=\frac{2}{3}\Rightarrow k-1\in B)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalMarkers.rational_interval_marker_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The interval [l,r] in the conclusion is an integer interval. The final two universal implications hold in every alternative. Since a pseudo-orbit exists, the error parameter is automatically nonnegative. The only supplied scale assumption is delta<=1/256. Exact rational inequalities give: u>=1/3 implies v>1/3; u>=2/3 implies v>2/3; and u<=1/3 implies v<2/3 for every admitted step u to v. On the closed band, the factorization 15u(1-u)-2(1+u)=(2/3-u)(15u-3)>=0 gives f(u)-u>=2/15. Thus v-u>=2/15-delta>1/8. Applying ScalarBandProgress.classify with eta=1/8 and N=3 gives r-l<3, hence at most three markers. At u=1/3 the next value is inside the band. At a value 2/3, its predecessor can lie in neither cap and is therefore marked. These implications make both cap alternatives strict at every time. The theorem supplies finite marker sums and their local index bounds. It establishes no continuous selector, shadowing-map property, or converse counterexample.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalMarkers.rational_interval_marker_classification`
- Dependency: [D5/S1/Dynamics/Shadowing/BiInfiniteBand](BiInfiniteBand.md)
