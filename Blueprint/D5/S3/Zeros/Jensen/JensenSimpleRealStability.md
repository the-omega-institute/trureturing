# Simple real polynomial stability

## Abstract

Simple real roots persist under uniform complex polynomial approximation.

**Theorem 1.1 (All roots and a common derivative margin).**

$$\begin{aligned}\forall p, m, Q, \operatorname{Monic}\left(p\right) \land \operatorname{degree}\left(p\right)=m\\ \land \operatorname{AllRootsRealSimple}\left(p\right) \land \operatorname{RealOnReal}\left(Q\right) \land \operatorname{ComplexApproximation}\left(Q, p\right)\implies\\\exists R\ge 1, \exists chi>0, \exists N, \forall n\ge N,\\n\ge 1 \land \exists u, \operatorname{Injective}\left(u\right) \land \forall i,\\\operatorname{Q}\left(n, \operatorname{u}\left(i\right)\right)=0 \land \operatorname{abs}\left(\operatorname{u}\left(i\right)\right)\le R \land \operatorname{absDerivative}\left(Q, n, \operatorname{u}\left(i\right)\right)\ge chi\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenSimpleRealStability.simple_real_polynomial_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a monic real polynomial of degree m. Assume every complex root of p is real and its derivative is nonzero. Let Q(n) be complex polynomials taking real values on the real line. For every q>=2 assume positive C and a natural N exist such that, for every n>=N, n>=1 and |Q(n)(z)-p(z)|<=C/sqrt(n) whenever |z|<=q.

Then R>=1, chi>0 and a natural N exist such that every n>=N has m distinct real zeros u(i) of Q(n), indexed injectively by Fin(m), with |u(i)|<=R and |Q(n)'(u(i))|>=chi for every i. The constants are common to all roots and all later n.

The fundamental theorem of algebra supplies the complete root multiset of p. Nonvanishing derivatives make this multiset simple. Small disjoint real intervals around all roots have opposite endpoint signs and a common derivative margin. Complex approximation on a larger disk controls derivatives on contained unit disks by the Cauchy estimate. The intermediate value theorem supplies one real zero in each interval, while separation proves injectivity.

This is the classical persistence of simple real polynomial roots, with a common quantitative derivative margin supplied by the Cauchy estimate and the intermediate value theorem. Every root is retained, including a root at zero, and m=0 is allowed. The statement constructs m simple real zeros of each approximating polynomial; a separate boundary comparison is needed to exclude additional roots in a specified disk.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/JensenSimpleRealStability.simple_real_polynomial_stability`
- Dependency: [D5/S3/Zeros/Jensen/JensenHermiteScaling](JensenHermiteScaling.md)
- Dependency: [D5/S3/Zeros/Jensen/PositiveThreeTermRootReality](PositiveThreeTermRootReality.md)
