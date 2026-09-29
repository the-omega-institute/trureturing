# Jointly Measurable L2 Versions

## Abstract

A Lipschitz curve in real L2 has a jointly measurable version on its original measure space.

**Theorem 1.1 (Dyadic representative construction).**

$$\mathrm{universe} ell; \forall Omega: \operatorname{Type}\left(ell\right), (\forall mOmega: \operatorname{MeasurableSpace}\left(Omega\right), (\forall P: \operatorname{Measure}\left(Omega, mOmega\right), (\forall f: \mathbb{R} \to \operatorname{Lp}\left(\mathbb{R}, 2, P\right), (\forall K: \mathbb{R}_{\ge0}, (\forall hf: \operatorname{LipschitzWith}\left(K, f\right), (\exists X: \mathbb{R} \to \left(Omega \to \mathbb{R}\right), (\operatorname{Measurable}\left(\operatorname{uncurry}\left(X\right)\right) \land \forall t: \mathbb{R}, (\operatorname{AlmostEverywhere}\left(P, (z: Omega \mapsto \operatorname{X}\left(t, z\right) = \operatorname{eval}\left(\operatorname{f}\left(t\right), z\right))\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/L2MeasurableVersion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be any measurable space, P any measure on Omega, K a nonnegative real number, and f a K-Lipschitz map from the real line to real L2(P). No finiteness or probability assumption on P is needed. The notation f(t)(z) uses the chosen measurable representative of the L2 class.

There is a function X(t,z) measurable for the product sigma-algebra such that, at each fixed real time t, X(t,z)=f(t)(z) for P-almost every z. The exceptional set may depend on t. The conclusion does not assert sample continuity or equality at every time on one common set.

Approximate time t by floor(2^n t)/2^n. Each approximation uses countably many measurable representatives and is jointly measurable. The L2 errors are bounded by K times 2^(-n), hence summable. At every fixed time their representatives converge almost everywhere to f(t). Taking the totalized pointwise limit gives the required jointly measurable X.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/L2MeasurableVersion.result`
