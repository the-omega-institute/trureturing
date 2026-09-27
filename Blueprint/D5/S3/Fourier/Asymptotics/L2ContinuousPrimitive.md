# Continuous Integral Versions of L2 Primitives

## Abstract

A continuous L2 derivative yields a measurable primitive with continuous paths on its original finite measure space.

**Theorem 1.1 (A common set of continuous paths).**

$$\mathrm{universe} ell; \forall Omega: \operatorname{Type}\left(ell\right), (\forall mOmega: \operatorname{MeasurableSpace}\left(Omega\right), (\forall P: \operatorname{Measure}\left(Omega, mOmega\right), (\forall finiteP: \operatorname{IsFiniteMeasure}\left(P\right), (\forall f: \mathbb{R} \to \operatorname{Lp}\left(\mathbb{R}, 2, P\right), (\forall u: \mathbb{R} \to \operatorname{Lp}\left(\mathbb{R}, 2, P\right), (\forall g: \mathbb{R} \to \left(Omega \to \mathbb{R}\right), (\forall hu: \operatorname{Continuous}\left(u\right), (\forall hg: \operatorname{Measurable}\left(\operatorname{uncurry}\left(g\right)\right), (\forall heq: \forall t: \mathbb{R}, (\operatorname{AlmostEverywhere}\left(P, (z: Omega \mapsto \operatorname{g}\left(t, z\right) = \operatorname{eval}\left(\operatorname{u}\left(t\right), z\right))\right)), (\forall hf: \forall t: \mathbb{R}, (\operatorname{f}\left(t\right) = \operatorname{f}\left(0\right) + \operatorname{intervalIntegral}\left(u, 0, t, volume\right)), (\mathrm{let} X: \mathbb{R} \to \left(Omega \to \mathbb{R}\right) := (t: \mathbb{R} \mapsto (z: Omega \mapsto \operatorname{eval}\left(\operatorname{f}\left(0\right), z\right) + \operatorname{intervalIntegral}\left((s: \mathbb{R} \mapsto \operatorname{g}\left(s, z\right)), 0, t, volume\right))); (\operatorname{Measurable}\left(\operatorname{uncurry}\left(X\right)\right) \land \left(\operatorname{AlmostEverywhere}\left(P, (z: Omega \mapsto \operatorname{Continuous}\left((t: \mathbb{R} \mapsto \operatorname{X}\left(t, z\right))\right))\right) \land \forall t: \mathbb{R}, (\operatorname{AlmostEverywhere}\left(P, (z: Omega \mapsto \operatorname{X}\left(t, z\right) = \operatorname{eval}\left(\operatorname{f}\left(t\right), z\right))\right))\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/L2ContinuousPrimitive.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be any measurable space and P a finite measure. Let f and u map the whole real line to real L2(P), with u continuous. Let g(t,z) be jointly measurable and, for every fixed t, equal P-almost everywhere to the chosen representative u(t)(z). Assume, for every real t, f(t)=f(0)+the Bochner integral of u from 0 to t.

Define X(t,z)=f(0)(z)+the oriented integral of g(s,z) from 0 to t. Then X is jointly measurable, its paths on the whole real line are continuous on one common P-almost-everywhere set, and at every fixed t it equals f(t)(z) P-almost everywhere. Equality to arbitrary chosen representatives is only asserted at each fixed time, not simultaneously at all times.

Continuity of u and finiteness of P imply integrability of g on every compact time interval times Omega. Testing against indicator functions in L2 and using Fubini identifies the representative of each Bochner integral. A countable exhaustion by bounded intervals gives one set of locally integrable sample functions, hence continuous primitives. Neither compact product integrability nor separate Bochner integrability is an additional hypothesis.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/L2ContinuousPrimitive.result`
