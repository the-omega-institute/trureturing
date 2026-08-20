# Minimal Suspension Continuum

## Abstract

A minimal compact suspension with positive continuous roof is compact and connected.

**Theorem 1.1 (A minimal positive-roof suspension is a continuum).**

$$\forall K: \operatorname{Type},\ [\operatorname{MetricSpace}(K)], [\operatorname{CompactSpace}(K)], [\operatorname{Nonempty}(K)],\ T: \operatorname{Homeomorph}(K, K), r: K \to \mathbb{R},\\h: (\forall x, 0 < r(x)),\\\operatorname{Continuous}(r) \land\\(\forall x, \operatorname{DenseRange}((n\in \mathbb{N} \mapsto T^n(x)))) \Rightarrow\\\operatorname{IsCompact}(\operatorname{univ}(Suspension(T, r, h))) \land\\\operatorname{IsConnected}(\operatorname{univ}(Suspension(T, r, h))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/MinimalSuspensionContinuum.minimal_suspension_compact_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The suspension is constructed from the compact normalized leaf domain. Its physical height at (x,u) is u times r(x), and the upper endpoint at x is identified with the lower endpoint at T(x). Strict positivity makes this physical endpoint relation a setoid.

Each base point determines a connected interval fiber. Consecutive fibers along a forward T-orbit meet at the identified endpoint, so their union is connected. Minimality makes the orbit dense; the product and quotient density lemmas make the fiber union dense in the whole suspension, whose connected closure is therefore all.

Compactness is inherited from the compact fundamental domain through the quotient. Repository and pinned-Mathlib searches found no packaged mapping-torus theorem; the proof directly applies the exact compact quotient, connected-chain, dense-product, quotient-density, and connected-closure results.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/MinimalSuspensionContinuum.minimal_suspension_compact_connected`
