# Minimal Predictive Summary

## Abstract

Every future-sufficient linear summary factors uniquely onto the predictive space.

**Theorem 1.1 (Future sufficiency forces the minimal dimension bound).**

$$\forall d, r, W,\\{}H: \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianTraceZero}(d), \operatorname{HermitianTraceZero}(d)), E: \operatorname{Fin}(r+1) \to\operatorname{HermitianTraceZero}(d),\\{}L: \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianTraceZero}(d), W),\\{}(\forall x, y, L(x) = L(y) \Rightarrow\\{}\forall n\in \mathbb{N}, a\in \operatorname{Fin}(r+1), \langle x, H^{n}(E(a))\rangle_{\mathbb{R}} = \langle y, H^{n}(E(a))\rangle_{\mathbb{R}}) \Rightarrow\\{}(\exists! h: \operatorname{LinearMap}(\mathbb{R}, \operatorname{range}(L), \operatorname{predictiveSpace}(H, E)), \operatorname{predictiveProjection}(H, E) = h \circ \operatorname{rangeRestrict}(L)) \land\\{}\operatorname{finrank}(\mathbb{R}, \operatorname{predictiveSpace}(H, E)) \leq \operatorname{finrank}(\mathbb{R}, \operatorname{range}(L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/MinimalPredictiveSummary.minimal_predictive_summary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the imported real HermitianTraceZero(d) space. The predictive space is constructed as the real span of every centered effect after every finite iterate of the given Heisenberg map.

The hypothesis states directly that equality under the linear summary forces equality of every such future inner-product coordinate for all carrier vectors. Hence the summary kernel lies in the kernel of the canonical orthogonal projection onto the predictive space.

The first isomorphism theorem then constructs a factor on the attainable summary range. Surjectivity of the orthogonal projection makes this factor surjective, giving the displayed finrank lower bound, while range witnesses prove uniqueness.

Repository search found the canonical trace-zero carrier and finite tower, but no vector-valued range factorization with this dimension clause. Pinned Mathlib supplies projectionOnto, liftQ, quotKerEquivRange, and finrank_le_finrank_of_surjective, all applied by the proof.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/MinimalPredictiveSummary.minimal_predictive_summary`
- Dependency: [D5/S3/Quantum/Fibers/CenteredEffectTowerStability](CenteredEffectTowerStability.md)
