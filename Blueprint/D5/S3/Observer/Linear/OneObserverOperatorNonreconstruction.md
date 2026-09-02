# One-Observer Operator Non-Reconstruction

## Abstract

One squared operator reading is reflection-invariant and cannot reconstruct direction.

**Theorem 1.1 (One observer cannot reconstruct operator direction).**

$$\begin{aligned}\forall V: \operatorname{Type},\\{}[\operatorname{NormedAddCommGroup}(V)] \land [\operatorname{NormedSpace}(\mathbb{R}, V)] \land [\operatorname{Nontrivial}(V)] \Rightarrow\\{}\forall t: \mathbb{R},\\{}(\neg \exists reconstruct: \operatorname{ModuleEnd}(\mathbb{R}, V) \Rightarrow \operatorname{ModuleEnd}(\mathbb{R}, V), \forall H: \operatorname{ModuleEnd}(\mathbb{R}, V), reconstruct(\operatorname{observerSquare}(H, t)) = H) \land\\{}(\forall H: \operatorname{ModuleEnd}(\mathbb{R}, V), \operatorname{observerSquare}(2 t \operatorname{id}(V) - H, t) = \operatorname{observerSquare}(H, t)) \land\\{}(\forall H: \operatorname{ModuleEnd}(\mathbb{R}, V), D: \operatorname{ModuleEnd}(\mathbb{R}, V), (\forall x: V, \operatorname{HasDerivAt}((s: \mathbb{R} \mapsto \operatorname{observerSquare}(H, s)(x)), D(x), t)) \Rightarrow (D = 2 {t \operatorname{id}(V) - H} \land t \operatorname{id}(V) - \frac{1}{2} D = H)) \land\\{}(\forall H: \operatorname{ModuleEnd}(\mathbb{R}, V), h: \mathbb{R}, h \neq 0 \Rightarrow t \operatorname{id}(V) + \frac{1}{2 h} {\operatorname{observerSquare}(H, t) - \operatorname{observerSquare}(H, t + h) + h^{2} \operatorname{id}(V)} = H).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/OneObserverOperatorNonreconstruction.one_observer_operator_nonreconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a nontrivial real normed vector space. For a linear endomorphism H and observer position t, the reading is constructed as observerSquare(H,t) = (H - t id)^2 on the same operator carrier.

No function of that single reading recovers every H. Reflection across t replaces H by 2t id - H and leaves the reading unchanged, giving the explicit ambiguity behind the non-reconstruction clause.

If D is the strong pointwise derivative of the operator bundle at t, derivative uniqueness gives D = 2(t id - H) and hence recovers H. For every nonzero free offset h, the displayed two-position formula likewise reconstructs H from the readings at t and t+h.

Repository, pinned Mathlib, and installed third-party package searches found no exact packaged theorem. The proof uses the endomorphism ring, pointwise polynomial differentiation, and derivative uniqueness.

## References

- Truth anchor: `D5/S3/Observer/Linear/OneObserverOperatorNonreconstruction.one_observer_operator_nonreconstruction`
