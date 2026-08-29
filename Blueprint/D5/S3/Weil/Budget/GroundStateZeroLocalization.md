# Ground-State Zero Localization

## Abstract

Vague residual-spectrum convergence forces eventual ground-transform zeros near each canonical zero ordinate.

**Theorem 1.1 (Residual supports localize ground-transform zeros).**

$$\begin{aligned}\forall Z: \operatorname{ZeroData}(), n: \mathbb{N},\\mu: \mathbb{N} \to \operatorname{Measure}(\mathbb{R}), F: \mathbb{N} \to \mathbb{R} \to \mathbb{C},\\U: \operatorname{Set}(\mathbb{R}), \operatorname{IsOpen}(U) \land \operatorname{mem}(\operatorname{im}(\operatorname{zero}(Z, n)), U) \land \forall j \in \mathbb{N},\; \operatorname{support}(\operatorname{apply}(mu, j)) \subseteq \left\{\operatorname{apply}(\operatorname{apply}(F, j), xi) = 0 \mid xi \in \mathbb{R}\right\} \land\\\forall phi \in \mathbb{R} \to \mathbb{R},\; \operatorname{Continuous}(phi) \land \operatorname{HasCompactSupport}(phi) \land (\forall xi \in \mathbb{R},\; 0 \leq \operatorname{apply}(phi, xi)) \Rightarrow \operatorname{Tendsto}((j: \mathbb{N} \mapsto \operatorname{lintegral}(\operatorname{apply}(mu, j), (xi: \mathbb{R} \mapsto \operatorname{ofReal}(\operatorname{apply}(phi, xi))))), \operatorname{atTop}(), \operatorname{nhds}(\operatorname{lintegral}(\operatorname{zeroCountingMeasure}(Z), (xi: \mathbb{R} \mapsto \operatorname{ofReal}(\operatorname{apply}(phi, xi)))))) \Rightarrow\\\operatorname{EventuallyAtTop}((j: \mathbb{N} \mapsto \operatorname{Nonempty}(\operatorname{inter}(\left\{\operatorname{apply}(\operatorname{apply}(F, j), xi) = 0 \mid xi \in \mathbb{R}\right\}, U)))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/GroundStateZeroLocalization.ground_state_zero_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target is the canonical multiplicity-weighted real-ordinate measure constructed from ZeroData. Vague convergence is exposed publicly through convergence against every nonnegative compactly supported continuous real test.

A smooth bump supported in the chosen open neighborhood equals one at the selected ordinate. Its target integral is positive because that ordinate has positive canonical multiplicity.

Eventually the residual bump integral is positive, so the neighborhood meets the residual support. The public support inclusion then places a ground-transform zero there. The argument works for any open neighborhood, so a separate isolation premise is unnecessary.

## References

- Truth anchor: `D5/S3/Weil/Budget/GroundStateZeroLocalization.ground_state_zero_localization`
- Dependency: [D5/S3/Weil/ZetaAnalytic/RiemannPoissonDensity](../ZetaAnalytic/RiemannPoissonDensity.md)
