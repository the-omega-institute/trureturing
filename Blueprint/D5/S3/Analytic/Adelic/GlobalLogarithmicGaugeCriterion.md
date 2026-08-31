# Global Logarithmic Gauge Criterion

## Abstract

A global analytic logarithm of the shifted completed-zeta reading exists exactly when every nontrivial zero lies on the critical line.

**Theorem 1.1 (Global analytic logarithms characterize the critical line).**

$$\begin{aligned}rightHalfPlane : \operatorname{Set}\left(\mathbb{C}\right) = \left\{0 < \operatorname{re}\left(z\right) \mid z \in \mathbb{C}\right\}\\shiftedXi : \mathbb{C} \to \mathbb{C} = (z \mapsto \operatorname{xiReading}\left(\frac{1}{2} + z\right))\\criticalLineHypothesis : Prop = \forall s \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(s\right) \Rightarrow \operatorname{re}\left(s\right) = \frac{1}{2}\\(\left(criticalLineHypothesis \Leftrightarrow \left(\exists L \in \mathbb{C} \to \mathbb{C},\; \operatorname{AnalyticOnNhd}\left(\mathbb{C}, L, rightHalfPlane\right) \land \operatorname{EqOn}\left((z \mapsto \operatorname{exp}\left(L\left(z\right)\right)), shiftedXi, rightHalfPlane\right)\right)\right) \land \left(\left(criticalLineHypothesis \Rightarrow \left(\exists L \in \mathbb{C} \to \mathbb{C},\; \operatorname{AnalyticOnNhd}\left(\mathbb{C}, L, rightHalfPlane\right) \land \left(\operatorname{EqOn}\left((z \mapsto \operatorname{exp}\left(L\left(z\right)\right)), shiftedXi, rightHalfPlane\right) \land \operatorname{ContinuousOn}\left((z \mapsto \operatorname{comp}\left(imCLM, \operatorname{restrictScalars}\left(\mathbb{R}, \operatorname{fderiv}\left(\mathbb{C}, L, z\right)\right)\right)), rightHalfPlane\right)\right)\right)\right) \land \left(\forall z0 \in \mathbb{C},\; \left(z0 \in rightHalfPlane \land shiftedXi\left(z0\right) = 0\right) \Rightarrow \left(\left(\neg \left(\exists L \in \mathbb{C} \to \mathbb{C},\; \operatorname{AnalyticOnNhd}\left(\mathbb{C}, L, rightHalfPlane\right) \land \operatorname{EqOn}\left((z \mapsto \operatorname{exp}\left(L\left(z\right)\right)), shiftedXi, rightHalfPlane\right)\right)\right) \land \left(\forall domain \in \operatorname{Set}\left(\mathbb{C}\right), L \in \mathbb{C} \to \mathbb{C},\; \operatorname{EqOn}\left((z \mapsto \operatorname{exp}\left(L\left(z\right)\right)), shiftedXi, domain\right) \Rightarrow \left(\neg z0 \in domain\right)\right)\right)\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/GlobalLogarithmicGaugeCriterion.global_logarithmic_gauge_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed rightHalfPlane, shiftedXi, and criticalLineHypothesis are the three literal let-definitions in the Lean theorem. The shift uses the repository's canonical completed-zeta reading.

The forward direction constructs the logarithm from a primitive of the logarithmic derivative on the open convex half-plane. The reverse direction uses nonvanishing of the complex exponential together with the canonical completed-zeta zero criterion and reflection.

The second conjunct exposes the imaginary real differential of the chosen analytic logarithm and proves it continuous on the whole right half-plane. The final conjunct states both obstructions: a zero rules out the global logarithm and cannot belong to any domain carrying an exponential lift of shiftedXi.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/GlobalLogarithmicGaugeCriterion.global_logarithmic_gauge_criterion`
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
- Dependency: [D5/S3/Zeros/Endpoints/XiEndpointValues](../../Zeros/Endpoints/XiEndpointValues.md)
