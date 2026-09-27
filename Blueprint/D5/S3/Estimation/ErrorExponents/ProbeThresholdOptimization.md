# Probe Threshold Optimization

## Abstract

A positive probability vector has a unique threshold, a capped quadratic optimizer, and an exact active-set value.

**Theorem 1.1 (The probe threshold is unique and globally optimal).**

$$\begin{gathered}\forall \iota: \operatorname{Type}, [\operatorname{Fintype}(\iota)]\\{}\forall a: (\iota) \to \mathbb{R}, \varepsilon: \mathbb{R},\\{}((\forall l, (0 < a_{l})) \land (\sum_{l} a_{l} = 1) \land (0 < \varepsilon \land \varepsilon < 1)) \Rightarrow\\{}(v = (l: \iota \mapsto \sqrt{a_{l}})), (F(x) = ({\sum_{l} v_{l} \cdot x_{l}}^{2} - \varepsilon \cdot \sum_{l} x_{l}^{2})),\\{}\exists c: \mathbb{R}, (0 < c) \land (\sum_{l} \min(a_{l}, \frac{v_{l}}{c}) = \varepsilon) \land (x_{*} = (l: \iota \mapsto \min(1, c \cdot v_{l}))) \land (H = \{l \mid 1 \le c \cdot v_{l}\}) \land\\(d = \sum_{l \in \iota \setminus H} a_{l}) \land (S = \sum_{l \in H} v_{l})\\((\forall l, (0 \le {x_{*}}_{l} \land {x_{*}}_{l} \le 1))) \land\\((\forall x: (\iota) \to \mathbb{R}, ((\forall l, (0 \le x_{l} \land x_{l} \le 1))) \Rightarrow (F(x) \le F(x_{*})))) \land\\(d < \varepsilon) \land\\(c = \frac{S}{\varepsilon - d}) \land\\(F(x_{*}) = \frac{\varepsilon \cdot S^{2}}{\varepsilon - d} - (\varepsilon \cdot \operatorname{card}(H))) \land (\forall c': \mathbb{R}, (0 < c') \Rightarrow (\sum_{l} \min(a_{l}, \frac{v_{l}}{c'}) = \varepsilon) \Rightarrow (c' = c)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/ProbeThresholdOptimization.probe_threshold_optimization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The threshold balances the capped square-root weights against epsilon. Strict decrease after the uncapped range makes this balance unique.

Linearizing the squared aggregate separates the box optimization by coordinate. Each coordinate is maximized by its capped linear response.

Splitting the coordinates at the cap gives the threshold identity and the exact objective value in terms of the active mass, active square-root sum, and active count.

## References

- Truth anchor: `D5/S3/Estimation/ErrorExponents/ProbeThresholdOptimization.probe_threshold_optimization`
