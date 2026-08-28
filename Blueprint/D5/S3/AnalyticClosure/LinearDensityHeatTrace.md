# Linear-Density Heat Trace

## Abstract

Linear spectral counting density gives a reciprocal-time heat trace up to bounded error.

**Theorem 1.1 (Linear density controls the heat trace).**

$$\forall spectrum: \mathbb{N} \to \mathbb{R}, c: \mathbb{R}, (\forall n: \mathbb{N}, 0 < \operatorname{spectrum}(n)) \land \operatorname{StrictMono}(spectrum) \land \operatorname{Tendsto}(spectrum, \operatorname{atTop}, \operatorname{atTop}) \land 0 < c \land (\exists C, U: \mathbb{R}, 0 \leq C \land \forall u: \mathbb{R}, U \leq u \Rightarrow \left|\operatorname{ncard}(\{n \in \mathbb{N} \mid \operatorname{spectrum}(n) \leq u\}) - c \times u\right| \leq C) \Rightarrow (\exists B, \delta: \mathbb{R}, 0 < \delta \land \forall t: \mathbb{R}, 0 < t \land t \leq \delta \Rightarrow \operatorname{Summable}(n \mapsto \operatorname{exp}(-t \times \operatorname{spectrum}(n))) \land \left|\operatorname{tsum}(n \mapsto \operatorname{exp}(-t \times \operatorname{spectrum}(n))) - \frac{c}{t}\right| \leq B).$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/LinearDensityHeatTrace.linear_density_heat_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let spectrum be a positive, strictly increasing real sequence tending to infinity, and let c be positive. Assume its sublevel counting function differs from c times u by a fixed bound for all large u.

Then there are constants B and delta, with delta positive, such that for every 0 < t <= delta the exponential spectral series is summable and its difference from c/t has absolute value at most B.

The proof first converts the counting estimate at spectrum(n) into a uniform displacement from the arithmetic lattice (n+1)/c. It then compares the heat series to the corresponding geometric series, bounding the finite head and the summable tail separately.

Repository searches for heat-trace, counting-density, Stieltjes, and Laplace bridge statements found no complete match. The local proof uses Mathlib's geometric-series sums, exponential remainder bounds, and infinite-sum comparison lemmas.

## References

- Truth anchor: `D5/S3/AnalyticClosure/LinearDensityHeatTrace.linear_density_heat_trace`
