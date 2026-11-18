# OriginalHalfBinomialLocalCharts

## Abstract

Native period and source continuation with fixed original normalization.

**Definition 1.1 (The exponential half-plane).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.E`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E consists of complex zeta with negative real part; its exponential lies in the punctured unit disk.

**Definition 1.2 (The normalized lifted ratio).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.T`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(zeta)=(i/pi)(log(16)-zeta)+H(exp(zeta)), with the literal normalized disk correction H.

**Definition 1.3 (The lifted denominator).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.Y`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.Y` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Y(zeta)=P(exp(zeta)), using the original period series P.

**Definition 1.4 (The lifted numerator).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.N`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(zeta)=Y(zeta)T(zeta).

**Definition 1.5 (The normalized inverse chart).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.localLog`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.localLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local inverse at exp(zeta) is zeta+Log(r/exp(zeta)). It takes exp(zeta) to zeta.

**Definition 1.6 (The chart domain).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartDomain`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chart domain consists of r in the unit disk for which r/exp(zeta) is in the principal slit plane.

**Definition 1.7 (The ratio in an r-chart).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartT`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replace zeta in the fixed normalized logarithmic formula by the normalized inverse chart.

**Definition 1.8 (The numerator in an r-chart).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartN`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartN` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chart numerator is P(r) times the chart ratio.

**Theorem 1.9 (Actual inverse holomorphic charts).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.native_chart`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.native_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each zeta in E, the chart domain is open and contains exp(zeta). The normalized inverse maps that domain into E, exponentiates to r, has derivative 1/r, and pulls T and N back to the displayed r-chart functions. Conversely the inverse composed with exp equals the identity on a neighborhood of zeta. These are neighborhood identities, including across the principal r-logarithm cut.

**Theorem 1.10 (Holomorphy and integer deck translations).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.cover_periods`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.cover_periods` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

T,Y,N are holomorphic on E. For every complex zeta and every integer k, translation by 2 pi i k adds 2k to T, fixes Y, and adds 2kY to N. The sign follows from i squared equal to minus one and the fixed log(16) normalization.

**Theorem 1.11 (The native equation in every chart).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chart_equations`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chart_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every zeta, the chart ratio and numerator are holomorphic on their open chart domain. At every r there, the ratio derivative is -i/(pi r(1-r)P(r)^2). The numerator has a differentiable derivative and satisfies r(1-r)n double-prime+(1-2r)n prime-n/4=0 and n prime P-nP prime=-i/(pi r(1-r)). The proof differentiates the actual constant Abel product and uses the original equation for P.

**Theorem 1.12 (Transition equality of holomorphic germs).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chart_transition`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chart_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If w lies in E and Im(w-zeta) lies strictly between -pi and pi, the two normalized inverse charts agree on a neighborhood of exp(w). Their ratio and numerator charts therefore agree as germs there. Continuity of the local inverse and the local identity Log(exp(u-zeta))=u-zeta supply that neighborhood.

**Theorem 1.13 (The literal initial germs on the full lens).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.native_initial_germ`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.native_initial_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every r in the full complex lens, Log(r) lies in E. The numerator chart based at Log(r) agrees on a neighborhood of r with iP(1-r), and its ratio chart agrees with the literal native tau. The existing full-lens continuation fixes the actual scalar phase and additive constant.

## References

- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.E`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.N`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.T`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.Y`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartDomain`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartN`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chartT`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chart_equations`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.chart_transition`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.cover_periods`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.localLog`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.native_chart`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts.native_initial_germ`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialContinuation](../OriginalHalfBinomialContinuation.md)
