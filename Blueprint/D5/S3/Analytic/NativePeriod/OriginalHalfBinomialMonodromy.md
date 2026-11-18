# OriginalHalfBinomialMonodromy

## Abstract

Native period and source continuation with fixed original normalization.

**Definition 1.1 (The native base point).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.b`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common base point is b=1/2.

**Definition 1.2 (The initial lift).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.baseLog`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.baseLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial lift is the principal complex logarithm of b.

**Definition 1.3 (The deck displacement).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.deck`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.deck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each integer k, deck(k)=2 pi i k.

**Definition 1.4 (The native path chart certificate).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.NativeCharts`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.NativeCharts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A certificate contains the continuous exponential projection into the negative half-plane, locally normalized inverse compatibility along the path, equality of numerator germs on transitions, holomorphy and the native equation and oriented Wronskian in every r-chart, and the literal initial numerator germ at b. The denominator in every such chart is the single-valued original P.

**Theorem 1.5 (Every continuous punctured-disk path).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.native_path_continuation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.native_path_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every continuous path gamma with norm less than one and nonzero values, starting at b, there is a unique continuous lift starting at Log(b) with this native chart certificate. The proof applies Complex.isCoveringMap_exp and IsCoveringMap.liftPath to the path valued in the nonzero complex subtype. Norm(exp(zeta))=exp(Re(zeta)) forces the lift into E. Continuity then makes neighboring normalized chart parameters differ in imaginary part by less than pi, which gives germ equality rather than just equality of path values.

**Theorem 1.6 (All integer endpoint actions).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.native_loop_monodromy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.native_loop_monodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such based loop, its lift ends at Log(b)+2 pi i k for an integer k, obtained from Complex.exp_eq_exp_iff_exists_int. The endpoint numerator germ is iP(1-r)+2kP(r), and the endpoint ratio germ is tau(r)+2k. No winding integral or differentiability of the path is assumed; negative integers and zero are included.

**Definition 1.7 (The positive zero loop).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.gamma0`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.gamma0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gamma0(t)=(1/2)exp(2 pi i t) for t in the real unit interval.

**Definition 1.8 (The positive lift).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.positiveLift`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.positiveLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit lift is Log(b)+2 pi i t.

**Theorem 1.9 (The exact native A0 action).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.positive_zero_monodromy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.positive_zero_monodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit positive lift carries the native chart certificate and ends at Log(b)+2 pi i. Its endpoint numerator germ is iP(1-r)+2P(r), while the denominator remains P(r). On the ordered column (n,y), this is A0=[[1,2],[0,1]].

## References

- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.NativeCharts`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.b`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.baseLog`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.deck`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.gamma0`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.native_loop_monodromy`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.native_path_continuation`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.positiveLift`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy.positive_zero_monodromy`
- Dependency: [D5/S3/Analytic/NativePeriod/OriginalHalfBinomialLocalCharts](OriginalHalfBinomialLocalCharts.md)
