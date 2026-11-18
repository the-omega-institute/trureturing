# OriginalHalfBinomialComplementMonodromy

## Abstract

Native period and source continuation with fixed original normalization.

**Definition 1.1 (The complementary chart domain).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementDomain`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complementary chart consists of r for which 1-r belongs to the normalized exponential chart domain.

**Definition 1.2 (The complementary numerator).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementN`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementN` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal numerator is iP(1-r), with its original scalar phase.

**Definition 1.3 (The complementary denominator).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementY`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementY` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continued denominator is -i times the continued native numerator at 1-r.

**Definition 1.4 (The complementary path).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementPath`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The path in the zero-centered disk is 1-gamma.

**Definition 1.5 (The positive one loop).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.gamma1`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.gamma1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gamma1(t)=1-(1/2)exp(2 pi i t). Its complementary path is exactly gamma0, so the exponential lift has positive orientation.

**Theorem 1.6 (The equation and Wronskian after complement).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_equations`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every complementary chart both components are holomorphic, have differentiable derivatives, and solve the same native Picard-Fuchs equation. Their oriented Wronskian is -i/(pi r(1-r)). The parameter reversal contributes a minus sign to first derivatives; the fixed scalar transformation contributes the second sign needed to preserve the native Wronskian. There is no assumption that the continued denominator never vanishes.

**Theorem 1.7 (Every full complementary path).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_path_continuation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_path_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every continuous path in the disk norm(1-r)<1 avoiding r=1 and starting at b has the native exponential lift of its complementary path. The transformed denominator charts agree as germs along this path and initially equal the original P as a germ. The numerator iP(1-r) is single-valued on this complementary disk.

**Theorem 1.8 (The exact native A1 action).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.positive_one_monodromy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.positive_one_monodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive loop around one has the same positive exponential lift in s=1-r. Its initial denominator germ is P and its returned denominator germ is P(r)-2iP(1-r), while the numerator is unchanged. On the original ordered column (n,y) the exact matrix is A1=[[1,0],[-2,1]], including the original scalar phase.

**Theorem 1.9 (All integer complementary loop actions).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_loop_monodromy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_loop_monodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every continuous based loop in the full punctured complementary disk, there is an integer endpoint displacement of its exponential lift. The initial denominator germ is the literal P; the returned denominator germ is P(r)-2kiP(1-r). The numerator remains iP(1-r). This is the exact ordered-column action A1 to the integer power k, including inverse winding.

**Theorem 1.10 (The exact initial phase on the full lens).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_initial_germ`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_initial_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex r in the full lens, the complementary denominator chart based at Log(1-r) equals the original P as a germ near r. The complementary numerator is literally iP(1-r). The identity n0(s)=iP(1-s) supplies the full overlap matching, including the fixed scalar minus i in the denominator transformation.

## References

- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementDomain`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementN`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementPath`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementY`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_equations`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_initial_germ`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_loop_monodromy`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.complementary_path_continuation`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.gamma1`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy.positive_one_monodromy`
- Dependency: [D5/S3/Analytic/NativePeriod/OriginalHalfBinomialMonodromy](OriginalHalfBinomialMonodromy.md)
