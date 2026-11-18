# OriginalGaussianSourceCharacter

## Abstract

Native period and source continuation with fixed original normalization.

**Definition 1.1 (The actual negative source).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.C`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C(r) is OriginalGaussianSourceEvaluation.sourceAmplitude false 0 r.

**Definition 1.2 (The normalized source on the complement cover).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.sourceCover`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.sourceCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lifted source is exp(-zeta/2), with normalization fixed by the original source amplitude.

**Definition 1.3 (The source in the native complement chart).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.sourceChart`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.sourceChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source chart is exp(-localLog(zeta,1-r)/2).

**Theorem 1.4 (The original source branch and its holomorphy).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_branch`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_branch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r in the full unit disk the literal negative zero amplitude equals exp(-Log(1-r)/2), is holomorphic on that disk, and equals the actual negative mode generator at u=0. This follows by evaluating the existing public HasSum sourceAmplitude_generators at u=0, without reproving its binomial series or copying the private closed-generator proof. The inequality Re(1-r)>0 fixes the principal branch.

**Theorem 1.5 (The exact integer source character).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.source_deck`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.source_deck` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized lifted source is entire. Translation by 2 pi i k multiplies it by (-1)^k for every integer k, including negative windings.

**Definition 1.6 (The actual source chart certificate).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.SourceCharts`

*Formalization.* `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.SourceCharts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source certificate contains holomorphic explicit complementary source charts, neighborhood equality of their transition germs, the initial literal negative source germ, and equality with the fixed normalized lifted source along the path. It is specific to the native period path charts.

**Theorem 1.7 (The source along every complementary path).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_path`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every continuous path with norm(1-r)<1 avoiding r=1 and beginning at b carries the native period lift and the actual source chart certificate. The proof uses normalized local inverse charts and their neighborhood transition identities, then matches their initial phase to the public source generator.

**Theorem 1.8 (The actual all-loop source character).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_loop_character`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_loop_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal source C is holomorphic on the entire original unit disk. This same disk is a neighborhood of every point of every path in that disk, and the theorem supplies the identical initial, transition and endpoint germs of C along every such path. Thus its germs continue around zero with character one. For every based continuous loop in the complementary punctured disk, the native lift has endpoint Log(b)+2 pi i k, and the returned source germ is (-1)^k times the actual C. This includes all integers and uses no differentiable-path or winding-integral assumption.

**Theorem 1.9 (The positive source sign around one).**

Lean statement: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.positive_source_monodromy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.positive_source_monodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive native loop gamma1 with its positive complementary exponential lift has the actual source chart certificate. Its endpoint source germ is minus the literal negative zero amplitude C; its initial germ is C. The phase comes from the actual source generator, without scalar freedom.

## References

- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.C`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.SourceCharts`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_branch`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_loop_character`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.actual_source_path`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.positive_source_monodromy`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.sourceChart`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.sourceCover`
- Truth anchor: `D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter.source_deck`
- Dependency: [D5/S3/Analytic/NativePeriod/OriginalHalfBinomialComplementMonodromy](OriginalHalfBinomialComplementMonodromy.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators](../../VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.md)
