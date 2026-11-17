# Literal weighted Möbius partial-sum divergence

## Abstract

Literal weighted Möbius partial-sum divergence.

This unit keeps the literal finite sum over 1 ≤ n ≤ floor(x), with coefficient the ordinary Möbius value divided by n, and the Lebesgue measure restricted to the open half-line (1,∞). The proof uses the shifted Möbius Dirichlet series, a general L² half-line Mellin pairing, and an unconditional nontrivial zeta-zero witness. It does not assume RH or add a conditional certificate premise.

**Definition 1.1 (Half-line Lebesgue measure).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMeasure`

*Formalization.* `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The measure is volume restricted to Ioi 1, exactly the domain used by the literal MemLp conclusion.

**Definition 1.2 (Literal weighted Möbius partial sum).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.mobiusPartialSum`

*Formalization.* `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.mobiusPartialSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real x the function sums the ordinary arithmetic Möbius coefficient over the finite integer interval 1 ≤ n ≤ floor(x), dividing each term by n. No abstract transform replaces this function.

**Definition 1.3 (General half-line Mellin functional).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin`

*Formalization.* `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any complex-valued function and complex parameter s, this is the Bochner integral of f(x) times x to the power -(s+1) over Ioi 1.

**Theorem 1.4 (Sharp L² half-line Mellin norm bound).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every MemLp-2 function on the half-line has Mellin functional norm at most its L² norm divided by sqrt(2 Re(s)+1), whenever Re(s)>-1/2. The proof computes the exact kernel energy and applies Cauchy–Schwarz.

**Theorem 1.5 (Local differentiability of the general Mellin functional).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_differentiableAt`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_differentiableAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Mellin functional is complex differentiable at every parameter in the half-plane Re(s)>-1/2. An integrable logarithmic derivative majorant supplies the local dominated-derivative argument.

**Theorem 1.6 (Analyticity of the general Mellin functional).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same general L² functional is analytic on neighborhoods throughout the half-plane Re(s)>-1/2.

**Theorem 1.7 (Unconditional literal Möbius partial-sum L² divergence).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.mobiusPartialSum_not_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.mobiusPartialSum_not_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem proves the exact unconditional negation of MemLp for the literal weighted Möbius partial sum on Ioi 1. The contradiction combines the shifted Möbius Dirichlet identity with analytic continuation of the product s·ζ(s+1) and the sharp half-line L² bound. A zero with real part at least one half is obtained unconditionally from the canonical zero data and reflection; the argument does not claim the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMeasure`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_analyticOnNhd`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_differentiableAt`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.halfLineMellin_norm_le`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.mobiusPartialSum`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.mobiusPartialSum_not_memLp`
- Dependency: [D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData](../ZeroData/UnconditionalCanonicalZeroData.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin](NymanFractionalMellin.md)
