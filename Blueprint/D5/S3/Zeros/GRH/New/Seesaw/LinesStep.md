# Lines Step

## Abstract

Lines Step

Support of unfolded periods: lattice lines move at most one step per lift.

**Theorem 1.1 (step).**

Lean statement: `D5/S3/Zeros/GRH/New/Seesaw/LinesStep.step`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Seesaw/LinesStep.step` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

One step of Grading.HasNearLines: from Y, x, m, k to Y', x', m', k + 1, where s' + 1 = s and m = m' (s odd) or m' + 1 (s even). Assume (c) = (aā), b | conj(α/a)∏_Q w, ϱ_f(b·Ô-vectors) fixes f, Grading.constTermAtT of t ⊗ f is non-zero at (x, x'), and adapted bases at x' have ord_w β_i + ord_{w̄} β_{s'−1−i} ≥ 0. Here c is the constant of the grading Y and α = WeilData.α.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Seesaw/LinesStep.step`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Periods/UnfoldingStep](../../Lib/Weil/Periods/UnfoldingStep.md)
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/EdgePair](EdgePair.md)
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/EqualLinesOrbit](EqualLinesOrbit.md)
