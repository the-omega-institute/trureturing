# Cumulative Riemann-von Mangoldt asymptotic

## Abstract

The cumulative positive zeta zero count has the classical leading constant.

**Theorem 1.1 (Positive zero count divided by height times log height).**

Lean statement: `D5/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt.cumulative_count_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt.cumulative_count_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Count every distinct nontrivial zeta zero with imaginary part strictly above zero and at most T, weighted by its analytic multiplicity. As T tends to infinity, this count divided by T log T tends to 1/(2 pi).

The public cumulative-count lemma in ZetaOrdinatePhaseStiffness supplies an error bounded by D T above a fixed threshold. Its source is UnconditionalCanonicalZeroData.zetaRiemannVonMangoldt. Division by T log T bounds the normalized error by D/log T, which tends to zero. The dyadic iteration is reused directly. No Riemann hypothesis is required.

This statement concerns the canonical zeta zero configuration. The extracted coarse-count interface is specific to that configuration.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt.cumulative_count_asymptotic`
- Dependency: [D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness](ZetaOrdinatePhaseStiffness.md)
