# Two New Midslope-Curvature Values

## Abstract

The two half-parameter midslope curvatures have exact logarithmic values and affine relations.

**Theorem 1.1 (The half-parameter values and their affine relations).**

$$J(\frac{1}{2})=\frac{5-12 \log 2}{6} \land J(-\frac{1}{2})=\frac{1-2 \log 2}{2} \land J(\frac{1}{2})=\frac{5}{6} J(0)+\frac{1}{3} J(1) \land J(-\frac{1}{2})=\frac{J(0)}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Midslope/TwoNewExactValues.two_new_exact_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof applies the frozen exact half-power evaluation, the affine identity, and the negative-half relation. The explicit negative-half value follows by substituting the frozen geometric-mean value.

All four clauses concern the canonical midslope-curvature integrals; no claim about other parameters is included.

## References

- Truth anchor: `D5/S3/Constants/Midslope/TwoNewExactValues.two_new_exact_values`
- Dependency: [D5/S3/Constants/MidslopeCurvatureValues](../MidslopeCurvatureValues.md)
