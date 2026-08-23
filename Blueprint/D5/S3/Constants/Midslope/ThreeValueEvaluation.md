# Three Midslope-Curvature Values

## Abstract

The arithmetic, geometric, and harmonic midslope-curvature integrals have exact values.

**Theorem 1.1 (The three elementary midslope values are exact).**

$$J(1)=-\log 2 \land J(0)=1-2 \log 2 \land J(-1)=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Midslope/ThreeValueEvaluation.three_value_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof applies the frozen arithmetic, geometric, and harmonic integral evaluations directly, without repeating any integral calculation.

The three conjuncts appear in parameter order 1, 0, and -1. No claim about any other parameter or about the full exact-value set is included.

## References

- Truth anchor: `D5/S3/Constants/Midslope/ThreeValueEvaluation.three_value_evaluation`
- Dependency: [D5/S3/Constants/MidslopeCurvatureValues](../MidslopeCurvatureValues.md)
