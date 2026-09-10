# Checked Real-X Exclusion Leaf

## Abstract

A concrete interval-certificate leaf bounds the actual seed residual on a continuous Cayley box.

**Theorem 1.1 (The first residual stays between two and four throughout the origin box).**

Lean statement: `D5/S3/Quantum/Tomography/RealXCheckedExclusionLeaf.origin_chart_first_seed_residual_enclosed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/RealXCheckedExclusionLeaf.origin_chart_first_seed_residual_enclosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first seed column is (b,1,1,conjugate(e),1,1), with b=(-3+4i)/5 and e=(-2+i sqrt(21))/5. For every point in the five-dimensional all-positive Cayley box of radius 1/1024, the literal checked expression encloses the actual first squared-modulus residual in [2,4]. The square root is enclosed by the proved rational bounds [4,5].

The numeric annotations have 76 shared expression nodes and are checked by ordinary kernel reduction in the proof script. A separate identity connects their real evaluation to the actual complex measurement. No numerical enclosure hypothesis is supplied. This proves one excluded region, not the full 32-chart cover; the source has not been locally elaborated in the authoring environment.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/RealXCheckedExclusionLeaf.origin_chart_first_seed_residual_enclosed`
- Dependency: [D5/S0/Certificates/RationalIntervalExpression](../../../S0/Certificates/RationalIntervalExpression.md)
