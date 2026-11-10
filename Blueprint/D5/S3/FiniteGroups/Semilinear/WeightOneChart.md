# The distinguished weight-one chart

## Abstract

Weight-one normalization removes scalar motion and preserves Galois dynamics and isotropy.

**Theorem 1.1 (The actual orbit quotient).**

Lean statement: `D5/S3/FiniteGroups/Semilinear/WeightOneChart.chartQuotientEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Semilinear/WeightOneChart.chartQuotientEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F and K be fields with an F-algebra structure on K, in the Type universe used by the existing weighted action. The residual coordinate type J has an independent arbitrary universe. Give none in Option J weight one and some j weight w(j). Chart is precisely the subtype A(none) nonzero, and chartAction restricts the existing weightedAction, with the same inverse scalar powers and semidirect multiplication. The weight parameter in Chart records which restricted action is intended; it adds no condition on A.

Writing a=A(none), the normalization is N(A)(j)=a to the power -w(j) times A(some j). Under g=(c,sigma), the leading coordinate becomes c inverse times sigma(a). These inverse weight powers cancel the scalar in every normalized coordinate: N(g A)=sigma N(A). Thus scalar normalization leaves the actual Galois dynamics. The section has leading coordinate one and residual tuple b. More generally, over any prescribed sigma the unique scalar carrying a chart point A to a point B with N(B)=sigma N(A) is sigma(A(none))/B(none). The source proves this reconstruction on the actual coordinates, then defines the equivalence of the native orbit-relation quotients by normalization and this section.

No finiteness, faithful-action, free-action or residual nonzero assumption is used. J may be empty, and every residual coordinate may vanish. These are raw orbits of the actual rational vectors. This chart supplements the full weighted classification and its original-jet bridge; it leaves the distinguished-coordinate-zero boundary to that full problem.

**Theorem 1.2 (The canonical stabilizer group isomorphism).**

Lean statement: `D5/S3/FiniteGroups/Semilinear/WeightOneChart.chartStabilizerEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Semilinear/WeightOneChart.chartStabilizerEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projection (c,sigma) maps to sigma and restricts to a multiplicative equivalence from the actual chart stabilizer to the native Galois stabilizer of N(A). Its inverse is the actual semidirect-product element (sigma(a)/a,sigma). The leading-coordinate fixed equation forces exactly this scalar; the remaining fixed equations are exactly sigma N(A)=N(A). The definition proves membership of both maps, both inverse laws and preservation of multiplication. In particular this identifies the groups, including their nontrivial isotropy, rather than merely equating cardinalities.

The elementary normalization and graph argument is the supplied standard mathematical derivation, implemented against the repository action and native Mathlib quotients and subgroups. No mathematical priority is claimed. Native orbit-stabilizer supplies subsequent cardinal arithmetic; it does not supply this nonlinear coordinate bridge.

General raw weighted scalar orbits must be distinguished from coarse weighted Proj rational points and from groupoid mass. For example, over F3 with weights (2,2), all eight nonzero vectors are distinct raw scalar orbits, whereas the coarse projective line has four rational points. Each raw orbit has stabilizer of order two, so their reciprocal-stabilizer mass is four. The weight-one chart admits a unique scalar normalization; no stack infrastructure is needed for the present theorem.

## References

- Truth anchor: `D5/S3/FiniteGroups/Semilinear/WeightOneChart.chartQuotientEquiv`
- Truth anchor: `D5/S3/FiniteGroups/Semilinear/WeightOneChart.chartStabilizerEquiv`
- Dependency: [D5/S3/FiniteGroups/Semilinear/WeightedOrbits](WeightedOrbits.md)
