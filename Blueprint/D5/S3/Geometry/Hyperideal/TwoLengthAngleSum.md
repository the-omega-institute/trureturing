# Two lengths and the sum over actual selected edge positions

## Abstract

The selected edges of a two-length generalized tetrahedron have a strict total-angle lower bound on the full unbounded parameter domain.

A and B are cosine-length coordinates, with A>1 and B>4A+5. The six local positions have the original order (12,13,14,34,24,23). S is any subset of these six positions with at least two elements; position j reads B exactly when j is in S and otherwise reads A. Cardinality counts positions, so repeated global labels do not collapse local occurrences.

For a six-vector x and target position q, use the existing FourCycleCurvature.frame to read the target, four neighbors and opposite coordinate in the original FourCycleEnvelopes.cosine. Thus the raw cosine is the original numerator divided by the two positive square roots. extendedAngle(x,q) is arccos(max(-1,min(rawCos(x,q),1))). AngleSum(A,B,S) abbreviates the sum of these extended angles over every q in S, with x(j)=B for j in S and A otherwise. card(S) denotes its finite cardinality.

**Theorem 1.1 (The complete selected-edge sum exceeds one quarter pi per occurrence).**

$$\forall A \in Real, B \in Real, S \in Finset\left(Fin\left(6\right)\right),\; \left(1 < A \land \left(add\left(mul\left(4, A\right), 5\right) < B \land 2 \le card\left(S\right)\right)\right) \Rightarrow div\left(mul\left(card\left(S\right), pi\right), 4\right) < AngleSum\left(A, B, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/TwoLengthAngleSum.two_length_angle_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof establishes the missing continuous cosine bounds from the actual numerator and radicands. Write a=A-1 and b=B-4A-5, so both are positive and B=9+4a+b. For each useful edge, the negative-numerator alternative or squared-denominator gap is exactly a polynomial with positive coefficients and a positive constant term. These certificates prove the inequalities for every real parameter in the stated unbounded region; no desired cosine or angle bound is assumed.

There are 57 selected-edge subsets of size at least two, grouped into nine K4 graph types. Adjacent pairs, triangles and four-cycles use every selected angle above pi/3. Opposite pairs use two angles above pi/2; stars and the all-six type use every selected angle above pi/4. A three-edge path uses its two endpoints above pi/2. The four-edge graph complementary to an adjacent pair uses its selected opposite pair above pi/2. A five-edge graph uses the four edges adjacent to the missing edge above pi/3. The finite slot routing checks every actual subset directly. Adding the other nonnegative extended angles gives the complete sum with all its multiplicities.

For A=2, B=14 and the path S={0,3,5}, the middle position 5 has raw numerator 2466, both radicands 1179, and raw cosine 274/131>1. Its extended angle is zero, while the total selected-edge estimate remains strict. The result therefore includes generalized states with zero angles and does not require the tetrahedron to be genuinely nondegenerate.

This is an estimate for the specified original six-slot cosine and its clipped extension. Its use with actual geometric dihedral angles requires their identification with this formula and one common global length vector. The theorem supplies neither volume-maximizer existence, global face gluing, normal-link topology nor same-manifold geometric realization, and it does not settle unrestricted CFMP. The original cosine formula and generic square-root, inverse-cosine and finite-sum facts are reused; no literature priority is asserted.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/TwoLengthAngleSum.two_length_angle_sum`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleCurvature](FourCycleCurvature.md)
