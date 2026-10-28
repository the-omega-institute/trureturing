# Critical edge incidence margins

## Abstract

Separate exact curvature margins for a six-occurrence global critical edge star.

A finite tetrahedron type T and a global edge-label type E carry an incidence map from each of six local edge slots to E. The star of e is the fibre of that map; StarOccurrence(s,e) is its subtype of local occurrences. Its cardinality counts local occurrences, including repeated tetrahedra and repeated neighbouring global labels. The local frame puts each target slot first and its opposite fourth.

Critical labels are low labels of degree six. Every occurrence of the target has at least three high neighbours. A chosen subset of at least four occurrences has four high neighbours and a critical opposite label. The global length function assigns one value to each global edge. All values lie in [1,2], high values are at most 5/4, and critical values are at least 4/3. The same box applies to both target faces.

**Theorem 1.1 (Each face has its own curvature margin).**

$$\forall T \in Type, E \in Type, s \in Incidence\left(T, E\right), critical \in E \to Prop, e \in E, good \in Finset\left(StarOccurrence\left(s, e\right)\right), x \in E \to Real,\; \left(Fintype\left(T\right) \land \left(DecidableEq\left(E\right) \land \left(critical\left(e\right) \land \left(4 \le card\left(good\right) \land \left(\left(\forall f \in E,\; critical\left(f\right) \Rightarrow \left(low\left(s, f\right) = true \land degree\left(s, f\right) = 6\right)\right) \land \left(\left(\forall a \in StarOccurrence\left(s, e\right),\; ThreeHigh\left(s, a\right)\right) \land \left(\left(\forall a \in StarOccurrence\left(s, e\right),\; a \in good \Rightarrow \left(FourHigh\left(s, a\right) \land critical\left(coordinate\left(s, a, 3\right)\right)\right)\right) \land \left(\forall f \in E,\; x\left(f\right) \in Icc\left(1, 2\right) \land \left(\left(low\left(s, f\right) = false \Rightarrow x\left(f\right) \le \frac{5}{4}\right) \land \left(critical\left(f\right) \Rightarrow \frac{4}{3} \le x\left(f\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(x\left(e\right) = \frac{4}{3} \Rightarrow 2\cdot pi-6\cdot arccos\left(\frac{4}{7}\right) \le curvature\left(s, x, e\right)\right) \land \left(x\left(e\right) = 2 \Rightarrow curvature\left(s, x, e\right) \le -{4\cdot gamma+2\cdot beta-2\cdot pi}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/CriticalIncidenceStar.critical_incidence_face_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At target length 4/3, each local cosine is at least 4/7; six angle terms give curvature at least 2pi-6arccos(4/7). At target length 2, every angle is at least beta=arccos(49/sqrt(6534)); each favourable angle is at least gamma=arccos(43/99). Four favourable occurrences give curvature at most the negative of 4gamma+2beta-2pi.

Both inequalities hold for any one global length vector satisfying the box and the stated target-face equality. Local occurrences with the same global neighbour read the same length. The result concerns the analytic angle formula on labelled edge incidence; it does not assert face-gluing manifold conditions or geometric realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CriticalIncidenceStar.critical_incidence_face_bounds`
- Dependency: [D5/S3/Geometry/Hyperideal/CriticalTransitionStar](CriticalTransitionStar.md)
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleCurvature](FourCycleCurvature.md)
