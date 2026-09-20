# A face signature prevents mixing the balanced local types

## Abstract

Opposite-paired global edge colours force one local type on each connected face-paired component.

T and E are arbitrary types. Incidence s specifies six global edge labels per tetrahedron and one Boolean low colour per global label. FacePairing(s) specifies an involutive partner map on T x Fin(4), a permutation of the three edges of each face, and equality of the corresponding global edge labels. Connected means every pair of tetrahedra is linked by a finite path of these face steps, expressed using Relation.ReflTransGen.

The local edge order is (12,13,14,34,24,23). Balanced(s) means opposite slots 0,3 have equal colour, as do 1,4 and 2,5. The indicator mark has value one on low labels and zero on high labels. P(s,t) is mark at slots 0,1,2 summed, which is the number of low opposite pairs under Balanced. F(s,t,f) is the count of low edge occurrences on face f. The four face edge lists are (3,4,5), (1,2,3), (0,2,4), and (0,1,5).

**Theorem 1.1 (One signature throughout a connected pairing).**

$$\forall T \in Type, E \in Type, s \in Incidence\left(T, E\right), p \in FacePairing\left(s\right),\; Balanced\left(s\right) \Rightarrow \left(Connected\left(p\right) \Rightarrow \left(\left(\forall t \in T, f \in Fin\left(4\right),\; F\left(s, t, f\right) = P\left(s, t\right)\right) \land \left(\forall t \in T, u \in T,\; P\left(s, t\right) = P\left(s, u\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FaceColourPropagation.balanced_signature_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Opposite colour equalities identify each face sum with P(s,t). The face-pairing equation preserves all three actual edge labels, and permuting the three summands preserves their sum. Thus paired faces have equal signatures. Induction along the finite face path propagates the equality to any two tetrahedra. Equality of neighbouring pair counts is derived from the gluing; it is not a hypothesis.

The four balanced types have P=0,1,2,3: all high, one low opposite pair, one low four-cycle, and all low. Consequently the one-pair and four-cycle types cannot coexist in a connected complex using only balanced types. A transition requires at least one tetrahedron with unequal colours on some opposite pair. This does not rule out general mixed-valence triangulations or refute CFMP.

The theorem is independent of lengths, curvature and manifold-link certification. It applies even to infinite carriers when the stated finite-path connectedness holds. Finite colour-pattern checks are diagnostics; the global proof does not enumerate complexes.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FaceColourPropagation.balanced_signature_constant`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleCurvature](FourCycleCurvature.md)
