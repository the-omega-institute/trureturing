# Nice cones and exact exposure of all original faces

## Abstract

Facial dual completeness exposes every original face in the ambient finite-dimensional real space.

**Definition 1.1 (The original ambient algebraic dual cone).**

Lean statement: `D5/S3/Quantum/Foundation/NiceConeFaces.ambientDual`

*Formalization.* `D5/S3/Quantum/Foundation/NiceConeFaces.ambientDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a subset s of V, ambientDual(s) is the cone of all original real-linear a:V->R with a(x)>=0 for every x in s. Both dual cones below live in the same V*, including when the face has proper linear span.

**Definition 1.2 (Facial dual completeness).**

Lean statement: `D5/S3/Quantum/Foundation/NiceConeFaces.Nice`

*Formalization.* `D5/S3/Quantum/Foundation/NiceConeFaces.Nice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original E:C.Face, ambientDual(E) equals the Minkowski sum of ambientDual(C) and the annihilator of span(E) in V*. The sum is a set sum, not a separately chosen restriction dual or an assumed exposing functional.

**Theorem 1.3 (Every original cone face is an exact support-zero section).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\operatorname{Nice}\left(C\right) \Rightarrow \left(\forall F \in \operatorname{Face}\left(C\right),\; \exists a \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\forall x \in V,\; x\in C \Rightarrow 0 \le \operatorname{apply}\left(a, x\right)\right) \land F = \left\{x \mid x \in C \land \operatorname{apply}\left(a, x\right) = 0\right\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/NiceConeFaces.every_face_exposed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite-dimensional real normed V, every closed PointedCone C, and every original face F of C, facial dual completeness gives a real-linear a nonnegative on C such that F={x in C | a(x)=0}. PointedCone means a cone containing zero; salience is not assumed. The quantifiers include subspace cones, their lineality face, zero-dimensional V and the whole face. The whole face permits a=0. Empty convex-set faces are outside the native cone-face type.

Choose a nonnegative a annihilating F whose support-zero section has least span dimension. Let E be that section. If F is proper in E, restrict both cones to span(E), where E generates. The original ExclusionBallFaces.proper_cone_face_support provides a functional nonzero on this relative ambient space, positive on E and zero on F. Extend it linearly to V. The nice identity at this same original E splits the extension into b positive on C and a term annihilating span(E). Thus b agrees with the relative support on E and is nonzero somewhere in E. The positive functional a+b still vanishes on F, while its zero section has strictly smaller span dimension, a contradiction. This proves equality with F rather than mere containment.

This is the nice-to-facially-exposed consequence in the existing IX119.12 chain. The mature attribution is Lourenco, Roshchina and Saunderson, arXiv:2011.07745v2, Proposition 2.3, and Pataki, arXiv:1202.4043v4, Theorem 3(1). No literature originality is claimed. It proves neither the other arrows in that chain nor all of Corollary 119.3. It supplies no unit-preserving projection, uniform error-bound constant, moving-face regularity or quantum realization. In the maximizing convention of IsExposed the corresponding exposing functional is -a.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/NiceConeFaces.Nice`
- Truth anchor: `D5/S3/Quantum/Foundation/NiceConeFaces.ambientDual`
- Truth anchor: `D5/S3/Quantum/Foundation/NiceConeFaces.every_face_exposed`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)
