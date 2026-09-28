# Compressed Resolvent Remainder

## Abstract

A coisometric compression has a positive second-order resolvent remainder with a cubic gap bound.

**Theorem 1.1 (The compressed resolvent has a positive cubic remainder).**

$$\begin{gathered}\forall K, R, E: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(R)], [\operatorname{InnerProductSpace}(K, R)], [\operatorname{FiniteDimensional}(K, R)],\\{}[\operatorname{NormedAddCommGroup}(E)], [\operatorname{InnerProductSpace}(K, E)], [\operatorname{FiniteDimensional}(K, E)],\\{}F: \operatorname{ContinuousLinearMap}(K, R, E), S: \operatorname{ContinuousLinearMap}(K, R, R), a: \mathbb{R}, u: \mathbb{R},\\{}(F \circ F^{*} = I_{E}) \Rightarrow (\operatorname{IsSelfAdjoint}(S)) \Rightarrow (0 < a) \Rightarrow\\{}(a \cdot I_{R} \leq S) \Rightarrow (0 \leq u) \Rightarrow\\{}P := F^{*} \circ F,\quad Q := I_{R} - P,\\{}A := F \circ S \circ F^{*},\quad delta := \left\lVert F \circ S \circ Q \circ S \circ F^{*} \right\rVert,\\{}S_{0} := P \circ S \circ P + Q \circ S \circ Q,\quad V := S - S_{0},\\{}R_{u} := (S + u \cdot I_{R})^{-1},\quad R_{u}^{0} := (S_{0} + u \cdot I_{R})^{-1},\\{}D_{u} := F \circ R_{u} \circ F^{*} - (A + u \cdot I_{E})^{-1},\\{}(R_{u} - R_{u}^{0} = -((R_{u}^{0} \circ V \circ R_{u}^{0})) + R_{u}^{0} \circ V \circ R_{u} \circ V \circ R_{u}^{0}) \land\\{}(D_{u} = (A + u \cdot I_{E})^{-1} \circ F \circ S \circ Q \circ R_{u} \circ Q \circ S \circ F^{*} \circ (A + u \cdot I_{E})^{-1}) \land\\{}(0 \leq D_{u}) \land\\{}(\left\lVert D_{u} \right\rVert \leq \frac{delta}{(a + u)^{3}}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CompressedResolventRemainder.compressed_resolvent_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a coisometry between finite-dimensional real or complex inner-product spaces. Let S be self-adjoint with spectral floor a, where a is positive, and let the resolvent parameter u be nonnegative.

The block-diagonal part S0 is formed with the visible projection P and its orthogonal complement Q. Substituting the two inverse-difference identities into one another isolates the displayed second-order term.

Compression removes the first-order cross-block term. The remaining expression is an adjoint sandwich of the positive resolvent, while the two leakage factors and three inverse factors give the stated cubic estimate.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/CompressedResolventRemainder.compressed_resolvent_remainder`
- Dependency: [D5/S3/Observer/BlockStructure/FourBlockDecomposition](../../Observer/BlockStructure/FourBlockDecomposition.md)
