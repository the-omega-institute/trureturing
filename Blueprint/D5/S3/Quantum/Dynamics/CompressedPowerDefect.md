# Compressed Power Defect

## Abstract

A coisometric compression has a quadratic power defect controlled by its two-step leakage.

**Theorem 1.1 (Compressed powers have a binomial leakage bound).**

$$\begin{gathered}\forall K, R, E: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(R)], [\operatorname{InnerProductSpace}(K, R)], [\operatorname{FiniteDimensional}(K, R)],\\{}[\operatorname{NormedAddCommGroup}(E)], [\operatorname{InnerProductSpace}(K, E)], [\operatorname{FiniteDimensional}(K, E)],\\{}F: \operatorname{ContinuousLinearMap}(K, R, E), S: \operatorname{ContinuousLinearMap}(K, R, R), b: \mathbb{R},\\{}F \circ F^{*} = I \Rightarrow \operatorname{IsSelfAdjoint}(S) \Rightarrow \left\lVert S \right\rVert \leq b \Rightarrow\\{}P := F^{*} \circ F,\quad Q := I - P,\\{}A := F \circ S \circ F^{*},\quad delta := \left\lVert F \circ S \circ Q \circ S \circ F^{*} \right\rVert,\\{}(F \circ S^{2} \circ F^{*} - A^{2} = F \circ S \circ Q \circ S \circ F^{*}) \land\\{}(\forall n: \operatorname{Nat}, 2 \leq n \Rightarrow \left\lVert F \circ S^{n} \circ F^{*} - A^{n} \right\rVert \leq \operatorname{choose}(n, 2) \cdot b^{{n - 2}} \cdot delta).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CompressedPowerDefect.compressed_power_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a coisometry between finite-dimensional real or complex inner-product spaces, and let S be a self-adjoint operator bounded in norm by b. The operator P = F*F is the visible projection and Q = I-P is its orthogonal complement.

The quadratic compression defect is exactly the path that leaves the visible subspace through Q and returns after the second application of S.

For every higher power, a commutator expansion controls hidden leakage at each possible crossing time. Iterating the resulting defect recursion sums these contributions to the binomial coefficient n choose 2.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/CompressedPowerDefect.compressed_power_defect`
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](../../Observer/HiddenFlow/ProjectionCommutatorIdentity.md)
