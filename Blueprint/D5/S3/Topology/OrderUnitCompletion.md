# Faithful completion of an order-unit space

## Abstract

The completion of the specified order-unit norm retains exactly the original cone and unit.

Let E be any real normed vector space and let A be OrderUnitNorm.Data on E: a closed salient convex cone C containing zero, with specified interior unit u. Assume the original norm equals A.orderNorm at every original vector. The equality is an actual hypothesis about that specified norm. No finite dimension, completeness or nonzero dimension is assumed.

X is UniformSpace.Completion E in the original norm, and i is UniformSpace.Completion.toComplₗᵢ, the canonical real linear isometry with dense range. completedCone(A) is exactly the closure in X of i(C). completedData(A) has that cone and i(u) as its unit; only its required proofs are constructed. The notation B below denotes this actual completedData, whose construction depends on the stated norm equality.

**Theorem 1.1 (Exact order intervals and faithful cone restriction).**

$$\forall E \in Types,\; RealNormedVectorSpace\left(E\right) \Rightarrow \left(\forall A \in Data\left(E\right),\; \left(\forall a \in E,\; Norm\left(a\right) = OrderNorm\left(A, a\right)\right) \Rightarrow \left(\left(\forall x \in Completion\left(E\right),\; \forall r \in R,\; Norm\left(x\right) \le r \Leftrightarrow \left(0 \le r \land \left(smul\left(r, Unit\left(CompletedData\left(A\right)\right)\right) - x \in Cone\left(CompletedData\left(A\right)\right) \land smul\left(r, Unit\left(CompletedData\left(A\right)\right)\right) + x \in Cone\left(CompletedData\left(A\right)\right)\right)\right)\right) \land \left(\left(\forall x \in Completion\left(E\right),\; OrderNorm\left(CompletedData\left(A\right), x\right) = Norm\left(x\right)\right) \land \left(\forall a \in E,\; Embed\left(a\right) \in Cone\left(CompletedData\left(A\right)\right) \Leftrightarrow a \in Cone\left(A\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitCompletion.faithful_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RealNormedVectorSpace includes the additive group and real normed-space instances. Types is the type universe, R is the real field, and Data(E) is precisely the original cone-unit data. Completion, Embed, CompletedData, Cone, Unit, Norm and OrderNorm refer to the constructions just specified. Every completed vector and every real radius are quantified, including negative radii. The radius condition explicitly includes nonnegativity, so it remains exact when E is zero.

The existing original norm_le_iff supplies attained order endpoints. For original positive vectors b,c, the order endpoints for b+c and cone addition bound the norm of b-c by the norm of b+c. Two successive closed-set arguments extend this difference bound to arbitrary positive vectors in the completed cone. Applying it to r i(u)-x and r i(u)+x gives the reverse completed interval estimate, using the original bound norm(u) at most one. This estimate is used in the delivered theorem, including in the proof that the completed cone is salient.

Completion induction extends the original attained norm endpoints to every x in X. Adding a nonnegative multiple of i(u) gives all larger radii. The unit ball translated to i(u) is contained in the cone, proving the interior-unit requirement. The exact completed interval characterization and the original definition of orderNorm as an infimum then identify the completed order norm with the original completion norm. The canonical embedding induces the original topology; closedness of C therefore gives i(a) in the completed cone if and only if a in C.

This is the order-unit completion subclaim in the completion paragraph of the original Unit 2.2 proof and the same-cone, same-norm requirement of Unit 6.1, in AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE. Order-unit completion is mature mathematics; no novelty is claimed. The present result supplies neither extension of the original multiplication S nor window approximation, zero-face dynamics, the unit law, Jordan or JB identification. Both original source entrances and all original S,C,u,N,theta and physical consumers retain their original quantifiers in the unresolved parent. Positive evaluations, including zero mass, are not removed or normalized; their continuous extension and the remaining product arguments are separate obligations.

## References

- Truth anchor: `D5/S3/Topology/OrderUnitCompletion.faithful_completion`
- Dependency: [D5/S3/Topology/OrderUnitNorm](OrderUnitNorm.md)
