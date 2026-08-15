# Finite-Stage Orthogonal Expansion

## Abstract

Finite orthogonal shell towers expand into the initial space, extracted shells, and residual.

**Theorem 1.1 (Finite orthogonal shell towers expand stagewise).**

$$\forall H: \operatorname{Type},\ [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(\mathbb{R}, H)] [\operatorname{CompleteSpace}(H)],\ \forall S, E: \mathbb{N} \to \operatorname{ClosedSub}(\mathbb{R}, H),\ (\forall k, S_{k+1} = \operatorname{join}(S_{k}, E_{k+1})) \Rightarrow (\forall k, E_{k+1} \subseteq S_{k}^{\perp}) \Rightarrow \forall n\in \mathbb{N},\ S_{n} = \operatorname{join}(S_{0}, \operatorname{finiteShellSpan}(E, n)) \land\\\operatorname{top} = \operatorname{join}(\operatorname{join}(S_{0}, \operatorname{finiteShellSpan}(E, n)), S_{n}^{\perp}) \land\\S_{n}^{\perp} = \operatorname{join}(E_{n+1}, S_{n+1}^{\perp}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/FiniteStageExpansion.finite_stage_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complete real inner-product space. Let S and E be sequences of closed subspaces. At each stage, S(k+1) is the join of S(k) and E(k+1), while E(k+1) lies in the orthogonal complement of S(k).

For every finite stage n, S(n) is the join of S(0) with the first n shells. The whole space is the join of that accumulated stage and its orthogonal residual. The current residual is itself the join of the next shell and the next residual.

Pinned Mathlib and Loogle returned Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection as the exact one-step splitting result, which the Lean proof imports and applies. Repository and library searches found no exact finite-stage expansion, so the shell accumulation is proved by induction.

The closed-subspace formulation preserves arbitrary complete Hilbert spaces and therefore includes finite-dimensional extracted shells without restricting the ambient space to finite dimension.

## References

- Truth anchor: `D5/S3/Observer/Tomography/FiniteStageExpansion.finite_stage_expansion`
