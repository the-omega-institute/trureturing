# Orthogonal Residual Recurrence

## Abstract

Recursive orthogonal extraction splits each residual and the ambient Hilbert space.

**Theorem 1.1 (Recursive orthogonal extraction splits residuals).**

$$\forall H: \operatorname{Type},\ [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(\mathbb{R}, H)] [\operatorname{CompleteSpace}(H)],\ \forall M: \operatorname{ClosedSub}(\mathbb{R}, H), E: \mathbb{N} \to \operatorname{ClosedSub}(\mathbb{R}, H),\ (\forall k, E_{k+1} \subseteq \operatorname{recursiveResidual}(M, E, k)) \Rightarrow \forall n\in \mathbb{N},\ \operatorname{recursiveResidual}(M, E, n+1) = \operatorname{accumulatedSubspace}(M, E, n+1)^{\perp} \land\\\operatorname{IsOrtho}(E_{n+1}, \operatorname{recursiveResidual}(M, E, n+1)) \land \operatorname{recursiveResidual}(M, E, n) = \operatorname{join}(E_{n+1}, \operatorname{recursiveResidual}(M, E, n+1)) \land\\\operatorname{IsOrtho}(\operatorname{accumulatedSubspace}(M, E, n+1), \operatorname{recursiveResidual}(M, E, n+1)) \land \operatorname{top} = \operatorname{join}(\operatorname{accumulatedSubspace}(M, E, n+1), \operatorname{recursiveResidual}(M, E, n+1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/OrthogonalResidualRecurrence.orthogonal_residual_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complete real inner-product space, let M be a closed subspace, and let E be a sequence of closed shells. Construct the accumulated tower from joins with E(n+1), and independently construct the residual tower from intersections with the orthogonal complements of E(n+1).

If every next shell lies in the current residual, then the next residual is the orthogonal complement of the next accumulated space. The current residual is the orthogonal direct sum of the next shell and next residual, and the ambient space is the orthogonal direct sum of the next accumulated space and residual.

Pinned Mathlib and Loogle returned ClosedSubmodule.inf_orthogonal and Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection as exact one-step identities. The Lean proof applies both directly.

## References

- Truth anchor: `D5/S3/Observer/Tomography/OrthogonalResidualRecurrence.orthogonal_residual_recurrence`
