# Recursive Completeness Criterion

## Abstract

Terminal residual vanishing characterizes complete recursive Hilbert decomposition.

**Theorem 1.1 (Terminal residual characterizes recursive completeness).**

$$\forall H: \operatorname{CompleteRealHilbertSpace}(H),\ \forall M: \operatorname{ClosedSub}(\mathbb{R}, H), E: \mathbb{N} \to \operatorname{ClosedSub}(\mathbb{R}, H),\ (\forall n\in \mathbb{N}, E_{n+1} \subseteq \operatorname{recursiveResidual}(M, E, n)) \Rightarrow\\((\operatorname{terminalResidual}(M, E) = \operatorname{bot}() \Leftrightarrow \operatorname{terminalAccumulated}(M, E) = \operatorname{top}()) \land\\(\operatorname{terminalAccumulated}(M, E) = \operatorname{top}() \Leftrightarrow \operatorname{shellExpansion}(M, E) = \operatorname{top}()) \land\\(\operatorname{terminalResidual}(M, E) = \operatorname{bot}() \Rightarrow \operatorname{IsHilbertSum}(\operatorname{knownShellFamily}(M, E))) \land\\(\operatorname{terminalResidual}(M, E) \neq \operatorname{bot}() \Rightarrow (\operatorname{IsHilbertSum}(\operatorname{fullShellFamily}(M, E)) \land\\\forall x, x\in \operatorname{terminalResidual}(M, E) \Rightarrow (x\in M^{\perp} \land \forall n\in \mathbb{N}, x\in E_{n+1}^{\perp})))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/RecursiveCompletenessCriterion.recursive_completeness_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complete real Hilbert space, M a closed initial subspace, and E a sequence of closed shells. The accumulated tower and residual tower are imported from the canonical recurrence family. The terminal accumulated space is their finite-stage supremum, while the terminal residual is the intersection of all residuals.

If each next shell lies in the current recursively constructed residual, then terminal residual zero, terminal accumulated space equal to the ambient space, and the closed expansion of M with every shell equal to the ambient space are equivalent.

In the complete case, M and all shells form an exact Hilbert sum. In the incomplete case, adjoining the terminal residual gives the exact Hilbert sum, and every vector in that residual is orthogonal to M and to every selected shell. This is the formal never-named sector.

Pinned library search found the exact infinite-intersection orthogonal identity and the internal Hilbert-sum constructor. The Lean proof applies them to the imported recursive residual semantics.

## References

- Truth anchor: `D5/S3/Observer/Tomography/RecursiveCompletenessCriterion.recursive_completeness_criterion`
- Dependency: [D5/S3/Observer/Tomography/OrthogonalResidualRecurrence](OrthogonalResidualRecurrence.md)
