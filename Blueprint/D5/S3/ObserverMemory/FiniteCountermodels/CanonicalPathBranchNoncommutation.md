# Path Limits and Canonical Transient Branches

## Abstract

Backward paths retain periodic dynamics but discard canonical transient branches.

**Theorem 1.1 (The same periodic path limit can carry different canonical branch trees).**

$$(\forall tau, sigma, e, x,\ p_0(BackwardEquiv(tau, sigma, e)(x)) = e(p_0(x))) \land 
(\exists c\in Fin(2), \neg Periodic(oneBranchMap, c)) \land (\exists c\in Fin(3), \neg Periodic(twoBranchMap, c)) \land 
(\forall p, countermodelCoreEquiv(oneBranchMap(p)) = twoBranchMap(countermodelCoreEquiv(p))) \land 
(\forall x, p_0(BackwardEquiv(oneBranchMap, twoBranchMap, countermodelCoreEquiv)(x)) = countermodelCoreEquiv(p_0(x))) \land 
(\forall c\in Fin(2), \neg Periodic(oneBranchMap, c) \Rightarrow IsEmpty(TransientChild(oneBranchMap, c))) \land (\forall c\in Fin(3), \neg Periodic(twoBranchMap, c) \Rightarrow IsEmpty(TransientChild(twoBranchMap, c))) \land 
\operatorname{card}(TransientChild(oneBranchMap, 0)) = 1 \land \operatorname{card}(TransientChild(twoBranchMap, 0)) = 2 \land \operatorname{card}(TransientChild(oneBranchMap, 0)) \neq \operatorname{card}(TransientChild(twoBranchMap, 0)) \land 
\neg\exists u: Fin(2) \equiv Fin(3),\ \operatorname{Semiconj}(u, oneBranchMap, twoBranchMap).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/CanonicalPathBranchNoncommutation.path_limit_branch_noncommutation_ssot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

BackwardOrbit is the repository's compatible predecessor-path type. The displayed backward equivalence evaluates at coordinate zero, transports through an equivalence of periodic cores, and applies the inverse canonical path map.

TransientChild is imported from the fixed-point family source of truth. Its subtype contains exactly the nonperiodic predecessors mapped to the specified parent. The constant maps on Fin 2 and Fin 3 have one-point periodic cores, but root child counts one and two.

Every transient child is a leaf. The periodic-core equivalence intertwines the induced periodic maps, while the canonical backward-path equivalence has the displayed coordinate-zero rule. No relabeling can conjugate carriers of different cardinalities.

Repository search found the exact path/core results and the canonical transient-child predicate. The frozen finite countermodel theorem is reused through the thinnest wrapper that exposes that predicate directly in all branch-sensitive public clauses.

## References

- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/CanonicalPathBranchNoncommutation.path_limit_branch_noncommutation_ssot`
- Dependency: [D5/S1/FixedPoints/RootedTransientTreeClassification](../../../S1/FixedPoints/RootedTransientTreeClassification.md)
- Dependency: [D5/S3/ObserverMemory/FiniteCountermodels/PathBranchNoncommutation](PathBranchNoncommutation.md)
