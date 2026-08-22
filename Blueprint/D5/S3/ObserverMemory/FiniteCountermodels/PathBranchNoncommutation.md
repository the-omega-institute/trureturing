# Path Limits and Transient Branches

## Abstract

Ordinary backward paths retain periodic dynamics but discard transient branches.

**Theorem 1.1 (The same periodic path limit can carry different complete branch trees).**

$$(\forall tau, sigma, e, x,\ p_0(BackwardEquiv(tau, sigma, e)(x)) = e(p_0(x))) \land 
(\exists c\in Fin(2), \neg Periodic(oneBranchMap, c)) \land (\exists c\in Fin(3), \neg Periodic(twoBranchMap, c)) \land 
(\forall p, countermodelCoreEquiv(oneBranchMap(p)) = twoBranchMap(countermodelCoreEquiv(p))) \land 
(\forall x, p_0(BackwardEquiv(oneBranchMap, twoBranchMap, countermodelCoreEquiv)(x)) = countermodelCoreEquiv(p_0(x))) \land 
(\forall c\in Fin(2), \neg Periodic(oneBranchMap, c) \Rightarrow IsEmpty(TransientChild(oneBranchMap, c))) \land (\forall c\in Fin(3), \neg Periodic(twoBranchMap, c) \Rightarrow IsEmpty(TransientChild(twoBranchMap, c))) \land 
\operatorname{card}(TransientChild(oneBranchMap, 0)) = 1 \land \operatorname{card}(TransientChild(twoBranchMap, 0)) = 2 \land \operatorname{card}(TransientChild(oneBranchMap, 0)) \neq \operatorname{card}(TransientChild(twoBranchMap, 0)) \land 
\neg\exists u: Fin(2) \equiv Fin(3),\ \operatorname{Semiconj}(u, oneBranchMap, twoBranchMap).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/PathBranchNoncommutation.path_limit_branch_noncommutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

BackwardOrbit is the repository's compatible predecessor-path type. The displayed backward equivalence is constructed by evaluating at coordinate zero, transporting through an equivalence of periodic cores, and applying the inverse canonical path map.

TransientChild(tau,p) is constructed from the source update: it contains exactly the nonperiodic x with tau(x)=p. The concrete constant maps on Fin 2 and Fin 3 have one-point periodic cores. Every transient child is a leaf, while their root child counts are one and two, so these are different complete height-one trees.

The periodic-core equivalence intertwines the induced periodic maps, and the canonical backward-path equivalence has the stated coordinate-zero computation. No relabeling can conjugate the maps because Fin 2 and Fin 3 have different cardinalities.

Repository search found exact canonical periodic-core/path results but no transient-child or branch-completion primitive. Pinned Mathlib supplied periodic-point membership and finite-cardinality support, but no theorem combining the path equivalence and countermodel.

## References

- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/PathBranchNoncommutation.path_limit_branch_noncommutation`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/IdentityFuturePastGap](../InverseLimits/IdentityFuturePastGap.md)
