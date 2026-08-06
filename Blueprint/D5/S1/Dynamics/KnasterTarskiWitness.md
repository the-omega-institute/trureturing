# Knaster–Tarski Witness

## Abstract

Frozen proofs assemble the extremal fixed-point theorem with its three-state instance.

**Theorem 1.1 (Extremal fixed points with the three-state successor instance).**

$$(\forall f:\alpha\to_{o}\alpha,\ \operatorname{lfp}(f)=\min\operatorname{Fix}(f)\ \land\ \operatorname{gfp}(f)=\max\operatorname{Fix}(f))\ \land\ \operatorname{lfp}(\sigma_{3})=\varnothing\ \land\ \operatorname{gfp}(\sigma_{3})=\mathrm{univ}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/KnasterTarskiWitness.knaster_tarski_with_three_cycle_instance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every monotone endomorphism of a complete lattice, the least fixed point is the least element of the fixed-point set and the greatest fixed point is its greatest element. For the three-state successor-cycle operator, the least fixed point is the empty set and the greatest fixed point is the full state set.

The statement is assembly-only: both conjuncts are witnessed by their frozen proofs in the Knaster–Tarski module, so the theorem packages the general result and its concrete instance behind a single declaration without re-proving either.

## References

- Dependency: [D5/S1/Dynamics/KnasterTarski](KnasterTarski.md)
