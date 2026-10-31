# Integral ordinary Specht traces

## Abstract

Integral ordinary traces of literal same-partition Specht modules

This source is part of the natively compiled full ordinary HSW consumer. The selected public supplier is TauCeti at revision 5a01f5fe3621126cccf9ba22e700493cbc7b7156; the repository pins are unchanged. The unfinished escape audit is issue 24542.

The rational trace is an algebraic integer by the pinned Mathlib theorem FDRep.isIntegral_character, hence an integer. Its numerator therefore casts back exactly. Finite scalar extension carries the rational trace to the complex trace. The existing D5 class-function descent and the full permutation partition give the integer value on a conjugacy class, including every fixed point. The independently constructed complex representation is the existing scalar extension of the polytabloid span for the literal YoungDiagram.ofPartition of the same partition.

**Theorem 1.1 (Same-partition ordinary trace certification).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \forall nu \in \operatorname{Partition}\left(n\right),\; (\operatorname{Simple}\left(\operatorname{SpechtComplex}\left(mu\right)\right)) \land (\exists sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{parts}\left(\operatorname{partition}\left(sigma\right)\right) = \operatorname{parts}\left(nu\right)) \land (\forall tau \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{parts}\left(\operatorname{partition}\left(tau\right)\right) = \operatorname{parts}\left(nu\right)) \Rightarrow (\operatorname{trace}\left(\operatorname{Complex}, \operatorname{rho}\left(\operatorname{SpechtComplex}\left(mu\right), tau\right)\right) = \operatorname{intCast}\left(\operatorname{spechtCharValue}\left(mu, nu\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtOrdinaryTrace.spechtCharValue_ordinaryTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

SpechtComplex(mu) denotes exactly TauCeti.spechtModuleℂ mu, with its existing action rho; parts(partition(sigma)) means the full permutation partition, including parts equal to one. Simple is the categorical simplicity of that finite-dimensional representation. The trace is LinearMap.trace over Complex of that action, and intCast is the integer-to-complex cast. The statement includes existence of a representative and equality at every representative. Its two conclusions certify the original irreducibility and trace obligations; integrality itself does not require simplicity. This bind-only source composition is a necessary semantic certification endpoint, with no independent admission claim.

SpechtThreeRowCauchy identifies the exact three-variable HSW.frobChar coefficient with this independently constructed same-shape ordinary trace through the mixed pairing and finite Cauchy Gram delta. Its two evaluated consumers retain literal positive parts and zero padding, full cycle partitions, both original weighted sums, reciprocal centralizer factors and the parity-dependent binomial value. The original full assertion is already preregistered in issue 21960; the coefficient audit 22528 does not close it.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtOrdinaryTrace.spechtCharValue_ordinaryTrace`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility](SpechtComplexIrreducibility.md)
