# Conditional Cross-Species Consensus

## Abstract

A shared irreducible complex symmetry forces every equivariant Hermitian observable to have one common real reading across normalized probes.

Let U be a representation of any group by finite complex matrices. The physical inputs remain explicit: all species use this same U, and h_irreducible says its invariant-subspace order is simple. The observable A is Hermitian and commutes with every U(g). No claim derives these assumptions from an observer principle. Unitary representations are included; unitarity is not needed for the stated conditional result.

**Theorem 1.1 (Equivariant observables are real scalar matrices).**

$$\operatorname{Irreducible}\left(U\right) \land \operatorname{Hermitian}\left(A\right) \land \operatorname{Equivariant}\left(U, A\right) \Rightarrow \operatorname{RealScalarIdentity}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CrossSpeciesConsensus.equivariant_selfAdjoint_eq_smul_id_of_irreducible` (`✓ std3`). ∎

*Citation.* Stepan Nesterov and the mathlib community (2026). *Irreducible representations and scalar intertwining endomorphisms*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RepresentationTheory/Irreducible.lean>.

*Commentary.*

Transport U and A through the matrix-to-linear-map algebra equivalence. Commutation makes A an intertwining endomorphism. Schur's lemma makes it a complex scalar identity; Hermitian diagonal entries make that scalar real. The argument permits every finite dimension.

**Theorem 1.2 (Every normalized probe reads the same scalar).**

$$\operatorname{ReTrProduct}\left(\operatorname{probe}\left(s\right), A\right) = r = \operatorname{ReTrProduct}\left(\operatorname{probe}\left(t\right), A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CrossSpeciesConsensus.cross_species_consensus` (`✓ std3`). ∎

*Citation.* Stepan Nesterov and the mathlib community (2026). *Irreducible representations and scalar intertwining endomorphisms*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RepresentationTheory/Irreducible.lean>.

*Commentary.*

For any species-indexed family rho_s with trace rho_s = 1, the theorem produces a single real r with A = r I and Re tr(rho_s A) = r for every species. Consequently any two readings agree. Positive density matrices satisfy the hypotheses; trace normalization alone suffices for the algebraic conclusion. This concerns the same observable, with the same calibration, for all species.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CrossSpeciesConsensus.cross_species_consensus`
- Truth anchor: `D5/S3/Quantum/Matrix/CrossSpeciesConsensus.equivariant_selfAdjoint_eq_smul_id_of_irreducible`
