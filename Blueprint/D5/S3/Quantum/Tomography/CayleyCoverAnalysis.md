# Cayley Cover Analysis

## Abstract

Analytic interfaces for compact chart coverage, local uniqueness, root migration and global residual barriers.

**Theorem 1.1 (Two compact charts cover each unit-circle coordinate).**

$$CompactSignedCayleyCover.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyCoverAnalysis.compact_signed_cayley_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unit-circle coordinate is represented by one of two closed signed Cayley charts with t in [-1,1]. Applied to five dephased phases, this gives the 32 compact charts including their seams. The theorem does not trust an external subdivision result.

**Theorem 1.2 (Derivative bounds imply quantitative local uniqueness).**

$$PreconditionedResidualControlsDisplacement.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyCoverAnalysis.preconditioned_residual_controls_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a convex set, if C times the actual Frechet derivative differs from the identity by operator norm at most q, then (1-q) times the distance between two points is bounded by their preconditioned residual difference. For q<1, a convex box contains at most one root. The proof consumes Mathlib's Frechet mean-value inequality.

**Theorem 1.3 (A small parameter perturbation bounds root motion).**

$$PreconditionedRootMigration.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyCoverAnalysis.root_displacement_le_of_preconditioned_parameter_perturbation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If roots of two parameter instances remain in one convex uniqueness box and the preconditioned residual perturbation is at most rho, their displacement is at most rho/(1-q). The theorem assumes the second root exists; it is a continuation bound, not a numerical existence oracle.

**Theorem 1.4 (A residual gap prevents roots outside the certified cover).**

$$UniformResidualRootCover.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyCoverAnalysis.root_mem_iUnion_of_uniform_residual_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the center-parameter residual is at least eta outside a union of certified root neighborhoods, while changing the parameter perturbs the residual by at most rho<eta. Then every root at the perturbed parameter remains inside that union. Compactness and interval arithmetic are deliberately external hypotheses to be discharged by later analytic reflection, rather than hidden inside this theorem.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/CayleyCoverAnalysis.compact_signed_cayley_cover`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyCoverAnalysis.preconditioned_residual_controls_displacement`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyCoverAnalysis.root_displacement_le_of_preconditioned_parameter_perturbation`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyCoverAnalysis.root_mem_iUnion_of_uniform_residual_gap`
