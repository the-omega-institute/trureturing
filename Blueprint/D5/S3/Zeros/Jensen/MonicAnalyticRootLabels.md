# Monic Analytic Root Labels

## Abstract

Simple-root monic analytic polynomial families have a covering zero graph and global analytic labels.

**Theorem 1.1 (The simple-root zero graph projects as a covering).**

Lean statement: `D5/S3/Zeros/Jensen/MonicAnalyticRootLabels.monic_analytic_simple_root_projection_isCovering`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/MonicAnalyticRootLabels.monic_analytic_simple_root_projection_isCovering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an open complex parameter domain, assume a monic fixed-degree polynomial family whose coefficients through the degree are analytic and every root is simple. The zero graph in the parameter subtype times the complex plane projects to the parameter subtype as a covering map.

The proof uses the finite coefficient sum for joint analyticity, the native complex implicit-function theorem for actual local root graphs, the fixed-degree monic properness theorem for compact preimages, and finite fibers. Degree zero and empty fibers are included.

The four-slot mathematical registration evidence compiles, but the covering audit is declared_unresolved: IE-C050 ClosedTruthReadout, unclassified_form, source.unlinked_operand at Classical.choice. The missing complete source/readout binding certificate is recorded in https://github.com/the-omega-institute/trureturing/issues/16328. The kernel theorem and its full telescope are retained.

**Theorem 1.2 (Simple roots admit globally compatible analytic labels).**

Lean statement: `D5/S3/Zeros/Jensen/MonicAnalyticRootLabels.monic_analytic_simple_roots_have_global_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/MonicAnalyticRootLabels.monic_analytic_simple_roots_have_global_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a simply connected open parameter subtype, the covering lifts of the identity, one for each root at a base point, produce exactly q analytic root labels indexed by Fin q. The labels are pairwise distinct and exhaust every root in every fiber; a root family analytic on the domain is uniquely determined by its base value.

Analyticity is obtained by comparing each continuous lift with the local implicit-function branch. Complex splitting and the simple-derivative hypothesis provide exactly q distinct base roots. The theorem makes no claim about RH, Robin inequalities above 5040, signed cofactor transfer, or a uniform collar beyond the open domain.

The global-labels audit is declared_validated with a source-equivalence certificate for the complete original telescope and the selected exhaustion readout. This status does not validate the separate covering audit.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/MonicAnalyticRootLabels.monic_analytic_simple_root_projection_isCovering`
- Truth anchor: `D5/S3/Zeros/Jensen/MonicAnalyticRootLabels.monic_analytic_simple_roots_have_global_labels`
- Dependency: [D5/S3/Zeros/Jensen/MonicRootProjectionProper](MonicRootProjectionProper.md)
