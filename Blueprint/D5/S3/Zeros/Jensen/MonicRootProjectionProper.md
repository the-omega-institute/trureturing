# Monic Root Projection Properness

## Abstract

Zero loci of continuous fixed-degree monic complex polynomial families project properly.

**Theorem 1.1 (Roots cannot escape above a compact parameter set).**

Lean statement: `D5/S3/Zeros/Jensen/MonicRootProjectionProper.monic_fixed_degree_root_projection_isProper`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/MonicRootProjectionProper.monic_fixed_degree_root_projection_isProper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be any Hausdorff compactly coherent topological space. Let P assign a monic complex polynomial to each t in A, all of natural degree q, for any natural number q. Assume the coefficient maps through degree q are continuous. On the zero graph E={(t,z):P(t)(z)=0}, the projection (t,z) to t is proper. Neither compactness of A nor simple roots nor a supplied uniform root bound nor a labeling of roots is required.

The polynomial evaluation is jointly continuous by its fixed finite coefficient sum. Above any compact K in A, the sum of the lower coefficient norms is bounded. The existing coefficient-sum Cauchy root bound then places every root above K inside one closed complex ball. The zero graph above K is a closed subset of K times that ball, hence compact. Transferring this compactness to E proves that every compact preimage is compact; Mathlib's proper-map criterion supplies the conclusion.

For q=0, monicity forces P(t)=1 and E is empty. This case is included without selecting a root or assuming surjectivity. For positive degree, repeated roots are allowed; properness alone supplies no local homeomorphism or covering. The theorem is intended to combine with separately proved simple-root local charts, so that the critical-root image is closed and root lifts can be considered on a simple-root domain.

This is a classical Cauchy-bound compactness argument. The root-bound proof is reused from the existing CompactSeparatedRealContinuation module through its public interface. The result proves no RH, Robin inequality above 5040, original-node sign law or signed cofactor transfer, and makes no claim of literature originality.

The faithful dependent registration and its four mathematical proof obligations compile. Complete source reconstruction remains unfinished: the main audit is declared_unresolved with IE-C050 ClosedTruthReadout, unclassified_form, source.observation_data. The exact failure and missing binding certificate are recorded in https://github.com/the-omega-institute/trureturing/issues/16310. The existing coefficient-sum helper audit is declared_validated. This distinction concerns audit evidence; the theorem's kernel proof retains its full hypotheses.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/MonicRootProjectionProper.monic_fixed_degree_root_projection_isProper`
- Dependency: [D5/S3/Zeros/Jensen/CompactSeparatedRealContinuation](CompactSeparatedRealContinuation.md)
