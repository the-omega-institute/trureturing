# Truthful Reporting Blocks an Inverted Spectrum

## Abstract

Exact public recovery forces phenomenal agreement; an inverted pair refutes it.

**Theorem 1.1 (Truthful public reporting forces phenomenal agreement).**

$$\forall State \in Type, Phenomenal \in Type, Public \in Type, p \in State \to Phenomenal, q \in State \to Public, x \in State, y \in State,\; \operatorname{TruthfulPublicReport}\left(p, q\right) \Rightarrow \left(q\left(x\right) = q\left(y\right) \Rightarrow p\left(x\right) = p\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/TruthfulReportBlocksInvertedSpectrum.truthful_public_report_forces_phenomenal_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

TruthfulPublicReport(p, q) requires a total recovery map from every public value to a phenomenal value, with p equal to that map after q. Thus the phenomenal readout is determined entirely by the public readout.

Consequently, any two states in the same public fiber must have the same phenomenal value. The conclusion concerns every pair of states, not only values in a chosen or observed part of the public image.

**Lemma 1.2 (An inverted pair forces premise failure).**

$$\forall x3 \in \left(\forall x3 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x4 \in \left(\forall x4 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x5 \in \mathord{\cdot},\; \forall x6 \in \mathord{\cdot},\; \mathit{x3}\left(\mathit{x5}\right) \ne \mathit{x3}\left(\mathit{x6}\right) \Rightarrow \left(\mathit{x4}\left(\mathit{x5}\right) = \mathit{x4}\left(\mathit{x6}\right) \Rightarrow \left(\neg \left(\forall x9 \in \mathord{\cdot},\; \forall x10 \in \mathord{\cdot},\; \mathit{x4}\left(\mathit{x9}\right) = \mathit{x4}\left(\mathit{x10}\right) \Rightarrow \mathit{x3}\left(\mathit{x9}\right) = \mathit{x3}\left(\mathit{x10}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/TruthfulReportBlocksInvertedSpectrum.inverted_spectrum_requires_premise_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose two states have the same public value but different phenomenal values. Substituting this pair into a claimed constancy law for all public fibers produces an immediate contradiction.

The result therefore denies the single fiber-constancy premise needed by exact truthful recovery. It establishes that some explanation of premise failure is unavoidable without selecting one particular failure mode.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reporting/TruthfulReportBlocksInvertedSpectrum.inverted_spectrum_requires_premise_failure`
- Truth anchor: `D5/S3/ConceptDynamics/Reporting/TruthfulReportBlocksInvertedSpectrum.truthful_public_report_forces_phenomenal_agreement`
