# Spectrum Commitment Settlement

## Abstract

A five-atom spectrum commitment settles by its fixed decisive-vote threshold.

**Theorem 1.1 (The fixed cutoff gives a total five-atom commitment verdict).**

$$\begin{aligned}K = \operatorname{localSpectrumCommitment}\left(atomFamily, scope, baseline, weightSpec, testPlan\right),\\\forall s: \operatorname{Fin}\left(5\right) \to Q,\\(\forall i: \operatorname{Fin}\left(5\right), \operatorname{terminalize}\left(\operatorname{s}\left(i\right)\right) \neq open) \land\\(\operatorname{localSettlement}\left(K, s\right) = success \iff 3 \leq \operatorname{decisiveCount}\left(\operatorname{comparator}\left(K\right), s\right)) \land\\(\operatorname{localSettlement}\left(K, s\right) = failure \iff \operatorname{decisiveCount}\left(\operatorname{comparator}\left(K\right), s\right) < 3).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentSettlement.spectrum_commitment_local_settlement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SpectrumCommitment is a typed seven-field record: atom family, scope, baseline, weight specification, comparator, test plan, and falsifiable prediction. The DESC-local instance fixes the last decision fields while leaving the descriptive fields explicit.

At the cutoff, an open research state terminalizes to invalid. The comparator counts only proved and refuted states among the five frozen parent atoms; statement-revised and invalid states do not contribute a decisive vote.

The prediction is a total pure function. It returns success exactly when the decisive count is at least three, and failure exactly when the count is below three, so no open verdict path remains.

Concrete five-state fixtures compile both branches: three proved states settle to success, while two refuted states and three statement-revised states settle to failure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentSettlement.spectrum_commitment_local_settlement`
