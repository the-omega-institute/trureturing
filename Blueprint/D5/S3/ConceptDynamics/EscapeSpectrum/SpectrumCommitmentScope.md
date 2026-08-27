# Spectrum Commitment Atom Family and Scope

## Abstract

The local DESC commitment has exactly five indexed atoms and the stated scope boundary.

**Theorem 1.1 (The five named DESC atoms have the exact local scope contract).**

$$\begin{aligned}\forall B, W, P: \operatorname{Type},\\b: B, w: W, p: P,\\K = \operatorname{descSpectrumCommitment}\left(b, w, p\right),\\\operatorname{card}\left(\operatorname{atomFamily}\left(K\right)\right) = 5 \land\\\operatorname{Bijective}\left(index\right) \land\\(\forall a: SpectrumAtom, a \in \operatorname{atomFamily}\left(K\right)) \land\\(\forall a: SpectrumAtom, \operatorname{scope}\left(K, a, finiteLanguage\right) = true \land \operatorname{scope}\left(K, a, countableLanguage\right) = true) \land\\\operatorname{scope}\left(K, T4, largerBoundaryLanguage\right) = true \land\\(\forall a: SpectrumAtom, \operatorname{scope}\left(K, a, largerBoundaryLanguage\right) = true \iff a = T4).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentScope.spectrum_commitment_atom_family_and_scope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The construction instantiates the frozen seven-field SpectrumCommitment record. It supplies a finite atom family and scope predicate while leaving baseline, weight specification, and test plan explicit.

SpectrumAtom has the five named constructors T1 through T5. Its public index map is bijective onto Fin 5, so no theorem atom collides with or is omitted from the settlement positions.

Every named atom admits finite-language and countable-language scopes. The explicitly larger boundary-language scope is admitted exactly for T4, matching the countermodel exception without widening the main theorem domain.

A concrete Boolean computation witnesses that T4 admits the larger boundary scope while T1 does not, and Unit metadata instantiates the generic theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentScope.spectrum_commitment_atom_family_and_scope`
- Dependency: [D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentSettlement](SpectrumCommitmentSettlement.md)
