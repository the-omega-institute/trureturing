# Raw Anchored Radical Descent

## Abstract

The raw C133-V balance yields the anchored free comparison form, its two-sided radical quotient, and the exact marker transport identities.

**Theorem 1.1 (Anchored radical descent and marker transport).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U \to M, c \to M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) \Rightarrow \operatorname{rawAnchoredRadicalDescent}\left(U, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_anchored_radical_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The construction uses the actual finite-support free real carrier e_a = δ_a − δ_1 and the bilinear kernel (c(a,1)+c(1,b)−c(a,b))/2. The two-sided radical is quotiented before marker transport. RawBalance supplies the exact marker invariance, period-three row and column readouts, anchored-form invariance, radical stability, beta(Ua) transport, R^3 beta identity, and the unit defect identities. No associativity, commutativity, cancellation, positivity or Hilbert representation is assumed.

This is a finite Section 2 dependency unit for C133 Continuation V. The ordered Fourier constraints, defect pairing isotropy and full Hilbert representation remain open until separately derived from the constructed quotient.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.raw_anchored_radical_descent`
- Dependency: [D5/S3/Quantum/Completion/RawThreePhaseDescent](RawThreePhaseDescent.md)
