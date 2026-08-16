# The Resonance Factors Select Alphabet Value Three

## Abstract

The two exceptional resonance factors vanish identically exactly at alphabet value three.

**Theorem 1.1 (The two resonance factors are identically zero exactly when m equals three).**

$$\forall m\in\mathbb{Z},\ (\forall p,r\in\mathbb{Z},\ (2\cdot r\cdot (m-3)\cdot (2p+r)=0 \land -2\cdot r\cdot (m-3)\cdot (p+r)=0)) \iff m=3$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/ResonanceFactors.resonance_factors_identically_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Residual E.67 isolates two exceptional deficit factors, 2r(m-3)(2p+r) and -2r(m-3)(p+r). Their common linear factor m-3 shows immediately that m=3 makes both factors vanish for every integer p and r. Conversely, if both factors vanish identically, evaluating the first one at p=0 and r=1 gives 2(m-3)=0 in the integers, hence m=3.

The Lean proof uses mathlib's integer zero-product characterization to cancel the nonzero factor 2 after this single evaluation. Local D5 and pinned-mathlib searches found no theorem for these specific factors; Loogle found only the generic Int.mul_eq_zero lemma, which the proof reuses.

This theorem closes only the explicit alphabet-resonance clause of E.67. It does not formalize the remaining sixteen deficit branches, the block-length resonance ps-qr=(-1)^l p_(k-l-1), or the surrounding continued-fraction recurrence audit.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/ResonanceFactors.resonance_factors_identically_zero_iff`
