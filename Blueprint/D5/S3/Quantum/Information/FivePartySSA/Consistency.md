# Marginal Consistency after Discarding E

## Abstract

Actual four-party and five-party submarginals agree.

The composed coordinate sums show that first discarding E and then retaining any register set needed by the proof gives the same density, up to a basis permutation. Entropy is invariant under that permutation. These are consumed consistency lemmas, not extra hypotheses.

**Theorem 1.1 (The AD entropy is unchanged).**

$$\operatorname{SAD}\left(\operatorname{TrE}\left(\rho\right)\right) = \operatorname{SAD}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FivePartySSA/Consistency.entropyAD_discard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retained AD marginal has the same entropy whether taken directly or through the ABCD partial trace. All required sibling identities use the same actual trace composition theorem.

## References

- Truth anchor: `D5/S3/Quantum/Information/FivePartySSA/Consistency.entropyAD_discard`
- Dependency: [D5/S3/Quantum/Information/FivePartySSA/Marginals](Marginals.md)
- Dependency: [D5/S3/Quantum/Information/FourPartyMarginals](../FourPartyMarginals.md)
