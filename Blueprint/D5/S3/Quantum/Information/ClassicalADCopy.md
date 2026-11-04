# Physical AD Conditional Copy

## Abstract

The copied density is built from arbitrary conditional BC states over a classical AD pointer.

Let p_ad be any finite nonnegative distribution of total mass one, and tau_ad any DensityState on B tensor C. classicalADState reorders recordState p tau into ABCD. copyState reorders recordState p (tau tensor Tr_B tau) into ABCDE, with E using C's finite carrier. Zero-weight blocks remain arbitrary. Conditional entanglement, singular states, and noncommuting C marginals are allowed.

**Theorem 1.1 (The physical copy recovers the original state).**

$$\operatorname{TrE}\left(omega\right) = \rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ClassicalADCopy.copyState_discard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual E partial trace of the ABCDE copy is exactly classicalADState p tau as a density state, not merely an entropy equality.

**Theorem 1.2 (ADE matches ACD as an actual density).**

$$\operatorname{omegaADE}\left(omega\right) = \operatorname{relabel}\left(\operatorname{rhoACD}\left(\rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ClassicalADCopy.copy_ade_eq_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An explicit coordinate equivalence sends the original ACD marginal to the copied ADE marginal. In particular S(E)=S(C), S(AE)=S(AC), S(DE)=S(CD), and S(ADE)=S(ACD); the smaller equalities are also proved from actual traces.

**Theorem 1.3 (The total copy entropy).**

$$\operatorname{S}\left(ABCDE\right) = \operatorname{S}\left(ABCD\right) + \operatorname{S}\left(ACD\right) - \operatorname{S}\left(AD\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ClassicalADCopy.copy_entropy_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Orthogonal CQ record entropy and product entropy imply S(ABCDE)=S(ABCD)+S(ACD)-S(AD), without any assumption on those entropy values.

**Theorem 1.4 (The actual conditional copy is Markov over AD).**

$$\operatorname{CMI}\left(E, BC, AD\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ClassicalADCopy.copy_zero_cmi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed state satisfies I(E:BC|AD)=0. This exact equality is consumed by the final theorem together with the eleven-SSA precursor.

## References

- Truth anchor: `D5/S3/Quantum/Information/ClassicalADCopy.copyState_discard`
- Truth anchor: `D5/S3/Quantum/Information/ClassicalADCopy.copy_ade_eq_relabel`
- Truth anchor: `D5/S3/Quantum/Information/ClassicalADCopy.copy_entropy_total`
- Truth anchor: `D5/S3/Quantum/Information/ClassicalADCopy.copy_zero_cmi`
- Dependency: [D5/S3/Quantum/Information/ClassicalConditionalCopy](ClassicalConditionalCopy.md)
- Dependency: [D5/S3/Quantum/Information/FivePartySSA/Consistency](FivePartySSA/Consistency.md)
