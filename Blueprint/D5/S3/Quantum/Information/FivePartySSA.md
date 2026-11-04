# Eleven Actual Strong Subadditivities

## Abstract

A quantum five-party precursor is the sum of eleven actual nonnegative CMIs.

Apply actual density SSA to I(A:B|E), I(A:D|CE), I(A:E|BCD), I(B:E|C), I(B:E|D), I(B:E|ACD), I(C:D|BE), I(C:E|A), I(C:E|AB), I(C:E|D), and I(D:E|ABC). Each term is evaluated on a genuine partial trace and index permutation of the same five-party state. Finite exact linear arithmetic combines these eleven inequalities.

**Theorem 1.1 (The eleven-term precursor).**

$$0 \le \operatorname{ElevenCMIs}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FivePartySSA.eleven_cmi_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum is -S(A)-S(C)-2S(D)-S(E)-S(AB)+S(AC)+2S(AE)+S(BC)+S(BD)+S(CD)+2S(DE)-S(ACD)-S(BCD)+3S(ABCD)-3S(ABCDE). This precursor holds for arbitrary quantum five-party states; the copy construction is used only in the final AD theorem.

## References

- Truth anchor: `D5/S3/Quantum/Information/FivePartySSA.eleven_cmi_nonnegative`
- Dependency: [D5/S3/Quantum/Information/FivePartySSA/Marginals](FivePartySSA/Marginals.md)
