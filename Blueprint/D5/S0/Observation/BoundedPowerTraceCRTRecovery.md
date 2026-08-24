# Bounded Power-Trace Recovery from a CRT Image

## Abstract

A CRT image modulo a product wider than a known trace interval uniquely recovers the bounded matrix power trace.

**Lemma 1.1 (A wide modulus separates bounded integers).**

$$\forall M, B \in \mathbb{N}, \forall m, n \in \mathbb{Z}, (2 \times B < M \land \left|m\right| < B \land \left|n\right| < B \land m \equiv n (\operatorname{mod} M)) \Rightarrow m = n.$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/BoundedPowerTraceCRTRecovery.bounded_int_unique_of_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M is strictly larger than twice B, reduction modulo M is injective on the integers whose absolute values are strictly below B. Thus two integers in that open interval with the same residue are equal.

Indeed, their difference has absolute value below M and is divisible by M. The only such multiple of M is zero, which forces the original integers to coincide.

**Theorem 1.2 (A wide CRT image uniquely determines a bounded power trace).**

$$\forall d: \operatorname{Type}, \forall M, B, j \in \mathbb{N}, \forall A, C \in \operatorname{Matrix}\left(d, d, \mathbb{Z}\right), (\operatorname{Fintype}\left(d\right) \land 2 \times B < M \land \left|\operatorname{tr}\left(A^{j}\right)\right| < B \land \left|\operatorname{tr}\left(C^{j}\right)\right| < B \land \operatorname{crtImage}\left(M, \operatorname{tr}\left(A^{j}\right)\right) = \operatorname{crtImage}\left(M, \operatorname{tr}\left(C^{j}\right)\right)) \Rightarrow \operatorname{tr}\left(A^{j}\right) = \operatorname{tr}\left(C^{j}\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Observation/BoundedPowerTraceCRTRecovery.power_trace_unique_of_crt_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and C be square integer matrices on the same finite index type. For any natural exponent j, suppose both jth-power traces lie strictly between -B and B and the product modulus M exceeds 2B. Equality of their assembled CRT images then forces the two traces to be equal.

The result is a uniqueness statement after the component residues have already been assembled into one residue modulo M. It neither constructs that CRT assembly nor recovers the matrices themselves; it recovers only the specified power trace.

## References

- Truth anchor: `D5/S0/Observation/BoundedPowerTraceCRTRecovery.bounded_int_unique_of_mod`
- Truth anchor: `D5/S0/Observation/BoundedPowerTraceCRTRecovery.power_trace_unique_of_crt_image`
