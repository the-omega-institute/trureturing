# Stephan's A005590 Zero-Set Characterization

## Abstract

The zeros of A005590 at multiples of three are exactly the Fibbinary indices.

All indices are natural numbers and the sequence r takes integer values. The predicate No11 recognizes natural numbers whose binary expansion contains no two adjacent one bits.

**Definition 1.1 (The integer sequence A005590).**

$$(\operatorname{r}\left(0\right) = 0 \land \left(\operatorname{r}\left(1\right) = 1 \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{r}\left(2 \cdot n\right) = \operatorname{r}\left(n\right)\right) \land \left(\forall n \in \mathbb{N},\; \operatorname{r}\left(2 \cdot n + 1\right) = \operatorname{r}\left(n + 1\right) - \operatorname{r}\left(n\right)\right)\right)\right))$$

*Formalization.* `D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.r` (`✓ std3`).

*Citation.* N. J. A. Sloane; Ralf Stephan (2003). *OEIS A005590, a(0)=0, a(1)=1, a(2n)=a(n), a(2n+1)=a(n+1)-a(n)*. URL: <https://oeis.org/A005590>.

*Commentary.*

The four equations define r at zero and one, and then on every even and odd index. The odd branch may take negative integer values.

**Definition 1.2 (Binary expansions without adjacent ones).**

$$\forall n \in \mathbb{N},\; \operatorname{No11}\left(n\right) \Leftrightarrow \left(\forall j \in \mathbb{N},\; (\operatorname{shiftRight}\left(n, j\right)) \bmod 4 \ne 3\right)$$

*Formalization.* `D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.No11` (`✓ std3`).

*Citation.* N. J. A. Sloane; Ralf Stephan (2003). *OEIS A005590, a(0)=0, a(1)=1, a(2n)=a(n), a(2n+1)=a(n+1)-a(n)*. URL: <https://oeis.org/A005590>.

*Commentary.*

Right-shifting n by j positions exposes bits j and j+1 as the two low bits. Their remainder modulo four is three exactly when both bits are one, so No11 excludes that pattern at every position.

**Theorem 1.3 (Stephan's zero-set conjecture).**

$$\forall n \in \mathbb{N},\; \operatorname{r}\left(3 \cdot n\right) = 0 \Leftrightarrow \operatorname{No11}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a005590-zero-set-fibbinary-characterization` (proved) by `D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a005590-zero-set-fibbinary-characterization","declaration_gid":"D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

A strong-induction invariant for each adjacent pair (r(n),r(n+1)) shows that the pair is nonzero and controls the sign of r(n)(r(n)-r(n+1)). It yields the zero-set classification modulo four. The corresponding add-a-bit classification for No11 then proves the equivalence for every natural n. This establishes only the zero-set equivalence; no growth-rate formula or further partial recurrence is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.No11`
- Truth anchor: `D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.r`
- Truth anchor: `D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.result`
