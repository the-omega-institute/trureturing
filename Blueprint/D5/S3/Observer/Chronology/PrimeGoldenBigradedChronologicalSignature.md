# Prime-Golden Bigraded Chronological Signature

## Abstract

Prime-factor count and Zeckendorf-selected short-step count form an additive bigrading beside the chronological Hopf signature.

**Theorem 1.1 (Bigrading survives reversal while Magnus orientation flips).**

$$\begin{gathered}\forall f, \forall t, \forall p: Nat.Primes, \forall w,\\{}\operatorname{isSinglePrimeWord}(p, w) \Rightarrow\\{}\operatorname{bigradedChronologicalSignature}(-f, \operatorname{reverse}(w)) = \operatorname{bigradedAntipode}(\operatorname{bigradedChronologicalSignature}(f, w)) \land\\{}\operatorname{factorParityCharacter}(\operatorname{primeGoldenBidegree}(w)) = \operatorname{liouville}(\operatorname{primeWordProduct}(w)) \land\\{}\operatorname{goldenStepParityCharacter}(\operatorname{primeGoldenBidegree}(w)) = \operatorname{prod}(\operatorname{map}(goldenStepParityLetter, w)) \land\\{}\operatorname{scalarStepEndpoint}(t, w) = \operatorname{bidegreePhase}(t, p, \operatorname{primeGoldenBidegree}(w)) \land\\{}\operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(-f, \operatorname{reverse}(w))) = -\operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, w)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/PrimeGoldenBigradedChronologicalSignature.prime_golden_bigraded_time_reversal_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Chronological concatenation multiplies the step-two signature and adds two unsigned degrees: prime-event count with multiplicity and the count of Zeckendorf-selected short golden steps.

Reverse-and-negate applies the Hopf antipode to the chronological component while preserving the bidegree. The first parity character is the Liouville value of the prime product. The second is the product of local golden long-short signs.

For a word contained in one prime channel, the scalar frequency and terminal Euler phase factor through the bidegree. The Magnus coordinate retains oriented order and changes sign under reversal.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimeGoldenBigradedChronologicalSignature.prime_golden_bigraded_time_reversal_laws`
- Dependency: [D5/S3/Observer/Chronology/PrimeWordAntipodeParityStepBridge](PrimeWordAntipodeParityStepBridge.md)
