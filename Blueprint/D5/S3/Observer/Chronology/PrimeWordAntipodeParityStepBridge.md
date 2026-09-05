# Prime-Word Antipode, Parity, and Golden-Step Bridge

## Abstract

Prime-word time reversal retains ordered information in the Magnus lift, leaves Liouville factor parity after commutative readout, and preserves the reversed golden step total and scalar endpoint.

**Theorem 1.1 (Three readouts of prime-step time reversal).**

$$\operatorname{A}(w)=\lambda(n) \operatorname{R}(w),\\{}\operatorname{Step}(rev(w))=\operatorname{Step}(w),\\{}\omega_{2}(S(w))=-\omega_{2}(w).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/PrimeWordAntipodeParityStepBridge.prime_word_time_reversal_readout_trichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chronological Hopf antipode reverses the event word and negates every observed primitive increment. Under a commutative integer readout the reversal disappears, while the degree sign remains and equals the Liouville value of the represented prime product.

The same event stream carries an independent Zeckendorf least-index parity. It selects the long phi-squared or short phi prime-local step. Reversing the list preserves its total frequency and terminal scalar phase, whereas the step-two Magnus coordinate changes sign.

The companion theorems separate the Mobius channel as Liouville parity restricted to squarefree products, with nonsquarefree products sent to zero. No identification of factor-count parity with Zeckendorf parity is asserted.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimeWordAntipodeParityStepBridge.prime_word_time_reversal_readout_trichotomy`
- Dependency: [D5/S3/Analytic/GoldenEulerBetaZeckendorf](../../Analytic/GoldenEulerBetaZeckendorf.md)
- Dependency: [D5/S3/Observer/Chronology/ChronologicalSignatureHopf](ChronologicalSignatureHopf.md)
- Dependency: [D5/S3/Observer/GoldenPrimeCircle/GoldenEulerStepPhaseLaw](../GoldenPrimeCircle/GoldenEulerStepPhaseLaw.md)
