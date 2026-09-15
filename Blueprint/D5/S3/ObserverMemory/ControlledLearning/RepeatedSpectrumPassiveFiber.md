# Repeated-spectrum passive observation

## Abstract

Repeated positive spectra have an exact commutant fiber for two passive learning steps.

**Theorem 1.1 (Complete two-step output fiber, including resonance).**

Lean statement: `D5/S3/ObserverMemory/ControlledLearning/RepeatedSpectrumPassiveFiber.two_step_outputs_iff_commuting_difference`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ControlledLearning/RepeatedSpectrumPassiveFiber.two_step_outputs_iff_commuting_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite real diagonal matrix with positive diagonal entries. Consider two pairs of symmetric external Gram blocks, the same S as initial output, and nonzero step sizes eta and tau. Each step is the exact simultaneous gradient-descent recurrence for the fixed loss one half of the squared Frobenius norm of the two-layer output. The first and second outputs agree exactly when there is a symmetric X with A2=A1+X, B2=B1-X, X S=S X, and D X commuting with the first output, where D=I-eta-squared S-squared.

The first-step equality determines the full difference of symmetric matrix entries. Positivity of the sum of two diagonal entries forces the two block differences to be opposite; the same equations then force commutation with S. Transport through the actual first step gives D X and minus D X, so the second output detects precisely their commutator with the observed first output. No distinct-eigenvalue assumption or inverse of D is used. Repeated eigenvalues and erased resonant directions are included.

The classification concerns symmetric-block recurrences. Physical Gram states additionally require positivity and a width rank bound. Generic four-step identification, resonance collapse and quantitative prediction require additional hypotheses and are not conclusions of this theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/ControlledLearning/RepeatedSpectrumPassiveFiber.two_step_outputs_iff_commuting_difference`
