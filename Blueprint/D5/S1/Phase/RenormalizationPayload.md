# Two-Face Renormalization Is Recoverable

## Abstract

The two golden face readings uniquely determine their renormalization map.

**Theorem 1.1 (Both face readings determine the renormalization map).**

$$R(x,y) = (\varphi x, \psi y)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/RenormalizationPayload.renormalization_payload` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a map on two real coordinates. If its first coordinate always scales the first input by the golden ratio and its second coordinate always scales the second input by the golden conjugate, then the whole map is uniquely the canonical two-face renormalization. The conclusion is equality of functions, not only agreement at a selected input, so the operator can be recovered extensionally from the pair of readings and is genuine payload.

Pinned Mathlib supplies `Real.goldenRatio`, `Real.goldenConj`, the two-coordinate vector constructor, function extensionality, and the finite case split. A source search found no declaration packaging this exact two-face recoverability statement, so the Lean theorem is a short new proof rather than a wrapper. The source atom makes a single dependency claim; no analytic limit, model-set density, or generating-series identity is added here.

## References

- Truth anchor: `D5/S1/Phase/RenormalizationPayload.renormalization_payload`
