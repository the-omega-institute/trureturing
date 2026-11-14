# Finite rational convergents

## Abstract

Executable finite rational lists and exact real convergent correspondence

For any rational x, convergents x starts with its integer floor. If its fractional part is zero the list stops there. Otherwise it recursively computes the list at the reciprocal fractional part, then adds the floor to the reciprocal of each recursive entry. The positive reduced denominator strictly decreases at each recursive call. This construction accepts negative rationals, zero and integers; no positive-input hypothesis is imposed. The list is finite by well-founded recursion, without an asserted length or operation-count bound.

The observable list candidates y Q N filters convergents of the rational y / Q by reduced denominator strictly less than N. Its only inputs are natural numbers y, Q and N. It has no order or spectral-numerator input. Rational division totalizes the definition also at Q equal to zero, while the recovery theorem uses a positive resolved clock. reduced s r denotes the rational s / r.

**Theorem 1.1 (Exact list correspondence).**

$$\forall x \in \mathit{Rat},\; \forall z \in \mathit{Rat},\; z \in \operatorname{convergents}\left(x\right) \Leftrightarrow \left(\exists k \in \mathit{Nat},\; \operatorname{realConvergent}\left(\operatorname{toReal}\left(x\right), k\right) = z\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents.mem_convergents_iff` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

In the display, realConvergent denotes Mathlib's Real.convergent and natDiv denotes natural-number division. Both directions follow the Euclidean denominator descent. At an integer, all totalized real convergents repeat that integer. At a noninteger, the head is the zeroth convergent, and the reciprocal-tail recurrence transports each tail index to its successor. Thus repeated terminal real convergents are represented by a single finite-list entry. The consuming recovery proof uses this equivalence to turn the index supplied by Mathlib's Legendre theorem into actual list membership.

**Theorem 1.2 (Reduced denominator).**

$$\forall s \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; 0 < r \Rightarrow \operatorname{den}\left(\operatorname{reduced}\left(s, r\right)\right) = \operatorname{natDiv}\left(r, \operatorname{gcd}\left(s, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents.reduced_den` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

The positive-denominator formula directly uses the pinned rational normalization laws. It remains valid at s equal to zero and r equal to one. The denominator divides r, is at most r, and equals r when s and r are coprime. These consequences are used inside the conditional Shor recovery proof.

Mathlib supplies the real convergent recurrence and Legendre approximation theorem. The finite-list correspondence connects that recurrence with executable rational Euclidean descent.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents.mem_convergents_iff`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents.reduced_den`
