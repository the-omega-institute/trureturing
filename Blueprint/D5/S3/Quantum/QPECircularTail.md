# Single-phase circular QPE tail

## Abstract

Single-phase circular QPE tail

**Theorem 1.1 (Uniform mass outside a circular window).**

$$\forall t \in \mathit{Nat},\; \forall phi \in \mathit{Real},\; \forall rho \in \mathit{Real},\; 0 < \mathit{rho} \Rightarrow \sum_{j:\operatorname{Fin}\left(2^{t}\right),\mathit{rho} \le \operatorname{circularDistance}\left(\mathit{phi}, j, 2^{t}\right)} \operatorname{probability}\left(2^{t}, \mathit{phi}, j\right) \le \frac{1}{2 \cdot 2^{t} \cdot \mathit{rho}} + \frac{1}{2 \cdot \left(2^{t} \cdot \mathit{rho}\right)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QPECircularTail.qpe_circular_tail_le` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Single-phase QPE circular-window tail*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Q is two to the natural width t. The sum is over exactly the labels whose circular distance is at least rho. circularDistance(phi, j, Q) is the norm of the image of the real number phi minus j.val / Q in UnitAddCircle, the real additive circle modulo one. All divisions in the displayed bound are real. The only premise is positivity of rho; phi is any real number.

The probability is exactly QuantumPhaseEstimationGeneral.probability Q phi j, the squared norm of the existing inverse-Fourier phase amplitude. That amplitude is one over Q times the finite sum of exp(2 pi i k.val (phi - j.val / Q)). The normalization and phase convention are those of ShorCountingMarginal. Comparing with a positive final Fourier transform requires reflecting the output label modulo Q.

Subtracting the nearest integer from each raw phase error gives a representative of absolute value at most one half. Its scaled error is Q phi minus an integer lift of j; reduction modulo Q proves that distinct labels have distinct lifts. The geometric amplitude has norm at most one over twice Q times the positive circular distance. Squaring and summing reduces the event to a finite two-sided reciprocal-square tail. Splitting about the floor of the center bounds each side by its first reciprocal-square term plus a telescoping reciprocal tail.

The bad event includes equality at rho, so the complementary good window has distance strictly less than rho. The estimate includes t equal to zero, integer-shifted and negative phases, wraparound, either midpoint representative, empty events and every positive radius, including radii larger than one half. No nearest-outcome, order or coprimality assumption is used. The bound describes one phase register at one eigenphase. Aggregate Shor success, eigenphase mixtures, repeated trials, continued-fraction recovery, factoring and hardware performance require separate results.

## References

- Truth anchor: `D5/S3/Quantum/QPECircularTail.qpe_circular_tail_le`
- Dependency: [D5/S3/Quantum/ShorCountingMarginal](ShorCountingMarginal.md)
