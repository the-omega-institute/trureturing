# A faithful divergence with different complete and conditional coefficients

## Abstract

Squared trace distance gives a strict complete versus conditional contraction gap.

DensityState(A) is a positive semidefinite complex CStarMatrix of trace one. QuantumChannel(A,B) is the canonical completely positive, trace-preserving map between these matrix spaces. All index types below lie in Type and carry the displayed finite enumerations and decidable equalities. The reference is the first coordinate. The map marginalRight traces out the second coordinate; referenceState(N,rho) applies the channel to that coordinate and preserves the reference marginal.

**Definition 1.1 (Finite faithful quantum divergences).**

$$\operatorname{FiniteDivergence} = \{(D: \forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \operatorname{DensityState}\left(A\right) \to \left(\operatorname{DensityState}\left(A\right) \to \mathbb{R}\right)) \mid (\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (rho: \operatorname{DensityState}\left(A\right)), \forall (sigma: \operatorname{DensityState}\left(A\right)), (0 \le \operatorname{value}\left(D, rho, sigma\right)) \land ((\operatorname{value}\left(D, rho, sigma\right) = 0) \Leftrightarrow (rho = sigma))) \land (\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (B: \operatorname{Type}), [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (N: \operatorname{QuantumChannel}\left(A, B\right)), \forall (rho: \operatorname{DensityState}\left(A\right)), \forall (sigma: \operatorname{DensityState}\left(A\right)), \operatorname{value}\left(D, \operatorname{mapState}\left(N, rho\right), \operatorname{mapState}\left(N, sigma\right)\right) \le \operatorname{value}\left(D, rho, sigma\right))\}$$

*Formalization.* `D5/S3/Quantum/Divergence/FaithfulConditionalGap.FiniteDivergence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FiniteDivergence stores a real-valued family D on density-state pairs over every finite index type, together with nonnegativity, zero exactly on equal states, and data processing for every canonical CPTP channel between arbitrary finite source and target dimensions. No additivity or direct-sum law is imposed. The family D in the display has precisely these density-state domains.

**Definition 1.2 (Complete ratios).**

$$\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (B: \operatorname{Type}), [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (D: \operatorname{FiniteDivergence}), \forall (N: \operatorname{QuantumChannel}\left(A, B\right)), \operatorname{completeRatios}\left(D, N\right) = \{(x: \mathbb{R}) \mid \exists (R: \operatorname{Type}), [\operatorname{Fintype}\left(R\right)] [\operatorname{DecidableEq}\left(R\right)] \exists (rho: \operatorname{DensityState}\left(R \times A\right)), \exists (sigma: \operatorname{DensityState}\left(R \times A\right)), (\operatorname{marginalRight}\left(rho\right) = \operatorname{marginalRight}\left(sigma\right)) \land ((0 < \operatorname{value}\left(D, rho, sigma\right)) \land (x = \frac{\operatorname{value}\left(D, \operatorname{referenceState}\left(N, rho\right), \operatorname{referenceState}\left(N, sigma\right)\right)}{\operatorname{value}\left(D, rho, sigma\right)}))\}$$

*Formalization.* `D5/S3/Quantum/Divergence/FaithfulConditionalGap.completeRatios` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The set includes every finite quantum reference R and every canonical density-state pair satisfying the displayed conditions. Denominators are strictly positive real numbers; all divergence values are finite.

**Definition 1.3 (Conditional ratios).**

$$\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (B: \operatorname{Type}), [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (D: \operatorname{FiniteDivergence}), \forall (N: \operatorname{QuantumChannel}\left(A, B\right)), \operatorname{conditionalRatios}\left(D, N\right) = \{(x: \mathbb{R}) \mid \exists (R: \operatorname{Type}), [\operatorname{Fintype}\left(R\right)] [\operatorname{DecidableEq}\left(R\right)] \exists (rho: \operatorname{DensityState}\left(R \times A\right)), \exists (sigma: \operatorname{DensityState}\left(R \times A\right)), (0 < \operatorname{value}\left(D, rho, sigma\right) - \operatorname{value}\left(D, \operatorname{marginalRight}\left(rho\right), \operatorname{marginalRight}\left(sigma\right)\right)) \land (x = \frac{\operatorname{value}\left(D, \operatorname{referenceState}\left(N, rho\right), \operatorname{referenceState}\left(N, sigma\right)\right) - \operatorname{value}\left(D, \operatorname{marginalRight}\left(rho\right), \operatorname{marginalRight}\left(sigma\right)\right)}{\operatorname{value}\left(D, rho, sigma\right) - \operatorname{value}\left(D, \operatorname{marginalRight}\left(rho\right), \operatorname{marginalRight}\left(sigma\right)\right)})\}$$

*Formalization.* `D5/S3/Quantum/Divergence/FaithfulConditionalGap.conditionalRatios` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The set includes every finite quantum reference R and every canonical density-state pair satisfying the displayed conditions. Denominators are strictly positive real numbers; all divergence values are finite.

**Definition 1.4 (Complete coefficient).**

$$\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (B: \operatorname{Type}), [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (D: \operatorname{FiniteDivergence}), \forall (N: \operatorname{QuantumChannel}\left(A, B\right)), \operatorname{completeCoefficient}\left(D, N\right) = \operatorname{sSup}\left(\operatorname{insert}\left(0, \operatorname{completeRatios}\left(D, N\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/FaithfulConditionalGap.completeCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Adjoining zero makes an empty admissible ratio set have coefficient zero. The squared trace-distance instance has the boundedness needed for the real supremum.

**Definition 1.5 (Conditional coefficient).**

$$\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (B: \operatorname{Type}), [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (D: \operatorname{FiniteDivergence}), \forall (N: \operatorname{QuantumChannel}\left(A, B\right)), \operatorname{conditionalCoefficient}\left(D, N\right) = \operatorname{sSup}\left(\operatorname{insert}\left(0, \operatorname{conditionalRatios}\left(D, N\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/FaithfulConditionalGap.conditionalCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Adjoining zero makes an empty admissible ratio set have coefficient zero. The squared trace-distance instance has the boundedness needed for the real supremum.

**Theorem 1.6 (A strict gap with unrestricted finite quantum references).**

$$\exists (D: \operatorname{FiniteDivergence}), \exists (N: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)), (\operatorname{completeCoefficient}\left(D, N\right) \le \frac{1}{4}) \land ((\frac{1}{4} < \frac{5}{12}) \land (\frac{5}{12} \le \operatorname{conditionalCoefficient}\left(D, N\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/FaithfulConditionalGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/hirche-george-nuradha-wilde-2026-faithful-conditional-gap` (proved) by `D5/S3/Quantum/Divergence/FaithfulConditionalGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hirche-george-nuradha-wilde-2026-faithful-conditional-gap","declaration_gid":"D5/S3/Quantum/Divergence/FaithfulConditionalGap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Take D(rho,sigma)=T(rho,sigma)^2, where T is one half of the trace norm of rho minus sigma. The channel measures in the binary computational basis and applies W=((3/4,1/4),(1/4,3/4)). Its four Kraus matrices are sqrt(W(y,x)) times the matrix unit at (y,x); their adjoint products sum to the identity. Its action is the diagonal matrix with entries (3X(0,0)+X(1,1))/4 and (X(0,0)+3X(1,1))/4.

For every finite quantum reference R, an equal-marginal difference X has X((r,0),(s,0))+X((r,1),(s,1))=0 for every r,s, including off-diagonal reference entries. Consequently the amplified channel sends X to one half of its binary pinching. That pinching is (X+UXU*)/2 for U=I_R tensor diag(1,-1), so its trace norm cannot increase. Squaring yields the uniform complete bound 1/4.

In the ordered basis (0,0),(0,1),(1,0),(1,1),(2,0),(2,1), use the actual density states with diagonals (1/2,0,0,0,1/2,0) and (0,0,1/2,0,0,1/2). Their channel outputs have diagonals (3/8,1/8,0,0,3/8,1/8) and (0,0,3/8,1/8,1/8,3/8). Their reference marginals are (1/2,0,1/2) and (0,1/2,1/2), and are preserved by the channel. The input, output and reference trace distances are 1, 3/4 and 1/2. The conditional denominator is 3/4, its numerator is 5/16, and the ratio is 5/12.

For heterogeneous CPTP data processing, decompose a Hermitian matrix into positive and negative Jordan parts. Positivity, trace preservation and the trace-norm triangle inequality give contraction without identifying the source and target dimensions. Trace norm vanishes only at zero; nonnegative squaring preserves data processing and faithfulness. The conditional ratios are bounded above by one. The conclusion answers the faithful-divergence existential in Section 9, second bullet, without specializing to relative entropy or determining either exact optimal coefficient.

Thus squared trace distance and the binary channel satisfy completeCoefficient <= 1/4 < 5/12 <= conditionalCoefficient. The complete bound holds for every finite quantum reference, while the displayed density-state pair has strictly positive conditional denominator and attains the ratio 5/12.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/FaithfulConditionalGap.FiniteDivergence`
- Truth anchor: `D5/S3/Quantum/Divergence/FaithfulConditionalGap.completeCoefficient`
- Truth anchor: `D5/S3/Quantum/Divergence/FaithfulConditionalGap.completeRatios`
- Truth anchor: `D5/S3/Quantum/Divergence/FaithfulConditionalGap.conditionalCoefficient`
- Truth anchor: `D5/S3/Quantum/Divergence/FaithfulConditionalGap.conditionalRatios`
- Truth anchor: `D5/S3/Quantum/Divergence/FaithfulConditionalGap.result`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation](../Information/ChenKatoBrandaoTraceNormCMIRefutation.md)
