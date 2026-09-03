# Local Positive-Spectrum Completion

## Abstract

Local positive definiteness is equivalent to positive spectral completion modulo the fixed window's invisible distributions.

**Definition 1.1 (Local well-posedness).**

Lean statement: `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.WellPosed`

*Formalization.* `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.WellPosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every test visible in the fixed local window has nonnegative source reading.

**Definition 1.2 (Positive spectral extension).**

Lean statement: `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.HasPositiveExtension`

*Formalization.* `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.HasPositiveExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive tempered spectrum has inverse Fourier transform differing from the source by an element of the window kernel.

**Definition 1.3 (Positive external correction).**

Lean statement: `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.HasPositiveCorrection`

*Formalization.* `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.HasPositiveCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Adding a window-invisible correction makes the Fourier spectrum positive.

**Theorem 1.4 (Local positive-spectrum completion).**

$$\begin{aligned}\forall D, S, T,\\F: \operatorname{AddEquiv}\left(D, S\right), r: \operatorname{AddHom}\left(D, \operatorname{Function}\left(T, \operatorname{Real}\left(\right)\right)\right),\\E: \operatorname{Function}\left(S, T, \operatorname{Real}\left(\right)\right), P: \operatorname{Predicate}\left(S\right),\\K: \operatorname{AddSubgroup}\left(D\right), W: D,\\\forall nu, f, r\left(\operatorname{inverse}\left(F, nu\right), f\right) = E\left(nu, f\right),\\\forall nu, P\left(nu\right) \Rightarrow \forall f, 0 \leq E\left(nu, f\right),\\\forall kappa, kappa \in K \Rightarrow \forall f, r\left(kappa, f\right) = 0,\\{\operatorname{WellPosed}\left(r, W\right) \Rightarrow \exists nu, P\left(nu\right) \land \operatorname{inverse}\left(F, nu\right) - W \in K} \Rightarrow\\(\operatorname{WellPosed}\left(r, W\right) \iff \exists nu, P\left(nu\right) \land \operatorname{inverse}\left(F, nu\right) - W \in K) \land\\(\exists nu, P\left(nu\right) \land \operatorname{inverse}\left(F, nu\right) - W \in K \iff \exists kappa, kappa \in K \land P\left(F\left(W + kappa\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.local_positive_spectrum_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source theorem is conditional on the standard finite-order tempered positive-definite extension theorem. Since pinned Mathlib has no such theorem, the formal statement exposes exactly its constructive local-to-global direction as a hypothesis.

The reverse implication is not assumed: a positive spectrum gives nonnegative local readings through the inverse-Fourier pairing and vanishing of every window-kernel correction.

For the final equivalence, an extension spectrum constructs the explicit correction F inverse of nu minus W. Conversely, a correction kappa constructs the explicit spectrum F of W plus kappa.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.HasPositiveCorrection`
- Truth anchor: `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.HasPositiveExtension`
- Truth anchor: `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.WellPosed`
- Truth anchor: `D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.local_positive_spectrum_completion`
