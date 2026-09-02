# Odd-Order Invisibility in a Finite Mirror Window

## Abstract

A finite mirror-closed zero window loses every odd transverse order while its even orders add across each reflected pair.

**Definition 1.1 (The finite transverse moment-generating function).**

$$\begin{gathered}\forall iota: Type,\\A: \operatorname{Finset}\left(iota\right), m: iota \to \mathbb{N},\\w: iota \to \mathbb{R}, delta: iota \to \mathbb{R},\\u: \mathbb{R},\\\operatorname{transverseMomentGeneratingFunction}\left(A, m, w, delta, u\right) = \sum_{a \in A} m\left(a\right) \cdot w\left(a\right) \cdot {e^{u \cdot delta\left(a\right)} + e^{-u \cdot delta\left(a\right)}}.\end{gathered}$$

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/FiniteMirrorCumulantOddOrderInvisibility.transverseMomentGeneratingFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set of right representatives, the function sums multiplicity times positive weight times the reflected exponential pair exp(u delta)+exp(-u delta). This is exactly the section-local Z_T formula, represented through the previously formalized reflected pair.

**Theorem 1.2 (Finite mirror symmetry hides precisely the odd transverse orders).**

$$\begin{gathered}\forall iota: Type,\\A: \operatorname{Finset}\left(iota\right), m: iota \to \mathbb{N},\\w: iota \to \mathbb{R}, delta: iota \to \mathbb{R},\\(\forall a \in A, 0 < w\left(a\right)) \Rightarrow\\(\forall a \in A, 0 \leq delta\left(a\right)) \Rightarrow\\(\forall r: \mathbb{N}, \operatorname{iteratedDeriv}\left(2 \cdot r + 1, \operatorname{transverseMomentGeneratingFunction}\left(A, m, w, delta\right), 0\right) = 0) \land\\(\forall a \in A, \forall r: \mathbb{N}, delta\left(a\right)^{2 \cdot r + 1} + {-delta\left(a\right)}^{2 \cdot r + 1} = 0) \land\\(\forall a \in A, \forall r: \mathbb{N}, delta\left(a\right)^{2 \cdot r} + {-delta\left(a\right)}^{2 \cdot r} = 2 \cdot delta\left(a\right)^{2 \cdot r}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/FiniteMirrorCumulantOddOrderInvisibility.finite_mirror_cumulant_odd_order_invisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public statement retains the finite representative set, natural multiplicities, strictly positive weights, and nonnegative right displacements from the source window.

Its first conjunct says that for every natural r, the (2r+1)-st iterated derivative of that concrete Z_T at zero is zero. Its second conjunct states pairwise cancellation of delta^(2r+1) with (-delta)^(2r+1). Its third conjunct states that the two even powers instead sum to 2 delta^(2r), so the narrative does not strengthen the Lean theorem into strict nonvanishing.

The proof differentiates the finite sum using pinned Mathlib and applies the imported arbitrary-order derivative formula for the reflected exponential pair. It uses only the displayed window hypotheses and no conjectural premise such as the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/FiniteMirrorCumulantOddOrderInvisibility.finite_mirror_cumulant_odd_order_invisibility`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/FiniteMirrorCumulantOddOrderInvisibility.transverseMomentGeneratingFunction`
- Dependency: [D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum](../Adelic/ReflectedGrowthPairSecondOrderSpectrum.md)
