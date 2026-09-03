# Alternating Zeta Continuation and Real-Axis Nonvanishing

## Abstract

The paired alternating zeta series gives the eta continuation away from one, which excludes real zeta zeros in the open critical interval and makes the ordinates of ZeroData nontrivial zeros nonzero.

**Theorem 1.1 (The alternating zeta partial sums converge away from one).**

$$\forall s \in \mathbb{C},\; \left(0 < \Re(s) \land s \ne 1\right) \Rightarrow \lim_{N\to\infty} \sum_{n=0}^{N-1} (-1)^{n}\,(n+1)^{-s} = (1-2^{1-s})\,\zeta(s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.tendsto_alternating_partialSums_eta_of_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjacent terms form an absolutely summable series on every right half-plane bounded away from zero. Locally uniform convergence makes its sum analytic. On real part greater than one, splitting the zeta series into even and odd terms identifies the sum with (1 - 2^(1-s)) zeta(s); the analytic identity principle and a real-axis limit extend the identity to positive real part away from one.

**Theorem 1.2 (The unqualified continuation statement fails at one).**

$$\neg{\lim_{N\to\infty} \sum_{n=0}^{N-1} (-1)^{n}\,(n+1)^{-1} = (1-2^{1-1})\,\zeta(1)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.alternating_partialSums_eta_atom_fails_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At s=1 the alternating harmonic series has a strictly positive paired sum, whereas Mathlib's point value makes the displayed right-hand side zero because its eta prefactor vanishes.

**Theorem 1.3 (Riemann zeta has no real zero in the open critical interval).**

$$\forall x \in \mathbb{R},\; \left(0 < x \land x < 1\right) \Rightarrow \zeta(x) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.riemannZeta_ne_zero_of_real_mem_Ioo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive real exponent, every adjacent eta pair is positive, so their summable series has positive real part. The continuation identity then prevents zeta from vanishing on the interval.

**Theorem 1.4 (ZeroData nontrivial zeros have nonzero imaginary part).**

$$\forall Z \in ZeroData, n \in \mathbb{N},\; \operatorname{IsNontrivialZero}(\operatorname{zero}(Z, n)) \Rightarrow \operatorname{Im}(\operatorname{zero}(Z, n)) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.im_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nontrivial zero with zero imaginary part would be a real zeta zero strictly between zero and one, contradicting real-axis nonvanishing. Thus separator theorems need no separate hIm assumption for ZeroData entries. This removes a hypothesis only; it does not assert the existence of any new zeros or prove RH.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.alternating_partialSums_eta_atom_fails_at_one`
- Truth anchor: `D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.im_ne_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.riemannZeta_ne_zero_of_real_mem_Ioo`
- Truth anchor: `D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.tendsto_alternating_partialSums_eta_of_ne_one`
