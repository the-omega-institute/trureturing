# CommonLowerHarmonicBound

## Abstract

A common positive lower matrix and a complex split

**Theorem 1.1 (A common positive lower matrix and a complex split).**

$$\forall u:\operatorname{Level}(),\ \forall d:\operatorname{Type}(u),\ {\operatorname{Fintype}(d)\land \operatorname{DecidableEq}(d)}\implies \forall P,Q,K:\operatorname{Matrix}(d, d, \mathbb{C}),\ {\operatorname{PosSemidef}(K)\land K\le P\land K\le Q}\implies \forall W:\operatorname{Prod}(\operatorname{Matrix}(d, d, \mathbb{C}), \operatorname{Matrix}(d, d, \mathbb{C})),\ {(\operatorname{fst}(W))+(\operatorname{snd}(W))=1}\implies K\le (2)\times (\operatorname{splitEnergy}(P, Q, W))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/CommonLowerHarmonicBound.common_lower_split_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For every split W1+W2=I, the common lower matrix K is bounded by twice the split energy. Both inputs can be singular. The residual for the equal K inputs is (W1-W2) adjoint times K times (W1-W2); monotonicity in each input gives the bound. The split matrices themselves can be arbitrary complex matrices. Applying this bound to the attained identity split of ParallelSumVariational.parallel_sum_minimum gives domination by twice the parallel sum for positive definite inputs. That application introduces no new theorem. The general split bound gives the closed-disk trace estimate and the pure-factor annihilation argument.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/CommonLowerHarmonicBound.common_lower_split_bound`
- Dependency: [D5/S3/Quantum/Hiai/ParallelSumVariational](ParallelSumVariational.md)
