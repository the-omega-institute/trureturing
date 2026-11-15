# Divergence forced by a local obstruction family

## Abstract

An eventual threshold must diverge when every right-hand neighborhood of the
endpoint contains a counterexample above each prescribed finite cutoff.

**Theorem 1.1 (Threshold divergence from local obstruction).**

Lean statement:
`D5/S3/Arith/Robin/Analytic/RobinThresholdDivergence.threshold_tendsto_atTop_of_local_obstruction`

*Proof.* Machine-checked in Lean as
`D5/S3/Arith/Robin/Analytic/RobinThresholdDivergence.threshold_tendsto_atTop_of_local_obstruction`
(`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let `P κ n` be a parameterized property and `T κ` a natural threshold. Assume
that `P κ n` holds for every `n > T κ` whenever `κ` is to the right of an
endpoint `a`. If, for every finite `M`, all sufficiently close right-hand
parameters have some counterexample `n > M`, then `T κ` is eventually at least
`M` in that right-hand neighborhood. Quantifying over `M` gives
`T κ → ∞` as `κ ↓ a`.

This theorem formalizes the order-theoretic implication used by Theorem 5.2 of
the LCM/Robin volume. Its local-obstruction premise is explicit; the theorem
does not prove the endpoint counterexample supplied there by the volume's
Theorem 2.3.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/RobinThresholdDivergence.threshold_tendsto_atTop_of_local_obstruction`
- Related open atom: Theorem 5.2 of `LCM_POWER_ROBIN_KAPPA_THRESHOLD.md`
