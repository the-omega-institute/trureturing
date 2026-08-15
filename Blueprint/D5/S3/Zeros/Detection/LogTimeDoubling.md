# Log-Time Doubling

## Abstract

A log-time shift by log 2 / delta doubles a positive exponential mode.

**Theorem 1.1 (The logarithmic lifetime shift doubles the growing mode).**

$$\forall \delta,u\in\mathbb{R},\ \delta>0 \Rightarrow \exp(\delta(u+\frac{\log 2}{\delta})) = 2 \exp(\delta\,u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Detection/LogTimeDoubling.log_time_shift_doubles_exponential_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let delta be a positive displacement from the critical line and u the logarithmic time coordinate. Advancing u by log 2 / delta multiplies the growing exponential mode by exactly two.

Pinned Mathlib supplies Real.exp_add and Real.exp_log. The Lean proof only cancels the nonzero delta and applies those two identities, so it is a thin wrapper around the library facts rather than a second proof of exponential or logarithmic laws.

This theorem closes the exact logarithmic-time doubling formula. It does not formalize the surrounding particle analogy, spectral-line interpretation, numerical table, or claims about physical time.

## References

- Truth anchor: `D5/S3/Zeros/Detection/LogTimeDoubling.log_time_shift_doubles_exponential_mode`
