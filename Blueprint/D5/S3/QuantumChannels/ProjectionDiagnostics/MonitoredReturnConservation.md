# Monitored Return Conservation

## Abstract

Monitored return amplitudes and survival probabilities obey exact finite conservation.

**Theorem 1.1 (Monitored stepwise and finite conservation).**

$$s_{0}=1,\quad\forall n \in \mathbb{N}, p_{n+1}=s_{n}-s_{n+1},\quad\forall N \in \mathbb{N}, \sum_{n=0}^{N-1}p_{n+1}+s_{N}=1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ProjectionDiagnostics/MonitoredReturnConservation.monitored_return_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be unitary on a complex Hilbert space and v a unit vector. P is the orthogonal projection onto the span of v, and Q is I minus P. The monitored history at time n is (QU) to the nth power applied to v; s is its squared norm. At positive time n, the return amplitude is the inner product of v with U applied to the previous monitored history, and p is its squared modulus. The repository interface applies Mathlib's orthogonal projection norm identity and finite telescoping sum.

## References

- Truth anchor: `D5/S3/QuantumChannels/ProjectionDiagnostics/MonitoredReturnConservation.monitored_return_conservation`
