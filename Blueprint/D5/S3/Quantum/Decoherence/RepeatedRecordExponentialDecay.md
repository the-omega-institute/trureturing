# Repeated Record Exponential Decay

## Abstract

Repeated finite records contract cross-class coherence at the uniform Gram rate.

**Theorem 1.1 (Repeated records converge exponentially to record-class pinching).**

$$\forall d: Nat, e: Nat,\\{}E: \operatorname{Fin}\left(d\right) \to \left(\operatorname{Fin}\left(e\right) \to \mathbb{C}\right),\\{}\forall i \in \operatorname{Fin}\left(d\right),\; \sum_{a \in \operatorname{Fin}\left(e\right)} \left\lVert E\left(i\right)\left(a\right) \right\rVert \cdot \left\lVert E\left(i\right)\left(a\right) \right\rVert = 1,\\{}q: \operatorname{Ico}\left(0, 1\right),\\{}{\forall i \in \operatorname{Fin}\left(d\right), j \in \operatorname{Fin}\left(d\right),\; E\left(i\right) \ne E\left(j\right) \Rightarrow \left\lVert \operatorname{recordGram}\left(E, i, j\right) \right\rVert \le q} \Rightarrow\\{}\operatorname{let} Pch: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \rho\mapsto \sum_{l \in \operatorname{range}\left(E\right)} \operatorname{recordClassProjector}\left(E, l\right) \cdot \rho \cdot \operatorname{recordClassProjector}\left(E, l\right); \left(\forall N \in Nat, rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), i \in \operatorname{Fin}\left(d\right), j \in \operatorname{Fin}\left(d\right),\; \operatorname{entry}\left(\operatorname{iterate}\left(\operatorname{recordChannel}\left(E\right), N, \rho\right), i, j\right) = \operatorname{recordGram}\left(E, i, j\right)^{N} \cdot \operatorname{entry}\left(\rho, i, j\right)\right) \land \left(\left(\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), i \in \operatorname{Fin}\left(d\right), j \in \operatorname{Fin}\left(d\right),\; \operatorname{entry}\left(Pch\left(\rho\right), i, j\right) = \operatorname{ite}\left(E\left(i\right) = E\left(j\right), \operatorname{entry}\left(\rho, i, j\right), 0\right)\right) \land \left(\forall N \in Nat, rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \left\lVert \operatorname{iterate}\left(\operatorname{recordChannel}\left(E\right), N, \rho\right) - Pch\left(\rho\right) \right\rVert \le q^{N} \cdot \left\lVert \rho - Pch\left(\rho\right) \right\rVert\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/RepeatedRecordExponentialDecay.repeated_record_exponential_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The record amplitudes construct both the Gram channel and the class projectors. The projector sum therefore uses the actual equality classes of environment records.

The first clause is the exact entrywise iterate. The second computes the projector sum, and the final clause is its Frobenius norm contraction under the stated cross-class Gram bound.

For a repeated-collision application, each system address labels a normalized environment amplitude vector. The Gram coefficient uses the amplitude at the first address times the conjugate amplitude at the second, summed over environment coordinates. The environment_marginal_channel theorem identifies this entry multiplier with tracing out a controlled record. Repeating the same reduced channel can be realized with fresh, initially uncorrelated environment registers and the same recording map. A correlated or reused environment is not covered merely by assigning it the same one-step overlap.

The error is relative to record-class pinching, in the Frobenius norm, the square root of the sum of squared entry magnitudes. It is bounded by the initial discarded coherence times the uniform cross-class overlap bound raised to the collision count. No positivity or trace-one premise is imposed on the system matrix, so density matrices are included as a special case. The estimate is not stated in trace norm or diamond norm, and does not by itself give a measurement discrimination error.

The equality classes contain identical amplitude vectors, not rays modulo phase. Distinct normalized vectors differing only by a phase have overlap of unit magnitude, so the strict cross-class bound excludes them. Distinctness alone therefore does not supply the decay hypothesis. Within each equality class the coherence is retained; complete basis dephasing requires singleton classes. Orthogonal distinct classes permit a zero bound and hence exact pinching after any positive collision count.

This application replaces a demand for exact orthogonality by a quantitative sufficient condition for small residual coherence. Normalization, the overlap bound and the repeated-channel description remain model premises. Their applicability to a particular experiment requires separate physical evidence; the mathematical estimate does not establish those premises.

A phase-adjusted application groups normalized records by their complex rays. Choose one unit representative for each ray, and repeat that representative at every system address in its class. Each original record is its representative multiplied by a scalar of unit modulus. Equality in Cauchy--Schwarz characterizes proportional unit vectors, so representatives of distinct rays have overlap magnitude strictly below one. Taking the maximum over the finitely many cross-ray pairs gives a uniform strict bound; if there are no such pairs, zero is a valid bound.

The phase correspondence must also be carried through the dynamics. The original Gram coefficient is the representative Gram coefficient times the first address's phase and the conjugate of the second address's phase. Entrywise multiplication therefore commutes with the associated diagonal phase action. At repetition count N, the original iterate is the representative-channel iterate conjugated by the diagonal matrix of the address phases raised to N. This preserves the original channel; replacing each record by its rank-one density matrix would instead change the Gram coefficient to its squared magnitude and would not give this identity.

Apply the stated theorem to these representative records. Their equal-vector pinching retains exactly the original same-ray entries. Diagonal conjugation by unit phases preserves the Frobenius norm, so the same decay rate bounds the distance from the original iterate to the conjugated ray pinching. The comparison is a moving coherent-block orbit: within a ray, an entry is multiplied by the two addresses' relative phase to N and need not approach a stationary value. The bound covers arbitrary complex system matrices and N equal to zero; empty finite system carriers are retained.

In this ray formulation the strict separation follows from finite unit-record geometry, whereas normalization, the specified controlled coupling and repeated application of one reduced channel remain premises of the physical model. The conditional phases belong to the coupling: the individual environment density matrices alone do not determine them. A rotating reference frame consequently needs the coupling or a phase calibration. This application does not establish a correlated-environment evolution, experimental support, or complete stationary dephasing.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/RepeatedRecordExponentialDecay.repeated_record_exponential_decay`
- Dependency: [D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel](EnvironmentMarginalChannel.md)
