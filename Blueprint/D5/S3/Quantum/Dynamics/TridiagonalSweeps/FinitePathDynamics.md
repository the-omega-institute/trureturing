# Finite-path rigidity and matrix decay

## Abstract

Weighted finite-path rigidity, boundary observability, and spectral power decay.

**Definition 1.1 (Zero endpoint extension).**

$$\forall m \in \mathbb{N},\; \forall z \in \operatorname{Fin}\left(m\right) \to \mathbb{C},\; \operatorname{zeroExtend}\left(z\right) = \operatorname{Fin}.\operatorname{cases}\left(0, \operatorname{Fin}.\operatorname{snoc}\left(z, 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.zeroExtend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m and complex vector z on Fin m, Fin.cases places zero at the left endpoint and Fin.snoc places zero at the right endpoint. The resulting vector has domain Fin(m + 2).

**Lemma 1.2 (The interior values are unchanged).**

$$\forall m \in \mathbb{N},\; \forall z \in \operatorname{Fin}\left(m\right) \to \mathbb{C},\; \forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{zeroExtend}\left(z\right)\left(\operatorname{Fin}.\operatorname{succ}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)\right) = z\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.extend_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Interior coordinate i is coordinate i + 1 of the zero endpoint extension.

**Lemma 1.3 (The right endpoint is zero).**

$$\forall m \in \mathbb{N},\; \forall z \in \operatorname{Fin}\left(m\right) \to \mathbb{C},\; \operatorname{zeroExtend}\left(z\right)\left(\operatorname{Fin}.\operatorname{last}\left(m + 1\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.extend_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The last coordinate of the extended vector is zero.

**Theorem 1.4 (Weighted harmonic Dirichlet rigidity).**

$$\forall m \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; \left(\forall j \in \operatorname{Fin}\left(m + 1\right),\; 0 < v\left(j\right)\right) \Rightarrow \left(\forall z \in \operatorname{Fin}\left(m\right) \to \mathbb{C},\; \left(\forall i \in \operatorname{Fin}\left(m\right),\; \frac{z\left(i\right) - \operatorname{zeroExtend}\left(z\right)\left(\operatorname{Fin}.\operatorname{castSucc}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)\right)}{(v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right):\mathbb{C})} = \frac{\operatorname{zeroExtend}\left(z\right)\left(\operatorname{Fin}.\operatorname{succ}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)\right) - z\left(i\right)}{(v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right):\mathbb{C})}\right) \Rightarrow z = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.harmonic_dirichlet_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary m and positive velocities, equal adjacent weighted slopes force every interior complex coordinate to vanish. Finite induction makes all edge slopes equal. Their telescoping sum is zero; the strictly positive total velocity forces the common slope to zero.

**Theorem 1.5 (A boundary zero propagates through the path).**

$$\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(\forall z \in \operatorname{Fin}\left(m\right) \to \mathbb{C},\; z\left(\operatorname{Fin}.\operatorname{mk}\left(0\right)\right) = 0 \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; z\left(i\right) = 0 \Rightarrow \left(\operatorname{zeroExtend}\left(z\right)\left(\operatorname{Fin}.\operatorname{castSucc}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)\right) = 0 \Rightarrow \operatorname{zeroExtend}\left(z\right)\left(\operatorname{Fin}.\operatorname{succ}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)\right) = 0\right)\right) \Rightarrow z = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.boundary_zero_observability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m ≥ 1, a zero first interior coordinate and a recurrence propagating two adjacent zeros imply that the entire vector is zero. The left endpoint supplied by zeroExtend starts the induction.

**Theorem 1.6 (Strict spectral bounds give real trajectory decay).**

$$\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(\forall N \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right),\; \left(\forall c \in \mathbb{C},\; c \in \operatorname{spectrum}\left(\mathbb{C}, \operatorname{Matrix}.\operatorname{map}\left(N, \operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right)\right) \Rightarrow \left\lVert c \right\rVert < 1\right) \Rightarrow \left(\forall u \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\lambda k:\mathbb{N},\operatorname{Matrix}.\operatorname{mulVec}\left(N^{k}, u\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.real_mulVec_powers_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m ≥ 1 and a real matrix N, every complex spectral modulus below one implies convergence of (N^k).mulVec u to zero for every real vector u. Gelfand's formula gives an eventual geometric bound on matrix powers in the complex operator norm. Continuity of matrix-vector multiplication and of coordinatewise real parts yields the real trajectory limit.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.boundary_zero_observability`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.extend_interior`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.extend_last`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.harmonic_dirichlet_zero`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.real_mulVec_powers_tendsto_zero`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.zeroExtend`
