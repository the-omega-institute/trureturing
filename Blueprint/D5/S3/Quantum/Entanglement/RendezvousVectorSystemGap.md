# Rendezvous vector systems

## Abstract

A quantitative gap for symmetric rendezvous vector systems.

**Definition 1.1 (Hypercube vertices).**

$$\forall d \in \mathbb{N},\; \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) = \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.Vertex` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

A vertex is a finite subset of Fin d, as in Wang's hypercube model in §2. WindowSeamCodes.Word is this finite-set type.

**Definition 1.2 (Fixed-cardinality outputs).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right) = \{(A: \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right)) // \operatorname{Finset.card}\left(A\right) = t\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.Output` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

An output is a t-element subset of Fin d. Erdos7.CommonTreeUnion.Choice is the subtype with this cardinality equation. These are the output sets in §2.

**Definition 1.3 (The rendezvous condition).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \forall B \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; (\operatorname{RendezvousVectorSystemGap.Wins}\left(sigma, tau, A, B\right)) \Leftrightarrow ((\operatorname{Disjoint}\left(\operatorname{Subtype.val}\left(A\right), \operatorname{Subtype.val}\left(B\right)\right)) \land ((\operatorname{Subtype.val}\left(A\right)) \cup (\operatorname{Subtype.val}\left(B\right)) = \operatorname{symmDiff}\left(sigma, tau\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.Wins` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

Equation (2.5) requires the two output sets to be disjoint and their union to equal the symmetric difference of the starting vertices.

**Definition 1.4 (Number of outputs as a real number).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{RendezvousVectorSystemGap.n}\left(d, t\right) = (\operatorname{Nat.cast}\left(\operatorname{Nat.choose}\left(d, t\right)\right): \mathbb{R})$$

*Formalization.* `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.n` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binomial coefficient counts the outputs. Its value here is cast from the natural numbers to the real numbers.

**Definition 1.5 (The quantitative gap).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{RendezvousVectorSystemGap.kappa}\left(d, t\right) = \frac{1}{(\operatorname{RendezvousVectorSystemGap.n}\left(d, t\right))^{4} \cdot (4 \cdot \operatorname{Real.sqrt}\left(2\right) \cdot (\operatorname{Nat.cast}\left(t\right): \mathbb{R}) + 2)^{2}}$$

*Formalization.* `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gap depends on the number of outputs and the step length. It is positive whenever the number of outputs is positive.

**Theorem 1.6 (A dimension-independent vector bound).**

$$\forall V \in Type*,\; \forall ag \in \operatorname{AddCommGroup}\left(V\right),\; \forall module \in \operatorname{Module}\left(\mathbb{R}, V\right),\; \forall C \in \operatorname{PreInnerProductSpace.Core}\left(\mathbb{R}, V, \operatorname{Real.instRCLike}, ag, module\right),\; \forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; (2 \le t) \Rightarrow ((2 \cdot t < d) \Rightarrow (\forall h \in V,\; \forall u \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) \to \left(\operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right) \to V\right),\; \forall v \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) \to \left(\operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right) \to V\right),\; \forall delta \in \mathbb{R},\; (0 \le delta) \Rightarrow ((delta \le 1) \Rightarrow ((\operatorname{Inner.inner}\left(\mathbb{R}, V, \operatorname{PreInnerProductSpace.Core.toInner}\left(\mathbb{R}, V, \operatorname{Real.instRCLike}, ag, module, C\right), h, h\right) = \operatorname{RendezvousVectorSystemGap.n}\left(d, t\right)) \Rightarrow ((\forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \operatorname{Inner.inner}\left(\mathbb{R}, V, \operatorname{PreInnerProductSpace.Core.toInner}\left(\mathbb{R}, V, \operatorname{Real.instRCLike}, ag, module, C\right), h, u\left(sigma, A\right)\right) = 1) \Rightarrow ((\forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall B \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \operatorname{Inner.inner}\left(\mathbb{R}, V, \operatorname{PreInnerProductSpace.Core.toInner}\left(\mathbb{R}, V, \operatorname{Real.instRCLike}, ag, module, C\right), h, v\left(tau, B\right)\right) = 1) \Rightarrow ((\forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \operatorname{Inner.inner}\left(\mathbb{R}, V, \operatorname{PreInnerProductSpace.Core.toInner}\left(\mathbb{R}, V, \operatorname{Real.instRCLike}, ag, module, C\right), u\left(sigma, A\right), u\left(sigma, A\right)\right) \le 1) \Rightarrow ((\forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall B \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \operatorname{Inner.inner}\left(\mathbb{R}, V, \operatorname{PreInnerProductSpace.Core.toInner}\left(\mathbb{R}, V, \operatorname{Real.instRCLike}, ag, module, C\right), v\left(tau, B\right), v\left(tau, B\right)\right) \le 1) \Rightarrow ((\forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \forall Aprime \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; (A \ne Aprime) \Rightarrow (\operatorname{Inner.inner}\left(\mathbb{R}, V, \operatorname{PreInnerProductSpace.Core.toInner}\left(\mathbb{R}, V, \operatorname{Real.instRCLike}, ag, module, C\right), u\left(sigma, A\right) + u\left(sigma, Aprime\right), u\left(sigma, A\right) + u\left(sigma, Aprime\right)\right) \le 2)) \Rightarrow ((\forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \forall B \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; (\operatorname{RendezvousVectorSystemGap.Wins}\left(sigma, tau, A, B\right)) \Rightarrow (\operatorname{Inner.inner}\left(\mathbb{R}, V, \operatorname{PreInnerProductSpace.Core.toInner}\left(\mathbb{R}, V, \operatorname{Real.instRCLike}, ag, module, C\right), u\left(sigma, A\right), v\left(tau, B\right)\right) = 1 - delta)) \Rightarrow (\operatorname{RendezvousVectorSystemGap.kappa}\left(d, t\right) \le delta)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.vector_system_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

Consider a real vector space with a positive semidefinite inner-product core. The two vector families have unit pairing with h, squared lengths at most one, and a two-outcome squared-length bound for the first family. Every winning pair has pairing 1 − delta. For t at least two and d greater than twice t, delta is at least kappa. Exchange paths compare vectors leading to the same meeting vertex; a family of one more meeting vertices than outputs then forces the stated bound. This argument uses the rendezvous geometry of Wang's §2.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.Output`
- Truth anchor: `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.Vertex`
- Truth anchor: `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.Wins`
- Truth anchor: `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.kappa`
- Truth anchor: `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.n`
- Truth anchor: `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.vector_system_gap`
- Dependency: [D5/S3/Arith/Congruence/ConditionalComparison/CommonTreeUnion](../../Arith/Congruence/ConditionalComparison/CommonTreeUnion.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes](../../ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.md)
