# A dimension witness for delayed remote control

## Abstract

Every Euclidean-unit complex data qubit admits positive preparations and a delayed remote-control dimension witness greater than four.

**Definition 1.1 (The controlled-A data gate).**

$$\forall (\beta: \mathbb{R}), \forall (\delta: \mathbb{R}), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.gateA}\left(\beta, \delta\right) = \begin{pmatrix}1&0\\0&\operatorname{Complex.exp}\left(\operatorname{Complex.ofReal}\left(\beta + \delta\right) \cdot \operatorname{Complex.I}\right)\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.gateA` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

Equation (3) gives the diagonal data gate A in the computational basis. Both parameters are real, and the exponential is complex.

**Definition 1.2 (The controlled-B data gate).**

$$\forall (\beta: \mathbb{R}), \forall (\delta: \mathbb{R}), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.gateB}\left(\beta, \delta\right) = \begin{pmatrix}0&-(1)\\\operatorname{Complex.exp}\left(\operatorname{Complex.ofReal}\left(\beta - \delta\right) \cdot \operatorname{Complex.I}\right)&0\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.gateB` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

Equation (3) gives the data gate B in the computational basis. Its upper-right entry is minus one, and its lower-left entry has phase beta minus delta.

**Definition 1.3 (The three-qubit circuit state).**

$$\forall (d: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (\beta: \mathbb{R}), \forall (\delta: \mathbb{R}), \forall (k: (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.circuitState}\left(d, \beta, \delta, k\right) = \sum_{(p: \operatorname{Fin}\left(2\right))} (\operatorname{D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard}\left((k).1, p\right) \cdot (\sum_{(q: \operatorname{Fin}\left(2\right))} (\sum_{(j: \operatorname{Fin}\left(2\right))} (((\text{if} ((p = 0) \land (q = 0)) \text{then} (1) \text{else} (0)) \cdot \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.gateA}\left(\beta, \delta, ((k).2).1, j\right) + (\text{if} ((p = 1) \land (q = 1)) \text{then} (1) \text{else} (0)) \cdot \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.gateB}\left(\beta, \delta, ((k).2).1, j\right)) \cdot \operatorname{D5.S3.QuantumBounds.CHSHWitness.bellVector}\left((q, ((k).2).2)\right) \cdot d\left(j\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.circuitState` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

The coordinates have the order program, data, remote control. The Bell vector is on the program and remote-control qubits. The two conditional terms are the entries of the controlled gate |0⟩⟨0| tensor A plus |1⟩⟨1| tensor B on the program and data qubits. The outer sum applies the Hadamard to the program qubit, as in Figure 3. All three sums range over Fin 2.

**Definition 1.4 (The remote outcome-zero vector).**

$$\forall (\beta: \mathbb{R}), \forall (\delta: \mathbb{R}), \forall (\gamma: \mathbb{R}), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.remote}\left(\beta, \delta, \gamma\right) = \begin{pmatrix}\operatorname{starRingEnd}\left(\mathbb{C}, \operatorname{Complex.exp}\left(\operatorname{Complex.ofReal}\left(\frac{-(\beta + \delta)}{2}\right) \cdot \operatorname{Complex.I}\right) \cdot \operatorname{Complex.ofReal}\left(\operatorname{Real.cos}\left(\frac{\gamma}{2}\right)\right)\right)\\\operatorname{starRingEnd}\left(\mathbb{C}, \operatorname{Complex.exp}\left(\operatorname{Complex.ofReal}\left(\frac{-(\beta - \delta)}{2}\right) \cdot \operatorname{Complex.I}\right) \cdot \operatorname{Complex.ofReal}\left(\operatorname{Real.sin}\left(\frac{\gamma}{2}\right)\right)\right)\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.remote` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

The two entries are the complex conjugates of the coefficients in Equation (3), with the global phase alpha equal to zero. The same beta and delta occur in the gates and in this vector. Its projector and complementary projector give the binary remote measurement.

**Definition 1.5 (The data measurement operators).**

$$\forall (b: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (n: \operatorname{Fin}\left(2\right)), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.dataProjector}\left(b, n\right) = (\text{if} (n = 0) \text{then} (\operatorname{Matrix.vecMulVec}\left(b, \operatorname{star}\left(b\right)\right)) \text{else} ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) - \operatorname{Matrix.vecMulVec}\left(b, \operatorname{star}\left(b\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.dataProjector` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

Outcome zero is the outer product of b with its complex conjugate, and outcome one is the identity matrix minus that outer product. For a Euclidean-unit b these are the two orthogonal projectors of the data measurement in Figure 3. The definition itself accepts every complex vector b.

**Definition 1.6 (The preparation probability).**

$$\forall (d: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (\beta: \mathbb{R}), \forall (\delta: \mathbb{R}), \forall (b: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (x: \operatorname{Fin}\left(4\right)), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.prepProb}\left(d, \beta, \delta, b, x\right) = \sum_{(r: \operatorname{Fin}\left(2\right))} (\sum_{(i: \operatorname{Fin}\left(2\right))} (\operatorname{Complex.normSq}\left(\sum_{(j: \operatorname{Fin}\left(2\right))} (\operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.dataProjector}\left(b, \operatorname{Fin.val}\left(x\right) \bmod 2, i, j\right) \cdot \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.circuitState}\left(d, \beta, \delta, (\left\lfloor\frac{\operatorname{Fin.val}\left(x\right)}{2}\right\rfloor, (j, r))\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.prepProb` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

The preparation label is x = 2m + n. The program outcome m is the integer quotient of Fin.val x by two, and the data outcome n is its remainder modulo two; both are interpreted as elements of Fin 2. The data projection is applied before summing Complex.normSq over the remaining remote and data coordinates. For unit d and b, this is the Born-rule probability of the program and data outcomes together.

**Definition 1.7 (The joint outcome-zero probability).**

$$\forall (d: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (\beta: \mathbb{R}), \forall (\delta: \mathbb{R}), \forall (\gamma_{0}: \mathbb{R}), \forall (\gamma_{1}: \mathbb{R}), \forall (b: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (x: \operatorname{Fin}\left(4\right)), \forall (y: \operatorname{Fin}\left(2\right)), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.jointProb}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, x, y\right) = \sum_{(i: \operatorname{Fin}\left(2\right))} (\operatorname{Complex.normSq}\left(\sum_{(r: \operatorname{Fin}\left(2\right))} (\operatorname{starRingEnd}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.remote}\left(\beta, \delta, (\text{if} (y = 0) \text{then} (\gamma_{0}) \text{else} (\gamma_{1})), r\right)\right) \cdot (\sum_{(j: \operatorname{Fin}\left(2\right))} (\operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.dataProjector}\left(b, \operatorname{Fin.val}\left(x\right) \bmod 2, i, j\right) \cdot \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.circuitState}\left(d, \beta, \delta, (\left\lfloor\frac{\operatorname{Fin.val}\left(x\right)}{2}\right\rfloor, (j, r))\right))))\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.jointProb` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

At remote setting y, gamma is gamma zero when y is zero and gamma one otherwise. Taking the inner product with the remote outcome-zero vector gives a sum over the remote coordinate. Complex.normSq is then summed over the data coordinate. The program and data outcomes use the same integer quotient and remainder as the preparation probability. For unit d and b, this is their joint Born-rule probability together with remote outcome zero.

**Definition 1.8 (The binary correlator).**

$$\forall (d: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (\beta: \mathbb{R}), \forall (\delta: \mathbb{R}), \forall (\gamma_{0}: \mathbb{R}), \forall (\gamma_{1}: \mathbb{R}), \forall (b: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (x: \operatorname{Fin}\left(4\right)), \forall (y: \operatorname{Fin}\left(2\right)), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, x, y\right) = 2 \cdot (\frac{\operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.jointProb}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, x, y\right)}{\operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.prepProb}\left(d, \beta, \delta, b, x\right)}) - 1$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.E` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

When the preparation probability is positive, the quotient is the conditional probability of remote outcome zero. Twice this probability minus one is the difference between the two binary outcome probabilities. The real division in the definition is total, so the formula also defines a value at zero preparation probability.

**Definition 1.9 (The dimension-witness expression).**

$$\forall (d: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \forall (\beta: \mathbb{R}), \forall (\delta: \mathbb{R}), \forall (\gamma_{0}: \mathbb{R}), \forall (\gamma_{1}: \mathbb{R}), \forall (b: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.S}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b\right) = \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, 0, 0\right) - \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, 0, 1\right) - \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, 1, 0\right) + \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, 1, 1\right) - \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, 2, 0\right) - \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, 2, 1\right) + \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, 3, 0\right) + \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.E}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b, 3, 1\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.S` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

This is the eight-term expression of Equation (2), using the source's first preparation labeling x = 2m + n. The signs are plus, minus, minus, plus, minus, minus, plus, plus in the order (0,0), (0,1), (1,0), (1,1), (2,0), (2,1), (3,0), (3,1). The expression is defined without imposing the classical bound of four.

**Definition 1.10 (A violation for every pure data qubit).**

$$(\operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.claim}) \Leftrightarrow (\forall (d: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), (\left\lVert (\operatorname{WithLp.toLp}\left(2, d\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)) \right\rVert = 1) \Rightarrow (\exists (\beta: \mathbb{R}), \exists (\delta: \mathbb{R}), \exists (\gamma_{0}: \mathbb{R}), \exists (\gamma_{1}: \mathbb{R}), \exists (b: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), (\left\lVert (\operatorname{WithLp.toLp}\left(2, b\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)) \right\rVert = 1) \land ((\forall (x: \operatorname{Fin}\left(4\right)), 0 < \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.prepProb}\left(d, \beta, \delta, b, x\right)) \land (4 < \operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.S}\left(d, \beta, \delta, \gamma_{0}, \gamma_{1}, b\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.claim` (`✓ std3`).

*Citation.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

The final paragraph of Section III conjectures a violation for every initial pure data qubit. Here the norm is the Euclidean norm on complex coordinate functions, obtained with WithLp.toLp 2. For each unit data vector, the four real parameters and a unit data-measurement vector may be chosen separately. Every preparation must have positive probability, and S must exceed four. The labeling is fixed to x = 2m + n.

**Theorem 1.11 (Normalization in two coordinates).**

$$\forall (d: (\operatorname{Fin}\left(2\right) \to \mathbb{C})), (\left\lVert (\operatorname{WithLp.toLp}\left(2, d\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)) \right\rVert = 1) \Rightarrow (\operatorname{Complex.normSq}\left(d\left(0\right)\right) + \operatorname{Complex.normSq}\left(d\left(1\right)\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.unit_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

The squared moduli of the two coordinates of a Euclidean-unit complex qubit sum to one.

**Theorem 1.12 (Every pure data qubit admits the violation).**

$$\operatorname{D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.result` (`✓ std3`). ∎

*Resolves.* `Problems/lin-wang-liu-huang-2026-delayed-rcqc-dimension-witness` (proved) by `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lin-wang-liu-huang-2026-delayed-rcqc-dimension-witness","declaration_gid":"D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peicun Lin, Dongyang Wang, Yong Liu, Anqi Huang (2026). *Nonclassicality of a delayed remote-controlled quantum computing model*. DOI: [10.48550/arXiv.2606.31103](https://doi.org/10.48550/arXiv.2606.31103). URL: <https://arxiv.org/abs/2606.31103v1>.

*Commentary.*

For a Euclidean-unit data vector d, choose β = 0, δ = −arg(conj(d₀)·d₁), γ₀ = π/2 and γ₁ = π. The vectors A d and e^{iδ} B d are orthonormal, including when either coordinate of d vanishes. Take b = cos(π/8)·A d + sin(π/8)·e^{iδ} B d. This vector is Euclidean-unit. Every preparation then has probability 1/4. In the order (0,0), (0,1), (1,0), (1,1), (2,0), (2,1), (3,0), (3,1), the correlators are √2/2 times the signs plus, minus, minus, plus, minus, minus, plus, plus. Consequently S = 4√2 > 4 for every pure data qubit.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.E`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.S`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.circuitState`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.dataProjector`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.gateA`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.gateB`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.jointProb`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.prepProb`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.remote`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.result`
- Truth anchor: `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.unit_coordinates`
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
