# A qubit pure-program obstruction

## Abstract

Three pure targets prevent a two-dimensional pure program register from producing a mixed qubit target.

**Definition 1.1 (Finite Kraus channels).**

$$\forall (A : Type), (\forall (B : Type), ([\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (T : \operatorname{Matrix}\left(A, A, \mathbb{C}\right) \to \operatorname{Matrix}\left(B, B, \mathbb{C}\right)), (\operatorname{IsChannel}\left(T\right) \Leftrightarrow \exists (r : \mathbb{N}), (\exists (K : \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(B, A, \mathbb{C}\right)), (\sum_{i : \operatorname{Fin}\left(r\right)} (\operatorname{conjTranspose}\left(K\left(i\right)\right) \cdot K\left(i\right)) = 1 \land \forall (rho : \operatorname{Matrix}\left(A, A, \mathbb{C}\right)), (T\left(rho\right) = \operatorname{ofKraus}\left(K, K\right)\left(rho\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction.IsChannel` (`✓ std3`).

*Citation.* Martina Gschwendtner, Andreas Bluhm, Andreas Winter (2021). *Programmability of covariant quantum channels*. DOI: [10.22331/q-2021-06-29-488](https://doi.org/10.22331/q-2021-06-29-488). URL: <https://arxiv.org/abs/2012.00717v2>.

*Commentary.*

PDF p. 3: “A quantum channel is a completely positive trace-preserving map T : B(H₁) → B(H₂), where d₁, d₂ ∈ ℕ.” The finite Kraus convention represents such channels on complex Matrix carriers. A and B may be arbitrary finite types, so a processor's product index is included. ofKraus denotes the frozen MatrixMap.of_kraus, whose action is the sum Kᵢ rho (Kᵢ)ᴴ; conjTranspose is the matrix conjugate transpose. The completeness identity preserves trace. finite_kraus_quantum_channel states the related canonical QuantumChannel formulation on CStarMatrix; it is not on this module's dependency path.

**Theorem 1.2 (Four targets are incompatible).**

$$\forall (d : \mathbb{N}), (\forall (P : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (x : \operatorname{Fin}\left(d\right)), (\forall (p0 : \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (p1 : \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (pp : \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\forall (pm : \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\left(\operatorname{IsChannel}\left(P\right) \land \left(P\left(\operatorname{kronecker}\left(\operatorname{single}\left(x, x, 1\right), \operatorname{rankOneDensity}\left(p0\right)\right)\right) = !![1, 0; 0, 0] \land \left(P\left(\operatorname{kronecker}\left(\operatorname{single}\left(x, x, 1\right), \operatorname{rankOneDensity}\left(p1\right)\right)\right) = !![0, 0; 0, 1] \land \left(P\left(\operatorname{kronecker}\left(\operatorname{single}\left(x, x, 1\right), \operatorname{rankOneDensity}\left(pp\right)\right)\right) = !![\frac{1}{2}, \frac{1}{2}; \frac{1}{2}, \frac{1}{2}] \land P\left(\operatorname{kronecker}\left(\operatorname{single}\left(x, x, 1\right), \operatorname{rankOneDensity}\left(pm\right)\right)\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(\frac{1}{2}, (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)\right)\right)\right)\right) \Rightarrow False)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction.no_four_replacements` (`✓ std3`). ∎

*Citation.* Daniel Braun, Olivier Giraud, Ion Nechita, Clément Pellegrini, Marko Žnidarič (2014). *A universal set of qubit quantum channels*. DOI: [10.1088/1751-8113/47/13/135302](https://doi.org/10.1088/1751-8113/47/13/135302). URL: <https://arxiv.org/abs/1306.0495v2>.

*Commentary.*

Braun, Giraud, Nechita, Pellegrini and Žnidarič, A universal set of qubit quantum channels, arXiv:1306.0495v2, Theorem IV.9, classify the pure outputs of qubit channels: three distinct pure outputs force unitary conjugation. Fixing a basis input of an exact processor gives a qubit channel from the program register to the output. In the GBW-5 covariant-program question, its three pure replacement targets therefore force every pure program output to be pure, excluding the fourth target, one half of the identity. The theorem here establishes a stronger algebraic formulation that does not require program normalization. The input dimension and the finite Kraus count are unrestricted. Fix the basis input Matrix.single x x 1. The program-to-output map is linear, and its Gram matrix is the processor output. The first two targets force independent program vectors with opposite zero rows. The third target forces their nonzero environment rows to be parallel. Every program image then has dependent rows, whereas one half of the identity has independent rows. kronecker is Matrix.kronecker, and rankOneDensity is the frozen vecMulVec p (star p) construction.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction.IsChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction.no_four_replacements`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
