# Gingrich's proposed three-qubit monotone increases on average under a local measurement

## Abstract

Gingrich (arXiv:quant-ph/0106042, Phys. Rev. A 65, 052302) proposes sigma_ABC = 3 - (I_1 + I_2 + I_3) I_4, built from three purities and the Kempe invariant I_4, as a fifth entanglement monotone of three-qubit pure states, supported by numerical tests. It is not one: a two-outcome diagonal measurement on qubit A of (5|000> + 5|011> + 2|110>)/(3 sqrt 6) raises its average by 169/1594323.

**Definition 1.1 (Polynomial invariants).**

$$\forall n : \mathbb{N}, \forall \sigma : \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right), \forall \tau : \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right), \forall \psi : (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, \operatorname{polyInvariant}\left(\sigma, \tau, \psi\right) = \sum_{x : \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right))} \prod_{r} \psi\left(x_{r}\right) \cdot \operatorname{star}\left(\psi\left((\left(x_{r}\right)\left(0\right), \left(x_{\sigma\left(r\right)}\right)\left(1\right), \left(x_{\tau\left(r\right)}\right)\left(2\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.polyInvariant` (`✓ std3`).

*Citation.* Robert M. Gingrich (2002). *Properties of entanglement monotones for three-qubit pure states*. DOI: [10.1103/PhysRevA.65.052302](https://doi.org/10.1103/PhysRevA.65.052302). URL: <https://arxiv.org/abs/quant-ph/0106042v2>.

*Commentary.*

For a three-qubit vector psi, a function from the configurations Fin 3 -> Fin 2 to the complex numbers with the qubits A, B, C at the indices 0, 1, 2, the amplitude t_{ijk} is psi at (i, j, k). For permutations sigma and tau of n elements, Eq. (8) of the paper sums, over n index triples x_r = (i_r, j_r, k_r), the product over r of t_{i_r j_r k_r} times the complex conjugate of t_{i_r j_{sigma(r)} k_{tau(r)}}.

**Definition 1.2 (The proposed monotone).**

$$\forall \psi : (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, \operatorname{sigmaABC}\left(\psi\right) = 3 - (\operatorname{polyInvariant}\left(1, \operatorname{swap}\left(0, 1\right), \psi\right) + \operatorname{polyInvariant}\left(\operatorname{swap}\left(0, 1\right), 1, \psi\right) + \operatorname{polyInvariant}\left(\operatorname{swap}\left(0, 1\right), \operatorname{swap}\left(0, 1\right), \psi\right)) \cdot \operatorname{polyInvariant}\left(\operatorname{finRotate}\left(3\right), \operatorname{finRotate}\left(3\right)^{-1}, \psi\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.sigmaABC` (`✓ std3`).

*Citation.* Robert M. Gingrich (2002). *Properties of entanglement monotones for three-qubit pure states*. DOI: [10.1103/PhysRevA.65.052302](https://doi.org/10.1103/PhysRevA.65.052302). URL: <https://arxiv.org/abs/quant-ph/0106042v2>.

*Commentary.*

The paper sets I_1 = P_{e,(12)}, I_2 = P_{(12),e}, I_3 = P_{(12),(12)} on two index triples and the Kempe invariant I_4 = P_{(123),(132)} on three index triples, and proposes sigma_ABC = 3 - (I_1 + I_2 + I_3) I_4. Here e is the identity permutation, swap(0, 1) is the transposition (12) of Fin 2, and finRotate(3), which sends 0 to 1, 1 to 2 and 2 to 0, is the cycle (123), with inverse (132).

**Definition 1.3 (The proposed monotonicity).**

$$(claim) \Leftrightarrow (\forall \psi : (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, (\sum_{w} \left\lVert \psi\left(w\right) \right\rVert^{2} = 1) \Rightarrow (\forall n : \mathbb{N}, \forall K : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), (\sum_{k} \left(K_{k}\right)^{H} \cdot K_{k} = 1) \Rightarrow (\forall p : \operatorname{Fin}\left(n\right) \to \mathbb{R}, (\forall k : \operatorname{Fin}\left(n\right), p_{k} = \sum_{w} \left\lVert (\operatorname{localOp}\left(0, K_{k}\right) \cdot \psi)\left(w\right) \right\rVert^{2}) \Rightarrow (\sum_{k : p_{k} \neq 0} p_{k} \cdot \operatorname{re}\left(\operatorname{sigmaABC}\left(\frac{1}{\sqrt{p_{k}}} \cdot (\operatorname{localOp}\left(0, K_{k}\right) \cdot \psi)\right)\right) \le \operatorname{re}\left(\operatorname{sigmaABC}\left(\psi\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.claim` (`✓ std3`).

*Citation.* Robert M. Gingrich (2002). *Properties of entanglement monotones for three-qubit pure states*. DOI: [10.1103/PhysRevA.65.052302](https://doi.org/10.1103/PhysRevA.65.052302). URL: <https://arxiv.org/abs/quant-ph/0106042v2>.

*Commentary.*

The paper calls a function an entanglement monotone if, for every state and every complete local instrument on one party, its value is at least the average of its values on the normalized outcomes, weighted by their probabilities. The displayed statement is this inequality for every normalized three-qubit vector and every complete instrument K_0, ..., K_{n-1} on qubit A (index 0), acting through the existing localOp, the product operator with factor K_k at qubit 0 and the identity elsewhere; the weights p are the outcome probabilities, outcomes with p_k = 0 are omitted, and sigma_ABC enters through its real part.

**Definition 1.4 (The counterexample state).**

$$\psi = \frac{1}{3 \cdot \sqrt{6}} \cdot (5 \cdot |000\rangle + 5 \cdot |011\rangle + 2 \cdot |110\rangle)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robert M. Gingrich (2002). *Properties of entanglement monotones for three-qubit pure states*. DOI: [10.1103/PhysRevA.65.052302](https://doi.org/10.1103/PhysRevA.65.052302). URL: <https://arxiv.org/abs/quant-ph/0106042v2>.

*Commentary.*

The state is (5|000> + 5|011> + 2|110>)/(3 sqrt 6), with norm one since 25 + 25 + 4 = 54.

**Definition 1.5 (The measurement on qubit A).**

$$K_{0} = \operatorname{diag}\left(\frac{3}{5}, 0\right),\qquad K_{1} = \operatorname{diag}\left(\frac{4}{5}, 1\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.instrument` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robert M. Gingrich (2002). *Properties of entanglement monotones for three-qubit pure states*. DOI: [10.1103/PhysRevA.65.052302](https://doi.org/10.1103/PhysRevA.65.052302). URL: <https://arxiv.org/abs/quant-ph/0106042v2>.

*Commentary.*

The two outcomes are K_0 = diag(3/5, 0) and K_1 = diag(4/5, 1) on qubit A, with K_0^dagger K_0 + K_1^dagger K_1 = I.

**Theorem 1.6 (The proposed monotone increases on average).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gingrich-2002-sigma-abc-monotone` (refuted) by `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gingrich-2002-sigma-abc-monotone","declaration_gid":"D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert M. Gingrich (2002). *Properties of entanglement monotones for three-qubit pure states*. DOI: [10.1103/PhysRevA.65.052302](https://doi.org/10.1103/PhysRevA.65.052302). URL: <https://arxiv.org/abs/quant-ph/0106042v2>.

*Commentary.*

For a vector a|000> + b|011> + c|110>, expanding Eq. (8) gives I_1 = (x + z)^2 + y^2, I_2 = x^2 + (y + z)^2, I_3 = (x + y)^2 + z^2 and I_4 = x^3 + y^3 + z^3 + 3xyz with x = |a|^2, y = |b|^2, z = |c|^2. The operator diag(k_0, k_1) on qubit A and a scalar keep this support. The outcome K_0 has probability 1/3 and normalized state (|000> + |011>)/sqrt 2, where sigma_ABC = 5/2; the outcome K_1 has probability 2/3 and normalized state (2|000> + 2|011> + |110>)/3, where sigma_ABC = 16792/6561. The state itself has sigma_ABC = 8097475/3188646, so the average after the measurement, 8097813/3188646, exceeds it by 169/1594323.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.instrument`
- Truth anchor: `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.polyInvariant`
- Truth anchor: `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.psi`
- Truth anchor: `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.sigmaABC`
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Information/StabilizerPairLocalUnitaryInequivalence.md)
