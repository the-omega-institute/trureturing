# Direct four-copy concentration exceeds the proposed bound

## Abstract

A fixed local singlet-sector measurement on four copies exceeds the conjectured pointwise concentration bound.

All computational-basis indices are zero-based. The coefficient matrix of a two-qubit pure state and the unnormalized Bell coefficient array have the following meanings:

$$
\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix} = \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)
$$

$$
\operatorname{D5.S3.Quantum.QubitWitnesses.bellCoefficients}\left(\right) = \begin{bmatrix}1&0\\0&1\end{bmatrix}
$$

The four coefficients c1, c2, c3, c4 in Eq. (1) are C(0,0), C(0,1), C(1,0), C(1,1), respectively. The superscript H denotes Matrix.conjTranspose, and a star between matrices denotes matrix multiplication. The double bars denote the complex norm; all sums below are finite.

**Definition 1.1 (The four-qubit local index).**

$$\operatorname{Q} = \left(\left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right) \times \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

The two product factors group positions (1,2) and (3,4) of one party's four qubits.

**Definition 1.2 (Normalized pure-state coefficients).**

$$\forall C \in \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix},\; \left(\left(\operatorname{normalized}\left(C\right)\right) \Leftrightarrow \left(\sum_{\left(i: \operatorname{Fin}\left(2\right)\right)} \left(\sum_{\left(j: \operatorname{Fin}\left(2\right)\right)} \left(\left(\left\lVert C\left(i, j\right) \right\rVert\right)^{2}\right)\right) = 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.normalized` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

Equation (1) requires the sum of the squared complex amplitudes to be one.

**Definition 1.3 (The four-copy input amplitudes).**

$$\forall C \in \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix},\; \left(\forall a \in \operatorname{Q},\; \left(\forall b \in \operatorname{Q},\; \left(\left(\operatorname{amp4}\left(C, a, b\right): \mathbb{C}\right) = \left(\left(\left(C\left(a.1.1, b.1.1\right)\right) * \left(C\left(a.1.2, b.1.2\right)\right)\right) * \left(C\left(a.2.1, b.2.1\right)\right)\right) * \left(C\left(a.2.2, b.2.2\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.amp4` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

For the four copies of the state in Eq. (1), a contains Alice's four bits and b contains Bob's. Each copy contributes one coefficient of C.

**Definition 1.4 (The product success operator on four copies).**

$$\forall KA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Q}, \mathbb{C}\right),\; \left(\forall KB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Q}, \mathbb{C}\right),\; \left(\forall C \in \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix},\; \left(\forall i \in \operatorname{Fin}\left(2\right),\; \left(\forall j \in \operatorname{Fin}\left(2\right),\; \left(\left(\operatorname{output}\left(KA, KB, C, i, j\right): \mathbb{C}\right) = \sum_{\left(a: \operatorname{Q}\right)} \left(\sum_{\left(b: \operatorname{Q}\right)} \left(\left(\left(KA\left(i, a\right)\right) * \left(KB\left(j, b\right)\right)\right) * \left(\operatorname{amp4}\left(C, a, b\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.output` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

The success branch acts by the single Kraus operator K_A tensor K_B. Its pure output has these coefficients. Bob's factor is transposed in the coefficient-matrix action, with no complex conjugation.

**Definition 1.5 (Universal conclusive pure-state concentration).**

$$\forall KA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Q}, \mathbb{C}\right),\; \left(\forall KB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Q}, \mathbb{C}\right),\; \left(\left(\operatorname{universal}\left(KA, KB\right)\right) \Leftrightarrow \left(\forall C \in \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix},\; \left(\left(\operatorname{normalized}\left(C\right)\right) \Rightarrow \left(\left(\operatorname{output}\left(KA, KB, C, 0, 1\right) = 0\right) \land \left(\left(\operatorname{output}\left(KA, KB, C, 1, 0\right) = 0\right) \land \left(\operatorname{output}\left(KA, KB, C, 0, 0\right) = \operatorname{output}\left(KA, KB, C, 1, 1\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.universal` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

Definition 1 for pure states says that the unnormalized output lies in the span of the Bell vector for every normalized input, including a zero output. This is exactly the vanishing of its two off-diagonal coefficients and equality of its two diagonal coefficients.

**Definition 1.6 (The success probability).**

$$\forall KA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Q}, \mathbb{C}\right),\; \left(\forall KB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Q}, \mathbb{C}\right),\; \left(\forall C \in \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix},\; \left(\left(\operatorname{success}\left(KA, KB, C\right): \mathbb{R}\right) = \sum_{\left(i: \operatorname{Fin}\left(2\right)\right)} \left(\sum_{\left(j: \operatorname{Fin}\left(2\right)\right)} \left(\left(\left\lVert \operatorname{output}\left(KA, KB, C, i, j\right) \right\rVert\right)^{2}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.success` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

For the normalized pure inputs of Eq. (1), the squared norm of the success output is the trace of the success branch, as in Theorem 3.

**Definition 1.7 (The proposed four-copy bound).**

$$\forall C \in \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix},\; \left(\left(\operatorname{B}\left(C\right): \mathbb{R}\right) = \left(\left(\left(2\right) * \left(\left\lVert \left(\left(C\left(0, 1\right)\right)^{4}\right) * \left(\left(C\left(1, 0\right)\right)^{4}\right) \right\rVert\right)\right) + \left(\left(2\right) * \left(\left\lVert \left(\left(C\left(0, 0\right)\right)^{4}\right) * \left(\left(C\left(1, 1\right)\right)^{4}\right) \right\rVert\right)\right)\right) - \left(\left(4\right) * \left(\left(\left(\left(\left(\left(C\left(0, 0\right)\right)^{2}\right) * \left(\left(C\left(1, 1\right)\right)^{2}\right)\right) * \left(\left(\operatorname{conj}\left(C\left(0, 1\right)\right)\right)^{2}\right)\right) * \left(\left(\operatorname{conj}\left(C\left(1, 0\right)\right)\right)^{2}\right)\right).\operatorname{re}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.B` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

This is literally the right-hand side of Eq. (8): the first two terms are norms of products of fourth powers, and the last term is four times the real part of the product with the two conjugated coefficients.

**Definition 1.8 (The direct four-copy concentration conjecture).**

$$\left(\operatorname{claim}\right) \Leftrightarrow \left(\forall KA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Q}, \mathbb{C}\right),\; \left(\forall KB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Q}, \mathbb{C}\right),\; \left(\left(\operatorname{Matrix.PosSemidef}\left(\left(1\right) - \left(\left(\left(KA\right)^{H}\right) * \left(KA\right)\right)\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.PosSemidef}\left(\left(1\right) - \left(\left(\left(KB\right)^{H}\right) * \left(KB\right)\right)\right)\right) \Rightarrow \left(\left(\operatorname{universal}\left(KA, KB\right)\right) \Rightarrow \left(\forall C \in \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix},\; \left(\left(\operatorname{normalized}\left(C\right)\right) \Rightarrow \left(\operatorname{success}\left(KA, KB, C\right) \le \operatorname{B}\left(C\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.claim` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

Section VIII conjectures that direct four-copy protocols cannot surpass B, the right-hand side of Eq. (8). Here the success branch has the single Kraus operator K_A tensor K_B, with each local operator a contraction. For either party, the positive square root R of the identity minus K_A^H K_A (or K_B^H K_B) gives failure operators |0><q|R, one for each local basis index q. Their adjoint products sum to R squared, so each party's instrument completes locally. The parties measure locally, communicate their success flags, and keep the output when both succeed. This is one-round LOCC processing the four copies directly. The predicate universal is Definition 1 for pure states. Thus every pair of operators quantified here gives a protocol in the conjectured class.

**Definition 1.9 (Singlets on consecutive pairs).**

$$\forall q \in \operatorname{Q},\; \left(\left(\operatorname{u}\left(q\right): \mathbb{C}\right) = \operatorname{D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.rationalSinglets}\left(\left(\left(q.1.1, q.2.1\right), \left(q.1.2, q.2.2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.u` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

The coordinate permutation turns the two-singlet coefficient function into the product of singlets on positions (1,2) and (3,4): (|0101> - |0110> - |1001> + |1010>)/2.

**Definition 1.10 (The orthogonal singlet-sector vector).**

$$\forall q \in \operatorname{Q},\; \left(\left(\operatorname{v}\left(q\right): \mathbb{C}\right) = \left(\left(\operatorname{Real.sqrt}\left(3\right): \mathbb{C}\right)^{-1}\right) * \left(\left(\left(2\right) * \left(\operatorname{D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.rationalSinglets}\left(q\right)\right)\right) - \left(\operatorname{u}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.v` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

The second pairing is the product of singlets on positions (1,3) and (2,4). Twice that vector minus u, divided by the complex cast of the real square root of three, is a unit vector orthogonal to u.

**Definition 1.11 (The local singlet-sector success operator).**

$$\forall i \in \operatorname{Fin}\left(2\right),\; \left(\forall q \in \operatorname{Q},\; \left(\left(\operatorname{K}\left(i, q\right): \mathbb{C}\right) = \operatorname{ite}\left(i = 0, \operatorname{u}\left(q\right), \operatorname{v}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

The rows are u and v. Both vectors have real entries, so these rows are also their bras. Their orthonormality makes K a coisometry and hence a local contraction.

**Definition 1.12 (A maximally entangled input with zero proposed bound).**

$$\left(\operatorname{C0}: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}\right) = \begin{bmatrix}\left(\frac{1}{2}: \mathbb{C}\right)&\frac{1}{2}\\-\frac{1}{2}&\frac{1}{2}\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.C0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

These rational coefficients form a normalized state with determinant one half.

**Theorem 1.13 (The direct four-copy bound is false).**

$$\neg \left(\operatorname{claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/orthey-philip-kondra-streltsov-2026-four-copy-concentration-bound` (refuted) by `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"orthey-philip-kondra-streltsov-2026-four-copy-concentration-bound","declaration_gid":"D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov (2026). *Optimality of universal conclusive entanglement concentration protocols*. DOI: [10.1103/bz3j-9njg](https://doi.org/10.1103/bz3j-9njg). URL: <https://arxiv.org/abs/2509.09423v2>.

*Commentary.*

The two singlet-pairing vectors are (|0101> - |0110> - |1001> + |1010>)/2 and (|0011> - |0110> - |1001> + |1100>)/2. The first is u; twice the second minus the first, divided by sqrt 3, is v. For every coefficient matrix C, output K K C is (det C) squared times the Bell array D5.S3.Quantum.QubitWitnesses.bellCoefficients, whose entries are one on the diagonal and zero off the diagonal. The fixed local contractions therefore give a universal conclusive protocol with success probability 2|det C| to the fourth power. At C0 this probability is 1/8, whereas B C0 is zero, contradicting the asserted inequality.

## References

- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.B`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.C0`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.K`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.Q`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.amp4`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.normalized`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.output`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.result`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.success`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.u`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.universal`
- Truth anchor: `D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.v`
- Dependency: [D5/S3/Quantum/Entanglement/QutritThresholdSharing](../Entanglement/QutritThresholdSharing.md)
- Dependency: [D5/S3/Quantum/QubitWitnesses](../QubitWitnesses.md)
- Dependency: [D5/S3/QuantumBounds/StatisticalStrengthMagicSquare](../../QuantumBounds/StatisticalStrengthMagicSquare.md)
