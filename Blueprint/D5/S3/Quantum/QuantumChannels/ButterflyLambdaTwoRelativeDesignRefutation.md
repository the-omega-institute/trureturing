# The single-pass butterfly fails the relative exterior-square two-design bound

## Abstract

A minor of every single-pass stride-doubling unitary butterfly vanishes. Its fourth-power Haar average is positive, so the lower relative completely positive bound forces error at least one in every dimension 2^K with K at least two.

**Definition 1.1 (Binary modes).**

$$\forall K : \mathbb{N}, \operatorname{Mode}\left(K\right) = (\operatorname{Fin}\left(K\right)) \to (\operatorname{Fin}\left(2\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Mode` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

Bit l has stride 2^l. Mathlib's finFunctionFinEquiv identifies these modes with Fin(2^K), with bit zero the least significant bit.

**Definition 1.2 (A layer's pair labels).**

$$\forall K : \mathbb{N}, \forall l : \operatorname{Fin}\left(K\right), \operatorname{Rest}\left(K, l\right) = (\operatorname{Subtype}\left((\lambda i : \operatorname{Fin}\left(K\right), i \ne l)\right)) \to (\operatorname{Fin}\left(2\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Rest` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

A pair is specified by every bit other than l; its two modes differ in bit l.

**Definition 1.3 (Independent parameter labels).**

$$\forall K : \mathbb{N}, \operatorname{AngleIndex}\left(K\right) = \operatorname{Sum}\left(\operatorname{Sigma}\left((\lambda l : \operatorname{Fin}\left(K\right), \operatorname{Rest}\left(K, l\right))\right), \operatorname{Prod}\left(\operatorname{Fin}\left(K\right), \operatorname{Mode}\left(K\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.AngleIndex` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

Sum is the disjoint sum of types and Sigma is the dependent sum. The left summand labels one RBS angle for each layer and pair; the right summand labels one phase for each layer and mode.

**Definition 1.4 (Real parameter assignments).**

$$\forall K : \mathbb{N}, \operatorname{Parameters}\left(K\right) = (\operatorname{AngleIndex}\left(K\right)) \to (\mathbb{R})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Parameters` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

All layer/pair and layer/mode coordinates are independent real angles.

**Definition 1.5 (Disjoint RBS blocks).**

$$\forall K : \mathbb{N}, \forall p : \operatorname{Parameters}\left(K\right), \forall l : \operatorname{Fin}\left(K\right), (\operatorname{rbs}\left(K, p, l\right) = \operatorname{submatrix}\left(\operatorname{blockDiagonal}\left((\lambda q : \operatorname{Rest}\left(K, l\right), \operatorname{val}\left(\operatorname{Matrix.planeConformalMatrix}\left(\operatorname{ofReal}\left(\operatorname{cos}\left(p\left(\operatorname{inl}\left(\operatorname{Sigma.mk}\left(l, q\right)\right)\right)\right)\right), -\operatorname{ofReal}\left(\operatorname{sin}\left(p\left(\operatorname{inl}\left(\operatorname{Sigma.mk}\left(l, q\right)\right)\right)\right)\right)\right)\right))\right), \operatorname{piSplitAt}\left(l, \operatorname{const}\left(\operatorname{Fin}\left(K\right), \operatorname{Fin}\left(2\right)\right)\right), \operatorname{piSplitAt}\left(l, \operatorname{const}\left(\operatorname{Fin}\left(K\right), \operatorname{Fin}\left(2\right)\right)\right)\right)) \land (\forall theta : \mathbb{R}, (\operatorname{val}\left(\operatorname{Matrix.planeConformalMatrix}\left(\operatorname{ofReal}\left(\operatorname{cos}\left(theta\right)\right), -\operatorname{ofReal}\left(\operatorname{sin}\left(theta\right)\right)\right)\right)\left(0, 0\right) = \operatorname{ofReal}\left(\operatorname{cos}\left(theta\right)\right)) \land ((\operatorname{val}\left(\operatorname{Matrix.planeConformalMatrix}\left(\operatorname{ofReal}\left(\operatorname{cos}\left(theta\right)\right), -\operatorname{ofReal}\left(\operatorname{sin}\left(theta\right)\right)\right)\right)\left(0, 1\right) = \operatorname{ofReal}\left(\operatorname{sin}\left(theta\right)\right)) \land ((\operatorname{val}\left(\operatorname{Matrix.planeConformalMatrix}\left(\operatorname{ofReal}\left(\operatorname{cos}\left(theta\right)\right), -\operatorname{ofReal}\left(\operatorname{sin}\left(theta\right)\right)\right)\right)\left(1, 0\right) = -\operatorname{ofReal}\left(\operatorname{sin}\left(theta\right)\right)) \land (\operatorname{val}\left(\operatorname{Matrix.planeConformalMatrix}\left(\operatorname{ofReal}\left(\operatorname{cos}\left(theta\right)\right), -\operatorname{ofReal}\left(\operatorname{sin}\left(theta\right)\right)\right)\right)\left(1, 1\right) = \operatorname{ofReal}\left(\operatorname{cos}\left(theta\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.rbs` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

piSplitAt splits a binary mode into its bit l and its remaining-bit function. const denotes the constant family with value Fin(2). The same equivalence reindexes both matrix coordinates of the block diagonal. Sigma.mk constructs the dependent layer/pair label. The blocks are the underlying matrices of Matrix.planeConformalMatrix(cos(theta), -sin(theta)); its nonzero premise follows from cos²(theta)+sin²(theta)=1. The four displayed entries use ofReal casts.

**Definition 1.6 (The full-width Rz phase layer).**

$$\forall K : \mathbb{N}, \forall p : \operatorname{Parameters}\left(K\right), \forall l : \operatorname{Fin}\left(K\right), \operatorname{phase}\left(K, p, l\right) = \operatorname{diagonal}\left((\lambda j : \operatorname{Mode}\left(K\right), \operatorname{val}\left(\operatorname{Circle.exp}\left(\frac{\sum_{i : \operatorname{Mode}\left(K\right)} (p\left(\operatorname{inr}\left(\operatorname{Prod.mk}\left(l, i\right)\right)\right))}{2} - p\left(\operatorname{inr}\left(\operatorname{Prod.mk}\left(l, j\right)\right)\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.phase` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

PDF p. 10: “The R_z gate acts as R_z(φ)|0⟩ = e^(iφ/2)|0⟩, R_z(φ)|1⟩ = e^(−iφ/2)|1⟩: a diagonal one-body unitary, hence passive FLO and particle-number preserving.” Circle.exp(a) is exp(i a) on the unit circle and val is its complex subtype value. Prod.mk constructs the layer/mode label. The sum/2 term retains the common vacuum phase of the literal full Rz layer.

**Definition 1.7 (One butterfly layer).**

$$\forall K : \mathbb{N}, \forall p : \operatorname{Parameters}\left(K\right), \forall l : \operatorname{Fin}\left(K\right), \operatorname{layer}\left(K, p, l\right) = (\operatorname{rbs}\left(K, p, l\right)) \cdot (\operatorname{phase}\left(K, p, l\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.layer` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

Phase gates act first and the disjoint RBS gates act second, exactly in the source's order.

**Definition 1.8 (The single-pass butterfly).**

$$\forall K : \mathbb{N}, \forall p : \operatorname{Parameters}\left(K\right), \operatorname{circuit}\left(K, p\right) = \operatorname{List.prod}\left(\operatorname{map}\left((\lambda l : \operatorname{Fin}\left(K\right), \operatorname{layer}\left(K, p, l\right)), \operatorname{reverse}\left(\operatorname{finRange}\left(K\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.circuit` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

Section IV, PDF p. 10: “An n-qubit unitary butterfly circuit of depth K = log₂ n consists of K layers. Layer ℓ ∈ {1,…,K} applies a full-width layer of n single-qubit phase gates followed by RBS gates on each of the n/2 disjoint pairs with stride 2^(ℓ−1):” The source displays U(θ,φ) = U^(K)⋯U^(1) and U^(ℓ) = [tensor_j RBS(θ_ℓ^(j))] · tensor_i R_z(φ_ℓ^(i)). Lean indices l=0,…,K−1 correspond to ℓ=l+1, so List.prod multiplies the reversed increasing index list.

**Definition 1.9 (Uniform product measure).**

$$\forall K : \mathbb{N}, \operatorname{parameterMeasure}\left(K\right) = \operatorname{MeasureTheory.Measure.pi}\left(\operatorname{const}\left(\operatorname{AngleIndex}\left(K\right), \operatorname{cond}\left(\operatorname{volume}\left(\right), \operatorname{Ico}\left(0, (2) \cdot (\operatorname{pi}\left(\right))\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.parameterMeasure` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

cond is normalized restriction of real Lebesgue measure. MeasureTheory.Measure.pi takes the independent product over all coordinates. The interval is [0,2π); the endpoints have zero measure. This is the uniform parameter-torus expectation in the source.

**Definition 1.10 (The ordered exterior basis).**

$$\forall K : \mathbb{N}, \operatorname{Wedge}\left(K\right) = \operatorname{Subtype}\left((\lambda p : \operatorname{Prod}\left(\operatorname{Mode}\left(K\right), \operatorname{Mode}\left(K\right)\right), \operatorname{finFunctionFinEquiv}\left(\operatorname{fst}\left(p\right)\right) < \operatorname{finFunctionFinEquiv}\left(\operatorname{snd}\left(p\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Wedge` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

The basis is e_i wedge e_j for i<j in binary mode order.

**Definition 1.11 (The second exterior representation).**

$$\forall K : \mathbb{N}, \forall W : \operatorname{Matrix}\left(\operatorname{Mode}\left(K\right), \operatorname{Mode}\left(K\right), \mathbb{C}\right), \forall i : \operatorname{Wedge}\left(K\right), \forall j : \operatorname{Wedge}\left(K\right), \operatorname{exteriorSquare}\left(K, W\right)\left(i, j\right) = (W\left(\operatorname{fst}\left(\operatorname{val}\left(i\right)\right), \operatorname{fst}\left(\operatorname{val}\left(j\right)\right)\right)) \cdot (W\left(\operatorname{snd}\left(\operatorname{val}\left(i\right)\right), \operatorname{snd}\left(\operatorname{val}\left(j\right)\right)\right)) - (W\left(\operatorname{fst}\left(\operatorname{val}\left(i\right)\right), \operatorname{snd}\left(\operatorname{val}\left(j\right)\right)\right)) \cdot (W\left(\operatorname{snd}\left(\operatorname{val}\left(i\right)\right), \operatorname{fst}\left(\operatorname{val}\left(j\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.exteriorSquare` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

Expanding (W e_i) wedge (W e_j) gives coefficient W_ai W_bj − W_aj W_bi in e_a wedge e_b. These coefficients define the induced second exterior representation, rather than a restriction of two independent single-particle copies. fst and snd select the two modes of an ordered pair.

**Definition 1.12 (Two exterior copies).**

$$\forall K : \mathbb{N}, \operatorname{TwoCopy}\left(K\right) = \operatorname{Prod}\left(\operatorname{Wedge}\left(K\right), \operatorname{Wedge}\left(K\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.TwoCopy` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

This indexes the tensor product of two copies of the second exterior space.

**Definition 1.13 (The Kronecker-square action).**

$$\forall K : \mathbb{N}, \forall W : \operatorname{Matrix}\left(\operatorname{Mode}\left(K\right), \operatorname{Mode}\left(K\right), \mathbb{C}\right), \operatorname{secondAction}\left(K, W\right) = \operatorname{kronecker}\left(\operatorname{exteriorSquare}\left(K, W\right), \operatorname{exteriorSquare}\left(K, W\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.secondAction` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

kronecker is Mathlib's matrix Kronecker product. Its row and column indices are ordered pairs of exterior-basis elements.

**Definition 1.14 (Second-moment matrix action).**

$$\forall K : \mathbb{N}, \forall X : \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)] \forall mu : \operatorname{Measure}\left(X\right), \forall W : (X) \to (\operatorname{Matrix}\left(\operatorname{Mode}\left(K\right), \operatorname{Mode}\left(K\right), \mathbb{C}\right)), \forall Y : \operatorname{Matrix}\left(\operatorname{TwoCopy}\left(K\right), \operatorname{TwoCopy}\left(K\right), \mathbb{C}\right), \forall i : \operatorname{TwoCopy}\left(K\right), \forall j : \operatorname{TwoCopy}\left(K\right), \operatorname{twirl}\left(K, X, mu, W, Y\right)\left(i, j\right) = \operatorname{integral}\left(mu, (\lambda p : X, \left(((\operatorname{secondAction}\left(K, W\left(p\right)\right)) \cdot (Y)) \cdot (\operatorname{adjoint}\left(\operatorname{secondAction}\left(K, W\left(p\right)\right)\right))\right)\left(i, j\right))\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.twirl` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

Each entry is a complex Bochner integral. The index set is finite; for the butterfly and Haar actions the integrands are continuous and integrable, so this agrees with the full finite-dimensional matrix Bochner integral. adjoint is conjugate transpose.

**Definition 1.15 (The butterfly second moment).**

$$\forall K : \mathbb{N}, \operatorname{butterflyMoment}\left(K\right) = \operatorname{twirl}\left(K, \operatorname{parameterMeasure}\left(K\right), \operatorname{circuit}\left(K\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.butterflyMoment` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

This is Φ₂^(Λ²,Wₙ) with n=2^K and independent uniform circuit parameters.

**Definition 1.16 (The compact unitary group).**

$$\forall K : \mathbb{N}, \operatorname{Unitary}\left(K\right) = \operatorname{unitary}\left(\operatorname{CStarMatrix}\left(\operatorname{Mode}\left(K\right), \operatorname{Mode}\left(K\right), \mathbb{C}\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Unitary` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

CStarMatrix is Mathlib's operator-norm type copy of complex matrices. Its unitary group has the same elements and multiplication as Matrix.unitaryGroup on these modes. The measurable space is its Borel space.

**Definition 1.17 (Normalized Haar probability).**

$$\forall K : \mathbb{N}, \operatorname{haarProbability}\left(K\right) = \operatorname{haarMeasure}\left((\operatorname{Top.top} : \operatorname{PositiveCompacts}\left(\operatorname{Unitary}\left(K\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.haarProbability` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

The unitary group is compact: it is a closed subset of the radius-one ball in a finite-dimensional proper normed space. Top.top at type PositiveCompacts (Unitary K) is the whole compact group, so Mathlib's Haar normalization assigns it mass one.

**Definition 1.18 (The Haar second moment).**

$$\forall K : \mathbb{N}, \operatorname{haarMoment}\left(K\right) = \operatorname{twirl}\left(K, \operatorname{haarProbability}\left(K\right), (\lambda U : \operatorname{Unitary}\left(K\right), \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(U\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.haarMoment` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

CStarMatrix.ofMatrix.symm returns the raw matrix of a unitary-group element; val is its subtype value.

**Definition 1.19 (Completely positive order).**

$$\forall iota : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall F : (\operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)) \to (\operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)), \forall G : (\operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)) \to (\operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)), \operatorname{CPLe}\left(iota, F, G\right) \Leftrightarrow (\exists H : \operatorname{CompletelyPositiveMap}\left(\operatorname{CStarMatrix}\left(iota, iota, \mathbb{C}\right), \operatorname{CStarMatrix}\left(iota, iota, \mathbb{C}\right)\right), \forall Y : \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right), \operatorname{CStarMatrix.ofMatrix.symm}\left(H\left(\operatorname{ofMatrix}\left(Y\right)\right)\right) = G\left(Y\right) - F\left(Y\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.CPLe` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

F ⪯ G means that G−F is the raw action of a canonical completely positive map H. Mathlib's bundled type contains complex linearity and positivity under every finite matrix amplification, acting entrywise on the matrix of blocks. This is the completely positive order on the Kronecker-square action; it is stronger than testing only positive inputs without amplification.

**Definition 1.20 (Conjecture 20: the relative design bound).**

$$claim \Leftrightarrow (\exists c : \mathbb{R}, \exists N : \mathbb{N}, \forall K : \mathbb{N}, (N \le 2^{K}) \Rightarrow (\exists epsilon : \mathbb{R}, (0 \le epsilon) \land ((epsilon \le \frac{c}{(\operatorname{Nat.cast}\left(2^{K}\right) : \mathbb{R})}) \land ((\operatorname{CPLe}\left(\operatorname{TwoCopy}\left(K\right), (\lambda Y : \operatorname{Matrix}\left(\operatorname{TwoCopy}\left(K\right), \operatorname{TwoCopy}\left(K\right), \mathbb{C}\right), \operatorname{smul}\left(1 - epsilon, \operatorname{haarMoment}\left(K, Y\right)\right)), \operatorname{butterflyMoment}\left(K\right)\right)) \land (\operatorname{CPLe}\left(\operatorname{TwoCopy}\left(K\right), \operatorname{butterflyMoment}\left(K\right), (\lambda Y : \operatorname{Matrix}\left(\operatorname{TwoCopy}\left(K\right), \operatorname{TwoCopy}\left(K\right), \mathbb{C}\right), \operatorname{smul}\left(1 + epsilon, \operatorname{haarMoment}\left(K, Y\right)\right))\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.claim` (`✓ std3`).

*Citation.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

Conjecture 20, PDF p. 16, equations (38)–(39): “The unitary butterfly W<sub>n</sub> at uniformly random parameters is an ε-approximate unitary 2-design on U(n) in the antisymmetric 2-particle representation Λ² ℂ<sup>n</sup>, in the *relative* (multiplicative) sense, with ε = O(1/n): writing Φ₂<sup>Λ²,W<sub>n</sub></sup>[Y] := E<sub>W<sub>n</sub></sub>[Λ²(W<sub>n</sub>)<sup>⊗ 2</sup> Y Λ²(W<sub>n</sub>)<sup>†⊗ 2</sup>], for Y ∈ End(Λ²ℂ<sup>n</sup> ⊗ Λ²ℂ<sup>n</sup>), and Φ₂<sup>Λ²,Haar</sup> for the corresponding Haar second moment, (1−ε) Φ₂<sup>Λ²,Haar</sup> ⪯ Φ₂<sup>Λ²,W<sub>n</sub></sup> ⪯ (1+ε) Φ₂<sup>Λ²,Haar</sup> as completely positive maps. In particular Φ₂<sup>Λ²,W<sub>n</sub></sup> has fixed-point space of dimension 3, matching the Haar decomposition Λ² ⊗ Λ² = V<sub>(2,2)</sub> ⊕ V<sub>(2,1,1)</sub> ⊕ V<sub>(1,1,1,1)</sub> into three irreducible U(n)-representations.”

The displayed claim encodes the relative bound that this conjecture asserts. A real c and natural threshold N precede every K with N≤2^K, followed by a nonnegative ε≤c/(2^K). Both lower and upper inequalities use CPLe. The fixed-point-space sentence is quoted as part of the source; refuting the relative bound refutes its full conjecture without asserting a separate fixed-point dimension result.

**Theorem 1.21 (Refutation in arbitrary dimension).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kerenidis-2026-butterfly-lambda-two-relative-design-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kerenidis-2026-butterfly-lambda-two-relative-design-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Iordanis Kerenidis (2026). *Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency*. DOI: [10.48550/arXiv.2607.24014](https://doi.org/10.48550/arXiv.2607.24014). URL: <https://arxiv.org/abs/2607.24014v2>.

*Commentary.*

For every K≥2 and every parameter assignment the minor W₀₀W₂₁−W₀₁W₂₀ vanishes. The first layer has stride-one support; the later product preserves bit zero, so the selected columns are proportional on rows zero and two. For Haar unitaries, the continuous fourth power of the minor is nonnegative and equals one at the permutation exchanging modes one and two; Haar positivity on nonempty open sets makes its integral positive. Apply the lower CP bound to the rank-one projector at x=(e₀ wedge e₁) tensor (e₀ wedge e₁) and read the diagonal at u=(e₀ wedge e₂) tensor (e₀ wedge e₂). Its butterfly value is zero, while its Haar value is positive, forcing ε≥1. Powers 2^K exceed any fixed c and threshold, contradicting ε≤c/(2^K). The additive one-copy design statement and the independent-halves ensemble are outside this conclusion.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.AngleIndex`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.CPLe`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Mode`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Parameters`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Rest`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.TwoCopy`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Unitary`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.Wedge`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.butterflyMoment`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.circuit`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.exteriorSquare`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.haarMoment`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.haarProbability`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.layer`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.parameterMeasure`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.phase`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.rbs`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.secondAction`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.twirl`
