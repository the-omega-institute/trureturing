# Binomial and kappa states do not exhaust truncated entropy minimizers

## Abstract

The loss-dephasing channel of Memarzadeh and Mancini has a qutrit input with strictly smaller output entropy than every binomial or kappa candidate at the same input energy. The channel is defined by the Kraus equations, including the infinite phase-Kraus series.

**Definition 1.1 (Amplitude damping Kraus operator).**

$$\forall K : \mathbb{N}, \forall j : \operatorname{Fin}\left(K + 1\right), \forall f : \mathbb{R}, \forall r : \operatorname{Fin}\left(K + 1\right), \forall c : \operatorname{Fin}\left(K + 1\right), \operatorname{amplitudeKraus}\left(K, j, f\right)\left(r, c\right) = \operatorname{ite}\left(\operatorname{val}\left(r\right) + \operatorname{val}\left(j\right) = \operatorname{val}\left(c\right), \operatorname{ite}\left(\operatorname{val}\left(j\right) \le \operatorname{val}\left(c\right), \operatorname{ofReal}\left(((\operatorname{sqrt}\left(\operatorname{toReal}\left(\operatorname{choose}\left(\operatorname{val}\left(c\right), \operatorname{val}\left(j\right)\right)\right)\right)) \cdot ((\operatorname{sqrt}\left(1 - f\right))^{\operatorname{NatSub}\left(\operatorname{val}\left(c\right), \operatorname{val}\left(j\right)\right)})) \cdot ((\operatorname{sqrt}\left(f\right))^{\operatorname{val}\left(j\right)})\right), 0\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.amplitudeKraus` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

Equation (4), pp. 1–2: indices range over Fin(K+1). val is the natural-number value of a finite index, choose is the natural binomial coefficient, toReal is the natural-to-real cast, ofReal is the real-to-complex cast, and NatSub is truncated natural subtraction. Integer powers of square roots express the half-integer powers in the source for f in [0,1].

**Definition 1.2 (Phase damping Kraus operator).**

$$\forall K : \mathbb{N}, \forall k : \mathbb{N}, \forall eta : \mathbb{R}, \forall r : \operatorname{Fin}\left(K + 1\right), \forall c : \operatorname{Fin}\left(K + 1\right), \operatorname{phaseKraus}\left(K, k, eta\right)\left(r, c\right) = \operatorname{ite}\left(r = c, \operatorname{ofReal}\left((\operatorname{sqrt}\left(\frac{(((2) \cdot ((\operatorname{toReal}\left(\operatorname{val}\left(r\right)\right))^{2})) \cdot (eta))^{k}}{\operatorname{toReal}\left(\operatorname{factorial}\left(k\right)\right)}\right)) \cdot (\operatorname{exp}\left(-\left(((\operatorname{toReal}\left(\operatorname{val}\left(r\right)\right))^{2}) \cdot (eta)\right)\right))\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.phaseKraus` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

Equation (5), p. 2: k is an arbitrary natural number; the phase-Kraus family remains infinite after space truncation. factorial is the natural factorial, cast to the reals before division.

**Definition 1.3 (The composed loss-dephasing channel).**

$$\forall K : \mathbb{N}, \forall epsilon : \mathbb{R}, \forall t : \mathbb{R}, \forall rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right), \operatorname{lossDephasingChannel}\left(K, epsilon, t, rho\right) = \sum_{j : \operatorname{Fin}\left(K + 1\right)} (\sum'_{k : \mathbb{N}} ((((\operatorname{amplitudeKraus}\left(K, j, 1 - \operatorname{exp}\left(((-2) \cdot (1 - epsilon)) \cdot (t)\right)\right)) \cdot (\operatorname{phaseKraus}\left(K, k, (epsilon) \cdot (t)\right))) \cdot (rho)) \cdot (\operatorname{adjoint}\left((\operatorname{amplitudeKraus}\left(K, j, 1 - \operatorname{exp}\left(((-2) \cdot (1 - epsilon)) \cdot (t)\right)\right)) \cdot (\operatorname{phaseKraus}\left(K, k, (epsilon) \cdot (t)\right))\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.lossDephasingChannel` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

Equation (3), p. 1, with E_jk=A_j P_k: the amplitude index j is finite after truncation, and the k sum is the infinite series. adjoint is conjugate transpose. The phase factor is obtained by summing that series, rather than assuming a matrix of output entries.

**Definition 1.4 (Truncated number observable).**

$$\forall K : \mathbb{N}, \operatorname{numberOperator}\left(K\right) = \operatorname{diagonal}\left(\lambda i : \operatorname{Fin}\left(K + 1\right), \operatorname{toComplex}\left(\operatorname{val}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.numberOperator` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

The truncated Fock number observable is diagonal with entries 0,...,K. toComplex is the natural-to-complex cast.

**Definition 1.5 (Spectral entropy in nats).**

$$\forall K : \mathbb{N}, \forall rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right), \operatorname{vonNeumannEntropy}\left(K, rho\right) = if h : \operatorname{IsHermitian}\left(rho\right) then \operatorname{shannonEntropy}\left(\operatorname{eigenvalues}\left(rho, h\right)\right) else 0$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.vonNeumannEntropy` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

For a Hermitian matrix, use the existing finite Shannon entropy sum of its real eigenvalues, counted with multiplicity: shannonEntropy(p)=sum_i -p_i log(p_i), with the continuous zero convention. The displayed dependent conditional binds the Hermiticity proof h in its true branch. For a non-Hermitian raw matrix the extension is zero. All outputs used below are Hermitian and positive. Natural logarithms differ from the source's base-two entropy by a positive constant and give the same ordering.

**Definition 1.6 (Fixed-energy density inputs).**

$$\forall K : \mathbb{N}, \forall N : \mathbb{R}, \forall rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right), \operatorname{admissible}\left(K, N, rho\right) \Leftrightarrow ((\operatorname{PosSemidef}\left(rho\right)) \land ((\operatorname{trace}\left(rho\right) = 1) \land (\operatorname{Re}\left(\operatorname{trace}\left((rho) \cdot (\operatorname{numberOperator}\left(K\right))\right)\right) = N)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.admissible` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

Equation (9), p. 2: admissible inputs are positive semidefinite matrices of trace one with number expectation N. PosSemidef is Mathlib's matrix predicate, trace is the complex matrix trace, and Re takes its real part.

**Definition 1.7 (Binomial state amplitudes).**

$$\forall K : \mathbb{N}, \forall M : \mathbb{N}, \forall mu : \mathbb{R}, \forall i : \operatorname{Fin}\left(K + 1\right), \operatorname{binomialKet}\left(K, M, mu\right)\left(i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) \le M, \operatorname{ofReal}\left(\operatorname{sqrt}\left(((\operatorname{toReal}\left(\operatorname{choose}\left(M, \operatorname{val}\left(i\right)\right)\right)) \cdot ((mu)^{\operatorname{val}\left(i\right)})) \cdot ((1 - mu)^{\operatorname{NatSub}\left(M, \operatorname{val}\left(i\right)\right)})\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.binomialKet` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

Equation (14), p. 3: the binomial amplitudes are supported on 0,...,M. Natural subtraction M-val(i) is NatSub; the probability powers have natural exponents.

**Definition 1.8 (The kappa state family).**

$$\forall K : \mathbb{N}, \forall N : \mathbb{R}, \forall alpha : \mathbb{R}, \forall i : \operatorname{Fin}\left(K + 1\right), \operatorname{kappaKet}\left(K, N, alpha\right)\left(i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) = 0, \operatorname{ofReal}\left(\operatorname{sqrt}\left(1 - \frac{N}{\operatorname{toReal}\left(K\right)}\right)\right), \operatorname{ite}\left(\operatorname{val}\left(i\right) = K, (\operatorname{ofReal}\left(\operatorname{sqrt}\left(\frac{N}{\operatorname{toReal}\left(K\right)}\right)\right)) \cdot (\operatorname{ComplexExp}\left((\operatorname{ComplexI}\left(\right)) \cdot (\operatorname{ofReal}\left((alpha) \cdot (\operatorname{toReal}\left(K\right))\right))\right)), 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.kappaKet` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

Equation (11), p. 2: for K>=1 the state has support at 0 and K and relative phase exp(i alpha K). The conditional order agrees with Lean, including its extension at K=0, which the claim excludes. ComplexI is the imaginary unit; real quotients use the real cast of K.

**Definition 1.9 (The two proposed optimizer families).**

$$\forall K : \mathbb{N}, \forall N : \mathbb{R}, \forall phi : \operatorname{Fin}\left(K + 1\right) \to \mathbb{C}, \operatorname{candidate}\left(K, N, phi\right) \Leftrightarrow ((\exists M : \mathbb{N}, (1 \le M) \land ((M \le K) \land (\exists mu : \mathbb{R}, (0 \le mu) \land ((mu \le 1) \land (((\operatorname{toReal}\left(M\right)) \cdot (mu) = N) \land (phi = \operatorname{binomialKet}\left(K, M, mu\right))))))) \lor (\exists alpha : \mathbb{R}, phi = \operatorname{kappaKet}\left(K, N, alpha\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.candidate` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

The binomial candidates obey 1<=M<=K, 0<=mu<=1 and M mu=N. The other candidates are kappaKet(K,N,alpha) for any real alpha. Equality here is equality of ket functions; the conjecture tests their outer-product matrices.

**Definition 1.10 (Conjecture 1).**

$$claim \Leftrightarrow (\forall K : \mathbb{N}, \forall N : \mathbb{R}, \forall epsilon : \mathbb{R}, \forall t : \mathbb{R}, (1 \le K) \Rightarrow ((0 \le N) \Rightarrow ((N \le \operatorname{toReal}\left(K\right)) \Rightarrow ((0 \le epsilon) \Rightarrow ((epsilon \le 1) \Rightarrow ((0 \le t) \Rightarrow (\exists phi : \operatorname{Fin}\left(K + 1\right) \to \mathbb{C}, (\operatorname{candidate}\left(K, N, phi\right)) \land (\forall rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right), (\operatorname{admissible}\left(K, N, rho\right)) \Rightarrow (\operatorname{vonNeumannEntropy}\left(K, \operatorname{lossDephasingChannel}\left(K, epsilon, t, \operatorname{rankOneDensity}\left(phi\right)\right)\right) \le \operatorname{vonNeumannEntropy}\left(K, \operatorname{lossDephasingChannel}\left(K, epsilon, t, rho\right)\right))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.claim` (`✓ std3`).

*Citation.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

Conjecture 1, section IV, arXiv v1 PDF p. 4: "In a truncated Hilbert space of dimension K+1, the minimal output entropy of the quantum channel (3) is achieved either by binomial states of Eq.(14) or by states |κ_α⟩ of Eq. (11), depending on the values of ε and t." The encoding quantifies over K>=1, N in [0,K], epsilon in [0,1] and t>=0. A candidate attains the minimum if its output entropy is no greater than the output entropy of every fixed-energy density input.

**Theorem 1.11 (Qutrit refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/memarzadeh-mancini-2016-truncated-loss-dephasing-optimizer-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"memarzadeh-mancini-2016-truncated-loss-dephasing-optimizer-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Laleh Memarzadeh; Stefano Mancini (2016). *Minimum output entropy of a non-Gaussian quantum channel*. DOI: [10.1103/PhysRevA.94.022341](https://doi.org/10.1103/PhysRevA.94.022341). URL: <https://arxiv.org/abs/1605.04525v1>.

*Commentary.*

Take K=2, N=3/2, epsilon=6/7, t=(7/2)log(2), and psi=(|1>+|2>)/sqrt(2). The only binomial candidate is M=2, mu=3/4. Every kappa phase is covered by diagonal unitary conjugation. The psi output has an eigenvalue above 1/2 and one below 1/8, whereas all eigenvalues of each candidate output lie strictly between 1/8 and 1/2. Trace-one strict majorization and strict concavity of -x log(x) give smaller entropy for psi. The defining Kraus equations give the kappa output's off-diagonal coefficient sqrt(3)/32768; the displayed section-III coefficient in the source differs from those equations. The result excludes these candidate families as minimizers; it does not assert global optimality of psi. The proof has proof_shape: bind-only and escape_witness: none; it applies the exponential-series, positive-definiteness and strict-concavity results to the displayed instance.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.admissible`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.amplitudeKraus`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.binomialKet`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.candidate`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.kappaKet`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.lossDephasingChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.numberOperator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.phaseKraus`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.vonNeumannEntropy`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../Entropy/MaxEntropy.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
