# Trace-distance anticoherence need not increase under covariant noise

## Abstract

A covariant spin-four channel decreases order-seven trace-distance anticoherence.

**Definition 1.1 (The spin representation in Dicke coordinates).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.specialUnitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{spinAction}\left(n, u\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right)\right) = \left(\left(\operatorname{Matrix.conjTranspose}\left(\operatorname{dickeIsometry}\left(n\right)\right)\right) \cdot \left(\operatorname{tensorOp}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Subtype.val}\left(u\right)\right)\right)\right)\right) \cdot \left(\operatorname{dickeIsometry}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.spinAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jérôme Denis, Tara Lacaille, John Martin and Eduardo Serrano-Ensástiga (2026). *Total, quantum, and classical measures of anticoherence for mixed spin states*. DOI: [10.48550/arXiv.2605.29436](https://doi.org/10.48550/arXiv.2605.29436). URL: <https://arxiv.org/abs/2605.29436v1>.

*Commentary.*

Embed spin n/2 into n qubits by the normalized Dicke embedding, apply n copies of the single-qubit special unitary matrix u, and compress back to Dicke coordinates. This gives a matrix of size n plus one. The symmetric-subspace interpretation is the one in arxiv.tex, lines 150–161; the displayed compression specifies its coordinates.

**Definition 1.2 (The reduced state in symmetric coordinates).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(t: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right)\right), \left(\left(\operatorname{reducedState}\left(t, \rho\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(t + 1\right), \operatorname{Fin}\left(t + 1\right), \mathbb{C}\right)\right) = \left(\operatorname{if} t \le n \operatorname{then} \left(\operatorname{let} \left(e: \operatorname{Equiv}\left(\left(\left(\left(\operatorname{Fin}\left(t\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \times \left(\left(\operatorname{Fin}\left(n - t\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right)\right) := \operatorname{Equiv.trans}\left(\operatorname{Fin.appendEquiv}\left(t, n - t\right), \operatorname{Equiv.cast}_{\left(\left(\operatorname{Fin}\left(t + \left(n - t\right)\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) = \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right)}\right) \operatorname{in} \left(\left(\left(\operatorname{Matrix.conjTranspose}\left(\operatorname{dickeIsometry}\left(t\right)\right)\right) \cdot \left(\operatorname{partialTraceRight}\left(\operatorname{Matrix.submatrix}\left(\left(\left(\operatorname{dickeIsometry}\left(n\right)\right) \cdot \left(\rho\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{dickeIsometry}\left(n\right)\right)\right), \operatorname{Equiv.toFun}\left(e\right), \operatorname{Equiv.toFun}\left(e\right)\right)\right)\right)\right) \cdot \left(\operatorname{dickeIsometry}\left(t\right)\right)\right)\right) \operatorname{else} 0\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.reducedState` (`✓ std3`).

*Citation.* Jérôme Denis, Tara Lacaille, John Martin and Eduardo Serrano-Ensástiga (2026). *Total, quantum, and classical measures of anticoherence for mixed spin states*. DOI: [10.48550/arXiv.2605.29436](https://doi.org/10.48550/arXiv.2605.29436). URL: <https://arxiv.org/abs/2605.29436v1>.

*Commentary.*

For t at most n, embed the matrix into n qubits, group the first t coordinates and the last n minus t coordinates by appending the two words, and trace over the second group. Compression by the t-qubit Dicke embedding expresses the result in the symmetric t-qubit basis. The equivalence e includes the equality t plus (n minus t) equals n. The subscript on Equiv.cast specifies the resulting equality of word types; its proof supplies only type transport. For t greater than n the definition is zero. This is the reduced-state notion of arxiv.tex, lines 150–161, with the full mixed-state range specified at line 178.

**Definition 1.3 (The largest distance from the maximally mixed state).**

$$\forall \left(t: \mathbb{N}\right), \left(\left(\operatorname{normalizer}\left(t\right): \mathbb{R}\right) = \operatorname{sSup}\left(\left\{\left(d: \mathbb{R}\right) \mid \exists \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(t + 1\right), \operatorname{Fin}\left(t + 1\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\sigma\right)\right) \land \left(\left(\operatorname{Matrix.trace}\left(\sigma\right) = 1\right) \land \left(d = \operatorname{traceNorm}\left(\sigma - \operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.designAverage}\left(t + 1\right)\right)\right)\right)\right)\right\}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.normalizer` (`✓ std3`).

*Citation.* Jérôme Denis, Tara Lacaille, John Martin and Eduardo Serrano-Ensástiga (2026). *Total, quantum, and classical measures of anticoherence for mixed spin states*. DOI: [10.48550/arXiv.2605.29436](https://doi.org/10.48550/arXiv.2605.29436). URL: <https://arxiv.org/abs/2605.29436v1>.

*Commentary.*

The maximally mixed reference is the identity divided by t plus one. Take the supremum of its trace norm distances from all positive semidefinite matrices of trace one on the symmetric t-qubit space. This expresses the normalization K_t of arxiv.tex, lines 333–337, using a real supremum. It uses the full Schatten one-norm, without a factor of one half.

**Definition 1.4 (The Schatten-one distance candidate).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(t: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right)\right), \left(\left(\operatorname{anticoherence}\left(t, \rho\right): \mathbb{R}\right) = 1 - \frac{\operatorname{traceNorm}\left(\operatorname{reducedState}\left(t, \rho\right) - \operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.designAverage}\left(t + 1\right)\right)}{\operatorname{normalizer}\left(t\right)}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.anticoherence` (`✓ std3`).

*Citation.* Jérôme Denis, Tara Lacaille, John Martin and Eduardo Serrano-Ensástiga (2026). *Total, quantum, and classical measures of anticoherence for mixed spin states*. DOI: [10.48550/arXiv.2605.29436](https://doi.org/10.48550/arXiv.2605.29436). URL: <https://arxiv.org/abs/2605.29436v1>.

*Commentary.*

Subtract from one the trace norm distance of the t-qubit reduction from the maximally mixed symmetric state, divided by the normalizer. This is the distance candidate of arxiv.tex, lines 338–358, at Schatten exponent one.

**Definition 1.5 (Complete positivity, trace preservation and spin covariance).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(\varphi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right)\right), \left(\left(\operatorname{IsCovariantChannel}\left(\varphi\right)\right) \Leftrightarrow \left(\left(\operatorname{MatrixMap.IsCompletelyPositive}\left(\varphi\right)\right) \land \left(\left(\operatorname{MatrixMap.IsTracePreserving}\left(\varphi\right)\right) \land \left(\forall \left(u: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.specialUnitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right)\right), \left(\varphi\left(\left(\left(\operatorname{spinAction}\left(n, u\right)\right) \cdot \left(x\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{spinAction}\left(n, u\right)\right)\right)\right) = \left(\left(\operatorname{spinAction}\left(n, u\right)\right) \cdot \left(\varphi\left(x\right)\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{spinAction}\left(n, u\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.IsCovariantChannel` (`✓ std3`).

*Citation.* Jérôme Denis, Tara Lacaille, John Martin and Eduardo Serrano-Ensástiga (2026). *Total, quantum, and classical measures of anticoherence for mixed spin states*. DOI: [10.48550/arXiv.2605.29436](https://doi.org/10.48550/arXiv.2605.29436). URL: <https://arxiv.org/abs/2605.29436v1>.

*Commentary.*

A complex-linear matrix map is required to be completely positive and trace preserving, and to commute with conjugation by spinAction n u for every single-qubit special unitary matrix u and every input matrix x. This is the covariant-channel notion in arxiv.tex, lines 186–198, expressed on the full matrix algebra.

**Definition 1.6 (Trace-distance monotonicity for every mixed-state order).**

$$\left(\operatorname{claim}\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\left(1 \le n\right) \to \left(\forall \left(t: \mathbb{N}\right), \left(\left(1 \le t\right) \to \left(\left(t \le n\right) \to \left(\forall \left(\varphi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right)\right), \left(\left(\operatorname{IsCovariantChannel}\left(\varphi\right)\right) \to \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \to \left(\left(\operatorname{Matrix.trace}\left(\rho\right) = 1\right) \to \left(\operatorname{anticoherence}\left(t, \rho\right) \le \operatorname{anticoherence}\left(t, \varphi\left(\rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jérôme Denis, Tara Lacaille, John Martin and Eduardo Serrano-Ensástiga (2026). *Total, quantum, and classical measures of anticoherence for mixed spin states*. DOI: [10.48550/arXiv.2605.29436](https://doi.org/10.48550/arXiv.2605.29436). URL: <https://arxiv.org/abs/2605.29436v1>.

*Commentary.*

For every natural n at least one and every order t between one and n, the assertion requires anticoherence to increase or stay constant under every covariant channel on spin n/2 and every positive semidefinite input of trace one. It is the trace-distance reading of axiom (T4) at arxiv.tex, lines 186–198 and 363. The mixed-state range is the full range at line 178, including t greater than n/2.

**Theorem 1.7 (A spin-four counterexample at order seven).**

$$\neg \left(\operatorname{claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/denis-lacaille-martin-serrano-ensastiga-2026-anticoherence-trace-distance` (refuted) by `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"denis-lacaille-martin-serrano-ensastiga-2026-anticoherence-trace-distance","declaration_gid":"D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jérôme Denis, Tara Lacaille, John Martin and Eduardo Serrano-Ensástiga (2026). *Total, quantum, and classical measures of anticoherence for mixed spin states*. DOI: [10.48550/arXiv.2605.29436](https://doi.org/10.48550/arXiv.2605.29436). URL: <https://arxiv.org/abs/2605.29436v1>.

*Commentary.*

Use n equal to 8 and t equal to 7, and let Jx, Jy and Jz be the spin-four matrices in the Dicke basis indexed by r from 0 to 8, with Jz diagonal entry 4 minus r. Let J+ be the raising matrix and put c = sqrt(3/3080). The five Kraus matrices, in order, are (3 Jz squared minus 20 I)/sqrt(1540), minus c times (Jz J+ plus J+ Jz), c times (Jz J+ adjoint plus J+ adjoint Jz), c times J+ squared, and c times (J+ adjoint) squared. Let Phi(X) be the sum of K X K adjoint over these five matrices.

Their nonzero entries shift the input index by 0, minus 1, 1, minus 2 and 2, respectively. For z = 4 minus r, the squared amplitudes are (3z squared minus 20) squared divided by 1540; 3(2z plus 1) squared times (20 minus z(z plus 1)) divided by 3080; 3(2z minus 1) squared times (20 minus (z minus 1)z) divided by 3080; 3(20 minus z(z plus 1))(20 minus (z plus 1)(z plus 2)) divided by 3080; and 3(20 minus (z minus 1)z)(20 minus (z minus 2)(z minus 1)) divided by 3080. Different input columns have disjoint supports for each Kraus matrix. Summing the squared amplitudes in each column gives one, so the sum of K adjoint K is I.

Choose rho = diag(209, 92, 560, 0, 441, 0, 294, 168, 0)/1764. Its entries are nonnegative and sum to one, so it is positive semidefinite with trace one. The same sparse-entry calculation, now summing over input columns, gives Phi(rho) = diag(22288, 30100, 25528, 13149, 45540, 10584, 24654, 11613, 10584)/194040.

To relate these spin coordinates to qubits, identify words with the same number of ones by permutations of their sites. There are Nat.choose n r such words of weight r. Their normalized indicator vectors are the Dicke columns, whose Gram matrix is the identity. A constant tensor power sends a Dicke column to a vector constant on each weight class. The Dicke projector therefore fixes this image, so the tensor action intertwines with spinAction. Splitting a weight-r Dicke column between t and n minus t sites gives, at weights k and l with k plus l equal to r, the coefficient sqrt(Nat.choose t k times Nat.choose (n minus t) l) divided by sqrt(Nat.choose n r), and zero otherwise. Apply CoherentHistorySchmidt.normalized_coefficient_factorization to the binary occupation multiset and identify its sector vectors with the Dicke columns. The sector multiplicities become binomial coefficients by sector_words_card_multinomial and Nat.binomial_eq_choose, giving the factorization through the two smaller Dicke embeddings. The partial-trace identity for product embeddings removes the isometry on the traced factor; compression by the remaining isometry gives exactly reducedState.

The ladder identity J+ J+ adjoint plus J+ adjoint J+ = 40 I minus 2 Jz squared implies that the sum of Jx squared, Jy squared and Jz squared is 20 I. For axes a,b in {x,y,z}, set S_ab = (Ja Jb plus Jb Ja)/2 minus (20/3) delta_ab I. These matrices are Hermitian, symmetric in a,b, and have S_xx plus S_yy plus S_zz equal to zero. Expressing the five Kraus matrices in these Cartesian components and expanding their sandwiches gives Phi(X) = (3/770) times the sum of S_ab X S_ab over all nine ordered pairs of axes.

The tensor power is unitary, and its intertwining with the isometric Dicke embedding makes spinAction unitary. The single-site Dicke sum identifies the three spin-four matrices with the compressions of collectiveSpin 8. For every special unitary qubit matrix u, Pauli conjugation gives a real orthogonal matrix r. Collective tensor rotation and the Dicke intertwining then give D Ja D adjoint = sum_c r_ac Jc, where D = spinAction 8 u. Quadratic rotation gives D S_ab D adjoint = sum_ce r_ac r_be S_ce. The Kronecker product of r with itself is orthogonal, so the orthogonal sandwich identity preserves the Cartesian sum. Thus Phi(D X D adjoint) = D Phi(X) D adjoint for every X. The Kraus form supplies complete positivity and the column identity supplies trace preservation, proving all three channel conditions.

For a real diagonal input with entries p_r, the splitting coefficients make the reduced matrix diagonal. Its k-th entry is the sum over r of p_r times Nat.choose t k times Nat.choose (n minus t) (r minus k), divided by Nat.choose n r, with an additional factor one when k is at most r and zero otherwise; r minus k is natural-number subtraction. At n = 8 and t = 7 this gives reducedState 7 rho = diag(21, 21, 40, 21, 21, 21, 21, 2)/168 and reducedState 7 (Phi(rho)) = diag(69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095)/517440. Subtract I/8 and sum the absolute values of the diagonal entries. The two trace norms are respectively 19/84 and 3933/17248.

The normalizer at order seven is positive. Indeed, the maximally mixed matrix is positive semidefinite of trace one, and every such matrix has trace norm one. The triangle inequality bounds every distance in the defining supremum by two. The rank-one diagonal state diag(1,0,0,0,0,0,0,0) has distance 7/4 from I/8, so 7/4 is at most normalizer 7.

Finally assume claim and apply it to this channel and rho at n = 8 and t = 7. It would give 1 minus (19/84)/(normalizer 7) at most 1 minus (3933/17248)/(normalizer 7). Since 19/84 is strictly smaller than 3933/17248 and the common denominator is positive, the reverse strict inequality holds. This contradiction proves the negation of claim. The counterexample uses a mixed state and t greater than n/2; it does not decide monotonicity for orders at most n/2, or alter the Schatten-two result of arxiv.tex, lines 359–362.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.IsCovariantChannel`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.anticoherence`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.normalizer`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.reducedState`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.spinAction`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT](../Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness](../Entanglement/Witness/WernerTesterIncompleteness.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation](../Information/ChenKatoBrandaoTraceNormCMIRefutation.md)
- Dependency: [D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance](AnticoherenceSpinCovariance.md)
- Dependency: [D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality](DetectorSensorDickeOptimality.md)
- Dependency: [D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization](DiagonalKrausInstrumentFactorization.md)
