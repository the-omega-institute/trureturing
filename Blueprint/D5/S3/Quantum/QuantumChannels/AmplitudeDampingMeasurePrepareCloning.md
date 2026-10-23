# Amplitude-damping channels resist perfect measure-and-prepare cloning

## Abstract

No finite measure-and-prepare ensemble perfectly clones every amplitude-damping channel into a positive number of outputs.

Matrix indices place the reference qubit before the output qubit. All Choi matrices are unnormalized: tracing out the output gives the identity on the reference. The functions Complex.ofReal in the formulas explicitly embed real numbers into the complex field; star is complex conjugation, and smul is scalar multiplication of a matrix. The order on complex scalars means that a nonnegative scalar is real and nonnegative.

**Definition 1.1 (The amplitude-damping Choi matrix).**

$$\forall (\gamma: \mathbb{R}), \operatorname{adChoi}\left(\gamma\right) = (\operatorname{let} (A: (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) := ![\begin{pmatrix}(1: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(((1: \mathbb{R})) - (\gamma)\right)\right)\end{pmatrix}, \begin{pmatrix}(0: \mathbb{C})&\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(\gamma\right)\right)\\(0: \mathbb{C})&(0: \mathbb{C})\end{pmatrix}]; (\lambda (x: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\lambda (y: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto \sum_{(k: \operatorname{Fin}\left(2\right))} ((A\left(k, x.2, x.1\right)) \cdot (\operatorname{star}\left(A\left(k, y.2, y.1\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.adChoi` (`✓ std3`).

*Citation.* Pavel Sekatski; Yelena Guryanova; Naga Bhavya Teja Kothakonda; Michalis Skotiniotis (2025). *Cloning Quantum Channels*. DOI: [10.48550/arXiv.2509.08059](https://doi.org/10.48550/arXiv.2509.08059). URL: <https://arxiv.org/abs/2509.08059v1>.

*Commentary.*

The two Kraus matrices are those of the amplitude-damping family in arxiv_v1.tex, lines 1538–1553. For a real damping parameter gamma, their matrix entries define the Choi matrix by summing each Kraus entry against the conjugate of the other. The definition accepts every real gamma; the channel interpretation uses gamma in [0,1]. On this interval the reference marginal is the identity and the trace is two.

**Definition 1.2 (Tensor powers in coordinates).**

$$\forall (J: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \forall (n: \mathbb{N}), \operatorname{choiPow}\left(J, n\right) = (\lambda (x: (\operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))) \mapsto (\lambda (y: (\operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))) \mapsto \prod_{(i: \operatorname{Fin}\left(n\right))} (J\left(x\left(i\right), y\left(i\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.choiPow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pavel Sekatski; Yelena Guryanova; Naga Bhavya Teja Kothakonda; Michalis Skotiniotis (2025). *Cloning Quantum Channels*. DOI: [10.48550/arXiv.2509.08059](https://doi.org/10.48550/arXiv.2509.08059). URL: <https://arxiv.org/abs/2509.08059v1>.

*Commentary.*

The n-fold tensor power has rows and columns indexed by assignments of one reference-output pair to each site in Fin n. An entry is the product of the corresponding single-site entries. The empty tensor power has one row, one column, and its sole entry is one.

**Definition 1.3 (Positivity and the reference marginal).**

$$\forall (n: \mathbb{N}), \forall (K: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), (\operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), \mathbb{C}\right)), (\operatorname{IsChannelChoi}\left(K\right)) \Leftrightarrow ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(K\right)) \land (\forall (r: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), \forall (r': (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), \sum_{(o: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)))} (K\left((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (r\left(i\right), o\left(i\right))), (\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (r'\left(i\right), o\left(i\right)))\right)) = \operatorname{ite}\left((r = r'), (1: \mathbb{C}), (0: \mathbb{C})\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.IsChannelChoi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pavel Sekatski; Yelena Guryanova; Naga Bhavya Teja Kothakonda; Michalis Skotiniotis (2025). *Cloning Quantum Channels*. DOI: [10.48550/arXiv.2509.08059](https://doi.org/10.48550/arXiv.2509.08059). URL: <https://arxiv.org/abs/2509.08059v1>.

*Commentary.*

A channel Choi matrix is positive semidefinite and has reference marginal equal to the identity. The sum uses the same output assignment o in both matrix indices. This condition allows an arbitrary global channel on n qubits, including channels whose Choi matrices do not factor over the sites.

**Definition 1.4 (The finite measure-and-prepare impossibility statement).**

$$\operatorname{claim} = (\forall (N: \mathbb{N}), \forall (M: \mathbb{N}), ((1: \mathbb{N}) \le M) \Rightarrow (\neg (\exists (L: \mathbb{N}), \exists (T: (\operatorname{Fin}\left(L\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), (\operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), \mathbb{C}\right))), \exists (K: (\operatorname{Fin}\left(L\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(M\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), (\operatorname{Fin}\left(M\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), \mathbb{C}\right))), (\forall (\ell: \operatorname{Fin}\left(L\right)), \operatorname{IsChannelChoi}\left(K\left(\ell\right)\right)) \land (\forall (\gamma: \mathbb{R}), (\gamma \in \operatorname{Set}.\operatorname{Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \Rightarrow ((\forall (\ell: \operatorname{Fin}\left(L\right)), (0: \mathbb{C}) \le \operatorname{Matrix}.\operatorname{trace}\left((T\left(\ell\right)) \cdot (\operatorname{choiPow}\left(\operatorname{adChoi}\left(\gamma\right), N\right))\right)) \land ((\sum_{(\ell: \operatorname{Fin}\left(L\right))} (\operatorname{Matrix}.\operatorname{trace}\left((T\left(\ell\right)) \cdot (\operatorname{choiPow}\left(\operatorname{adChoi}\left(\gamma\right), N\right))\right)) = (1: \mathbb{C})) \land (\sum_{(\ell: \operatorname{Fin}\left(L\right))} (\operatorname{smul}\left(\operatorname{Matrix}.\operatorname{trace}\left((T\left(\ell\right)) \cdot (\operatorname{choiPow}\left(\operatorname{adChoi}\left(\gamma\right), N\right))\right), K\left(\ell\right)\right)) = \operatorname{choiPow}\left(\operatorname{adChoi}\left(\gamma\right), M\right))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.claim` (`✓ std3`).

*Citation.* Pavel Sekatski; Yelena Guryanova; Naga Bhavya Teja Kothakonda; Michalis Skotiniotis (2025). *Cloning Quantum Channels*. DOI: [10.48550/arXiv.2509.08059](https://doi.org/10.48550/arXiv.2509.08059). URL: <https://arxiv.org/abs/2509.08059v1>.

*Commentary.*

The source defines measure-and-prepare cloning as a measurement followed by an outcome-dependent global channel preparation, in arxiv_v1.tex, lines 1094–1099. Its conjecture at lines 1684–1685 excludes perfect cloning at N = M. The displayed formulation ranges over every natural N, including zero, and every positive M, with a finite number L of outcomes.

Each fixed matrix T indexed by an outcome gives that outcome's probability as its trace pairing with the N-fold input Choi matrix. These complex trace values must be nonnegative and sum to one for every gamma in [0,1]. The fixed preparation matrices K are global channel Choi matrices. Their probability-weighted sum would have to equal the M-fold target Choi matrix throughout the interval. The trace representation of a finite measurement process supplies the physical interpretation of T; the statement quantifies over all matrices satisfying the displayed scalar conditions.

**Theorem 1.5 (Polynomial probabilities contradict exact cloning).**

$$\forall (N: \mathbb{N}), \forall (M: \mathbb{N}), ((1: \mathbb{N}) \le M) \Rightarrow (\neg (\exists (L: \mathbb{N}), \exists (T: (\operatorname{Fin}\left(L\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), (\operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), \mathbb{C}\right))), \exists (K: (\operatorname{Fin}\left(L\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(M\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), (\operatorname{Fin}\left(M\right) \to (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))), \mathbb{C}\right))), (\forall (\ell: \operatorname{Fin}\left(L\right)), \operatorname{IsChannelChoi}\left(K\left(\ell\right)\right)) \land (\forall (\gamma: \mathbb{R}), (\gamma \in \operatorname{Set}.\operatorname{Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \Rightarrow ((\forall (\ell: \operatorname{Fin}\left(L\right)), (0: \mathbb{C}) \le \operatorname{Matrix}.\operatorname{trace}\left((T\left(\ell\right)) \cdot (\operatorname{choiPow}\left(\operatorname{adChoi}\left(\gamma\right), N\right))\right)) \land ((\sum_{(\ell: \operatorname{Fin}\left(L\right))} (\operatorname{Matrix}.\operatorname{trace}\left((T\left(\ell\right)) \cdot (\operatorname{choiPow}\left(\operatorname{adChoi}\left(\gamma\right), N\right))\right)) = (1: \mathbb{C})) \land (\sum_{(\ell: \operatorname{Fin}\left(L\right))} (\operatorname{smul}\left(\operatorname{Matrix}.\operatorname{trace}\left((T\left(\ell\right)) \cdot (\operatorname{choiPow}\left(\operatorname{adChoi}\left(\gamma\right), N\right))\right), K\left(\ell\right)\right)) = \operatorname{choiPow}\left(\operatorname{adChoi}\left(\gamma\right), M\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.result` (`✓ std3`). ∎

*Resolves.* `Problems/sekatski-guryanova-kothakonda-skotiniotis-2025-amplitude-damping-measure-prepare-cloning` (proved) by `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sekatski-guryanova-kothakonda-skotiniotis-2025-amplitude-damping-measure-prepare-cloning","declaration_gid":"D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pavel Sekatski; Yelena Guryanova; Naga Bhavya Teja Kothakonda; Michalis Skotiniotis (2025). *Cloning Quantum Channels*. DOI: [10.48550/arXiv.2509.08059](https://doi.org/10.48550/arXiv.2509.08059). URL: <https://arxiv.org/abs/2509.08059v1>.

*Commentary.*

Put gamma = 1 − s² with s in [0,1]. In the ordered basis (00,01,10,11), the Choi matrix is w times its conjugate transpose plus Complex.ofReal(1 − s²) times u times its conjugate transpose, where w = (1,0,0,Complex.ofReal(s)) and u = (0,0,1,0). Consequently every entry is a polynomial in s. Summing over the output index gives the identity reference marginal. The (00,11) entry is Complex.ofReal(s), so two such Choi matrices are equal only when their parameters s are equal.

For a preparation on n + 1 qubits, fix every reference site except the first to zero and trace out the other n output sites. The resulting matrix is a qubit channel Choi matrix: positivity follows by restricting a positive semidefinite matrix to a submatrix and taking a partial trace, while its reference marginal follows by summing the original channel marginal over the remaining output assignments. Applied to a tensor power of a matrix J, this operation gives J multiplied by the n-th power of the sum of J((0,o),(0,o)) over o in Fin 2. For the amplitude-damping matrix that sum is one, so the operation gives its single-qubit Choi matrix. Finite sums and scalar multiplication commute with this operation.

Next suppose that the single-qubit Choi matrix at s is a sum of nonnegative weights q times channel Choi matrices R. Choose an outcome ell with nonzero weight. Every vector annihilated by the sum is annihilated by R at ell: the corresponding quadratic forms are nonnegative, their weighted sum is zero, and positive semidefiniteness turns a zero quadratic form into a zero matrix-vector product. Apply this first to the basis vector at 01, then to Complex.ofReal(s) times the basis vector at 00 minus the basis vector at 11. The 01 column vanishes, and the 11 column is Complex.ofReal(s) times the 00 column. Hermitian symmetry gives the corresponding row relations.

The channel marginal now fixes the remaining entries of R at ell. The (00,00) entry is one and the (00,10) entry is zero; Hermitian symmetry makes the (10,00) entry zero. The (11,00) entry is Complex.ofReal(s), the (11,10) entry is zero, and the (10,10) entry is one minus Complex.ofReal(s) squared. Together with the column and row relations these determine every entry and give precisely the amplitude-damping Choi matrix at s. Thus any summand with nonzero weight must be that matrix. This argument includes both endpoints of the interval.

For a fixed input matrix T, form a complex polynomial by summing over row and column assignments x and y: each summand is the constant coefficient T(x,y) times the product, over all input sites i, of the polynomial entry at (y(i),x(i)). Evaluation at Complex.ofReal(s) is exactly the trace pairing of T with the N-fold Choi matrix at gamma = 1 − s². If a fixed matrix R must equal the amplitude-damping matrix whenever this polynomial is nonzero, then the polynomial is identically zero. Indeed, either it vanishes everywhere on [0,1], or a point t where it is nonzero forces every other nonzero point to equal t, by the (00,11) entry. In either case it has infinitely many distinct complex roots, since the real interval remains infinite after removing one point and the embedding into the complex field is injective.

Finally assume a finite ensemble satisfying the claim's equalities and write M = n + 1. For each outcome ell, take its trace polynomial and the fixed qubit channel obtained from K at ell by the preceding reduction. At every s in [0,1], the ensemble equality reduces to a nonnegative sum equal to the single-qubit amplitude-damping matrix. A nonzero polynomial value is a nonzero weight, so the summand argument forces that fixed qubit channel to equal the amplitude-damping matrix at s. The polynomial therefore vanishes identically. Evaluating it at s = 0 makes every outcome probability at gamma = 1 zero, contradicting their sum being one. The contradiction holds for every N and every positive M.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.IsChannelChoi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.adChoi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.choiPow`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.result`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
