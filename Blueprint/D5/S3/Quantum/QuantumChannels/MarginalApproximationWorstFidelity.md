# The sharp fidelity bound for marginal process approximations

## Abstract

The product of single-site process marginals has squared fidelity at least four to the minus N, with equality for cyclic wire permutations on at least two qubits.

**Definition 1.1 (Completely positive trace-preserving process matrices).**

$$\forall (N: \mathbb{N}), (\forall (chi: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), \mathbb{C}\right)), ((\operatorname{IsProcessCPTP}\left(chi\right)) \Leftrightarrow ((\operatorname{Matrix.PosSemidef}\left(chi\right)) \land (\sum_{a: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)} (\sum_{b: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)} ((chi\left(a, b\right)) \cdot ((\operatorname{tensorOp}\left(\lambda (k: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{sigma}\left(b\left(k\right)\right))\right)) \cdot (\operatorname{tensorOp}\left(\lambda (k: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{sigma}\left(a\left(k\right)\right))\right))))) = (1: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.IsProcessCPTP` (`✓ std3`).

*Citation.* James Sud; Jeffrey Marshall; Zhihui Wang; Eleanor Rieffel; Filip A. Wudarski (2022). *Dual-map framework for noise characterization of quantum computers*. DOI: [10.1103/PhysRevA.106.012606](https://doi.org/10.1103/PhysRevA.106.012606). URL: <https://arxiv.org/abs/2112.04414v1>.

*Commentary.*

A Pauli string a assigns one of the four Pauli matrices to each qubit. The operator tensorOp assembles their tensor product. The matrix χ, written chi in the formulas, is completely positive and trace preserving when it is positive semidefinite and the sum of χ(a,b) times the ordered Pauli products P_b P_a is the identity on the qubits. This is the process representation of main.tex lines 234–249, extended to Pauli strings. The Pauli basis is unnormalized; taking the trace of this identity gives trace χ equal to one.

**Definition 1.2 (The partial trace onto one process coordinate).**

$$\forall (N: \mathbb{N}), (\forall (chi: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), \mathbb{C}\right)), (\forall (k: \operatorname{Fin}\left(N\right)), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), (\operatorname{marginal}\left(chi, k, i, j\right) = \sum_{y: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)} (\operatorname{ite}\left(y\left(k\right) = i, chi\left(y, \operatorname{Function.update}\left(y, k, j\right)\right), (0: \mathbb{C})\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.marginal` (`✓ std3`).

*Citation.* James Sud; Jeffrey Marshall; Zhihui Wang; Eleanor Rieffel; Filip A. Wudarski (2022). *Dual-map framework for noise characterization of quantum computers*. DOI: [10.1103/PhysRevA.106.012606](https://doi.org/10.1103/PhysRevA.106.012606). URL: <https://arxiv.org/abs/2112.04414v1>.

*Commentary.*

For a site k, the entry (i,j) of marginal χ k sums the entries whose row has value i at k and whose column agrees with that row away from k and has value j at k. Function.update changes precisely that coordinate. This is the single-site partial trace used in MATEN, main.tex lines 226–232, and for process matrices in lines 284–287. Each retained coordinate has dimension four. The definition applies to every complex matrix, without a positivity or normalization assumption.

**Definition 1.3 (Pauli coefficients of the cyclic wire permutation).**

$$\forall (N: \mathbb{N}), (\forall (a: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), ((\operatorname{shiftCoeff}\left(N, a\right): \mathbb{C}) = (\operatorname{Inv.inv}\left(((2: \mathbb{C}))^{N}\right)) \cdot (\operatorname{Matrix.trace}\left((\operatorname{tensorOp}\left(\lambda (k: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{sigma}\left(a\left(k\right)\right))\right)) \cdot (\operatorname{Matrix.transpose}\left(\operatorname{qubitPermutation}\left(\operatorname{finRotate}\left(N\right)\right)\right))\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.shiftCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* James Sud; Jeffrey Marshall; Zhihui Wang; Eleanor Rieffel; Filip A. Wudarski (2022). *Dual-map framework for noise characterization of quantum computers*. DOI: [10.1103/PhysRevA.106.012606](https://doi.org/10.1103/PhysRevA.106.012606). URL: <https://arxiv.org/abs/2112.04414v1>.

*Commentary.*

The permutation finRotate N cyclically rotates the qubit positions. The coefficient shiftCoeff N a is the trace pairing of the Pauli string a with the transpose of qubitPermutation (finRotate N), divided by two to the power N. The transpose fixes the direction of the wire permutation in this convention. Both the power of two and its inverse are complex numbers. These coefficients specify the pure process matrix used to attain the bound.

**Theorem 1.4 (Tensor products of diagonal matrices).**

$$\forall (iota: \operatorname{Type}\left(\right)), ((\operatorname{Fintype}\left(iota\right)) \to ((\operatorname{DecidableEq}\left(iota\right)) \to (\forall (d: iota \to \left(\operatorname{Fin}\left(4\right) \to \mathbb{C}\right)), (\operatorname{productMap}\left(\operatorname{Function.const}\left(iota, \operatorname{Fin}\left(4\right)\right), \lambda (k: iota) \mapsto (\operatorname{Matrix.diagonal}\left(d\left(k\right)\right))\right) = \operatorname{Matrix.diagonal}\left(\lambda (a: iota \to \operatorname{Fin}\left(4\right)) \mapsto (\prod_{(k: iota)} (d\left(k, a\left(k\right)\right)))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.productMatrix_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James Sud; Jeffrey Marshall; Zhihui Wang; Eleanor Rieffel; Filip A. Wudarski (2022). *Dual-map framework for noise characterization of quantum computers*. DOI: [10.1103/PhysRevA.106.012606](https://doi.org/10.1103/PhysRevA.106.012606). URL: <https://arxiv.org/abs/2112.04414v1>.

*Commentary.*

For any finite index type, the tensor product of four-dimensional diagonal matrices is diagonal, and its entry at a word is the product of the selected local entries.

**Definition 1.5 (The universal lower bound and cyclic-shift attainment).**

$$(\operatorname{claim}) \Leftrightarrow ((\forall (N: \mathbb{N}), (((1: \mathbb{N}) \le N) \Rightarrow (\forall (chi: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), \mathbb{C}\right)), ((\operatorname{IsProcessCPTP}\left(chi\right)) \Rightarrow (\frac{(1: \mathbb{R})}{((4: \mathbb{R}))^{N}} \le \operatorname{sqFidelity}\left(chi, \operatorname{productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(4\right)\right), \operatorname{marginal}\left(chi\right)\right)\right)))))) \land (\forall (N: \mathbb{N}), (((2: \mathbb{N}) \le N) \Rightarrow ((\sum_{a: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)} ((\operatorname{shiftCoeff}\left(N, a\right)) \cdot (\operatorname{tensorOp}\left(\lambda (k: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{sigma}\left(a\left(k\right)\right))\right))) = \operatorname{Matrix.transpose}\left(\operatorname{qubitPermutation}\left(\operatorname{finRotate}\left(N\right)\right)\right)) \land ((\operatorname{IsProcessCPTP}\left(\operatorname{rankOneDensity}\left(\operatorname{shiftCoeff}\left(N\right)\right)\right)) \land ((\forall (k: \operatorname{Fin}\left(N\right)), (\operatorname{marginal}\left(\operatorname{rankOneDensity}\left(\operatorname{shiftCoeff}\left(N\right)\right), k\right) = (\frac{(1: \mathbb{C})}{(4: \mathbb{C})}) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right))))) \land (\operatorname{sqFidelity}\left(\operatorname{rankOneDensity}\left(\operatorname{shiftCoeff}\left(N\right)\right), \operatorname{productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(4\right)\right), \operatorname{marginal}\left(\operatorname{rankOneDensity}\left(\operatorname{shiftCoeff}\left(N\right)\right)\right)\right)\right) = \frac{(1: \mathbb{R})}{((4: \mathbb{R}))^{N}})))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* James Sud; Jeffrey Marshall; Zhihui Wang; Eleanor Rieffel; Filip A. Wudarski (2022). *Dual-map framework for noise characterization of quantum computers*. DOI: [10.1103/PhysRevA.106.012606](https://doi.org/10.1103/PhysRevA.106.012606). URL: <https://arxiv.org/abs/2112.04414v1>.

*Commentary.*

The source conjectures the worst-case fidelity value in main.tex lines 284–290 and computes four to the minus N for a pure process with maximally mixed marginals in lines 292–296. The first conjunct asserts this lower bound for every CPTP process matrix on every positive number N of qubits.

The second conjunct specifies an attaining family: for every N at least two, the Pauli expansion with coefficients shiftCoeff N equals the transposed cyclic wire permutation, its rank-one process matrix is CPTP, every marginal is one quarter of the four-dimensional identity, and its squared fidelity with the product of its marginals is exactly four to the minus N. The cyclic-shift construction supplies this attainment assertion. Here productMap forms the tensor product of its matrix arguments, rankOneDensity v has entries v(a) times the complex conjugate of v(b), and sqFidelity is the square of the real part of the trace of the positive square root of √ρ σ √ρ. Its values and the bound are real.

**Theorem 1.6 (The lower bound is sharp).**

$$(\forall (N: \mathbb{N}), (((1: \mathbb{N}) \le N) \Rightarrow (\forall (chi: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)), \mathbb{C}\right)), ((\operatorname{IsProcessCPTP}\left(chi\right)) \Rightarrow (\frac{(1: \mathbb{R})}{((4: \mathbb{R}))^{N}} \le \operatorname{sqFidelity}\left(chi, \operatorname{productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(4\right)\right), \operatorname{marginal}\left(chi\right)\right)\right)))))) \land (\forall (N: \mathbb{N}), (((2: \mathbb{N}) \le N) \Rightarrow ((\sum_{a: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right)} ((\operatorname{shiftCoeff}\left(N, a\right)) \cdot (\operatorname{tensorOp}\left(\lambda (k: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{sigma}\left(a\left(k\right)\right))\right))) = \operatorname{Matrix.transpose}\left(\operatorname{qubitPermutation}\left(\operatorname{finRotate}\left(N\right)\right)\right)) \land ((\operatorname{IsProcessCPTP}\left(\operatorname{rankOneDensity}\left(\operatorname{shiftCoeff}\left(N\right)\right)\right)) \land ((\forall (k: \operatorname{Fin}\left(N\right)), (\operatorname{marginal}\left(\operatorname{rankOneDensity}\left(\operatorname{shiftCoeff}\left(N\right)\right), k\right) = (\frac{(1: \mathbb{C})}{(4: \mathbb{C})}) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right))))) \land (\operatorname{sqFidelity}\left(\operatorname{rankOneDensity}\left(\operatorname{shiftCoeff}\left(N\right)\right), \operatorname{productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(4\right)\right), \operatorname{marginal}\left(\operatorname{rankOneDensity}\left(\operatorname{shiftCoeff}\left(N\right)\right)\right)\right)\right) = \frac{(1: \mathbb{R})}{((4: \mathbb{R}))^{N}}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.result` (`✓ std3`). ∎

*Resolves.* `Problems/sud-marshall-wang-rieffel-wudarski-2022-maten-worst-case-fidelity` (proved) by `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sud-marshall-wang-rieffel-wudarski-2022-maten-worst-case-fidelity","declaration_gid":"D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* James Sud; Jeffrey Marshall; Zhihui Wang; Eleanor Rieffel; Filip A. Wudarski (2022). *Dual-map framework for noise characterization of quantum computers*. DOI: [10.1103/PhysRevA.106.012606](https://doi.org/10.1103/PhysRevA.106.012606). URL: <https://arxiv.org/abs/2112.04414v1>.

*Commentary.*

First consider a probability distribution p on the Pauli strings and write q(k,j) for its marginal at site k. Weighted arithmetic–geometric mean applied with weights q(k,j) and values q(k,j)⁻¹ bounds the reciprocal of the product of q(k,j) to the powers q(k,j) by four. Zero weights contribute zero to the arithmetic sum and one to the geometric product. Consequently each such geometric product is at least one quarter. Factoring the product over strings by their k-th coordinates and applying weighted arithmetic–geometric mean again, now with weights p(x) and values the product of q(k,x(k)) over k, gives an overlap of at least four to the minus N.

For a CPTP process χ, tracing its trace-preservation identity and using Pauli trace orthogonality gives trace χ equal to one. Splitting a string into its k-th coordinate and the remaining coordinates identifies marginal χ k with a partial trace and proves its positivity. The product of these marginals is positive: its entries are products of the marginal entries, so induction over sites expresses it as successive Hadamard products of positive matrices pulled back along coordinate maps. Denote this product by χ_MA.

Tensor products preserve matrix multiplication, adjoints, diagonal matrices and identities, hence products of unitary matrices are unitary. Splitting off site k also expresses a product unitary as a Kronecker product; the partial trace therefore transforms by conjugation with its k-th factor. Choose a unitary U(k) diagonalizing each marginal, let V be their tensor product, and put Ψ = Vᴴ χ V. Positivity and trace one make p(x) = Re Ψ(x,x) a probability distribution. The marginals of p are exactly the eigenvalues of the corresponding marginals of χ. In this basis the product of the marginals is diagonal, with diagonal entries the products of those eigenvalues. Cyclic invariance of trace then identifies the classical overlap with Re tr(χ χ_MA), proving the same lower bound for this trace.

For positive matrices ρ and σ, put A = √ρ σ √ρ and S = √A. These matrices are positive. Cyclic invariance gives tr A = tr(ρσ), and S² = A. For a positive matrix the real trace of its square is at most the square of its real trace. Thus Re tr(ρσ) is at most (Re tr S)², which is sqFidelity ρ σ. Applying this inequality with ρ = χ and σ = χ_MA completes the universal lower bound.

For attainment, Pauli trace orthogonality expands the transposed cyclic wire permutation with precisely the coefficients shiftCoeff N. It is a permutation matrix and hence unitary. Hermiticity of the Pauli strings turns the conjugated coefficient sum into its adjoint. Multiplying the two expansions proves trace preservation of the positive rank-one matrix χ = rankOneDensity (shiftCoeff N).

To compute its k-th marginal, expand the trace pairing as a sum over qubit strings x of the product, over sites l, of the entry of σ indexed by a(l) in row x(l) and column x(finRotate N l). Split a into its value i at k and a string z on the other N−1 sites. In the product of this sum and its complex conjugate, summing each coordinate of z uses Pauli completeness: the sum of σ_a(u,v) times the conjugate of σ_a(u′,v′) is two when both pairs agree and zero otherwise. The resulting constraints identify x(l) with y(l) and the rotated coordinates for every l other than k. Since N is at least two, the predecessor of k differs from k, so these constraints also identify x(k) with y(k). Only x = y remains, with factor two to the power N−1. The two coordinates k and finRotate N k are distinct. Summing them uses Pauli orthogonality, giving two for i = j and zero otherwise; the remaining N−2 coordinates contribute two to the power N−2. The full contraction is therefore (2ᴺ)² times one quarter of the Kronecker delta. Multiplication by the squared coefficient normalization gives marginal χ k = I₄/4.

Finally let c = 1/4ᴺ as a real number. The product of the marginals is (c : ℂ) times the identity. Trace one normalizes the coefficient vector, so its rank-one density χ satisfies χ² = χ and √χ = χ. The positive square root of (c : ℂ)χ is (√c : ℂ)χ. Substituting these identities into sqFidelity, taking the trace and using trace χ = 1 gives (√c)² = c. This supplies all four attainment assertions for every N at least two.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.IsProcessCPTP`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.marginal`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.productMatrix_diagonal`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.shiftCoeff`
- Dependency: [D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank](../Codes/StabilizerGenuineEntanglementCommutationRank.md)
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall](../Entanglement/AbsoluteSeparability/GurvitsBarnumBall.md)
- Dependency: [D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation](../Information/LiTheilHarrowChuangPurifyCloneRefutation.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
- Dependency: [D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness](../../QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.md)
