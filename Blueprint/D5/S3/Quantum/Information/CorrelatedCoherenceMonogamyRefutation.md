# Correlated coherence need not be monogamous for pure three-qubit states

## Abstract

A pure state of three qubits has a negative l1 correlated-coherence monogamy difference.

Work in the computational product basis. Fin(n) consists of the indices 0 through n − 1, and a basis index of three qubits is a function from Fin(3) to Fin(2). Qubits 0, 1 and 2 are A, B and C, respectively. Complex absolute values are moduli. The anonymous brackets Fintype n and DecidableEq n supply a finite enumeration and decidable equality for the matrix indices.

**Definition 1.1 (Coherence in a fixed basis).**

$$\forall (n: \operatorname{Type}), ([\operatorname{Fintype}\left(n\right)], ([\operatorname{DecidableEq}\left(n\right)], (\forall (\rho: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), (\operatorname{l1Coherence}\left(\rho\right) = \sum_{(i: n)} (\sum_{(j: n), i \ne j} (\left|\rho\left(i, j\right)\right|))))))$$

*Formalization.* `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.l1Coherence` (`✓ std3`).

*Citation.* Marcos L. W. Basso; Jonas Maziero (2020). *Monogamy and trade-off relations for correlated quantum coherence*. DOI: [10.1088/1402-4896/abafcb](https://doi.org/10.1088/1402-4896/abafcb). URL: <https://arxiv.org/abs/2006.14037v2>.

*Commentary.*

The l1 coherence is the sum of the moduli of all off-diagonal matrix entries. Each ordered pair of distinct indices is counted once. The expression is defined for every complex square matrix, without positivity or trace assumptions, and is the l1-norm coherence used in Section II.

**Definition 1.2 (The seven-term monogamy difference).**

$$\forall (\psi: ((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), (\operatorname{monogamyGap}\left(\psi\right) = \operatorname{l1Coherence}\left(\left(\operatorname{Tr}_{\operatorname{Fin}\left(3\right) \setminus \left\{0, 1, 2\right\}}\right)\left((\psi \psi^{*})\right)\right) + \operatorname{l1Coherence}\left(\left(\operatorname{Tr}_{\operatorname{Fin}\left(3\right) \setminus \left\{0\right\}}\right)\left((\psi \psi^{*})\right)\right) + \operatorname{l1Coherence}\left(\left(\operatorname{Tr}_{\operatorname{Fin}\left(3\right) \setminus \left\{1\right\}}\right)\left((\psi \psi^{*})\right)\right) + \operatorname{l1Coherence}\left(\left(\operatorname{Tr}_{\operatorname{Fin}\left(3\right) \setminus \left\{2\right\}}\right)\left((\psi \psi^{*})\right)\right) - (\operatorname{l1Coherence}\left(\left(\operatorname{Tr}_{\operatorname{Fin}\left(3\right) \setminus \left\{0, 1\right\}}\right)\left((\psi \psi^{*})\right)\right) + \operatorname{l1Coherence}\left(\left(\operatorname{Tr}_{\operatorname{Fin}\left(3\right) \setminus \left\{0, 2\right\}}\right)\left((\psi \psi^{*})\right)\right) + \operatorname{l1Coherence}\left(\left(\operatorname{Tr}_{\operatorname{Fin}\left(3\right) \setminus \left\{1, 2\right\}}\right)\left((\psi \psi^{*})\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.monogamyGap` (`✓ std3`).

*Citation.* Marcos L. W. Basso; Jonas Maziero (2020). *Monogamy and trade-off relations for correlated quantum coherence*. DOI: [10.1088/1402-4896/abafcb](https://doi.org/10.1088/1402-4896/abafcb). URL: <https://arxiv.org/abs/2006.14037v2>.

*Commentary.*

For a vector ψ and a set S of qubits, the partial trace over Fin(3) outside S of ψ ψ* is its reduced matrix on S. The star on the column vector denotes conjugate transpose; equivalently, the pure matrix has entry ψ(x) times the complex conjugate of ψ(y). The retained basis is the set of functions from S to Fin(2). A trace over the empty set retains the full pure matrix. Write M for monogamyGap. Its four positive terms are the full coherence and the three single-qubit coherences; its three subtracted terms are the two-qubit coherences. This is Eq. (33), the difference between the correlated coherence across A versus BC and the sum of those across AB and AC. The formula itself does not require ψ to have norm one.

**Definition 1.3 (The conjecture for three qubits).**

$$\operatorname{claim} \Leftrightarrow (\forall (\psi: ((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), ((\sum_{(x: (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)))} (\left|\psi\left(x\right)\right|^{2}) = 1) \Rightarrow (0 \le \operatorname{monogamyGap}\left(\psi\right))))$$

*Formalization.* `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.claim` (`✓ std3`).

*Citation.* Marcos L. W. Basso; Jonas Maziero (2020). *Monogamy and trade-off relations for correlated quantum coherence*. DOI: [10.1088/1402-4896/abafcb](https://doi.org/10.1088/1402-4896/abafcb). URL: <https://arxiv.org/abs/2006.14037v2>.

*Commentary.*

Section III.A conjectures monogamy for every tripartite pure state. Here it is restricted to three qubits: every complex vector whose squared moduli sum to one has a nonnegative monogamy difference. All reduced matrices use the same computational product basis. The sufficient conditions (22)–(24) are not assumed in this conjecture.

**Theorem 1.4 (A pure three-qubit state with a negative difference).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/basso-maziero-2020-correlated-coherence-monogamy-refutation` (refuted) by `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"basso-maziero-2020-correlated-coherence-monogamy-refutation","declaration_gid":"D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marcos L. W. Basso; Jonas Maziero (2020). *Monogamy and trade-off relations for correlated quantum coherence*. DOI: [10.1088/1402-4896/abafcb](https://doi.org/10.1088/1402-4896/abafcb). URL: <https://arxiv.org/abs/2006.14037v2>.

*Commentary.*

Take ψ = (−16, 1, 128, −16, −128, −16, 1, −128)/√49922, in the order |000⟩, |001⟩, |010⟩, |011⟩, |100⟩, |101⟩, |110⟩, |111⟩. The first bit is qubit 0. The sum of the squares of the eight integer amplitudes is 49922, so ψ is a unit vector.

For the full state and the marginals A, B, C, AB, AC and BC, respectively, the l1 coherences are 138434/49922, 8416/49922, 288/49922, 288/49922, 48928/49922, 48928/49922 and 50336/49922. Each reduced entry is the sum, over a common configuration of the discarded qubits, of the two corresponding integer amplitudes multiplied together and divided by 49922. Summing the moduli of its off-diagonal entries gives these seven values.

The alternating sum is M(ψ) = −766/49922 = −383/24961, which is negative. Thus a pure three-qubit state contradicts claim and hence the conjecture for all tripartite pure states. This does not contradict Theorem 4: its trade-off hypothesis is not assumed by the conjecture.

## References

- Truth anchor: `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.l1Coherence`
- Truth anchor: `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.monogamyGap`
- Truth anchor: `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum](../Entanglement/PurityTimeReversalOverlapMinimum.md)
