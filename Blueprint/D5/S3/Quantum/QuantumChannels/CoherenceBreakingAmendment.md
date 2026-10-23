# Amending coherence-breaking iterates with one unitary

## Abstract

Every incoherent trace-preserving Kraus channel of finite coherence-breaking index at least two admits one unitary conjugation repeated between its successive applications.

All matrices are complex and use the fixed incoherent basis indexed by Fin d. The superscript H denotes conjugate transpose, tr is the matrix trace, and a superscript [m] denotes m-fold function iteration. Subtraction in an iteration count is natural-number subtraction.

**Definition 1.1 (Incoherent Kraus operators).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsIncoherentKraus}\left(K\right) \Leftrightarrow (\forall s \in \operatorname{Fin}\left(r\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; \exists k \in \operatorname{Fin}\left(d\right),\; \forall i \in \operatorname{Fin}\left(d\right),\; (i \ne k) \Rightarrow (K\left(s, i, j\right) = 0))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.IsIncoherentKraus` (`✓ std3`).

*Citation.* Long-Mei Yang; Bin Chen; Tao Li; Shao-Ming Fei; Zhi-Xi Wang (2018). *Amending Coherence-Breaking Channels via Unitary Operations*. DOI: [10.1007/s10773-018-3890-4](https://doi.org/10.1007/s10773-018-3890-4). URL: <https://arxiv.org/abs/1810.09642v1>.

*Commentary.*

Section 2 calls a Kraus representation incoherent when each individual Kraus operator preserves incoherence on every incoherent input. Equivalently, each column of every Kraus operator has support in at most one row: each basis vector is sent to a scalar multiple of a basis vector. This predicate imposes no trace-preservation condition.

**Definition 1.2 (Coherence-breaking maps).**

$$\forall d \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsCoherenceBreaking}\left(Phi\right) \Leftrightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{tr}\left(rho\right) = 1) \Rightarrow (\forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; (i \ne j) \Rightarrow (Phi\left(rho\right)\left(i, j\right) = 0))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.IsCoherenceBreaking` (`✓ std3`).

*Citation.* Long-Mei Yang; Bin Chen; Tao Li; Shao-Ming Fei; Zhi-Xi Wang (2018). *Amending Coherence-Breaking Channels via Unitary Operations*. DOI: [10.1007/s10773-018-3890-4](https://doi.org/10.1007/s10773-018-3890-4). URL: <https://arxiv.org/abs/1810.09642v1>.

*Commentary.*

The output of every positive semidefinite matrix of trace one has zero entries away from the diagonal. This is the coherence-breaking condition of Section 2. The predicate itself is defined for every matrix-valued function; in the conjecture it is applied to quantum channels and their composites.

**Definition 1.3 (The same conjugation between successive channels).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall n \in \mathbb{N},\; \operatorname{amended}\left(K, U, n\right) = (\operatorname{krausApply}\left(K\right)) \circ (((\operatorname{LinearMap.mulLeftRight}\left(\mathbb{C}, (U, (U)^{H})\right)) \circ (\operatorname{krausApply}\left(K\right)))^{[n - 1]})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.amended` (`✓ std3`).

*Citation.* Long-Mei Yang; Bin Chen; Tao Li; Shao-Ming Fei; Zhi-Xi Wang (2018). *Amending Coherence-Breaking Channels via Unitary Operations*. DOI: [10.1007/s10773-018-3890-4](https://doi.org/10.1007/s10773-018-3890-4). URL: <https://arxiv.org/abs/1810.09642v1>.

*Commentary.*

The composition in Section 5 has n copies of the channel and n minus one copies of the same conjugation when n is at least one. The definition also includes n = 0 through natural-number subtraction. For the finite dimensions used here, the Kraus action and matrix conjugation are given by the following formulas. No normalization of K or unitarity of U is needed to define these maps.

$$
\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{krausApply}\left(K, X\right) = \sum_{(s:\operatorname{Fin}\left(r\right))} (((K\left(s\right)) \cdot (X)) \cdot ((K\left(s\right))^{H}))
$$

$$
\forall d \in \mathbb{N},\; \forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{LinearMap.mulLeftRight}\left(\mathbb{C}, (U, (U)^{H})\right)\left(X\right) = ((U) \cdot (X)) \cdot ((U)^{H})
$$

**Definition 1.4 (The finite-index amendment conjecture).**

$$\operatorname{claim} \Leftrightarrow (\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{IsKrausChannel}\left(K\right)) \Rightarrow ((\operatorname{IsIncoherentKraus}\left(K\right)) \Rightarrow (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow ((\operatorname{IsCoherenceBreaking}\left((\operatorname{krausApply}\left(K\right))^{[n]}\right)) \Rightarrow ((\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow ((k < n) \Rightarrow (\neg (\operatorname{IsCoherenceBreaking}\left((\operatorname{krausApply}\left(K\right))^{[k]}\right))))) \Rightarrow (\exists U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land (\neg (\operatorname{IsCoherenceBreaking}\left(\operatorname{amended}\left(K, U, n\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.claim` (`✓ std3`).

*Citation.* Long-Mei Yang; Bin Chen; Tao Li; Shao-Ming Fei; Zhi-Xi Wang (2018). *Amending Coherence-Breaking Channels via Unitary Operations*. DOI: [10.1007/s10773-018-3890-4](https://doi.org/10.1007/s10773-018-3890-4). URL: <https://arxiv.org/abs/1810.09642v1>.

*Commentary.*

Section 5 conjectures amendment for incoherent trace-preserving Kraus channels with coherence-breaking index n at least two. The n-th iterate is coherence-breaking, and none of the iterates with 1 <= k < n is coherence-breaking, as in the minimum defining the index in Section 2, Eq. (1). There is one unitary U whose conjugation, inserted in every intervening slot, makes the composite fail to be coherence-breaking. Trace preservation is the Kraus completeness equality below.

$$
\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsKrausChannel}\left(K\right) \Leftrightarrow (\sum_{(s:\operatorname{Fin}\left(r\right))} (((K\left(s\right))^{H}) \cdot (K\left(s\right))) = 1)
$$

**Theorem 1.5 (A permutation with fourth-root phases amends the channel).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.result` (`✓ std3`). ∎

*Resolves.* `Problems/yang-chen-li-fei-wang-2018-coherence-breaking-amendment` (proved) by `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yang-chen-li-fei-wang-2018-coherence-breaking-amendment","declaration_gid":"D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Long-Mei Yang; Bin Chen; Tao Li; Shao-Ming Fei; Zhi-Xi Wang (2018). *Amending Coherence-Breaking Channels via Unitary Operations*. DOI: [10.1007/s10773-018-3890-4](https://doi.org/10.1007/s10773-018-3890-4). URL: <https://arxiv.org/abs/1810.09642v1>.

*Commentary.*

Write Phi for the Kraus channel, let P erase the diagonal entries of a matrix, and put T = P composed with Phi. Incoherence implies that T kills every diagonal matrix, so T = T composed with P. Choose a permutation sigma and phases omega(c) in {1,i,-1,-i}; the unitary U sends the c-th basis vector to omega(c) times the sigma(c)-th basis vector. Its conjugation Lambda commutes with P. The off-diagonal part of the amended composite is (T Lambda)^(n-1) T.

If that composite were coherence-breaking, this linear map would vanish on every density matrix. Density matrices span the Hermitian matrices over the reals, and every complex matrix is a Hermitian matrix plus i times a Hermitian matrix, so the map would vanish identically. Multiplication on the right by Lambda then gives (T Lambda)^n = 0. Nilpotency forces Tr(T Lambda) = 0, where Tr is the trace of a linear endomorphism of the matrix space.

Minimality of n >= 2 implies that Phi itself is not coherence-breaking, hence T is nonzero. Since T kills diagonal matrices and has only off-diagonal outputs, there are a != b and k != l for which the (k,l) entry of T(E_ab) is nonzero. Choose sigma with sigma(k) = a and sigma(l) = b. The weighted sum of Tr(T Lambda) over all fourth-root phase assignments, with weight conjugate(omega(k)) omega(l), is 4^d times that nonzero entry. Orthogonality of the phase characters therefore supplies a unitary for which Tr(T Lambda) is nonzero. This contradicts the trace forced by coherence-breaking and proves the conjecture.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.IsCoherenceBreaking`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.IsIncoherentKraus`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.amended`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments](../Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.md)
- Dependency: [D5/S3/Quantum/Matrix/MonomialDiagonalPreserving](../Matrix/MonomialDiagonalPreserving.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation](OutputMaximalCoherenceTensorizationRefutation.md)
