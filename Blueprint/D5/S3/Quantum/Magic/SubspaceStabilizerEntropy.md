# Subspace average linear stabilizer entropy and fourth-moment cycle traces

## Abstract

Single-qudit phased Weyl displacement operators, fourfold symmetric Haar moment projectors, cycle-trace Hermitian fourth-moment polynomials, odd- and even-dimension intrinsic closed forms, rank-one linear stabilizer entropy, and subspace isometry invariance.

**Definition 1.1 (Displacement phase factor).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.tau`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.tau` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a natural dimension d, tau(d) = -exp(pi * i / d) is the half-angle phase factor multiplying unphased shift-clock Weyl words.

**Definition 1.2 (Phased Weyl displacement operators).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.paperDisplacement`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.paperDisplacement` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension d and phase-space label a = (a_1, a_2) in (Z / dZ)^2, paperDisplacement(d, a) = tau(d)^{val(a_1) val(a_2)} X^{val(a_1)} Z^{val(a_2)} acts on C^d in the computational basis indexed by Z / dZ.

**Definition 1.3 (Integer-indexed phased Weyl operators).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intPaperDisplacement`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intPaperDisplacement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension d and integer coordinates x, y in Z, intPaperDisplacement(d, x, y) multiplies the modular shift-clock displacement word at (x mod d, y mod d) by the integer power tau(d)^{x y}.

**Definition 1.4 (Pure-state linear stabilizer entropy).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.linearStabilizerEntropy`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.linearStabilizerEntropy` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a vector psi in C^d, linearStabilizerEntropy(psi) = 1 - d^{-1} sum_{a in (Z / dZ)^2} |<psi | D_a | psi>|^4 measures the fourth-moment Weyl nonstabilizerness of psi.

**Definition 1.5 (Fourfold tensor power of a matrix).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.power4`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.power4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a rectangular matrix V : C^Q -> C^P, power4(V) is the fourfold tensor product V^{otimes 4} acting on four-tuples of indices.

**Definition 1.6 (Alternating fourfold tensor product).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.alt`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.alt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a square matrix A on H, alt(A) is the fourfold tensor product A otimes A^* otimes A otimes A^*.

**Definition 1.7 (Four-factor tensor permutation operators).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.T`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.T` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For an index type H and a permutation sigma in S_4, T(H, sigma) permutes the four factors of (C^H)^{otimes 4} by reindexing four-tuples along sigma^{-1}.

**Definition 1.8 (Symmetric four-tensor projector).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.symProjector4`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.symProjector4` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a finite index type H, symProjector4(H) = (1 / 24) sum_{sigma in S_4} T(H, sigma) is the orthogonal projector onto the symmetric subspace Sym^4(C^H).

**Definition 1.9 (Normalized Haar fourth-moment state).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.A4`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.A4` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a finite index type H, A4(H) = binom(|H| + 3, 4)^{-1} symProjector4(H) is the normalized projector onto Sym^4(C^H), equal to the Haar fourth-moment density operator of pure states on C^H.

**Definition 1.10 (Fourth-moment Weyl operator).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.Q`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.Q` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension d, Q(d) = d^{-2} sum_{a in (Z / dZ)^2} alt(paperDisplacement(d, a)) averages the alternating fourfold Weyl tensor products over phase space.

**Definition 1.11 (Compressed single-label Haar fourth moment).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.labelFourthMoment`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.labelFourthMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For an isometric frame E : C^S -> C^d and phase-space label a in (Z / dZ)^2, labelFourthMoment(E, a) = tr(alt(E^* D_a E) A4(S)) is the Haar expectation of |<psi | D_a | psi>|^4 over unit vectors psi in the column space of E.

**Definition 1.12 (Subspace extrinsic fourth-moment score).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.extrinsicScore`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.extrinsicScore` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a frame E : C^S -> C^d, extrinsicScore(E) = d tr(Q(d) E^{otimes 4} A4(S) (E^{otimes 4})^*) is the ambient Weyl fourth-moment contribution of the subspace.

**Definition 1.13 (Single-qudit intrinsic fourth-moment term).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intrinsicTerm`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intrinsicTerm` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension k, intrinsicTerm(k) = k tr(Q(k) A4(Z / kZ)) is the single-qudit Weyl fourth-moment average on C^k.

**Definition 1.14 (Average linear stabilizer-entropy gap).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.aseGap`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.aseGap` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a frame E : C^S -> C^d with |S| nonzero, aseGap(E) = intrinsicTerm(|S|) - extrinsicScore(E) is the difference between the ambient subspace average linear stabilizer entropy and the intrinsic single-qudit average on C^{|S|}.

**Definition 1.15 (Symmetric four-tensor Schur twirl).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.symTwirl4`

*Formalization.* `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.symTwirl4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension d and a four-tensor operator X on (C^d)^{otimes 4}, symTwirl4(d, X) = tr(symProjector4(Z / dZ) X) A4(Z / dZ) projects X onto the scalar multiple of A4(Z / dZ) matching its trace on Sym^4(C^d).

**Theorem 1.16 (Odd-dimension Weyl periodicity, phase cancellation, and Hermitian fourth-moment polynomial).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.fourth_moment_cycle_and_hermitian_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.fourth_moment_cycle_and_hermitian_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

When d is odd, tau(d) equals the (d + 1) / 2 power of the primitive d-th root of unity exp(2 pi i / d), so tau(d)^d = 1 and intPaperDisplacement(d, x, y) depends only on (x, y) modulo d, matching tau(d)^{x y} X^x Z^y for all natural x, y and paperDisplacement(d, (x mod d, y mod d)) for all integers x, y. Because unimodular scalar factors cancel between A and A^* in alt(A), labelFourthMoment(E, a) depends only on the unphased Weyl word X^{a_1} Z^{a_2} and extrinsicScore(E) equals d^{-1} sum_a labelFourthMoment(E, a). Furthermore, for every Hermitian matrix A on a finite index set H, evaluating tr(alt(A) T(H, sigma)) across the twenty-four permutations of S_4 grouped by cycle structure (1^4, 2 1^2, 2^2, 3 1, 4) yields |H|(|H| + 1)(|H| + 2)(|H| + 3) tr(alt(A) A4(H)) = (tr A)^4 + 6 (tr A)^2 tr(A^2) + 3 (tr(A^2))^2 + 8 (tr A) tr(A^3) + 6 tr(A^4).

**Theorem 1.17 (Closed-form single-qudit intrinsic terms and one-dimensional pure-state entropy equality).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intrinsic_term_and_rank_one_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intrinsic_term_and_rank_one_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For every nonzero natural dimension k, summing the twenty-four permutation cycle traces over (Z / kZ)^2 via Weyl trace orthogonality and two-torsion phase-space counting gives intrinsicTerm(k) = 3 / (k + 2) when k is odd and intrinsicTerm(k) = 3(k + 2) / ((k + 1)(k + 3)) when k is even; in particular intrinsicTerm(1) = 1. For every unit vector psi in C^d with rank-one density matrix rho = |psi><psi|, linearStabilizerEntropy(psi) equals both 1 - d^{-1} sum_a |tr(D_a^* rho)|^4 and 1 - d tr(Q(d) rho^{otimes 4}). Consequently, for every one-dimensional isometric frame E : C^S -> C^d with |S| = 1 and E^* E = I, aseGap(E) equals the pure-state linear stabilizer entropy of the unique basis column of E.

**Theorem 1.18 (Basis independence of subspace moments and gaps, unitary label symmetry, and fourfold Schur twirl).**

Lean statement: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.subspace_gap_isometry_invariance_and_twirl`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.subspace_gap_isometry_invariance_and_twirl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For any two isometric frames E_1 : C^{S_1} -> C^d and E_2 : C^{S_2} -> C^d satisfying E_1^* E_1 = I and E_2^* E_2 = I, their column spaces coincide if and only if E_1 E_1^* = E_2 E_2^*, which forces |S_1| = |S_2|, labelFourthMoment(E_1, a) = labelFourthMoment(E_2, a) for every label a, extrinsicScore(E_1) = extrinsicScore(E_2), and aseGap(E_1) = aseGap(E_2). For every isometric frame E, labelFourthMoment(E, (0, 0)) = 1, and any unitary U on C^d commuting with E E^* such that U D_a U^* = c D_b with |c| = 1 satisfies labelFourthMoment(E, a) = labelFourthMoment(E, b). Moreover, symTwirl4(d, E^{otimes 4} A4(S) (E^{otimes 4})^*) = A4(Z / dZ), so pairing Q(d) with the symmetric four-tensor twirl of the embedded Haar fourth moment gives d tr(Q(d) symTwirl4(d, E^{otimes 4} A4(S) (E^{otimes 4})^*)) = intrinsicTerm(d).

## References

- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.A4`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.Q`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.T`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.alt`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.aseGap`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.extrinsicScore`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.fourth_moment_cycle_and_hermitian_formula`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intPaperDisplacement`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intrinsicTerm`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.intrinsic_term_and_rank_one_entropy`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.labelFourthMoment`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.linearStabilizerEntropy`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.paperDisplacement`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.power4`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.subspace_gap_isometry_invariance_and_twirl`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.symProjector4`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.symTwirl4`
- Truth anchor: `D5/S3/Quantum/Magic/SubspaceStabilizerEntropy.tau`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementTrace](../Algebra/WeylDisplacementTrace.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementTwoTorsion](../Algebra/WeylDisplacementTwoTorsion.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylPhaseArithmetic](../Algebra/WeylPhaseArithmetic.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
