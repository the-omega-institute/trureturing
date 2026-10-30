# An extreme POVM with rank vector (3,3,2,2,2,2,2,2)

## Abstract

An explicit extreme eight-outcome POVM on complex seven-space refutes the proposed rank-vector exclusion.

**Definition 1.1 (Midpoint extremality of a finite POVM).**

$$\forall (n: \mathbb{N}), (\forall (M: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix.IsExtreme}\left(M\right) = \left((\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(M\right)) \land (\forall (A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)), (\forall (B: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(A\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(B\right)) \Rightarrow ((\forall (j: \operatorname{Fin}\left(n\right)), (M\left(j\right) = \operatorname{SMul.smul}\left(\frac{(1: \mathbb{C})}{(2: \mathbb{C})}, (A\left(j\right)) + (B\left(j\right))\right))) \Rightarrow ((A = M) \land (B = M)))))))\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.IsExtreme` (`✓ std3`).

*Citation.* Erkka Haapasalo; Juha-Pekka Pellonpää (2020). *Effective methods for constructing extreme quantum observables*. DOI: [10.1088/1751-8121/ab8d52](https://doi.org/10.1088/1751-8121/ab8d52). URL: <https://arxiv.org/abs/1809.09935v1>.

*Commentary.*

An n-outcome family of complex 7 by 7 matrices is extreme when it is a POVM and every midpoint decomposition into two POVMs has both factors equal to the original family. This is the midpoint formulation of extremality in Haapasalo and Pellonpää, lines 148–152.

**Definition 1.2 (Ranks after omitting rank-one outcomes).**

$$\forall (n: \mathbb{N}), (\forall (M: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix.bigRanks}\left(M\right) = \operatorname{Multiset.filter}\left((\lambda (r: \mathbb{N}) \mapsto (2 \le r)), \operatorname{Multiset.map}\left((\lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Matrix.rank}\left(M\left(j\right)\right))), \operatorname{Finset.val}\left(\operatorname{Finset.univ}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.bigRanks` (`✓ std3`).

*Citation.* Erkka Haapasalo; Juha-Pekka Pellonpää (2020). *Effective methods for constructing extreme quantum observables*. DOI: [10.1088/1751-8121/ab8d52](https://doi.org/10.1088/1751-8121/ab8d52). URL: <https://arxiv.org/abs/1809.09935v1>.

*Commentary.*

bigRanks maps the finite outcome index set to the natural ranks of the effects and filters out all ranks below two. It is the multiset form of the source's rank vector convention, which orders ranks with repetition and omits rank-one outcomes (lines 219–222).

**Definition 1.3 (The proposed rank-vector exclusion).**

$$(\operatorname{D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix.claim}: Prop) = \forall (n: \mathbb{N}), (\forall (M: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(M\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix.IsExtreme}\left(M\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix.bigRanks}\left(M\right) \ne \operatorname{insert}\left(3, \operatorname{insert}\left(3, \operatorname{insert}\left(2, \operatorname{insert}\left(2, \operatorname{insert}\left(2, \operatorname{insert}\left(2, \operatorname{insert}\left(2, \operatorname{singleton}\left(2\right)\right)\right)\right)\right)\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Erkka Haapasalo; Juha-Pekka Pellonpää (2020). *Effective methods for constructing extreme quantum observables*. DOI: [10.1088/1751-8121/ab8d52](https://doi.org/10.1088/1751-8121/ab8d52). URL: <https://arxiv.org/abs/1809.09935v1>.

*Commentary.*

The formal claim says that every extreme finite POVM on complex seven-space has a big-rank multiset different from two rank-three effects followed by six rank-two effects. This is the negative existence question for the problematic vector (3₂,2₆)₇ named in the source at lines 307–314.

**Theorem 1.4 (An explicit counterexample to the exclusion).**

$$\neg (\operatorname{D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.result` (`✓ std3`). ∎

*Resolves.* `Problems/haapasalo-pellonpaa-2020-extreme-povm-rank-vector-three-three-two-six` (refuted) by `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"haapasalo-pellonpaa-2020-extreme-povm-rank-vector-three-three-two-six","declaration_gid":"D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Erkka Haapasalo; Juha-Pekka Pellonpää (2020). *Effective methods for constructing extreme quantum observables*. DOI: [10.1088/1751-8121/ab8d52](https://doi.org/10.1088/1751-8121/ab8d52). URL: <https://arxiv.org/abs/1809.09935v1>.

*Commentary.*

The construction uses the ordered coordinates (e₀,e₁,e₂,f₀,f₁,f₂,g) of complex seven-space. Eight blocks of vectors are formed: two coordinate blocks consisting of the three e coordinates and the three f coordinates, and six phase blocks with phase-zero and phase-i choices for each of the three pairs of e coordinates. Four of the six phase blocks contain the apex coordinate g. For each block, form the positive matrix effect j by summing b bᴴ over its vectors, and let frame be the sum of all eight effects.

Lean's frame_posDef lemma proves positive definiteness of frame using its positive-semidefinite sum decomposition and an exact coordinate calculation showing that its matrix-vector action is injective. The positive square-root factorization of a strictly positive matrix then supplies an invertible normalizer with normalizer · frame · normalizerᴴ = 1. Conjugating every effect by this normalizer gives witness; congruence preserves positive semidefiniteness, the conjugated effects sum to the identity, and congruence by an invertible matrix preserves rank.

The block-column factorization effect j = columns j · (columns j)ᴴ identifies each effect rank with the cardinality of its block. The two coordinate blocks have cardinality three and the other six blocks cardinality two, so witness has bigRanks equal to the target multiset. For each block, an explicit left inverse of its columns is verified by finite coordinate cases. Expanding the conjugated products therefore reduces independence to the 42 within-block products, whose coefficients are separated by the two phase choices, the apex coordinates, and the coordinate blocks.

For a midpoint decomposition of witness into POVMs A and B, positivity and the midpoint equation imply that each A j is supported on the column space of the corresponding block. The left inverse gives a coefficient matrix for A j − witness j, and the normalized expansion expresses the difference as a linear combination of the independent 42 conjugated within-block products. Summing over j gives zero because both families sum to the identity, so every coefficient vanishes. Thus A = witness, and the midpoint equation then gives B = witness. Hence witness is extreme and its target big-rank multiset contradicts claim at n = 8.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.IsExtreme`
- Truth anchor: `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.bigRanks`
- Truth anchor: `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
