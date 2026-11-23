---
bibkey: kato2025exactlocalcompression
authors: Kohtaro Kato
year: 2025
title: Exact and Local Compression of Quantum Bipartite States
doi: 10.1109/TIT.2025.3562884
url: https://arxiv.org/abs/2309.07434
claim: "Equation (62) counts distinct posterior laws on the marginal support. The tentative joint-unitary marginal-rank formula in Eq. (61) fails on faithful classical sources."
strata_touched:
  - D5/S3/Quantum/Recovery/DiagonalRecordCapacity
  - D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation
  - D5/S3/Quantum/Recovery/LocalCompression/JointMarginalRank
  - D5/S3/Quantum/Measurements/FiniteLabelRecordDilation
  - D5/S3/Quantum/Recovery/LocalCompression/QutritPure
  - D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalReset
  - D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetDistortion
  - D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum
license: citation-only
triage: anchor
---

# Exact local compression of classical correlations

## Verified locator

[Journal record](https://doi.org/10.1109/TIT.2025.3562884) · [arXiv record](https://arxiv.org/abs/2309.07434)

Definition 1 in Section II.B quantifies over quantum encoding and recovery channels after restricting to the marginal support.
Section III.B, Eq. (17), defines the trace-one Choi state by applying the trace conditional expectation to the second half of a normalized Bell pair. Theorem 1, Eq. (19), computes the dimension via the selected purification, and Corollary 1, Eq. (22), gives the rank of the Choi state itself. [Primary text, p. 4](https://arxiv.org/pdf/2309.07434v2#page=4)

Section V.C, Eq. (61), tentatively proposes minimizing the rank of the partial trace after an unrestricted joint unitary on the two Choi factors. [Primary text, p. 7](https://arxiv.org/pdf/2309.07434v2#page=7)

Section VI.A, equation (62), counts the distinct conditional laws of the classical bipartite experiment.
[Primary text, p. 8](https://arxiv.org/pdf/2309.07434v2#page=8)

## Formalization scope

The repository counts vectors of likelihood ratios for a diagonal experiment with a specified reference law.
For a finite family, assigning positive priors to the comparisons and the reference gives a classical bipartite experiment with the same classes on the reference support.
This identifies the relation between the two dimension criteria.
The formal theorem also allows a comparison index type without a finiteness assumption because the vectors are realized on a finite basis.

The count in Section VI.A is for unrestricted encoding and recovery channels on the marginal support.
The finite pure-environment label-record criterion adds per-class rounded memory requirements and a whole-input isometry bound.

## Faithful counterexamples to Eq. (61)

For each alphabet size `n ≥ 2` and `0 < t < 1`, assign `(a,b)` probability
`(t · 1[a = b] + (1 − t)/n)/n`. All entries are positive and both marginals
are uniform. Joint recovery on B is equivalent to recovery of all the
conditional states of B given A. Their uniform mixture is the reference
state and there are n distinct likelihood vectors, so the exact recovery
minimum is n.

The trace conditional expectation is coordinate dephasing. Its Eq. (17)
Choi state has weight 1/n at each basis ket |b,b⟩. The permutation
|x,y⟩ ↦ |x − y mod n,y⟩ places every supported ket in row zero.
The resulting marginal is |0⟩⟨0|, and trace preservation makes one the
least possible rank. The refutation concerns the tentative Eq. (61).
Theorem 1 and Eq. (19) use a different optimization on the purifying systems.
The binary example (3,1,1,3)/8 and the initial refutation were supplied by
the ChatGPT Pro reasoning seat.

## The unrestricted unitary minimum

For a positive semidefinite joint matrix of rank r and a traced space of
dimension e > 0, the unitary minimum is the ceiling of r/e. The support of
any marginal of rank s can contain joint support of dimension at most s e.
An eigenbasis permutation attains the bound by placing the nonzero joint
eigenvalues into successive product-basis rows.

Applying this formula to Eq. (22) gives an arithmetic comparison. Write
aᵢ and bᵢ for the two positive block dimensions and n = Σᵢ aᵢ bᵢ for the
dimension of the marginal support. Equation (61) gives the ceiling of
(Σᵢ aᵢ²)/n, while Eq. (19) gives Σᵢ aᵢ. With multiple blocks the ceiling
is at most maxᵢ aᵢ, strictly below the sum. With one block it is the ceiling
of a₁/b₁, which equals a₁ precisely when a₁ = 1 or b₁ = 1.

For related spectral arguments, Reeb and Wolf group joint eigenvalues into
product-basis rows in §3.3 after Proposition 5 and in Remark 6. Fan's
variational principle bounds the mass captured by a fixed number of marginal
coordinates through the corresponding joint eigenvalue sum.
[Reeb–Wolf, p. 12](https://arxiv.org/pdf/1306.4352v3#page=12) ·
[Fan, Theorem 1](https://doi.org/10.1073/pnas.35.11.652). Li, Poon and Wang
study rank constraints when the marginals are prescribed.
[Li–Poon–Wang](https://arxiv.org/abs/1710.11416v2)

## Approximate pure-qutrit compression

Section VII proposes approximate local compression as a direction for further
work. The pure-qutrit increment keeps the normalized Bell source and its
reference, and measures half the joint trace norm of the reconstruction error.
For output in a fixed two-dimensional subspace the minimum is 2/3. Projection
with reset attains it. A fixed encoder and decoder through a qubit attain at
most 10189/15750 using a decoder with two Kraus operators. [Primary text, §VII](https://arxiv.org/abs/2309.07434v2)

For plane-preserving encoders with diagonal reset, the companion
*Exact Bell-source distortion with a reversible encoder on a hyperplane*
manuscript gives a matched-coordinate comparison for arbitrary CPTP decoders.
In dimension three, the lower block uses the square root of the weaker matched
probability. Its entries follow from the decoder's Choi positivity and trace
preservation, and the pure reset with a two-Kraus attenuating decoder realizes
that block. The local manuscript is the source of this comparison. Kato
Section VII supplies the approximate-compression setting.

The companion isotropic-compression manuscript also supplies the stationary
characteristic polynomial and the exact rational enclosure for the pure
diagonal-reset minimum. The optimal amplitude lies strictly between
0.80680296 and 0.80680298, and the attained error is one third of the
stationary spectral parameter. The minimum uses the joint Bell-state error
and permits any decoder after a plane-preserving diagonal reset. Kato §VII
provides the research direction. Farber–Gour Theorem 5 optimizes purification
fidelity, and Cha–Park–Lee Proposition 3.7 gives a nonisometric decoding
advantage for average ensemble fidelity.
[Farber–Gour](https://arxiv.org/abs/2610.14785) ·
[Cha–Park–Lee](https://arxiv.org/abs/2605.01258)
