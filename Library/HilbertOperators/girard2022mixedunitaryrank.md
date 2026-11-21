---
bibkey: girard2022mixedunitaryrank
authors: Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous
year: 2022
title: On the Mixed-Unitary Rank of Quantum Channels
doi: 10.1007/s00220-022-04412-y
url: https://arxiv.org/abs/2003.14405
claim: "The symmetric Werner–Holevo channel has minimal mixed-unitary rank exactly when the complex symmetric matrix space has a Hilbert–Schmidt orthogonal unitary basis. Girard et al. prove this rank for positive even dimensions and dimension three and conjecture it for every positive dimension."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineRank
  - D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo
license: citation-only
triage: anchor
---

# Girard et al., mixed-unitary rank of quantum channels

## Verified locator

The journal article appeared in Communications in Mathematical Physics
394, 919–951 (2022). Section 6 contains equations (117)–(119),
Theorems 19, 21, and 23, and the conjecture after Theorem 23.
[Journal DOI](https://doi.org/10.1007/s00220-022-04412-y)
[ArXiv record](https://arxiv.org/abs/2003.14405)

## Rank criterion and known cases

Section 6 defines the symmetric Werner–Holevo channel as
$\Phi^+(X)=(\operatorname{tr}(X)I+X^\mathsf{T})/(n+1)$. Its
unnormalized Choi matrix is $2P_+/(n+1)$, with $P_+$ the
projection onto the symmetric tensor subspace. The Choi rank is
$n(n+1)/2$. Each unitary conjugation contributes a rank-one Choi
matrix, so a mixed-unitary decomposition needs at least that many
terms. [Primary paper, equations (117)–(119)](https://arxiv.org/pdf/2003.14405)

Theorem 19(1) equates attainment with a Hilbert–Schmidt orthogonal
basis consisting of complex symmetric unitaries. The proof uses
vectorization to identify the symmetric matrix space with the range of
$P_+$. The vectors obtained by dividing the basis matrices by
$\sqrt n$ resolve $P_+$. The resulting decomposition has equal
weights $2/(n(n+1))$. Theorems 21 and 23 supply all positive even
dimensions and dimension three. The concluding paragraph after Theorem
23 conjectures minimal mixed-unitary rank in every positive dimension.
[Primary paper, Theorems 19, 21, and 23](https://arxiv.org/pdf/2003.14405)

The project's affine construction treats $n=9^d$ for every natural
exponent $d\ge2$, beginning at $n=81$.
It uses affine lines of order nine, followed by distinct edge sums
across each parallel class and additive characters. The resulting
unitaries form an orthogonal basis of the entire complex symmetric
matrix space of dimension $n(n+1)/2$. The Lean theorem gives the
least length of a finite mixed-unitary decomposition in these
dimensions. The conjecture for every positive dimension remains open.

Levick and Rahaman prove attainment for primes congruent to seven
modulo eight. Ma gives rigorous interval certificates for odd
dimensions through 67.
[Levick–Rahaman, Corollary 3.12](https://arxiv.org/abs/2105.00975)
[Ma, Theorem 10](https://doi.org/10.5281/zenodo.24246318)
