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
  - D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing
  - D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint
  - D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint
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

## The order-27 seed for transversal gluing

Qiyuan Ma's Hexagon preprint 2611.00505v1, §4, Theorem 10 (p. 5)
and Table 1 (p. 6, row $n=27$), gives a full Hilbert–Schmidt
orthogonal basis of 378 symmetric unitary matrices in order 27.
The version 1.1 Zenodo supplement includes the archive `code.zip`.
From its `sym-unitary-code` directory, run `certify.py` with the
arguments `27 --from-center` to read `centers/cert_sol_n27.npy`.
This reproduces the Krawczyk inclusion in 128-bit Arb ball
arithmetic on the archived box of radius $10^{-9}$.
[Ma, §4, Theorem 10 and Table 1](https://hexagonmath.org/pdf/2611.00505v1#page=5)
[Zenodo supplement, version 1.1](https://doi.org/10.5281/zenodo.24246318)

The Lean gluing extends a full order-$m$ basis to order $9m$ given
a resolvable transversal design $\mathrm{TD}(9,m)$ and $3\mid m$.
Finite fields supply the design for $m=3^r$ when $r\ge2$.
The power-of-three rank theorem takes the full order-27 basis as an
explicit hypothesis. It uses induction for odd exponents and the
affine power-of-nine result for even exponents. The Lean kernel
checks this implication. Ma's order-27 seed has the separate
interval verification described above.

## Chirped construction in order 73

Qiyuan Ma's *Symmetric Unitary Orthogonal Bases in Odd Dimensions*,
Hexagon 2611.00505v1, §2, Theorem 5 (p. 3), separates the
Hilbert–Schmidt pairing of chirped circulants into a seed pairing and
a quadratic character sum. Section 5.2, Proposition 12 (p. 7),
reduces the prime-order construction to the correlations within one
multiplicative orbit and its pairing with one fixed unchirped seed.
Ma's Theorem 10 (p. 5) certifies odd orders through 67.
[Ma, Theorems 5 and 10 and Proposition 12](https://zenodo.org/records/24246318/files/paper.pdf)

In order 73, the 36 shifted chirped seeds and one fixed unchirped seed
give 37 seed vectors. The formal certificate uses 37 real Cayley
coordinates and checks a unique zero on the closed sup-norm ball of
radius $2^{-30}$ about the supplied dyadic center. Integer replay checks
the residual, derivative defect and preconditioner bounds. The analytic
proof identifies the replay with the exact system and bounds derivative
drift on the ball. Orthogonality follows from the recorded correlations
and the finite pair-coverage check. The 73 modulations of each seed
give a full Hilbert–Schmidt orthogonal basis of 2701 symmetric unitaries.

By Girard et al., Theorem 19(1), the basis gives the uniform
2701-term decomposition of the symmetric Werner–Holevo channel.
The Choi rank is $73(73+1)/2=2701$, which is also a lower bound for
every finite mixed-unitary decomposition of the channel. This settles
the order-73 case. The conjecture for all positive dimensions remains open.
[Girard et al., Theorem 19(1)](https://arxiv.org/pdf/2003.14405)

## Chirped construction in order 69

Ma's *Symmetric Unitary Orthogonal Bases in Odd Dimensions*,
Hexagon 2611.00505v1, §2, Theorem 5 (p. 3), factors the
Hilbert–Schmidt pairing of chirped circulants into a seed pairing and
a quadratic character sum. Proposition 12 (p. 7) gives an orbit
reduction in prime order. The order-69 construction uses the Gram
factorization over the composite ring $\mathbb Z/69\mathbb Z$, with four
seed layouts and multiplicative orbits of lengths 22, 11, 1 and 1.
Ma's Theorem 10 (p. 5) certifies odd orders through 67.
[Ma, Theorems 5 and 10 and Proposition 12](https://zenodo.org/records/24246318/files/paper.pdf)

The 32 recorded correlations give 63 real equations in 63 real
Cayley coordinates. The midpoint self-correlation is real by the
orbit involution, so it contributes one equation. Integer replay and
the analytic derivative drift bound certify a unique zero on the
closed sup-norm ball of radius $2^{-30}$ about the dyadic center.
At this zero, the recorded equations and finite pair coverage make
the 35 shifted seeds orthogonal. Their 69 modulations give 2415
Hilbert–Schmidt orthogonal symmetric unitaries spanning the complex
symmetric matrix space.

By Girard et al., Theorem 19(1), this basis yields a uniform
2415-term decomposition of $X\mapsto(\operatorname{tr}(X)I+
X^\mathsf{T})/70$. The Choi rank is $69(69+1)/2=2415$ and gives the
matching lower bound for every finite mixed-unitary decomposition.
The theorem establishes the order-69 case of the rank conjecture.
The all-dimension conjecture remains open.
[Girard et al., Theorem 19(1)](https://arxiv.org/pdf/2003.14405)
