---
bibkey: hemmerstraubwestrem2025riordan
authors: Hemmer, David J.; Straub, Armin; Westrem, Karlee J.
year: 2025
title: New identities in the character table of symmetric groups involving Riordan numbers
doi: 10.37236/14401
url: https://arxiv.org/abs/2509.02796v1
claim: Conjecture 2.3 equates the alternating Ev sum over even three-row characters with the Ev sum of the two-row character; Lemma 3.1 supplies the Frobenius character interpretation.
strata_touched:
  - D5/S3/Combinatorics/Partitions/HemmerStraubWestrem
license: citation-only
triage: anchor
---

# The Ev character identity

## Verified locator

DOI: https://doi.org/10.37236/14401

Source: https://arxiv.org/abs/2509.02796v1

The journal publication is Electronic Journal of Combinatorics 33(1), P1.57 (2026).
Page references below use the arXiv v1 PDF.

Conjecture 2.3 (N = 1 version), page 3, states:

> For any partition λ ⊢ n, we have ∑_{λ̃∈Ev(λ)} ∑_{µ∈R₃(2n)} (−1)^{ℓ(λ̃)} χ^µ_{λ̃} = ∑_{λ̃∈Ev(λ)} χ^{(n,n)}_{λ̃}. (2.4)

The definition of Ev on page 1 states:

> In [Amd23], Amdeberhan defined Ev(λ) to be the set of all partitions of 2n obtained by replacing each λᵢ with either 2λᵢ or two copies of λᵢ, and then reordering the parts to be nonincreasing.

The encoding uses lists of cycle lengths before sorting. Permuting a cycle list
does not change the power-sum product or its Frobenius coefficient. Each binary
choice of replacements is retained, so repeated cycle types retain multiplicity.

The preceding paragraph, page 3, states:

> When N = 1, the set R^c_{2N}(2n) is the single partition (n, n), and the set R_{2N+1}(2n) consists of all partitions of 2n with at most three parts, all even.

Lemma 3.1, page 5, citing Stanley, Corollary 7.17.4, states:

> Let µ, λ ⊢ n. We have: χ^µ_λ = ⟨p_λ, s_µ⟩.

Section 6, page 12, states:

> We have proved Conjecture 2.3 for all partitions with a single part size, thus affirmatively answering Question 2.2 for those partitions and N = 1. It is a natural question to pursue whether the present techniques can be extended to prove identity (2.4) of Conjecture 2.3 for all partitions.

The Lean definitions use the three-variable power-sum product and the
Vandermonde coefficient at µ + (2,1,0). Its identification with the ordinary
irreducible character is the classical Frobenius formula, as expressed through
the Schur inner product in Lemma 3.1. This identification is a literature input;
the module proves the coefficient identity and does not construct Specht modules.
The triples in R3 are weakly decreasing, even, and padded by zeros. evTypes
retains multiplicity: each occurrence of a part independently contributes either
one doubled part or two copies. Section 2.1, page 4, gives multiplicities
1,4,6,4,1 for the five cycle types of Ev((1,1,1,1)).

Both sums reduce to the same difference of adjacent coefficients of
∏ᵢ(X^{2aᵢ} + X^{aᵢ} + 1), multiplied by 2 to the number of parts.
The proof applies to every ordered list of positive parts with positive sum,
so mixed part sizes require no additional hypothesis.
The identities for N ≥ 2, the closed form of Conjecture 6.1, and explicit
bijective proofs remain separate questions.

Literature completeness is ASSUMED-UNVERIFIED. Westrem's dissertation
(DOI 10.37099/mtu.dc.etdr/1892) was not read in full. Its landing-page abstract
in the Internet Archive capture of 2025-08-21 describes a Chapter 4 proof that
a special case of the alternating Ev sum vanishes; it indicates no general
proof of Conjecture 2.3.
