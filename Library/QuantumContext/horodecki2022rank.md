---
bibkey: horodecki2022rank
authors: K. Horodecki; J. Zhou; M. Stankiewicz; R. Salazar; P. Horodecki; R. Raussendorf; R. Horodecki; R. Ramanathan; E. Tyhurst
year: 2022
title: "The rank of contextuality"
doi: 10.1088/1367-2630/acdf78
url: https://arxiv.org/abs/2205.10307
claim: "Definition III.1 defines the rank of contextuality; Section IX asks for a quantum behavior whose rank is not a power of two."
strata_touched:
  - D5/S3/QuantumContext/RankOfContextualityNonPowerTwo
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1088/1367-2630/acdf78

Journal: https://doi.org/10.1088/1367-2630/acdf78

Source: https://arxiv.org/abs/2205.10307

# The rank of contextuality

K. Horodecki et al., arXiv:2205.10307v1; New Journal of Physics 25 (2023), 073003.
The page numbers below refer to the published PDF.

Section 2, PDF page 4:

> We refer to output A given input X as an ordered list of outcomes (a₁, a₂, . . . , a|X|)), that is, it assigns a value to every observable in the context corresponding to X.

> We refer to a given point in polytope P(A | X) as a behavior, with input X and output A.

> In other words: a non-contextual behavior PNC is a probabilistic mixture of deterministic behaviors that have fixed values of outcomes to any observable beforehand.

Section 3, Definition 3.1, PDF page 5:

> Let P be a behavior. Let N be the set of all non-contextual behaviors, each of the form Nᵢ(A | X). Then we define the rank of contextuality denoted as RC in the following way

Equation (3): RC(P) := min {|S| : S ⊂ N, ∀ X = i, ∃ N(A | X) ∈ S, ∀ A, N(A | X = i) = P(A | X = i)}.

> where |S| denotes the cardinality of the set S.

Section 9 (Section IX in the arXiv source), PDF page 19:

> Finally, it would be interesting to construct a quantum behavior having the rank of contextuality different from the power of 2 (the power of 2 is achieved by a tensor product of the Peres-Mermin behaviors).

The binary encoding uses finite observable labels, ordered context lists and Boolean outcomes.
The bit true denotes eigenvalue −1. Noncontextuality uses a nonnegative normalized real
weight on all global assignments, with each local distribution obtained by restriction.
The minimum in equation (3) is expressed by IsLeast on the set of finite cover cardinalities.
The quantum realization uses commuting Hermitian involutions and their spectral projections
on a positive semidefinite trace-one matrix. The constructed behavior is the product of two
Peres–Mermin squares, with 18 observables, 36 contexts and rank 3.

The existence of this behavior answers the quoted construction question. Classification of
all quantum ranks and the paper's other questions remains open here.
