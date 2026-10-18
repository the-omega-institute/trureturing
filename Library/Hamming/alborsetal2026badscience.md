---
bibkey: alborsetal2026badscience
authors: Alex Albors, Hisham Bhatti, Lukshya Ganjoo, Raymond Guo, Dmitriy Kunisky, Rohan Mukherjee, Alicia Stepin, Tony Zeng
year: 2026
title: On the Structure of Bad Science Matrices
doi: 10.2140/involve.2026.19.443
url: https://arxiv.org/abs/2408.00933
claim: Section 1.4 asks whether the displayed five-by-five unit-row matrix with beta equal to (2 + 3 sqrt(3))/4 is optimal.
strata_touched:
  - D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality
license: citation-only
triage: anchor
---

# On the Structure of Bad Science Matrices

The source defines, for real matrices whose rows have Euclidean length one,
β(A) = 2⁻ⁿ ∑_{x∈{−1,1}ⁿ} ‖Ax‖∞. Section 1 (arXiv v2, p. 1) says:

> The bad science matrix problem [4] is concerned with understanding, for matrices A ∈ ℝⁿˣⁿ whose rows are normalized to have ℓ²-length 1, the size of the quantity

The displayed quantity is β above. Section 1.4 (arXiv v2, p. 3) gives
A = (1/(2√3)) times the matrix with rows
(2,2,0,0,2), (−2,2,0,2,0), (−2,0,0,−2,2),
(0,−√3,√3,√3,√3), (0,√3,√3,−√3,−√3), and asks:

> We do not know whether this matrix is indeed optimal.

It also states:

> Indeed, even for relatively small dimensions, like n = 3 or n = 4, rigorously proving that a certain candidate matrix is indeed extremal appears to be a highly nontrivial problem.

The same section evaluates β(A) as (2 + 3√3)/4, with eight cube vertices
having image sup norm 2 and the other twenty-four having image sup norm √3.
The repository result proves optimality for every real five-by-five matrix with
unit rows. It does not classify all maximizers or determine the optimum in
higher dimensions. The journal reference is Involve 19 (2026), 443–460.

## Verified locator

DOI: https://doi.org/10.2140/involve.2026.19.443

Source: https://arxiv.org/abs/2408.00933

The quoted definition and question are in arXiv:2408.00933v2, Section 1
(p. 1) and Section 1.4 (p. 3). The journal version of record has not been read.
