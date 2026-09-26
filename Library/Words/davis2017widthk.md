---
bibkey: davis2017widthk
authors: Robert Davis
year: 2017
title: Width-k Generalizations of Classical Permutation Statistics
doi: 10.48550/arXiv.1701.04788
url: https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf
claim: Conjecture 9 states the coprime width-descent difference formula for G_{n,k}(q).
strata_touched:
  - D5/S1/Words/DavisWidthDescentDifferenceCoprime
license: citation-only
triage: anchor
---

# Coprime width-descent differences

Davis gives the following descent-set line, generating function, and
MacMahon identification together at the top of printed page 2. Printed page
1 ends with the preceding descent-count formula:

> where Des σ = {i ∈ [n − 1] | a_i > a_{i+1}}.
> Given any statistic st, one may form the generating function
> F_n^{st}(q) = Σ_{σ∈S_n} q^{st σ}.
> A famous result due to MacMahon [6] states that F_n^{des}(q) =
> F_n^{exc}(q), and that both are equal to the Eulerian polynomial A_n(q).
> The Eulerian polynomials themselves may be defined via the identity
> Σ_{j≥0} (1 + j)^n q^j = A_n(q)/(1 − q)^{n+1}.

The width statistic is defined on printed page 2:

> For each of the following definitions, we assume n ∈ Z_{>0}, k ∈ [n − 1],
> ∅ ≠ K ⊆ [n − 1], and σ = a_1 a_2 ··· a_n ∈ S_n. We define a width-k
> descent of σ to be an index i ∈ [n − k] for which a_i > a_{i+k}. Thus the
> width-1 descents are the usual descents of a permutation. Let
> Des_k(σ) = {i ∈ [n − k] | a_i > a_{i+k}} denote the set of all width-k
> descents of σ, and set des_k(σ) = |Des_k(σ)|.

Printed page 6 defines the Laurent polynomial and states the numbered
conjecture:

> We now show that interesting behavior occurs when considering the function
> G_{n,k}(q) = Σ_{σ∈S_n} q^{des_k(σ)−des_{n−k}(σ)}.
> According to computational data, the following conjecture holds for all
> n ≤ 9 and 1 ≤ k < n for which gcd(k, n) = 1.
>
> Conjecture 9. If gcd(k, n) = 1, then
> G_{n,k}(q) = n q^{1−k} A_{n−1}(q).

The formal encoding uses the paper's stated identification
`F_m^{des}(q) = A_m(q)` as the definition of the Eulerian polynomial; it does
not separately formalize the infinite-series identity. Positions are shifted
from one-based indexing to `Fin n`, so membership in `[n-k]` becomes
`i.val + k < n`. The signed exponent is represented in the Laurent polynomial
ring over the integers.

The paper reports computation through `n <= 9`. Independent enumeration for
all 34 coprime pairs with `n <= 8` gives coefficientwise agreement. In
particular, `G(3,1) = 3 + 3q` and
`G(5,2) = 5q^{-1} + 55 + 55q + 5q^2`. The non-coprime pair has
`G(4,2) = 24`, outside Conjecture 9's hypothesis.

MathDB entry `/p/335077` records the same statement under the title "The
coprime-width formula for the generalized descent difference polynomial" and
reported zero solutions on 2026-09-20. The two papers then citing Davis,
arXiv:1912.08551 and arXiv:2402.16251, do not state a proof or refutation of
Conjecture 9.

The journal article has no journal DOI. The DOI in the frontmatter identifies
the arXiv preprint through DataCite.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1701.04788
- URL: https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf
- Scope: Section 1, printed page 2, and Section 2, printed page 6,
  Conjecture 9.
