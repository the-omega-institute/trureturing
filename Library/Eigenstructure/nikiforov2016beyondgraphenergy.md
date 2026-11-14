---
bibkey: nikiforov2016beyondgraphenergy
authors: Vladimir Nikiforov
year: 2016
title: "Beyond graph energy: norms of graphs and matrices"
doi: null
url: https://arxiv.org/abs/1510.02850v2
claim: "Conjecture 4.42 asserts a Schatten upper bound and characterizes equality by the entrywise modulus being balanced Turán adjacency."
strata_touched:
  - D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation
license: citation-only
triage: anchor
---

# Complex multipartite matrices and Conjecture 4.42

## Locator

V. Nikiforov, *Beyond graph energy: norms of graphs and matrices*,
arXiv:1510.02850v2, §2.2 (multipartite matrices), §4.5.1,
Conjecture 4.42; Linear Algebra and its Applications 506, 82–138.
The versioned preprint is the statement source. No identity assertion
between every preprint and journal statement is needed.

The source defines an r-partite complex matrix by a partition of its
common row and column index set into r nonempty parts, with every
within-part principal block zero. It defines the max-norm as the maximum
of the absolute values of all entries, and the Schatten p-norm as the
p-th root of the sum of p-th powers of singular values.

Conjecture 4.42 states:

> Let p > 2, n ≥ r ≥ 2, and let A = [aᵢⱼ] be an n × n complex matrix
> with ‖A‖max ≤ 1. If A is r-partite, then ‖A‖p ≤ ‖Tᵣ(n)‖p.
> Equality holds if and only if the matrix |A| = [|aᵢⱼ|] is the
> adjacency matrix of Tᵣ(n).

The Turán graph has r nonempty parts whose sizes differ by at most one.
Adjacency means that two vertices belong to different parts; its labels
are arbitrary and change by simultaneous row and column permutation.
The matrix A is not assumed symmetric, Hermitian or nonnegative.

## Exact counterexample and boundary

For p = 6 and n = r = 3, take

$$
A=\begin{pmatrix}0&1&1\\-1&0&1\\-1&-1&0\end{pmatrix}.
$$

Singleton index parts satisfy the multipartite hypothesis, every entry
has modulus at most one, and |A| is T₃(3) with the identity labeling.
The column-Gram cubic traces are 54 for A and 66 for T₃(3).
These are the sixth powers of their Schatten 6-norms. Thus the
modulus condition does not imply equality, refuting the entire
conjunction in the conjecture. This argument leaves its upper-bound-only
assertion unresolved. It makes no dimension-minimality or general-family
claim.

The source supplies the conjecture and conventions. The counterexample
and its formal derivation are repository results. The bounded literature
screen recorded in issue #30394 is not exhaustive novelty clearance.

Source byte identities: PDF SHA-256
`c1d733d77f0391d43fbe936fe94542e2332cedd105a27e82564c3473402d2e87`;
original TeX SHA-256
`c6861ca23b14aa470734cec834a60fcf5fcc5f098d38167dbc7da43622a54075`.
