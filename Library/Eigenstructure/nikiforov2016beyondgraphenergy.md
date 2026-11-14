---
bibkey: nikiforov2016beyondgraphenergy
authors: Vladimir Nikiforov
year: 2016
title: "Beyond graph energy: norms of graphs and matrices"
doi: 10.1016/j.laa.2016.05.011
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
arXiv:1510.02850v2, https://arxiv.org/abs/1510.02850v2,
§2.2 (multipartite matrices), §4.5.1,
Conjecture 4.42, printed p. 48; Linear Algebra and its Applications 506,
82–138, DOI 10.1016/j.laa.2016.05.011.
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

## Source and literature boundary

The versioned PDF and original TeX contain the quoted assertion. The
definitions are in §1.1 (complex matrices, max-norm and singular values),
Definition 1.4 (Schatten p-norm), Definition 2.15 (common-index
multipartiteness), and §4.5 (balanced Turán graph). The DOI identifies the
journal publication; its full text was inaccessible for textual comparison.
The target is the versioned preprint, and journal/preprint textual identity
is unverified. This note is citation-only and does not redistribute either
full text or assert a license for them.

The bounded source screen in [#30394](https://github.com/the-omega-institute/trureturing/issues/30394)
includes the following readings and search limits:

- The arXiv version record retains v2 as its latest listed version. The
  returned Crossref record and bounded erratum/corrigendum query identify
  no correction to this work; unindexed corrections are not excluded.
- Ivan Lazarević, *Extended Schatten norms of random graphs and Nikiforov
  conjecture*, Hacet. J. Math. Stat. 51(3), 737–742,
  [DOI 10.15672/hujms.914884](https://doi.org/10.15672/hujms.914884),
  was read through the legal publisher PDF. Its §3 addresses survey
  Conjecture 4.28 for undirected loopless graphs, including even powers,
  certain strongly regular graphs and trees. It does not settle the full
  complex multipartite assertion or its modulus equality criterion.
- The Semantic Scholar citation endpoint returned 100 records at offset
  zero and none at offset 100. Titles and available relevant abstracts
  contained no identified exact resolution. This index omits the known
  Lazarević paper; not all citing full texts were read. *Energy of
  matrices*, DOI 10.1016/j.amc.2017.05.051, had a withheld abstract and
  inaccessible publisher text (HTTP 403), so its content is not cleared.
- The Crossref query `Nikiforov Schatten r-partite matrices 4.42` returned
  12 records without an identified exact resolution in their metadata.
  The arXiv API query for `4.42` and `Nikiforov` returned no records.
  OpenAlex returned HTTP 429. The survey publisher endpoint returned a
  rate-limit payload, so it supplied no full-text evidence.

These bounds support no exhaustive absence or originality claim. The
repository source screen distinguishes the older Ky Fan-gap target
(survey Conjecture 3.20), complete homogeneous symmetric polynomial
norms, and norm compression from Conjecture 4.42. Native spectral and
finite-partition results are reused in the saved proof. The publication
dossier is [nikiforov-2016-conjecture-4-42](../../Problems/nikiforov-2016-conjecture-4-42.md).
