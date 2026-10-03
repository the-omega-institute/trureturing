---
bibkey: chenkitaevzhang2024separable
authors: Joanna N. Chen, Sergey Kitaev, and Philip B. Zhang
year: 2024
title: "Distributions of statistics on separable permutations"
doi: 10.1016/j.dam.2024.05.004
url: https://arxiv.org/abs/2404.18517v1
claim: "Strict record distributions on literal 2413/3142 avoiders; Section 3 Conjecture 2 asks for all-length class-conditioned unimodality with a maximum at record count three."
strata_touched:
  - D5/S1/Words/Patterns/Separable/ActualCardinality
  - D5/S1/Words/Patterns/Separable/MinimumCutKernel
  - D5/S1/Words/Patterns/Separable/CutFactorization
  - D5/S1/Words/Patterns/Separable/ProperCut
license: citation-only
triage: anchor
---

# Record distributions on separable permutations

## Verified locator

- Primary v1: https://arxiv.org/abs/2404.18517v1, 29 April 2024, 19 pages;
  Conjecture 2 and Table 4 are in Section 3, page 17. Definitions are in
  Sections 1 and 1.2, and functional equations are in Section 2.
- DOI: https://doi.org/10.1016/j.dam.2024.05.004

The journal reference is
*Discrete Applied Mathematics* 355 (2024), 169–179.
The [institutional preprint](https://strathprints.strath.ac.uk/89387/1/Distributions-of-statistics-on-separable-permutations.pdf)
and [author manuscript](https://zhangbiaomath.github.io/papers/2024-dam-separable-perms.pdf)
also retain Conjecture 2. Neither manuscript establishes the content of the
journal version of record; that body remains unverified.

The source class is the actual classical $2413/3142$-avoiding permutations.
The four statistics count positions with strict comparisons: a right maximum
exceeds all later values, a left minimum is below all earlier values, a left
maximum exceeds all earlier values, and a right minimum is below all later
values. Counts are unshifted. Direct sums put prefix values below suffix values;
skew sums put them above. Irreducibility means positive length and no proper
direct cut. The empty permutation belongs to neither the irreducible nor the
reducible class; the singleton is irreducible and the reducible class at length
one is empty.

For a class $X$ and statistic $t$, write
$a_{X,t}(n,k)=|\{\pi\in X_n:t(\pi)=k\}|$.
Conjecture 2 asks, for each of
$(X,t)=(\mathrm{irreducible},\mathrm{rmax}),
(\mathrm{irreducible},\mathrm{lmin}),
(\mathrm{reducible},\mathrm{lmax}),
(\mathrm{reducible},\mathrm{rmin})$, that for every integer $n\ge5$ and
every integer $k\ge0$,

$$
\begin{aligned}
k<3&\ \Longrightarrow\ a_{X,t}(n,k)\le a_{X,t}(n,k+1),\\
k\ge3&\ \Longrightarrow\ a_{X,t}(n,k+1)\le a_{X,t}(n,k),\\
a_{X,t}(n,k)&\le a_{X,t}(n,3).
\end{aligned}
$$

A maximum at three is interpreted weakly; uniqueness is not needed for these
inequalities. All four full assertions remain open in the project.

The [strict-record mathematical source](../../docs/develop/theory/SEPARABLE_SIGNED_RECORD_WEIGHTS.md)
states the known block-sum identities for arbitrary actual permutations,
including empty factors: a direct sum has only the suffix right maxima
when the suffix is nonempty, retains the prefix count when the suffix is
empty, and right maxima add in a skew sum. It also gives the
record-weighted least-proper-cut convolution for both signs and all natural
lengths and record indices on the actual avoiding class. The direct summand
is $j(0,c)U(n-c,k)$ and the skew summand is
$\sum_{b=0}^{k}J(1,c,b)U(n-c,k-b)$, summed over $0<c<n$, where $j$ counts
the no-proper-cut prefix class, $J$ its exact record fiber, and $U$ the
full avoiding record fiber. Both factor lengths are positive. At lengths
zero and one there are no proper cuts. These helper formulas are known
source and normalization reductions, obtained by strict block comparisons
and weighting the existing minimum-cut reconstruction. They are source/library
intake, with four ingested definition/theorem atoms still open, and carry no
retained new Lean formalization, theorem settlement, or novelty claim.

`ActualCardinality.actual_schroder_cardinality` supplies the existing actual
signed least-cut equivalence with exact dependent-length reconstruction.
Its factorization uses `MinimumCutKernel`, `CutFactorization`, and `ProperCut`.
Fu–Lin–Zeng Proposition 2.1 supplies the recursive direct/skew characterization
of separable permutations; it does not itself supply a least-cut record
equivalence. The least-cut reconstruction used by the mathematical source is
the existing project supplier. Fu–Lin–Zeng's later greatest-cut tree
construction is a separate decomposition.

The full actual record generating-function bridge, its unmarked series
identification and boundary corrections, universal coefficient positivity
and peak-three inequalities, and avoidance/class/record symmetry transports
for all four pairs remain missing. The signed record helpers supply none of
these full assertions by themselves. The relevant scalar cut and cardinality
results are in `ActualCardinality`, `MinimumCutKernel`, `CutFactorization`,
and `ProperCut`; descent statistics in Fu–Lin–Zeng are a different question.

The supplied bounded literature screen reports examination of the primary
and manuscript bodies, five known citing bodies, and related record, descent,
and Schröder-class papers. The five citing bodies are Li–Kitaev,
[*King permutations and partially ordered patterns*](https://math.colgate.edu/~integers/aa59/aa59.pdf),
Integers 26 (2026), A59, DOI 10.5281/zenodo.19949822; Han,
[*Joint distributions of 10 classical statistics over permutations avoiding two patterns of length 3*](https://math.colgate.edu/~integers/aa18/aa18.pdf),
Integers 26 (2026), A18, DOI 10.5281/zenodo.18305021; Liao–Yang–Yu,
arXiv:2510.12046v1; Gao–Kitaev–Li–Ruan, arXiv:2509.14341v1 and the
journal-formatted manuscript for DOI 10.1016/j.dam.2025.09.017; and
Han–Kitaev–Zhang, arXiv:2408.12865v1. The screen found no equivalent proof
or refutation of Conjecture 2 within that corpus. This scope does not establish
global priority, exhaustive citation coverage, exclusive ownership, or the
unavailable journal body's contents. No originality or open-problem resolution
is attributed to the two helper identities.
