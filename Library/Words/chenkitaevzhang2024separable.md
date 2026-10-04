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
  - D5/S1/Words/Patterns/Separable/RecordPeak
  - D5/S1/Words/Patterns/Separable/RecordTransport
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
and weighting the existing minimum-cut reconstruction. They are used locally
in the actual right-maximum proof below; no new standalone normalization helper
theorems are retained.

`ActualCardinality.actual_schroder_cardinality` supplies the existing actual
signed least-cut equivalence with exact dependent-length reconstruction.
Its factorization uses `MinimumCutKernel`, `CutFactorization`, and `ProperCut`.
Fu–Lin–Zeng Proposition 2.1 supplies the recursive direct/skew characterization
of separable permutations; it does not itself supply a least-cut record
equivalence. The least-cut reconstruction used by the mathematical source is
the existing project supplier. Fu–Lin–Zeng's later greatest-cut tree
construction is a separate decomposition.

For every $n\ge4$, the actual $2413/3142$ avoiders with no proper direct cut
and exactly two strict right maxima are at most those with exactly three:
$a_{\mathrm{irreducible},\mathrm{rmax}}(n,2)\le
a_{\mathrm{irreducible},\mathrm{rmax}}(n,3)$. This is supplied by
[`RecordPeak.actual_record_rising`](../../Blueprint/D5/S1/Words/Patterns/Separable/RecordPeak.md)
with no generating-function premise. Local finite-fiber and scalar
generating-function derivations, together with a universal positive quotient
and derivative composition argument, establish this adjacent comparison.

[`RecordTransport.actual_four_record_transports_and_rising`](../../Blueprint/D5/S1/Words/Patterns/Separable/RecordTransport.md)
gives the exact all-length actual transports. If $i_t$ and $d_t$ are the
positive irreducible and proper-direct-cut record counts, then
$i_{\mathrm{lmin}}=i_{\mathrm{rmax}}$ and
$d_{\mathrm{lmax}}+\delta=d_{\mathrm{rmin}}+\delta=i_{\mathrm{rmax}}$,
where $\delta(n,k)=1$ exactly at $n=k=1$. The theorem constructs actual
reverse, complement and reverse-complement avoidance and cut transports,
and restricts their record-position bijections to the exact record fibers.
It excludes the empty permutation from irreducibility and treats the
singleton separately. It also proves, for all four class/statistic pairs,
zero counts at record zero for positive lengths, zero counts at record one
for $n\ge2$, and every adjacent rising comparison $k<3$ for every $n\ge4$.
The two-to-three right-maximum comparison uses the existing `RecordPeak`
theorem directly.

[`RecordFirstDecline.actual_four_record_first_decline`](../../Blueprint/D5/S1/Words/Patterns/Separable/RecordFirstDecline.md)
gives the actual comparison $a(n,4)\le a(n,3)$ at every natural length,
and the strict comparison $a(n,4)<a(n,3)$ for every $n\ge3$, for all four
class/statistic pairs. Its actual weighted difference is $t^3F(q(t))$,
where $F(x)=1+4x+2x^2-8x^3-6x^4+11x^5+15x^6+5x^7$.
The exact quotient $(1+x)^2F'(x)/(1-2x-x^2)$ has coefficients
$4,20,32,16,47,286,889,2224,5372$ through index eight and an unbounded
nonnegative tail satisfying $v_m=2v_{m-1}+v_{m-2}$. Its positive-index
composition coefficients dominate those of $20q(t)$; the scalar Schröder
recurrence gives positivity of the actual $q$ at every positive index.
The derivative identity and $F(0)=1$ therefore establish strict positivity
of every coefficient of $F(q(t))$. The theorem applies the existing
record transports directly. It has no conditional generating-function
premise and uses no finite length cutoff.

The declining inequalities at arbitrary $k\ge4$ and the global maximum
at three remain open. The universal Motzkin differential recurrence,
support and Newton identity, the other quotient certificates, and their
actual-series applications are not established by these partial results.
The [problem dossier](../../Problems/chenkitaevzhang-2024-separable-record-peak-three.md)
keeps the complete target distinct from them. Full CKZ Conjecture 2 and C15
remain OPEN; no partial theorem is a full external resolution, novelty or
priority claim. The relevant scalar cut and cardinality results are in
`ActualCardinality`, `MinimumCutKernel`, `CutFactorization` and `ProperCut`;
descent statistics in Fu–Lin–Zeng are a different question.

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
is attributed to these partial conclusions.
