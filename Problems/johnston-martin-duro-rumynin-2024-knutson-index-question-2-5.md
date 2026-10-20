---
slug: johnston-martin-duro-rumynin-2024-knutson-index-question-2-5
bibkey: johnston2025knutson
doi: 10.1080/00927872.2025.2498055
url: https://arxiv.org/abs/2403.18498v6
triage: theorem
motivation_gids:
  - D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.result
---

# Johnston–Martín Duro–Rumynin Question 2.5

## Problem

Johnston, Martín Duro and Rumynin define the Knutson index and the finite-set
subindex for a finitely generated commutative ring $R$, a homomorphism
$\alpha : R \to \mathbb{Z}$ and a regular element $r$. Question 2.5 asks
whether there is a finite $S \subset R$ such that
$\mathcal{K}_r(x)=\mathcal{K}_r^S(x)$ for every $x\in R$.

### Statement echo

The Lean definitions `IsRegularElement`, `knutsonIndex`, `eligible`,
`eligibleIndex` and `knutsonSubindex` mirror the source conventions. The
settling declaration `result` proves the negation of the universal `claim`.
The ring hypotheses are `[CommRing R]` and `[Algebra.FiniteType ℤ R]`, and the
comparison is in $\mathbb{N}_\infty$ after casting the ordinary index.

## Motivation

The frozen declaration
`D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.result` refutes the
universal affirmative answer. It supplies a finitely generated nonreduced
rank-five ring in which every finite set fails for a suitable element.

## Gap

The source states Proposition 2.6 for reduced rings. The supplied literature
screen found no later answer to Question 2.5 in the cited source or in the
searched citing and later papers. Its completeness is `ASSUMED-UNVERIFIED`.

## Route

Use the integer-coordinate ring with elements $(d,a,b,f,t)$ and augmentation
$d+2a+2b+4t$. Let $r=(0,0,0,0,1)$ and
$X(k)=(0,1,2k,0,-k)$, $Y(k)=(0,1,-2k,0,k)$. Coordinate multiplication proves
$X(k)Y(k)=r$, so $X(k)$ has ordinary index one. For finite $S$, take
$k=1+\sum_{s\in S}|s.b|$. Eligibility gives $s.d=0$ and
$s.b=-2ks.a$; the bound forces $s.a=s.b=0$, and the coefficient of $r$ is
$2s.t$. Every eligible coefficient is therefore even, so the finite-set
subindex is even or infinite and cannot equal one.

## Falsifier

The refutation would fail if the coordinate multiplication did not make
$X(k)Y(k)=r$, if $X(k)$ did not have index one, or if a finite $S$ could produce
an odd eligible coefficient at the selected $k$.

## Evidence

The kernel-checked declaration `result` has type `¬ claim`. Its proof uses the
coordinate ring, `regular_r`, `XY`, `knutsonIndex_X`, `eligible_equations` and
`subindex_ne_one_of_even`. The axiom closure is contained in
$\{\mathrm{propext},\ \mathrm{Classical.choice},\ \mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The experiment is [the-omega-institute/trureturing-experiments@6f1f4aaf2d0338fdf0ff503460d5f8f606ae43bb](https://github.com/the-omega-institute/trureturing-experiments/tree/6f1f4aaf2d0338fdf0ff503460d5f8f606ae43bb/docs/reports/johnston-martin-duro-rumynin-2025-knutson-finite-subindex), using `check.py`; its SHA-256 is `552bc8a7aebd1863234bb9321dbff2ae031f02f336b03ada66994ed0331bc1ae`. Running `python3 check.py` exits 0 with `RESULT PASS`; it checks even $n<60$, regularity on 500 random elements, and 300 finite-set trials.

## Triage

| item | status | evidence |
| --- | --- | --- |
| Ring laws and finite module generation | proved | Kernel-checked coordinate extensionality and `coordMap_surjective`; `moduleFinite` supplies finite generation. |
| Eligibility equations | proved | Kernel-checked `eligible_equations`. |
| Parity obstruction | proved | Kernel-checked `subindex_ne_one_of_even`, with `eligibleIndex_even` as its consumed helper. |
| Final negative answer | proved | Kernel-checked `result : ¬ claim`; this is the settling node. |
| Numerical checker | computed | `python3 /Users/auric/trureturing-experiments/docs/reports/johnston-martin-duro-rumynin-2025-knutson-finite-subindex/check.py`, exit 0, script SHA-256 `552bc8a7aebd1863234bb9321dbff2ae031f02f336b03ada66994ed0331bc1ae`; scope $n<60$, 500 regularity samples and 300 finite-set trials. |
| Tracked delivery | computed | `git diff --name-only origin/dev...HEAD` identifies the Lean source, Scribe, emitted Markdown, Library note, state record and this dossier; there are no experimental sources in the delivery. |
| Literature screen | open | The searched source and cited/later papers yielded no located settlement; completeness is `ASSUMED-UNVERIFIED`. |

### What the settlement shows

**Mechanism (proved).** The nilpotent direction makes the annihilator slope
$b=-2ka$ vary with $k$, while the congruence modulo four forces the resulting
coefficient to have parity determined by $a$. A finite set contains only
finitely many slopes, so the selected $k$ forces every eligible coefficient to
be even.

**Reduced case (literature reading).** Proposition 2.6 gives a finite set for
reduced rings. The source's applications embedding in finite products of
$\mathbb{C}$ retain that hypothesis.

**Rank and nonreducedness (proved in prose).** The coordinate carrier is
$\mathbb{Z}^5$ with coordinatewise addition and integer scaling, so its five
coordinate vectors are a free $\mathbb{Z}$-basis. The nonzero coordinate vector
$(0,0,0,1,0)$ has square zero by the displayed multiplication. Thus the example
is nonreduced. Finite generation is kernel-checked through `moduleFinite` and
the inferred `Algebra.FiniteType` instance in `result`. Together with `result`,
these facts show that reducedness cannot simply be removed from Proposition 2.6.

**Neighbouring scope (open).** Whether finite subsets suffice for restricted
classes of nonreduced rings remains open. Rings embedding in finite products of
$\mathbb{C}$ are reduced and remain covered by the source's reduced result.

## ASSUMED-UNVERIFIED

The literature search is not exhaustive: citation APIs were rate-limited and
Carl Faith's cited paper was checked only bibliographically. The kernel proof
authenticates the formal proposition, not the external source's publication
history or priority.
