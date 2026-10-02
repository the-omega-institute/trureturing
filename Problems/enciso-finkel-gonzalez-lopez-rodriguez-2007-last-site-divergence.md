---
slug: enciso-finkel-gonzalez-lopez-rodriguez-2007-last-site-divergence
bibkey: enciso2007nearestneighbor
doi: 10.1016/j.nuclphysb.2007.07.001
url: https://arxiv.org/abs/0704.3046v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence.result
---

# Divergence of the last site of the nearest-neighbor QES chain

## Problem

A. Enciso, F. Finkel, A. González-López and M. A. Rodríguez,
arXiv:0704.3046v1, §2, printed pp. 9–10, around Eq. (19), ask:

> It is also of interest to determine whether the position of the last spin tends to infinity as N → ∞, since according to our interpretation of the chain’s geometry the number 2ξN/π is the radius of the circle on which the spins lie.

The sites are increasing real solutions of Eq. (6),

$$
\xi_i=\frac1{\xi_i-\xi_{i-1}}+\frac1{\xi_i-\xi_{i+1}},
\qquad \xi_0=\xi_N,\quad \xi_{N+1}=\xi_1.
$$

Issue #11858 preregisters the fully quantified assertion: for every real
$B$ there is a natural $N_0$ such that every $N\geq N_0$, $N\geq3$, and
every strictly increasing cyclic site solution satisfy $B<\xi_N$.
The source motivates the assertion by Eq. (19), then cautions that the
inverse-error-function argument in Eq. (18) is accurate only up to terms
of order $1/N$.

## Motivation

`D5/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence.result`
proves this assertion uniformly over all admissible configurations.
The source's index $N$ is the zero-based `Fin N` index $N-1$.
Existence at each $N\geq3$ follows directly from the frozen
`NearestNeighborFreezingUniqueMinimum.result` and is checked by an
anonymous example, with no additional public theorem.

## Gap

A heuristic approximation at an endpoint does not imply uniform
divergence when its error affects that endpoint's scale. A finite list of
large chain lengths also cannot establish the quantified target.
The literature reading in #11858 is `not-found-in-searched-scope`;
its unverified sources remain explicit below.

## Route

Use zero-based indices and set $R=\xi_{N-1}$ and
$d_k=\xi_k-\xi_{k-1}$ for $1\leq k<N$. A maximum-coordinate comparison
proves uniqueness of increasing solutions locally inside `result`.
Reversal and negation preserve the cyclic equations and the increasing
chamber, so uniqueness gives $\xi_0=-R$; strict increase gives $R>0$.

The prefix sum uses Mathlib's `Fin.partialSum` directly. Summing the
first $k$ equations retains the wrap-around term:

$$
\sum_{i=0}^{k-1}\xi_i=-\frac1{2R}-\frac1{d_k}.
$$

Every prefix coordinate is at least $-R$, and $1/(2R)>0$, hence
$1/d_k<kR$ and $1/k<Rd_k$. The consecutive gaps sum to $2R$, giving

$$
H_{N-1}=\sum_{k=1}^{N-1}\frac1k<2R^2.
$$

Mathlib's `Real.tendsto_sum_range_one_div_nat_succ_atTop` supplies
harmonic divergence. Choose a harmonic prefix exceeding $2B^2$;
positivity of $R$ rules out $R\leq B$ for every sufficiently large $N$.
The symmetric suffix estimate is unnecessary for this target.

## Falsifier

An unbounded sequence of lengths with increasing cyclic site solutions
whose last coordinates stay below a fixed real $B$ contradicts `result`.
Removing the cyclic wrap-around edge changes the equations and does not
produce a counterexample to this claim. A verified earlier settlement
would invalidate the literature admission premise, without changing the
kernel-checked statement.

## Evidence

The public mathematical surface is the closed proposition `claim` and
the single settling theorem `result : claim`. `gapAt` is a private
consecutive-difference definition; all auxiliary proofs are local haves.
`Sites` and non-vacuity are reused from the frozen chain module.
The accepted axiom boundary is `propext`, `Classical.choice` and
`Quot.sound`. Frozen membership and declaration identities are maintained
by the canonical door. No atom or digestion coverage is used.

## Triage

Tier 1: the explicit last-site question in the 2007 mathematical-physics
paper, under preregistration #11858. Resolution: Proved.
`proof_shape: result: content`; `admission_basis: open-problem-resolution`.
`utility: none`: this is an analytic theorem at arbitrary chain length,
not bounded enumeration, a checker, numerical reduction or a certified
finite instance. Information-escape registration is paused under
CLAUDE.md §3.9.

### What the settlement shows

**Proved in this module:** every fixed real bound is eventually exceeded
by the last site of every strictly increasing solution of the cyclic
equations, at all lengths $N\geq3$. The statement does not assume a
chosen sequence of solutions, an asymptotic approximation, an energy
minimum or any numerical accuracy premise.

**Proved inside `result`:** the decisive estimate is $H_{N-1}<2R^2$,
obtained from the exact cyclic prefix identity and its positive
wrap-around contribution. Reflection supplies endpoint symmetry and
$R>0$. All three steps work for every admissible configuration and
arbitrary chain length; the harmonic estimate is a lower bound, not an
asymptotic equality or an upper bound.

**Open:** sharpness of the harmonic lower bound; a matching upper bound;
the source's inverse-error-function approximation (19) and asymptotic
formulas (20)–(21); and the stronger bound obtained from both prefix and
suffix estimates with $\min(k,N-k)$. None is a separate theorem here.

**Source consequence of the proved assertion:** the geometric radius
$2\xi_N/\pi$ in the quoted interpretation cannot stay bounded as the
number of spins tends to infinity. The paper's qualitative divergence
question is discharged; its claimed endpoint approximation and numerical
fit retain their separate status. The frozen unique-minimum result is
unaffected, and no spectral, partition-function or freezing-limit theorem
is established by this module.

**Open:** weighted equations, different interaction graphs, non-increasing
chambers and the cases $N<3$. The proof supplies no statement for these
altered hypotheses.

## ASSUMED-UNVERIFIED

The statement source is arXiv v1. The journal full text and the 2008 JNMP
review are unverified for an earlier settlement. The source and citation
searches in #11858 are orchestrator-reported, not an additional literature
search by this implementation seat, and do not establish global priority.
Enciso's thesis arXiv:0906.1167 repeats the question; the technique
precedent arXiv:1412.1563 is seat-reported for a different open-boundary
recurrence. Model-family independence of the carriers is
ASSUMED-UNVERIFIED.
