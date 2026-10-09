---
slug: lichtenfelz-modin-preston-2026-zeitlin-ricci-limit
bibkey: lichtenfelz2026zeitlin
doi: 10.1007/s00220-025-05533-w
url: https://arxiv.org/abs/2508.09833v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.result
---

# The averaged Zeitlin Ricci curvature tends to minus half of the harmonic number minus one

## Problem

L. Lichtenfelz, K. Modin and S. C. Preston, *Ricci curvature for hydrodynamics on the sphere*,
arXiv:2508.09833v1; Commun. Math. Phys. 407, 37 (2026), Section 2.2, Conjecture 2: "For each fixed
$\ell > 1$, the averaged Ricci curvature $\tilde r_\ell(N)$ of the Zeitlin metric on $SU(N)$ becomes
negative for sufficiently large $N$, and in the limit $\tilde r_\ell(N)\to-(H_\ell-1)/2$, as $N\to\infty$."
Here $\tilde r_\ell(N)=(r_\ell(N)^+-r_\ell(N)^-)/(N^2-1)$ with $r_\ell(N)^\pm$ the finite sums of squared
Wigner 6j symbols $\{\ell\,k\,k';\,s\,s\,s\}$, $s=(N-1)/2$, over $1\le k,k'<N$ with $k+k'+\ell$ odd, in
eq. (2.4). The verbatim statements are in
[the literature note](../Library/FluidDynamics/lichtenfelz2026zeitlin.md).

Issue [#14664](https://github.com/the-omega-institute/trureturing/issues/14664) reads both clauses for
every natural $\ell\ge2$: the limit along $N\to\infty$ and eventual negativity.

## Motivation

The authors interpret negative averaged Ricci curvature in the higher eigenspaces as a geometric
mechanism for the mixing observed in two-dimensional hydrodynamics, with positive curvature only in the
lowest modes. Conjecture 2 fixes the exact limiting value behind that interpretation.

## Gap

The source proves the negative part exactly (Theorem 3) under its Conjecture 1, which the repository
proves in [the six-j identities dossier](lichtenfelz-modin-preston-2026-zeitlin-sixj-identities.md), and
gives only an $N$-independent upper bound for the positive part. It states that the conjecture "would
follow by deriving a sharper upper bound for $r_\ell(N)^+$ in order to prove that
$\lim_{N\to\infty}\tilde r_\ell(N)^+=0$", and its remark restricts the cited Brussaard–Tolhoek asymptotics
to even parity. Issue #14664 records the literature check before any Lean;
`not-found-in-searched-scope`.

## Route

1. *Negative part.* For $2\le\ell<N$, $\tilde r_\ell(N)^-=(H_\ell-1)/2$ exactly, from the sum rules
   (2.11)–(2.13) after splitting the parity condition.
2. *Fixed labels.* For fixed $b,c\ge1$ the odd-parity weighted moment satisfies
   $N\sum_{i:\,i+b+c\text{ odd}}\lambda_i(2i+1)W_N(i,b,c)^2=\tfrac12\big[(\lambda_b+\lambda_c)(1-P_N(b,c))-2\lambda_b\lambda_c/(N^2-1)\big]$
   by the signed and unsigned sum rules (2.11), (2.12) and the terminating Racah expansion of the central
   symbol $\mathcal W_b^c$, whose polynomial $P_N(b,c)$ tends to $1$. Its nonnegative summands give
   $N\,W_N(a,b,c)^2\to0$ for every fixed $a$ with $a+b+c$ odd; a zero label is inadmissible.
3. *Positive part.* Grouping $\tilde r_\ell(N)^+$ by rows $k$, each row tends to $0$ by 2, and away from
   the diagonal row the inverse-Casimir rule (2.10) bounds the row by
   $\lambda_\ell(2k+1)/(\lambda_k|k-\ell|(k+\ell+1))$, summable in $k$; Tannery's theorem gives
   $\tilde r_\ell(N)^+\to0$.
4. The limit is $-(H_\ell-1)/2<0$ for $\ell\ge2$, hence $\tilde r_\ell(N)<0$ eventually.

## Falsifier

An error in the correspondence between the Lean sums and eq. (2.4), or a reading of $\tilde r_\ell$ other
than (2.15). Exact rational evaluation at $\ell=2,3$ for $N$ up to $48$ agrees with the identity in step 1
and with the decay of the positive part.

## Evidence

The canonical source is `D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit.lean`, with public `rPlus`,
`rMinus`, `rTilde`, `claim`, `fixed_labels_odd_tendsto_zero`, `rPlus_tendsto_zero`, `rMinus_eq` and
`result : claim`, on top of the frozen `Racah` and `SumRules` modules. The axiom closure of `result` is
exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` or `native_decide`.
The module statement is `sha256:d6ca83976e5bada997c69c513c2d53a99216b62a284aa77d6d902a196e5c90e8`; `result`
is `sha256:3ec8d9659f5e6b15f371e039f64775d26acff44b3cd9337b08a9b1af9dcddb36` and `claim` is
`sha256:52bc3249893decb35e39b462d1ba0e02fd2e67bf01b44d22908b15611b984a3e`. The frozen `SumRules` module
exposes seven of its local proofs, unchanged, as public lemmas used here (`sixJ_cycle_columns`,
`sixJ_swap_columns`, `sixJ_flip_pair`, `sum_shifted_support`, `central_symbol_is_W`, `channel_center_label`,
`W_swap`); its earlier declarations keep their statement identities.

## Triage

Tier 1 named conjecture of a 2025 paper (published 2026), preregistered in issue #14664 before any Lean.
`theorem`; resolution `proved`.

Proof shape: `result` and `rPlus_tendsto_zero` are content. Their non-binding fact is the summable row
majorant (`rowBound_summable`: $\lVert\mathrm{rowBound}_\ell(k)\rVert\le8\lambda_\ell/(k+1)^2$ for $k\ge2\ell+1$,
compared with the $p$-series), which carries the dominated-convergence step. `fixed_labels_odd_tendsto_zero`
and `rMinus_eq` are bind-only declarations on the live proof path of `result`. Admission basis
`open-problem-resolution` (issue #14664).

Utility is `none`. There is no digestion atom.

### What the proof shows

**Proved by `result`:** for every $\ell\ge2$, $\tilde r_\ell(N)\to-(H_\ell-1)/2$ and $\tilde r_\ell(N)<0$ for
all sufficiently large $N$; the positive part tends to $0$ and the negative part is constant for $N>\ell$.

**Proved inside the derivation:** `fixed_labels_odd_tendsto_zero` gives $N\,W_N(a,b,c)^2\to0$ for every
fixed odd-parity triple. The source's remark after its upper bound for $(\mathcal W^{ij\ell})^2$ observes that the
Brussaard–Tolhoek asymptotics fail when $i+j+\ell$ is odd and that "numerically it seems that a sharper bound
… is possible in the case of $i+j+\ell$ odd, which would help with Conjecture 2, but this requires exploiting
this parity assumption somehow". The parity enters through the sign of the signed sum rule (2.11); the
sharper bound is $o(1/N)$ for each fixed triple, not a uniform rate.

**Argued, not formalized (bounded numerics).** At $\ell=2,3$ the positive part decreases roughly like
$1/N$ ($\tilde r_2^+=0.178,\,0.066,\,0.022,\,0.012$ at $N=8,16,32,48$); the first sizes $N=\ell+1$ have
positive curvature, so negativity is eventual, as stated.

**Open.** The rate of convergence of $\tilde r_\ell(N)^+$ and the threshold $N_0(\ell)$ beyond which
$\tilde r_\ell(N)<0$ (the source reports a sign transition near $\ell/N\approx1/3$).

## ASSUMED-UNVERIFIED

The journal text was not compared sentence by sentence with arXiv v1. The bounded literature check does
not establish exhaustive worldwide novelty, priority, or the absence of an independent proof.
