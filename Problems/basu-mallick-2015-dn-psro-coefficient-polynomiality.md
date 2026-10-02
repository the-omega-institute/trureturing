---
slug: basu-mallick-2015-dn-psro-coefficient-polynomiality
bibkey: basumallick2015dn
doi: 10.1016/j.nuclphysb.2015.06.016
url: https://arxiv.org/abs/1503.08231v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.result
---

# Polynomiality of the coefficients f_{N,k}(q) of the D_N-type spin chain with PSRO

## Problem

B. Basu-Mallick, C. Datta, F. Finkel and A. González-López, *Rational quantum
integrable systems of $D_N$ type with polarized spin reversal operators*,
arXiv:1503.08231v1, Section 3, and Nucl. Phys. B 898 (2015) 53–77,
conjecture:

> Although it is well known that the $q$-binomial coefficient $\qbinom N{k}{q^2}$ in \eq{m40} is indeed an even polynomial in $q$ of degree $2k(N-k)$~\cite{Ci79}, it is not clear whether $f_{N,k}(q)$ is also a polynomial. In fact, we have verified that this is the case for a wide range of values of $N$ and all $k\le N$. We conjecture that this is true in general

Here
$f_{N,k}(q)=\frac{q^{N-k}+q^k}{1+q^N}\,[N,k]_{q^2}$ with
$[N,k]_{q^2}=(q^2)_N/((q^2)_k(q^2)_{N-k})$ and
$(q^2)_j=\prod_{i=1}^j(1-q^{2i})$. The conclusions repeat the conjecture
and record that the authors could not find an analytic proof.

## Motivation

The partition function of the $D_N$-type Polychronakos–Frahm chain with
polarized spin reversal operators is
$\sum_k f_{N,k}(q)\,\mathcal Z_{A,k}(q^2)\,\mathcal Z_{A,N-k}(q^2)$; the
polynomiality of every $f_{N,k}$ makes the partition function a polynomial
and the energies integers. The frozen declaration
`D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.result`
proves the conjecture.

## Gap

Issue #12062 classifies the conjecture as Tier 1 and records the bounded
literature check before any Lean:

- arXiv v1 is the only version;
- the two citing works (arXiv:1704.00635, 1909.12125) and the group's earlier
  arXiv:1402.2759 do not contain $f_{N,k}$;
- searches for the divisibility of $(q^{N-k}+q^k)[N,k]_{q^2}$ by $1+q^N$ and
  for the closed form below returned nothing;
- Guo–Krattenthaler's arXiv:1301.7651 on divisibility of $q$-binomial
  coefficients has no $1+q^n$ divisibility;
- Mathlib has no Gaussian binomials.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer.

## Route

Write $B(a,b)=[a+b,a]_{q^2}$.

1. From $(q^2)_{j+1}=(q^2)_j(1-q^{2(j+1)})$ and
   $(1-q^{2a})+q^{2a}(1-q^{2b})=1-q^{2(a+b)}$, the $q$-Pascal rules
   $B(a,b)=B(a-1,b)+q^{2a}B(a,b-1)$ and $B(a,b)=q^{2b}B(a-1,b)+B(a,b-1)$
   hold for $a,b\ge1$.
2. $B(a,0)=B(0,b)=1$, so induction on $a+b$ shows that $B(a,b)$ is a
   polynomial.
3. Multiplying the first rule by $q^b$ and the second by $q^a$ and adding:
   $(q^b+q^a)B(a,b)=(1+q^{a+b})\bigl(q^bB(a-1,b)+q^aB(a,b-1)\bigr)$.
4. With $a=k$, $b=N-k$:
   $f_{N,k}=q^{N-k}[N-1,k-1]_{q^2}+q^k[N-1,k]_{q^2}$ for $1\le k\le N-1$,
   and $f_{N,0}=f_{N,N}=1$.

## Falsifier

The kernel-checked `result` states that for every $N$ and every $k\le N$
the rational function $f_{N,k}(q)$ equals a polynomial with rational
coefficients. Changing the factor $q^{N-k}+q^k$ or the denominator $1+q^N$
changes the question: for example, $(q^2+1)[3,1]_{q^2}$ is not divisible by
$1+q^3$.

## Evidence

Exact SymPy arithmetic for $1\le N\le30$ and all $k\le N$ (495 cases) finds
$(q^{N-k}+q^k)[N,k]_{q^2}$ divisible by $1+q^N$ with the closed-form
quotient; the controls above leave nonzero remainders (issue #12062).

The canonical source is
`D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.lean`.
Its public declarations are `qPoch`, `qBinom`, `coeffF`, `claim` and
`result`. The frozen module state has statement identity `sha256:0241c12a039aaa8e716e1f022b66016ebd3458100f739e002c8d24cfbe07eb71`. The
result declaration has statement identity `sha256:010c33b475611f182816d2d670bc0a352129d45c0cd373c400092e462d79538c`. The Freeze event is
`sha256:c63a2491ce9833f38880f7d32c664f31656e9ca305dfc3459f343b9b95629521`. It has no project-level frozen prerequisites (pinned Mathlib
only). The proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 published conjecture; resolution `Proved` by
`D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.result`.
`proof_shape: content` (escape witness form (2): the conclusion is produced
by the induction and the identity of steps 2–3);
`admission_basis: open-problem-resolution` (issue #12062). Utility `none`.

### What the proof shows

- **Proved in this module:** $f_{N,k}(q)$ is a polynomial in $q$ for every
  $N$ and $k\le N$.
- **The mechanism:** the two $q$-Pascal rules for base $q^2$ differ by the
  side carrying the factor $q^{2a}$ or $q^{2b}$; weighting them by $q^b$ and
  $q^a$ makes the two weights $1+q^{a+b}$ times $q^b$ and $q^a$, which is
  exactly the denominator of $f_{N,k}$. The conjecture needs no property of
  the spin chain.
- **Model derivation, not formalized:** the closed form of step 4 shows that
  $f_{N,k}$ has nonnegative integer coefficients, since Gaussian binomials
  do; hence the energies of the chain with $m_2>0$ are nonnegative integers,
  as the paper also derives by another route.
- **Computed, not formalized (orchestrator, $N\le20$, 230 cases):** the
  coefficients of $f_{N,k}$ are nonnegative and palindromic, and its degree
  is $2k(N-k)+\max(N-k,k)-N$ for $0<k<N$.
- **Open here:** a combinatorial interpretation of $f_{N,k}$ (for example as
  a generating function of $k$-subsets by a signed or type-$D$ statistic).
- **Unchanged:** the paper's spectra, partition-function formulas and
  statistical results do not depend on the conjecture.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent proof. The Lean kernel verifies the encoded
statement and its axiom closure; correspondence to the external paper,
including the encoding of "polynomial in $q$" as equality in
$\mathbb{Q}(q)$ with the image of a polynomial with rational coefficients,
is checked by reading the source and the definitions.
