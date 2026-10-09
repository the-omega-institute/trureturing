---
slug: gazeau-2026-problem-4-3-hilbert-realization
bibkey: gazeau2026interlaced
doi: null
url: https://arxiv.org/abs/2609.28511v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/GazeauNormalRealization.result
---

# Gazeau Problem 4.3: no normal Hilbert realization

## Problem

Jean-Pierre Gazeau, *Bi-Oriented Interlaced Matrix Multiplication and an
Operator Factorisation of the Quantum Harmonic Oscillator*, arXiv:2609.28511v1,
Problem 4.3, asks:

> Is D essentially self-adjoint, skew-adjoint, or normal with respect to a natural
> Hilbert-space structure on L2(R) direct sum L2(R)?

The ordinary action on the full complex Schwartz core is
$D_0(f,h)=(xf+i h',-i f'+xh)$. The fixed vector space is the product of the
usual complex Lebesgue L2 spaces, including their almost-everywhere equivalence
classes. A candidate positive Hermitian metric must make that entire vector
space a complete Hilbert space.

## Motivation

`D5/S3/Quantum/Analysis/GazeauNormalRealization.result` excludes a closed,
densely defined self-adjoint, skew-adjoint, or normal extension preserving
every pair of this source graph, for every complete positive Hilbert metric.
An arbitrary algebraic complex-linear equivalence to a complete complex
Hilbert space represents the metric; continuity relative to the standard L2
norm and equivalence of norms are not assumed.

## Gap

[Issue 14380](https://github.com/the-omega-institute/trureturing/issues/14380)
preregisters the exact source question, full quantifiers, Tier 1 classification,
and bounded literature checks before the first Lean invocation. Its source
HTML has SHA-256
`5035cc1bf634fb575b6364bbb2c69722e949ba920c9226390c7efdd4ea32fa4b`.
The accepted checks covered the versioned source, related arXiv metadata,
Crossref near-title results, the published problem index, and repository
sources. No settlement was found in that scope. Related full papers and all
issue bodies were not exhaustively inspected; no worldwide priority claim
follows from these bounded negative findings.

## Route

The existing Gaussian Schwartz construction supplies the actual real
Gaussian. Complex postcomposition gives $g(x)=e^{-x^2/2}$ as a complex
Schwartz map. Real exponential differentiation gives $g'=-xg$ and the
product rule gives $(xg)'=g-x^2g$.

For $c_v=(g,-ig)$ and $c_w=(xg,-ixg)$,
$D_0c_v=0$ and $D_0c_w=c_v$. The transported L2 vector $v$ is nonzero:
$g(0)=1$, the Schwartz-to-L2 map is injective, and the algebraic equivalence
is injective. Full graph containment gives $Tv=0$ and $Tw=v$.

Normality is stated as equality of the two maximal product graph relations:
for every $x,z$, there exists $y$ with $(x,y)$ in the graph of $T$ and
$(y,z)$ in the graph of $T^*$ if and only if there exists $y$ with
$(x,y)$ in the graph of $T^*$ and $(y,z)$ in the graph of $T$. These
existentials impose the actual product domains.

At $(v,0)$ this gives $T^*v=a$, with $a$ in the domain of $T$ and
$Ta=0$. The adjoint identity yields
$\langle a,a\rangle=\langle v,Ta\rangle=0$, so $a=0$. At $w$ it then
yields $\langle v,v\rangle=\langle a,w\rangle=0$, contradicting $v\ne0$.
The literal self-adjoint and skew-adjoint alternatives directly imply
$T^*v=\pm Tv=0$ and give the same contradiction. Equality of partial maps
includes equality of their domains.

## Falsifier

A changed source action, a core omitting either displayed Gaussian pair,
a quotient killing the nonzero Gaussian class, or a product normality
condition that omits its domain equality would change the target. The
formal statement uses the full source graph, actual L2 classes, all
algebraic transports, actual density, closed graph, and maximal product
relations, without any of those substitutions.

## Evidence

The exact theorem compiles with Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` through the canonical cache guard.
Its axiom closure is exactly `{propext, Classical.choice, Quot.sound}`.
The only direct frozen mathematical supplier is
`D5/S3/Quantum/Analysis/GaussianSchwartz.exists_gaussian_schwartz`, with
module statement identity
`sha256:b411d800128993afb17586dd15cc07b7943852e2c911dbee8d91ff89005c2714`.
Its Apache-2.0 source attribution and license remain at their existing owner.
The Scribe attaches a `Refuted` `OpenProblemResolutionClaim` to `result`.

## Triage

Tier 1; external named question; admission basis `open-problem-resolution`.
The conservative declaration classification is `proof_shape: bind-only`:
existing analytic suppliers and adjoint identities, instantiated locally,
plus algebraic normalization establish the conclusion. No named auxiliary
or companion theorem is added and no escape witness is claimed. Utility is
`none`: this theorem does not deliver a finite computational API.
Information-escape registration is suspended under CLAUDE.md section 3.9.
Independent implementation reviews and canonical admission remain separate
obligations from the scoped kernel result.

### What the settlement shows

- **Kernel proved by result:** the full source action forces a nonzero vector
  in both kernel and range of every extension. Positive definiteness and the
  actual adjoint domains exclude all three adjoint alternatives under every
  quantified Hilbert metric. A change of positive Hilbert metric cannot
  remove the two source graph pairs.
- **Ordinary consequence of result:** a genuine self-adjoint or skew-adjoint
  graph closure containing the source graph is excluded. This implication
  uses actual closed graph containment; no bare closure value with a junk
  fallback is used as a certificate.
- **Open here:** closed nonnormal realizations, Problem 4.4 on closed
  interlaced factorization, and distributional eigenoperator questions are
  unaffected. Their operations or target spaces differ from this result.
- **Outside the theorem:** indefinite or degenerate metrics, modified
  actions or domains, and quotients of the fixed source vector space.

## ASSUMED-UNVERIFIED

No closability or density of the Schwartz core for an arbitrary transported
metric is asserted. No separate essential-adjointness or standard-metric
closability theorem is delivered. The literature boundary remains the
bounded source qualification above.
