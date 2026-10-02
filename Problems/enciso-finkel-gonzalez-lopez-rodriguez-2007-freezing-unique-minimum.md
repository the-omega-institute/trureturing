---
slug: enciso-finkel-gonzalez-lopez-rodriguez-2007-freezing-unique-minimum
bibkey: enciso2007nearestneighbor
doi: 10.1016/j.nuclphysb.2007.07.001
url: https://arxiv.org/abs/0704.3046v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.result
---

# Unique minimum of the nearest-neighbor QES chain potential

## Problem

A. Enciso, F. Finkel, A. González-López and M. A. Rodríguez,
arXiv:0704.3046v1, §3, printed p. 13, after Eqs. (31)–(32), state:

> The first one is the requirement that ξ be the unique minimum of the potential U in the domain C. Although our numerical calculations suggest that this is indeed the case, we have not been able to provide a rigorous proof of this fact.

The chamber is $C=\{x\in\mathbb R^N:x_1<\cdots<x_N\}$ from Eq. (10).
With cyclic indices $x_0=x_N$ and $x_{N+1}=x_1$, Eq. (31) is

$$
U(x)=\sum_i x_i^2+\sum_i\frac{2}{(x_i-x_{i+1})^2}
     +\sum_i\frac{2}{(x_i-x_{i-1})(x_i-x_{i+1})}.
$$

The sites obey Eq. (6),
$\xi_i=1/(\xi_i-\xi_{i-1})+1/(\xi_i-\xi_{i+1})$.
Issue #11857 fixes the settlement for every natural $N\geq3$, with
existence of an increasing site configuration and equality only there.

## Motivation

`D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.result`
proves the preregistered claim: for every $N\geq3$ there is an increasing
site configuration $\xi$, and every increasing $x$ satisfies
$U(x)\geq U(\xi)$, with equality implying $x=\xi$.
This supplies the uniqueness premise identified by the source as the first
limitation of the usual freezing-trick argument.

## Gap

The source identifies an absolute minimum and the value $2N$, but states
that it lacks a rigorous proof of uniqueness. The target includes every
increasing comparison configuration at every length $N\geq3$; a local
minimum, a numerical approximation or a bounded list of lengths would
not settle it. The literature status in #11857 is
`not-found-in-searched-scope`, with the unread sources listed below.

## Route

Put $g_i(x)=1/(x_i-x_{i-1})+1/(x_i-x_{i+1})$ and
$F_i(x)=x_i-g_i(x)$. Cyclic edge pairing gives
$\sum_i x_i g_i(x)=N$. Expanding the interaction terms yields

$$
U(x)=2N+\sum_i F_i(x)^2
$$

on the increasing chamber. The square completion is a local `have` in
`result`, corresponding to preregistered step 2 and the public-conclusion
form (2) of the escape witness.

The private theorem `existence`, preregistered step 4 and witness form (1),
constructs an increasing site configuration by maximizing

$$
P(x)=\left(\prod_i|x_i-x_{i+1}|\right)
     \exp\left(-\frac12\sum_i x_i^2\right).
$$

Gaussian decay supplies a maximum on the closed monotone chamber. A
positive value at a strictly increasing point excludes its boundary;
coordinate derivatives of its logarithm give the site equations.
Uniqueness of the increasing site configuration is a local step in
`result`, with no separate declaration. For two increasing configurations,
each corresponding cyclic-gap product is positive, and cyclic pairing of
their site equations forces the sum of squared coordinate differences to
vanish. The square completion then proves the minimum and its uniqueness.

## Falsifier

A length $N\geq3$ with no increasing site configuration, a strictly
increasing $x$ below its potential value, or a distinct increasing $x$
with the same value would contradict `result`. The proof retains the
cyclic wrap-around edge and both interaction sums. A verified earlier
settlement would invalidate the literature-based admission premise,
without changing the kernel-checked statement.

## Evidence

The canonical module imports pinned
`Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`. Its public
surface is exactly the definitions `Sites`, `U`, `claim` and the single
theorem `result : claim`. The private theorem `existence` is retained;
all uniqueness and square-completion steps are local to `result`.
The axiom boundary is `propext`, `Classical.choice` and `Quot.sound`.
Declaration identities and frozen membership are maintained by the
canonical door; no atom or digestion coverage is used.

## Triage

Tier 1: the explicit unproved claim in the 2007 mathematical-physics
paper, under preregistration #11857. Resolution: Proved.
`proof_shape: result: content; existence: content`.
`admission_basis: open-problem-resolution`; `utility: none` because this
is an analytic theorem at arbitrary chain length, rather than a finite
computation or certified instance.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

**Proved in this module:** every length $N\geq3$ has an increasing
solution of the cyclic site equations, and that configuration is the
unique global minimum of the specified potential in the increasing chamber.

**Proved inside `result`:** the decisive square completion
$U=2N+\sum_i F_i^2$ makes $2N$ a sharp lower bound, attained at the site
configuration. Equality forces every residual $F_i$ to vanish. The local
uniqueness step then identifies the configuration; it is not an additional
public theorem or an additional escape witness.

**Source consequence, not a spectral theorem proved here:** the first
limitation on the freezing-trick argument quoted on p. 13 has its
uniqueness premise discharged for $N\geq3$. The source's second limitation,
that the dynamical models are only quasi-exactly solvable and their full
spectra are needed, remains. No partition-function limit, spectral
completeness or eigenfunction-localization theorem is claimed by this module.

**Open:** divergence of the last site as $N\to\infty$ (the separate
candidate #11858); extensions to other chambers, interaction graphs,
weights or smaller chain lengths. These require separate statements and
proofs and are outside this settlement.

## ASSUMED-UNVERIFIED

The checked statement source is the arXiv v1 PDF. The journal full text
and the 2008 JNMP review have not been read for preservation or settlement
of this claim. The bounded literature searches in #11857 do not establish
global absence of an earlier proof or priority. The Hamiltonians and the
freezing-trick spectral argument are not formalized here. Model-family
independence of the seat carriers is ASSUMED-UNVERIFIED.
